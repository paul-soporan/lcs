use std::{
    any::Any,
    collections::{BTreeMap, BTreeSet},
};

use as_variant::as_variant;
use colored::Colorize;
use derive_more::Debug;
use indexmap::IndexMap;
use itertools::Itertools;
use winnow::{
    ascii::{digit0, digit1, space0},
    combinator::{
        alt, delimited, eof, opt, preceded, repeat, separated, separated_foldl1, separated_foldr1,
        separated_pair, terminated,
    },
    error::{
        AddContext, ContextError, ErrMode, ErrorKind, ParserError, StrContext, StrContextValue,
    },
    stream::{Compare, Stream, StreamIsPartial},
    token::{one_of, take_while},
    PResult, Parser, Stateful,
};

use crate::{explanation::Explanation, markdown::Markdown};

use super::{
    substitution::Substitution,
    types::{
        Associativity, Constant, Expression, Formula, FunctionSymbol, PredicateSymbol, Term,
        Variable,
    },
};

#[derive(Debug, Clone)]
pub struct Signature {
    pub functions: IndexMap<String, FunctionSymbol>,
    pub predicates: IndexMap<String, PredicateSymbol>,
    pub is_constant: fn(&str) -> bool,
}

impl Signature {
    pub fn is_name_available(&self, name: &str) -> bool {
        !self.functions.contains_key(name)
            && !self.predicates.contains_key(name)
            && !(self.is_constant)(name)
    }

    fn group_functions_by_precedence(&self) -> BTreeMap<usize, Vec<String>> {
        let mut grouped_functions = BTreeMap::new();
        for (name, symbol) in &self.functions {
            if let &FunctionSymbol::Infix { precedence, .. } = symbol {
                grouped_functions
                    .entry(precedence)
                    .or_insert_with(Vec::new)
                    .push(name.clone());
            }
        }
        grouped_functions
    }
}

#[derive(Debug, Clone, Default)]
pub struct ExpressionSymbols {
    pub functions: BTreeSet<String>,
    pub predicates: BTreeSet<String>,
    pub constants: BTreeSet<Constant>,
    // pub variables_by_scope: BTreeMap<String, BTreeMap<Variable, bool>>,
}

impl ExpressionSymbols {
    pub fn extend(&mut self, other: ExpressionSymbols) {
        self.functions.extend(other.functions);
        self.predicates.extend(other.predicates);
        self.constants.extend(other.constants);

        // for (scope, variables) in other.variables_by_scope {
        //     self.variables_by_scope
        //         .entry(scope)
        //         .or_insert_with(BTreeMap::new)
        //         .extend(variables);
        // }
    }
}

#[derive(Debug)]
struct State<'a> {
    signature: Signature,
    explanation: &'a mut Explanation,
    steps: Vec<String>,
}

type Input<'a> = Stateful<&'a str, State<'a>>;

pub fn parse_substitution(
    input: &str,
    signature: &Signature,
    explanation: &mut Explanation,
) -> Result<Substitution, String> {
    let state = State {
        signature: signature.clone(),
        explanation,
        steps: Vec::new(),
    };
    let mut input = Stateful { input, state };
    terminated(substitution, eof)
        .parse_next(&mut input)
        .map_err(|e| e.into_inner().unwrap().to_string())
}

fn substitution(input: &mut Input) -> PResult<Substitution> {
    delimited(
        spaced('{'),
        separated(0.., substitution_component, spaced(',')).map(|components: Vec<_>| {
            let mut substitution = Substitution {
                name: "σ".to_owned(),
                mapping: IndexMap::new(),
            };
            for (variable, term) in components {
                substitution.mapping.insert(variable, term);
            }
            substitution
        }),
        spaced('}'),
    )
    .parse_next(input)
}

fn substitution_component(input: &mut Input) -> PResult<(Variable, Term)> {
    separated_pair(variable, spaced('←'), term)
        .map(|(variable, term)| (variable, term))
        .parse_next(input)
}

pub fn parse_expression(
    input: &str,
    signature: &Signature,
    explanation: &mut Explanation,
) -> Result<Expression, String> {
    let state = State {
        signature: signature.clone(),
        explanation,
        steps: Vec::new(),
    };
    let mut input = Stateful { input, state };
    terminated(expression, eof)
        .parse_next(&mut input)
        .map_err(|e| e.into_inner().unwrap().to_string())
}

fn expression(input: &mut Input) -> PResult<Expression> {
    alt((formula.map(Expression::Formula), term.map(Expression::Term))).parse_next(input)
}

fn formula(input: &mut Input) -> PResult<Formula> {
    alt((quantified_formula, compound_formula))
        .context(StrContext::Expected(StrContextValue::Description(
            "formula",
        )))
        .parse_next(input)
}

fn base_formula(input: &mut Input) -> PResult<Formula> {
    alt((
        delimited('(', formula, ')'),
        quantified_formula,
        negation,
        predicate_application,
        infix_predicate_application,
    ))
    .context(StrContext::Expected(StrContextValue::Description(
        "formula",
    )))
    .parse_next(input)
}

fn quantified_formula(input: &mut Input) -> PResult<Formula> {
    alt((universal_quantification, existential_quantification)).parse_next(input)
}

fn universal_quantification(input: &mut Input) -> PResult<Formula> {
    preceded(spaced('∀'), (variable, formula))
        .map(|(variable, formula)| Formula::UniversalQuantification(variable, Box::new(formula)))
        .parse_next(input)
}

fn existential_quantification(input: &mut Input) -> PResult<Formula> {
    let predicates = input.state.signature.predicates.clone();

    preceded(spaced('∃'), (opt('!'), variable, formula))
        .map(|(unique, variable, mut formula)| {
            if unique.is_some() {
                if !predicates.contains_key("=") {
                    panic!("Unique quantification requires the equality predicate to be defined");
                }

                formula.relabel_variable(&variable.0, "y");

                Formula::ExistentialQuantification(
                    variable.clone(),
                    Box::new(Formula::UniversalQuantification(
                        Variable("y".to_owned()),
                        Box::new(Formula::Equivalence(
                            Box::new(Formula::PredicateApplication {
                                predicate: "=".to_owned(),
                                arguments: vec![
                                    Term::Variable(Variable("y".to_owned())),
                                    Term::Variable(variable),
                                ],
                                symbol: predicates.get("=").unwrap().clone(),
                            }),
                            Box::new(formula),
                        )),
                    )),
                )
            } else {
                Formula::ExistentialQuantification(variable, Box::new(formula))
            }
        })
        .parse_next(input)
}

fn compound_formula(input: &mut Input) -> PResult<Formula> {
    equivalence.parse_next(input)
}

fn equivalence(input: &mut Input) -> PResult<Formula> {
    separated_foldr1(implication, spaced('⇔'), |left, _, right| {
        Formula::Equivalence(Box::new(left), Box::new(right))
    })
    .parse_next(input)
}

fn implication(input: &mut Input) -> PResult<Formula> {
    separated_foldr1(
        conjunction_or_disjunction,
        spaced('⇒'),
        |left, _, right| Formula::Implication(Box::new(left), Box::new(right)),
    )
    .parse_next(input)
}

fn conjunction_or_disjunction(input: &mut Input) -> PResult<Formula> {
    separated_foldr1(
        base_formula,
        spaced(one_of(['∧', '∨'])),
        |left, operation, right| match operation {
            '∧' => Formula::Conjunction(Box::new(left), Box::new(right)),
            '∨' => Formula::Disjunction(Box::new(left), Box::new(right)),
            _ => unreachable!(),
        },
    )
    .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<Formula> {
    preceded(spaced('¬'), base_formula)
        .map(|f| Formula::Negation(Box::new(f)))
        .parse_next(input)
}

fn predicate_application(input: &mut Input) -> PResult<Formula> {
    let name = predicate_name(input)?;

    let symbol = input.state.signature.predicates.get(&name).unwrap().clone();

    let checkpoint = input.checkpoint();

    let arguments: Vec<Term> = argument_list.parse_next(input)?;
    if !symbol.supports_arity(arguments.len()) {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Many)
            .add_context(
                input,
                &checkpoint,
                StrContext::Label(
                    format!("predicate application for {name} - arity mismatch - expected TODO arguments, got {}", arguments.len()).leak(),
                ),
            )
            .cut());
    }

    Ok(Formula::PredicateApplication {
        predicate: name,
        arguments,
        symbol,
    })
}

fn infix_predicate_application(input: &mut Input) -> PResult<Formula> {
    let predicate_names = input
        .state
        .signature
        .predicates
        .iter()
        .filter_map(|(name, symbol)| match symbol {
            PredicateSymbol::Infix => Some(name),
            _ => None,
        })
        .cloned()
        .collect::<Vec<_>>();

    if predicate_names.is_empty() {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Alt));
    }

    let mut predicate_name_parsers = predicate_names
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let predicate_name_parser = spaced(alt(predicate_name_parsers.as_mut_slice()));

    let symbols = input.state.signature.predicates.clone();

    let mut parser = separated_foldl1(
        term_list.map(|list| (list, Vec::new())),
        predicate_name_parser,
        |(left, mut accumulator), predicate, (right, _)| {
            let mut conjunction = Vec::new();

            for term1 in &left {
                for term2 in &right {
                    conjunction.push(Formula::PredicateApplication {
                        predicate: predicate.to_owned(),
                        arguments: vec![term1.clone(), term2.clone()],
                        symbol: symbols[predicate].clone(),
                    });
                }
            }

            accumulator.extend(conjunction);

            (right, accumulator)
        },
    )
    .verify_map(|(_, accumulator)| {
        if accumulator.len() == 0 {
            None
        } else {
            Some(
                accumulator
                    .into_iter()
                    .reduce(|left, right| Formula::Conjunction(Box::new(left), Box::new(right)))
                    .unwrap(),
            )
        }
    });

    parser.parse_next(input)
}

fn predicate_name(input: &mut Input) -> PResult<String> {
    let predicate_names = input
        .state
        .signature
        .predicates
        .keys()
        .cloned()
        .collect::<Vec<_>>();

    if predicate_names.is_empty() {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Alt));
    }

    let mut predicate_name_parsers = predicate_names
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let mut parser = alt(predicate_name_parsers.as_mut_slice()).map(|name: &str| name.to_owned());
    parser.parse_next(input)
}

fn term_list(input: &mut Input) -> PResult<Vec<Term>> {
    separated(1.., term, spaced(',')).parse_next(input)
}

fn term(input: &mut Input) -> PResult<Term> {
    infix_function_application
        .context(StrContext::Expected(StrContextValue::Description("term")))
        .parse_next(input)
}

fn base_term(input: &mut Input) -> PResult<Term> {
    alt((
        delimited('(', term, ')'),
        vertical_bar_function_application,
        function_application,
        prefix_function_application,
        constant.map(|c| Term::Constant(c)),
        variable.map(|v| Term::Variable(v)),
    ))
    .context(StrContext::Expected(StrContextValue::Description("term")))
    .parse_next(input)
}

fn function_application(input: &mut Input) -> PResult<Term> {
    let name = function_name(input)?;

    let symbol = input.state.signature.functions.get(&name).unwrap().clone();

    let checkpoint = input.checkpoint();

    let arguments: Vec<Term> = argument_list.parse_next(input)?;
    if !symbol.supports_arity(arguments.len()) {
        return Err(
            ErrMode::from_error_kind(input, ErrorKind::Many)
                .add_context(
                    input,
                    &checkpoint,
                    StrContext::Label(
                        format!("function application for {name} - arity mismatch - expected {} arguments, got {}", "", arguments.len()).leak(),
                        // format!("function application for {name} - arity mismatch - expected {} arguments, got {}", symbol.arities.iter().join(" or "), arguments.len()).leak(),
                    ),
                )
        );
    }

    Ok(Term::FunctionApplication {
        function: name,
        arguments,
        symbol,
    })
}

fn vertical_bar_function_application(input: &mut Input) -> PResult<Term> {
    delimited('|', term, '|')
        .map(|term| Term::FunctionApplication {
            function: "||".to_owned(),
            arguments: vec![term],
            symbol: FunctionSymbol::Infix {
                precedence: 0,
                associativity: Associativity::None,
            },
        })
        .parse_next(input)
}

fn invisible_function_application(input: &mut Input) -> PResult<Term> {
    repeat(
        1..,
        spaced(alt((
            delimited('(', term, ')'),
            vertical_bar_function_application,
            function_application,
            constant.verify_map(|c| {
                if c.0.starts_with('-') {
                    None
                } else {
                    Some(Term::Constant(c))
                }
            }),
            variable.map(|v| Term::Variable(v)),
        ))),
    )
    .map(|arguments: Vec<Term>| {
        if arguments.len() == 1 {
            arguments.into_iter().next().unwrap()
        } else {
            arguments
                .into_iter()
                .reduce(|left, right| Term::FunctionApplication {
                    function: "[][]".to_owned(),
                    arguments: vec![left, right],
                    symbol: FunctionSymbol::Infix {
                        precedence: 0,
                        associativity: Associativity::None,
                    },
                })
                .unwrap()
        }
    })
    .parse_next(input)
}

fn prefix_function_application(input: &mut Input) -> PResult<Term> {
    let unary_functions = input
        .state
        .signature
        .functions
        .iter()
        .filter_map(|(name, symbol)| {
            if symbol.supports_arity(1) {
                Some(name)
            } else {
                None
            }
        })
        .cloned()
        .collect::<Vec<_>>();

    if unary_functions.is_empty() {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Alt));
    }

    let mut function_name_parsers = unary_functions
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let function_name_parser = spaced(alt(function_name_parsers.as_mut_slice()));

    let symbols = input.state.signature.functions.clone();

    let mut parser =
        (function_name_parser, base_term).map(|(function, argument)| Term::FunctionApplication {
            function: function.to_owned(),
            arguments: vec![argument],
            symbol: symbols[function].clone(),
        });

    parser.parse_next(input)
}

fn infix_function_application(input: &mut Input) -> PResult<Term> {
    let function_groups = input.state.signature.group_functions_by_precedence();

    let mut last_parser: Box<dyn Parser<_, _, _>> =
        Box::new(alt((invisible_function_application, base_term)));

    for functions in function_groups.values().rev() {
        let associativity = as_variant!(
            input.state.signature.functions.get(&functions[0]).unwrap(),
            FunctionSymbol::Infix { associativity, .. } => associativity
        )
        .unwrap();

        let mut function_names = Vec::new();

        for function in functions {
            let symbol_associativity = as_variant!(input.state.signature.functions.get(function).unwrap(), FunctionSymbol::Infix { associativity, .. } => associativity).unwrap();

            if symbol_associativity != associativity {
                continue;
            }

            function_names.push(function.as_str());
        }

        if function_names.is_empty() {
            continue;
        }

        let function_name_parser = for<'a, 'b> move |input: &'a mut Input<'b>| -> PResult<&'b str> {
            spaced(alt(function_names.as_mut_slice())).parse_next(input)
        };

        let symbols = input.state.signature.functions.clone();

        last_parser = match associativity {
            Associativity::None => Box::new((last_parser, function_name_parser, term).map(
                move |(left, function, right)| Term::FunctionApplication {
                    function: function.to_owned(),
                    arguments: vec![left, right],
                    symbol: symbols[function].clone(),
                },
            )),
            Associativity::Left => Box::new(separated_foldl1(
                last_parser,
                function_name_parser,
                move |left, function, right| Term::FunctionApplication {
                    function: function.to_owned(),
                    arguments: vec![left, right],
                    symbol: symbols[function].clone(),
                },
            )),
            Associativity::Right | Associativity::Full => Box::new(separated_foldr1(
                last_parser,
                function_name_parser,
                move |left, function, right| Term::FunctionApplication {
                    function: function.to_owned(),
                    arguments: vec![left, right],
                    symbol: symbols[function].clone(),
                },
            )),
        }
    }

    last_parser.parse_next(input)
}

fn function_name(input: &mut Input) -> PResult<String> {
    let function_names = input
        .state
        .signature
        .functions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut function_name_parsers = function_names
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let mut parser = alt(function_name_parsers.as_mut_slice()).map(|name: &str| name.to_owned());
    parser.parse_next(input)
}

fn argument_list<'a>(input: &mut Input) -> PResult<Vec<Term>> {
    delimited('(', separated(1.., term, spaced(',')), ')').parse_next(input)
}

fn constant(input: &mut Input) -> PResult<Constant> {
    let original_input = input.input;

    let mut name = alt((
        take_while(1.., char::is_alphanumeric),
        preceded('-', digit1).take(),
    ))
    .parse_next(input)?;
    while !name.is_empty() {
        if (input.state.signature.is_constant)(name) {
            return Ok(Constant(name.to_owned()));
        }
        name = &name[..name.char_indices().last().unwrap().0];
        input.input = &original_input[name.len()..];
    }

    Err(ErrMode::from_error_kind(input, ErrorKind::Many))
}

fn variable(input: &mut Input) -> PResult<Variable> {
    let signature = input.state.signature.clone();

    (one_of(('a'..='z', 'α'..='ω', 'Α'..='Ω')), digit0)
        .verify_map(|(letter, index)| {
            let name = format!("{letter}{index}");
            if signature.is_name_available(&name) {
                Some(Variable(name))
            } else {
                None
            }
        })
        .parse_next(input)
}

fn spaced<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
) -> impl Parser<Input<'a>, T, ContextError> {
    delimited(space0, parser, space0)
}

// fn describe<'a, T: Any>(
//     mut parser: impl Parser<Input<'a>, T, ContextError>,
//     what: &'static str,
// ) -> impl FnMut(&mut Input<'a>) -> PResult<T>
// where
//     T: Debug,
// {
//     move |input| {
//         input.state.explanation.step(format!(
//             "Trying to parse {} at the beginning of '{}'",
//             what.magenta().markdown(),
//             input.blue().markdown()
//         ));

//         let mut explanation = input.state.explanation.clone();

//         input.state.explanation = explanation.subexplanation(format!("Parsing {}", what));

//         // let mut explanation = mem::take(input.state.explanation);
//         // let subexplanation = explanation.subexplanation("");

//         // input.state.explanation = subexplanation;
//         let result = parser.parse_next(input);

//         input.state.explanation = &mutexplanation;

//         input.state.explanation.step(match &result {
//             Ok(result) => format!(
//                 "=> {}",
//                 format!("{}", {
//                     let result_any = result as &dyn Any;
//                     // if let Some(p) = result_any.downcast_ref::<Proposition>() {
//                     //     let tree_display = p.get_tree().to_string();
//                     //     tree_display
//                     //         .trim_end()
//                     //         .split('\n')
//                     //         .enumerate()
//                     //         .map(|(i, line)| {
//                     //             format!(
//                     //                 "{}{}",
//                     //                 indent(if i == 0 {
//                     //                     0
//                     //                 } else {
//                     //                     unsafe { INDENTATION + INDENT_STEP + 1 }
//                     //                 }),
//                     //                 line
//                     //             )
//                     //         })
//                     //         .collect::<Vec<_>>()
//                     //         .join("\n")
//                     // } else {
//                     //     format!("{:?}", result)
//                     // }
//                     format!("{:?}", result)
//                 })
//                 .green()
//                 .markdown()
//             ),
//             Err(e) => match e {
//                 ErrMode::Backtrack(_) => format!("=> {}", "Backtrack".yellow().markdown()),
//                 ErrMode::Cut(e) => format!(
//                     "=> Fatal parsing error: {}",
//                     e.to_string().replace("\n", "; ").red().markdown()
//                 ),
//                 ErrMode::Incomplete(_) => unimplemented!(),
//             },
//         });

//         result
//     }
// }

fn indent(indentation: usize) -> String {
    " ".repeat(indentation)
}

static mut INDENTATION: usize = 0;
const INDENT_STEP: usize = 2;

fn describe_str(s: impl AsRef<str>) -> String {
    format!("{}{}", indent(unsafe { INDENTATION }), s.as_ref())
}

fn describe<'a, T: Any>(
    mut parser: impl Parser<Input<'a>, T, ContextError>,
    what: &'static str,
) -> impl FnMut(&mut Input<'a>) -> PResult<T>
where
    T: Debug,
{
    move |input| {
        input.state.steps.push(describe_str(format!(
            "Trying to parse {} at the beginning of '{}'",
            what.magenta().markdown(),
            input.blue().markdown()
        )));

        unsafe { INDENTATION += INDENT_STEP };
        let result = parser.parse_next(input);
        unsafe { INDENTATION -= INDENT_STEP };

        input.state.steps.push(describe_str(match &result {
            Ok(result) => format!(
                "=> {}",
                format!("{}", {
                    let result_any = result as &dyn Any;
                    // if let Some(p) = result_any.downcast_ref::<Proposition>() {
                    //     let tree_display = p.get_tree().to_string();
                    //     tree_display
                    //         .trim_end()
                    //         .split('\n')
                    //         .enumerate()
                    //         .map(|(i, line)| {
                    //             format!(
                    //                 "{}{}",
                    //                 indent(if i == 0 {
                    //                     0
                    //                 } else {
                    //                     unsafe { INDENTATION + INDENT_STEP + 1 }
                    //                 }),
                    //                 line
                    //             )
                    //         })
                    //         .collect::<Vec<_>>()
                    //         .join("\n")
                    // } else {
                    //     format!("{:?}", result)
                    // }
                    format!("{:?}", result)
                })
                .green()
                .markdown()
            ),
            Err(e) => match e {
                ErrMode::Backtrack(_) => format!("=> {}", "Backtrack".yellow().markdown()),
                ErrMode::Cut(e) => format!(
                    "=> Fatal parsing error: {}",
                    e.to_string().replace("\n", "; ").red().markdown()
                ),
                ErrMode::Incomplete(_) => unimplemented!(),
            },
        }));

        result
    }
}

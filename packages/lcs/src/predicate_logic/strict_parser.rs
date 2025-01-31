use std::{any::Any, fmt::Debug};

use colored::Colorize;
use winnow::{
    ascii::{digit0, digit1, space0},
    combinator::{alt, delimited, eof, preceded, separated, separated_pair, terminated},
    error::{
        AddContext, ContextError, ErrMode, ErrorKind, ParserError, StrContext, StrContextValue,
    },
    stream::Stream,
    token::{one_of, take_while},
    PResult, Parser, Stateful,
};

use crate::{explanation::Explanation, markdown::Markdown};

use super::{
    parser::Signature,
    types::{Constant, Expression, Formula, Term, Variable},
};

#[derive(Debug)]
struct State {
    signature: Signature,
    explanation: Explanation,
}

type Input<'a> = Stateful<&'a str, State>;

fn final_parser<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
    name: &'static str,
) -> impl FnMut(&'a str, &Signature, &mut Explanation) -> Result<T, String> {
    let mut parser = terminated(parser, eof);

    move |input: &'a str,
          signature: &Signature,
          explanation: &mut Explanation|
          -> Result<T, String> {
        let cloned_explanation = explanation.clone();

        let state = State {
            signature: signature.clone(),
            explanation: cloned_explanation,
        };
        let mut parser_input = Stateful { input, state };
        let result = parser
            .parse_next(&mut parser_input)
            // .map_err(|e| e.into_inner().unwrap().to_string())
            .map_err(|_| format!("Failed to parse {name}: \"{input}\""));

        let _ = std::mem::replace(explanation, parser_input.state.explanation);

        result
    }
}

pub fn parse_expression_strict(
    input: &str,
    signature: &Signature,
    explanation: &mut Explanation,
) -> Result<Expression, String> {
    final_parser(expression, "expression")(input, signature, explanation)
}

fn expression(input: &mut Input) -> PResult<Expression> {
    describe(
        alt((term.map(Expression::Term), formula.map(Expression::Formula))),
        "expression",
    )
    .parse_next(input)
}

fn formula(input: &mut Input) -> PResult<Formula> {
    describe(
        alt((quantified_formula, compound_formula, predicate_application)).context(
            StrContext::Expected(StrContextValue::Description("formula")),
        ),
        "formula",
    )
    .parse_next(input)
}

fn quantified_formula(input: &mut Input) -> PResult<Formula> {
    describe(
        alt((universal_quantification, existential_quantification)),
        "quantified formula",
    )
    .parse_next(input)
}

fn universal_quantification(input: &mut Input) -> PResult<Formula> {
    describe(
        (preceded('∀', variable), formula).map(|(variable, formula)| {
            Formula::UniversalQuantification(variable, Box::new(formula))
        }),
        "universally quantified formula",
    )
    .parse_next(input)
}

fn existential_quantification(input: &mut Input) -> PResult<Formula> {
    describe(
        (preceded('∃', variable), formula).map(|(variable, formula)| {
            Formula::ExistentialQuantification(variable, Box::new(formula))
        }),
        "existentially quantified formula",
    )
    .parse_next(input)
}

fn compound_formula(input: &mut Input) -> PResult<Formula> {
    describe(
        delimited(
            '(',
            alt((negation, conjunction, disjunction, implication, equivalence)),
            ')',
        ),
        "compound formula",
    )
    .parse_next(input)
}

fn implication(input: &mut Input) -> PResult<Formula> {
    describe(
        separated_pair(formula, spaced('⇒'), formula)
            .map(|(left, right)| Formula::Implication(Box::new(left), Box::new(right))),
        "implication",
    )
    .parse_next(input)
}

fn equivalence(input: &mut Input) -> PResult<Formula> {
    describe(
        separated_pair(formula, spaced('⇔'), formula)
            .map(|(left, right)| Formula::Equivalence(Box::new(left), Box::new(right))),
        "equivalence",
    )
    .parse_next(input)
}

fn conjunction(input: &mut Input) -> PResult<Formula> {
    describe(
        separated_pair(formula, spaced('∧'), formula)
            .map(|(left, right)| Formula::Conjunction(Box::new(left), Box::new(right))),
        "conjunction",
    )
    .parse_next(input)
}

fn disjunction(input: &mut Input) -> PResult<Formula> {
    describe(
        separated_pair(formula, spaced('∨'), formula)
            .map(|(left, right)| Formula::Disjunction(Box::new(left), Box::new(right))),
        "disjunction",
    )
    .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<Formula> {
    describe(
        preceded('¬', formula).map(|f| Formula::Negation(Box::new(f))),
        "negation",
    )
    .parse_next(input)
}

fn predicate_application(input: &mut Input) -> PResult<Formula> {
    describe(|input: &mut Input| {
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
    }, "predicate application").parse_next(input)
}

fn predicate_name(input: &mut Input) -> PResult<String> {
    describe(
        |input: &mut Input| {
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

            let mut parser =
                alt(predicate_name_parsers.as_mut_slice()).map(|name: &str| name.to_owned());

            parser.parse_next(input)
        },
        "predicate name",
    )
    .parse_next(input)
}

fn term(input: &mut Input) -> PResult<Term> {
    describe(
        alt((
            function_application,
            constant.map(|c| Term::Constant(c)),
            variable.map(|v| Term::Variable(v)),
        ))
        .context(StrContext::Expected(StrContextValue::Description("term"))),
        "term",
    )
    .parse_next(input)
}

fn function_application(input: &mut Input) -> PResult<Term> {
    describe(|input: &mut Input| {
        let name = function_name(input)?;

        let symbol = input.state.signature.functions.get(&name).unwrap().clone();

        let checkpoint = input.checkpoint();

        let arguments: Vec<Term> = argument_list.parse_next(input)?;
        if !symbol.prefix.contains(&arguments.len()) {
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
    }, "function application").parse_next(input)
}

fn function_name(input: &mut Input) -> PResult<String> {
    describe(
        |input: &mut Input| {
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

            if function_name_parsers.is_empty() {
                return Err(ErrMode::from_error_kind(input, ErrorKind::Alt));
            }

            let mut parser =
                alt(function_name_parsers.as_mut_slice()).map(|name: &str| name.to_owned());
            parser.parse_next(input)
        },
        "function name",
    )
    .parse_next(input)
}

fn argument_list<'a>(input: &mut Input) -> PResult<Vec<Term>> {
    describe(
        delimited('(', separated(0.., term, spaced(',')), ')'),
        "argument list",
    )
    .parse_next(input)
}

fn constant(input: &mut Input) -> PResult<Constant> {
    describe(
        |input: &mut Input| {
            let original_input = input.input;

            let mut name = alt((
                take_while(1.., char::is_alphanumeric),
                preceded('-', digit1).take(),
            ))
            .parse_next(input)?;
            while !name.is_empty() {
                if input.state.signature.is_constant(name) {
                    return Ok(Constant(name.to_owned()));
                }
                name = &name[..name.char_indices().last().unwrap().0];
                input.input = &original_input[name.len()..];
            }

            Err(ErrMode::from_error_kind(input, ErrorKind::Many))
        },
        "constant",
    )
    .parse_next(input)
}

fn variable(input: &mut Input) -> PResult<Variable> {
    let signature = input.state.signature.clone();

    describe(
        (one_of(('a'..='z', 'α'..='ω', 'Α'..='Ω')), digit0).verify_map(move |(letter, index)| {
            let name = format!("{letter}{index}");
            if signature.is_name_available(&name) {
                Some(Variable(name))
            } else {
                None
            }
        }),
        "variable",
    )
    .parse_next(input)
}

fn spaced<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
) -> impl Parser<Input<'a>, T, ContextError> {
    delimited(space0, parser, space0)
}

fn describe<'a, T: Any>(
    mut parser: impl Parser<Input<'a>, T, ContextError>,
    what: &'static str,
) -> impl FnMut(&mut Input<'a>) -> PResult<T>
where
    T: Debug,
{
    move |input| {
        let subexplanation = input.state.explanation.subexplanation(format!(
            "Trying to parse {} at the beginning of '{}'",
            what.magenta().markdown(),
            input.cyan().markdown()
        ));

        let mut next_input = Input {
            input: input.input,
            state: State {
                signature: input.state.signature.clone(),
                explanation: subexplanation.clone(),
            },
        };

        let result = parser.parse_next(&mut next_input);

        next_input
            .state
            .explanation
            .with_subexplanation("Result", |explanation| match &result {
                Ok(result) => {
                    let result_any = result as &dyn Any;
                    if let Some(term) = result_any.downcast_ref::<Term>() {
                        explanation.use_tree(term.get_tree());
                    } else if let Some(formula) = result_any.downcast_ref::<Formula>() {
                        explanation.use_tree(formula.get_tree());
                    } else if let Some(expression) = result_any.downcast_ref::<Expression>() {
                        explanation.use_tree(expression.get_tree());
                    } else {
                        explanation.step(format!("{:?}", result));
                    }
                }
                Err(e) => explanation.step(match e {
                    ErrMode::Backtrack(_) => "Backtrack".yellow().markdown(),
                    ErrMode::Cut(e) => format!(
                        "Fatal parsing error: {}",
                        e.to_string().replace("\n", "; ").red().markdown()
                    ),
                    ErrMode::Incomplete(_) => unimplemented!(),
                }),
            });

        let _ = std::mem::replace(subexplanation, next_input.state.explanation);
        input.input = next_input.input;

        result
    }
}

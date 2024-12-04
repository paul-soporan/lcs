use std::{any::Any, fmt::Debug, mem};

use colored::Colorize;
use indexmap::{IndexMap, IndexSet};
use replace_with::replace_with_or_abort;
use winnow::{
    ascii::{digit0, space0},
    combinator::{alt, delimited, preceded, separated, separated_pair},
    error::{
        AddContext, ContextError, ErrMode, ErrorKind, ParserError, StrContext, StrContextValue,
    },
    stream::Stream,
    token::one_of,
    PResult, Parser, Stateful,
};

use crate::{
    explanation::{self, Explanation},
    markdown::Markdown,
};

#[derive(Debug, Clone)]
pub struct Signature {
    pub functions: IndexMap<String, usize>,
    pub predicates: IndexMap<String, usize>,
    pub constants: IndexSet<String>,
}

#[derive(Debug)]
pub struct Variable(String);

#[derive(Debug)]
pub struct Constant(String);

#[derive(Debug)]
pub enum Term {
    Variable(Variable),
    Constant(Constant),
    FunctionApplication {
        function: String,
        arguments: Vec<Term>,
    },
}

#[derive(Debug)]
pub enum Formula {
    PredicateApplication {
        predicate: String,
        arguments: Vec<Term>,
    },
    Negation(Box<Formula>),
    Conjunction(Box<Formula>, Box<Formula>),
    Disjunction(Box<Formula>, Box<Formula>),
    Implication(Box<Formula>, Box<Formula>),
    Equivalence(Box<Formula>, Box<Formula>),
    UniversalQuantification(Variable, Box<Formula>),
    ExistentialQuantification(Variable, Box<Formula>),
}

#[derive(Debug)]
pub enum Expression {
    Term(Term),
    Formula(Formula),
}

#[derive(Debug)]
struct State<'a> {
    signature: Signature,
    explanation: &'a mut Explanation,
}

type Input<'a> = Stateful<&'a str, State<'a>>;

pub fn parse_expression(
    input: &str,
    signature: Signature,
    explanation: &mut Explanation,
) -> Result<Expression, String> {
    let state = State {
        signature,
        explanation,
    };
    let mut input = Stateful { input, state };
    expression(&mut input).map_err(|e| e.into_inner().unwrap().to_string())
}

fn expression(input: &mut Input) -> PResult<Expression> {
    alt((term.map(Expression::Term), formula.map(Expression::Formula))).parse_next(input)
}

// pub fn parse_formula(input: &str, signature: Signature) -> Formula {
//     let state = State { signature };
//     let mut input = Stateful { input, state };
//     formula(&mut input).unwrap()
// }

fn formula(input: &mut Input) -> PResult<Formula> {
    alt((quantified_formula, compound_formula, predicate_application))
        .context(StrContext::Expected(StrContextValue::Description(
            "formula",
        )))
        .parse_next(input)
}

fn quantified_formula(input: &mut Input) -> PResult<Formula> {
    alt((universal_quantification, existential_quantification)).parse_next(input)
}

fn universal_quantification(input: &mut Input) -> PResult<Formula> {
    (preceded('∀', variable), formula)
        .map(|(variable, formula)| Formula::UniversalQuantification(variable, Box::new(formula)))
        .parse_next(input)
}

fn existential_quantification(input: &mut Input) -> PResult<Formula> {
    (preceded('∃', variable), formula)
        .map(|(variable, formula)| Formula::ExistentialQuantification(variable, Box::new(formula)))
        .parse_next(input)
}

fn compound_formula(input: &mut Input) -> PResult<Formula> {
    delimited(
        '(',
        alt((negation, conjunction, disjunction, implication, equivalence)),
        ')',
    )
    .parse_next(input)
}

fn implication(input: &mut Input) -> PResult<Formula> {
    separated_pair(formula, spaced('⇒'), formula)
        .map(|(left, right)| Formula::Implication(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn equivalence(input: &mut Input) -> PResult<Formula> {
    separated_pair(formula, spaced('⇔'), formula)
        .map(|(left, right)| Formula::Equivalence(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn conjunction(input: &mut Input) -> PResult<Formula> {
    separated_pair(formula, spaced('∧'), formula)
        .map(|(left, right)| Formula::Conjunction(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn disjunction(input: &mut Input) -> PResult<Formula> {
    separated_pair(formula, spaced('∨'), formula)
        .map(|(left, right)| Formula::Disjunction(Box::new(left), Box::new(right)))
        .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<Formula> {
    preceded('¬', formula)
        .map(|f| Formula::Negation(Box::new(f)))
        .parse_next(input)
}

fn predicate_application(input: &mut Input) -> PResult<Formula> {
    let name = predicate_name(input)?;
    let arity = *input.state.signature.predicates.get(&name).unwrap();

    let checkpoint = input.checkpoint();

    let arguments: Vec<Term> = argument_list.parse_next(input)?;
    if arguments.len() != arity {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Many)
            .add_context(
                input,
                &checkpoint,
                StrContext::Label(
                    format!("predicate application for {name} - arity mismatch - expected {arity} arguments, got {}", arguments.len()).leak(),
                ),
            )
            .cut());
    }

    Ok(Formula::PredicateApplication {
        predicate: name,
        arguments,
    })
}

fn predicate_name(input: &mut Input) -> PResult<String> {
    let predicate_names = input
        .state
        .signature
        .predicates
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut predicate_name_parsers = predicate_names
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let mut parser = alt(predicate_name_parsers.as_mut_slice()).map(|name: &str| name.to_owned());
    parser.parse_next(input)
}

// pub fn parse_term(input: &str, signature: Signature) -> Term {
//     let state = State { signature };
//     let mut input = Stateful { input, state };
//     term(&mut input).unwrap()
// }

fn term(input: &mut Input) -> PResult<Term> {
    alt((
        function_application,
        constant.map(|c| Term::Constant(c)),
        variable.map(|v| Term::Variable(v)),
    ))
    .context(StrContext::Expected(StrContextValue::Description("term")))
    .parse_next(input)
}

fn function_application(input: &mut Input) -> PResult<Term> {
    let name = function_name(input)?;
    let arity = *input.state.signature.functions.get(&name).unwrap();

    let checkpoint = input.checkpoint();

    let arguments: Vec<Term> = argument_list.parse_next(input)?;
    if arguments.len() != arity {
        return Err(ErrMode::from_error_kind(input, ErrorKind::Many)
            .add_context(
                input,
                &checkpoint,
                StrContext::Label(
                    format!("function application for {name} - arity mismatch - expected {arity} arguments, got {}", arguments.len()).leak(),
                ),
            )
            .cut());
    }

    Ok(Term::FunctionApplication {
        function: name,
        arguments,
    })
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
    let constants = input.state.signature.constants.clone();
    let mut constant_parsers = constants
        .iter()
        .map(|name| name.as_str())
        .collect::<Vec<_>>();

    let mut parser =
        alt(constant_parsers.as_mut_slice()).map(|name: &str| Constant(name.to_owned()));
    parser.parse_next(input)
}

fn variable(input: &mut Input) -> PResult<Variable> {
    (one_of('a'..='z'), digit0)
        .map(|(letter, index)| Variable(format!("{letter}{index}")))
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

use std::{any::Any, fmt::Debug};

use colored::Colorize;
use winnow::{
    ascii::space0,
    combinator::{alt, cut_err, delimited, eof, preceded, terminated},
    error::{ContextError, ErrMode, StrContext, StrContextValue},
    token::one_of,
    PResult, Parser, Stateful,
};

use crate::{explanation::Explanation, markdown::Markdown};

use super::ast::{Proposition, PropositionalVariable};

#[derive(Debug)]
struct State {
    explanation: Explanation,
}

type Input<'a> = Stateful<&'a str, State>;

const BINARY_LOGICAL_CONNECTIVES: [char; 4] = ['∧', '∨', '⇒', '⇔'];

pub fn parse_proposition_strict(
    input: &str,
    explanation: &mut Explanation,
) -> Result<Proposition, String> {
    final_parser(proposition, "proposition")(input, explanation)
}

fn final_parser<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
    name: &'static str,
) -> impl FnMut(&'a str, &mut Explanation) -> Result<T, String> {
    let mut parser = terminated(parser, eof);

    move |input: &'a str, explanation: &mut Explanation| -> Result<T, String> {
        let cloned_explanation = explanation.clone();

        let state = State {
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

fn proposition(input: &mut Input) -> PResult<Proposition> {
    describe(
        alt((
            compound_proposition,
            propositional_variable.map(|p| p.into()),
        )),
        "proposition",
    )
    .parse_next(input)
}

fn compound_proposition(input: &mut Input) -> PResult<Proposition> {
    delimited(
        '(',
        alt((binary_operation, negation)),
        ')'.context(StrContext::Expected(StrContextValue::Description(
            "closing parenthesis",
        ))),
    )
    .parse_next(input)
}

fn binary_operation(input: &mut Input) -> PResult<Proposition> {
    describe(
        (
            proposition,
            describe(
                cut_err(
                    delimited(space0, one_of(BINARY_LOGICAL_CONNECTIVES), space0).context(
                        StrContext::Expected(StrContextValue::Description(
                            "binary logical connective",
                        )),
                    ),
                ),
                "binary logical connective",
            ),
            cut_err(
                proposition
                    .context(StrContext::Label("right-hand side"))
                    .context(StrContext::Expected(StrContextValue::Description(
                        "proposition",
                    ))),
            ),
        )
            .map(|(left, op, right)| match op {
                '∧' => Proposition::Conjunction(vec![left, right]),
                '∨' => Proposition::Disjunction(vec![left, right]),
                '⇒' => Proposition::Implication(Box::new(left), Box::new(right)),
                '⇔' => Proposition::Equivalence(Box::new(left), Box::new(right)),
                _ => unreachable!("Invalid operator"),
            }),
        "binary operation",
    )
    .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<Proposition> {
    describe(
        preceded(describe('¬', "unary logical connective"), proposition)
            .map(|p| Proposition::Negation(Box::new(p))),
        "negation",
    )
    .parse_next(input)
}

// TODO: Support indices.
fn propositional_variable(input: &mut Input) -> PResult<PropositionalVariable> {
    describe(
        one_of('A'..='Z').map(|name: char| PropositionalVariable(name.to_string())),
        "propositional variable",
    )
    .parse_next(input)
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
                    if let Some(term) = result_any.downcast_ref::<Proposition>() {
                        explanation.use_tree(term.get_tree());
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

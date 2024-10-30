use std::fmt::Debug;

use colored::Colorize;
use winnow::{
    ascii::space0,
    combinator::{alt, cut_err, delimited, preceded},
    error::{ContextError, ErrMode, StrContext, StrContextValue},
    token::one_of,
    PResult, Parser,
};

use crate::ast::{
    BinaryOperation, CompoundProposition, Proposition, PropositionalVariable, UnaryOperation,
};

type Input<'a> = &'a str;

const BINARY_LOGICAL_CONNECTIVES: [char; 4] = ['∧', '∨', '⇒', '⇔'];

pub fn parse(input: &str) -> Result<Proposition, String> {
    let result = proposition.parse(input);
    result.map_err(|e| e.to_string())
}

fn proposition(input: &mut Input) -> PResult<Proposition> {
    describe(
        alt((
            compound_proposition.map(|p| p.into()),
            propositional_variable.map(|p| p.into()),
        )),
        "proposition",
    )
    .parse_next(input)
}

fn compound_proposition(input: &mut Input) -> PResult<CompoundProposition> {
    delimited(
        '(',
        alt((binary_operation, negation)),
        ')'.context(StrContext::Expected(StrContextValue::Description(
            "closing parenthesis",
        ))),
    )
    .parse_next(input)
}

fn binary_operation(input: &mut Input) -> PResult<CompoundProposition> {
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
            .map(|(left, op, right)| {
                let operation = match op {
                    '∧' => BinaryOperation::Conjunction,
                    '∨' => BinaryOperation::Disjunction,
                    '⇒' => BinaryOperation::Implication,
                    '⇔' => BinaryOperation::Equivalence,
                    _ => unreachable!("Invalid operator"),
                };

                CompoundProposition::BinaryOperation {
                    operation,
                    left,
                    right,
                }
            }),
        "binary operation",
    )
    .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<CompoundProposition> {
    describe(
        preceded(describe('¬', "unary logical connective"), proposition).map(|p| {
            CompoundProposition::UnaryOperation {
                operation: UnaryOperation::Negation,
                proposition: p,
            }
        }),
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

fn indent(indentation: usize) -> String {
    " ".repeat(indentation)
}

static mut INDENTATION: usize = 0;
const INDENT_STEP: usize = 2;

fn describe_str(s: impl AsRef<str>) {
    println!("{}{}", indent(unsafe { INDENTATION }), s.as_ref());
}

fn describe<'a, T>(
    mut parser: impl Parser<Input<'a>, T, ContextError>,
    what: &'static str,
) -> impl FnMut(&mut Input<'a>) -> PResult<T>
where
    T: Debug,
{
    move |input| {
        describe_str(
            format!("Trying to parse a {} at '{}'", what.magenta(), input.blue()).as_str(),
        );

        unsafe { INDENTATION += INDENT_STEP };
        let result = parser.parse_next(input);
        unsafe { INDENTATION -= INDENT_STEP };

        match &result {
            Ok(result) => describe_str(format!("=> {}", format!("{result:?}").green())),
            Err(e) => match e {
                ErrMode::Backtrack(_) => describe_str(format!("=> {}", "Backtrack".yellow())),
                ErrMode::Cut(e) => describe_str(format!(
                    "=> Fatal parsing error: {}",
                    e.to_string().replace("\n", "; ").red()
                )),
                ErrMode::Incomplete(_) => unimplemented!(),
            },
        }

        result
    }
}

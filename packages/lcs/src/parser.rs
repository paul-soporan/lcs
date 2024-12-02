use std::{any::Any, collections::BTreeSet, fmt::Debug};

use colored::Colorize;
use winnow::{
    ascii::{digit0, space0},
    combinator::{
        alt, cut_err, delimited, eof, preceded, separated, separated_foldr1, separated_pair,
        terminated,
    },
    error::{ContextError, ErrMode, StrContext, StrContextValue},
    token::one_of,
    PResult, Parser, Stateful,
};

use crate::{
    ast::{
        BinaryOperation, CompoundProposition, LogicalConsequence, LogicalEquivalence,
        NaryOperation, Proposition, PropositionalVariable, UnaryOperation,
    },
    evaluate::ExplainedValue,
    markdown::Markdown,
    normal_forms::Literal,
};

#[derive(Debug)]
struct State {
    steps: Vec<String>,
}

type Input<'a> = Stateful<&'a str, State>;

fn make_parser<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
    input: &'a str,
) -> ExplainedValue<Result<T, String>> {
    let steps = Vec::new();
    let state = State { steps };
    let mut input = Stateful { input, state };

    let result = terminated(
        parser,
        describe(
            cut_err(
                eof.void()
                    .context(StrContext::Expected(StrContextValue::Description(
                        "end of input",
                    ))),
            ),
            "end of input",
        ),
    )
    .parse_next(&mut input);

    ExplainedValue {
        value: result.map_err(|e| e.to_string()),
        steps: input.state.steps,
    }
}

pub fn parse_clause_set(
    input: &str,
) -> ExplainedValue<Result<BTreeSet<BTreeSet<Literal>>, String>> {
    make_parser(clause_set, input)
}

pub fn parse_clause(input: &str) -> ExplainedValue<Result<BTreeSet<Literal>, String>> {
    make_parser(clause, input)
}

fn clause_set(input: &mut Input) -> PResult<BTreeSet<BTreeSet<Literal>>> {
    delimited('{', separated(0.., clause, spaced(',')), '}').parse_next(input)
}

fn clause(input: &mut Input) -> PResult<BTreeSet<Literal>> {
    delimited('{', separated(0.., literal, spaced(',')), '}').parse_next(input)
}

fn literal(input: &mut Input) -> PResult<Literal> {
    alt((
        describe(
            preceded(
                '¬',
                describe(propositional_variable, "propositional variable"),
            )
            .map(|v| Literal(v, false)),
            "negated literal",
        ),
        describe(
            propositional_variable.map(|v| Literal(v, true)),
            "positive literal",
        ),
    ))
    .parse_next(input)
}

pub fn parse_logical_consequence(
    input: &str,
) -> ExplainedValue<Result<LogicalConsequence, String>> {
    make_parser(logical_consequence, input)
}

pub fn parse_logical_equivalence(
    input: &str,
) -> ExplainedValue<Result<LogicalEquivalence, String>> {
    make_parser(logical_equivalence, input)
}

fn logical_consequence(input: &mut Input) -> PResult<LogicalConsequence> {
    separated_pair(
        separated(0.., proposition, spaced(',')),
        spaced('⊨'),
        proposition,
    )
    .map(|(premises, conclusion)| LogicalConsequence {
        premises,
        conclusion,
    })
    .parse_next(input)
}

fn logical_equivalence(input: &mut Input) -> PResult<LogicalEquivalence> {
    separated_pair(proposition, spaced('∼'), proposition)
        .map(|(left, right)| LogicalEquivalence { left, right })
        .parse_next(input)
}

pub fn parse_proposition(input: &str) -> ExplainedValue<Result<Proposition, String>> {
    make_parser(proposition, input)
}

fn proposition(input: &mut Input) -> PResult<Proposition> {
    describe(equivalence, "proposition").parse_next(input)
}

fn equivalence(input: &mut Input) -> PResult<Proposition> {
    describe(
        separated_foldr1(
            implication,
            spaced(describe('⇔', "equivalence logical connective")),
            |left, _, right| {
                CompoundProposition::BinaryOperation {
                    operation: BinaryOperation::Equivalence,
                    left,
                    right,
                }
                .into()
            },
        ),
        "equivalence",
    )
    .parse_next(input)
}

fn implication(input: &mut Input) -> PResult<Proposition> {
    describe(
        separated_foldr1(
            conjunction_or_disjunction,
            spaced(describe('⇒', "implication logical connective")),
            |left, _, right| {
                CompoundProposition::BinaryOperation {
                    operation: BinaryOperation::Implication,
                    left,
                    right,
                }
                .into()
            },
        ),
        "implication",
    )
    .parse_next(input)
}

fn conjunction_or_disjunction(input: &mut Input) -> PResult<Proposition> {
    describe(
        separated_foldr1(
            base_expression,
            spaced(describe(
                one_of(['∧', '∨']),
                "conjunction or disjunction logical connective",
            )),
            |left, sep, right| {
                let operation = match sep {
                    '∧' => NaryOperation::Conjunction,
                    '∨' => NaryOperation::Disjunction,
                    _ => unreachable!(),
                };

                match right {
                    Proposition::Compound(box CompoundProposition::NaryOperation {
                        operation: r_operation,
                        mut propositions,
                    }) if r_operation == operation => {
                        propositions.insert(0, left);
                        CompoundProposition::NaryOperation {
                            operation: r_operation,
                            propositions,
                        }
                    }

                    _ => CompoundProposition::NaryOperation {
                        operation,
                        propositions: vec![left, right],
                    },
                }
                .into()
            },
        ),
        "conjunction or disjunction",
    )
    .parse_next(input)
}

fn base_expression(input: &mut Input) -> PResult<Proposition> {
    describe(
        alt((
            propositional_variable.map(|v| v.into()),
            parenthesized_expression,
            negation,
            tautology,
            contradiction,
        )),
        "base expression",
    )
    .parse_next(input)
}

fn negation(input: &mut Input) -> PResult<Proposition> {
    describe(
        preceded(
            describe('¬', "negation logical connective"),
            base_expression,
        )
        .map(|p| {
            CompoundProposition::UnaryOperation {
                operation: UnaryOperation::Negation,
                proposition: p,
            }
            .into()
        }),
        "negation",
    )
    .parse_next(input)
}

// TODO: Disallow parenthesized atomic propositions.
fn parenthesized_expression(input: &mut Input) -> PResult<Proposition> {
    describe(
        delimited(
            '(',
            proposition,
            ')'.context(StrContext::Expected(StrContextValue::Description(
                "closing parenthesis",
            ))),
        ),
        "parenthesized expression",
    )
    .parse_next(input)
}

fn tautology(input: &mut Input) -> PResult<Proposition> {
    describe('⊤'.map(|_| Proposition::Tautology), "tautology").parse_next(input)
}

fn contradiction(input: &mut Input) -> PResult<Proposition> {
    describe('⊥'.map(|_| Proposition::Contradiction), "contradiction").parse_next(input)
}

fn propositional_variable(input: &mut Input) -> PResult<PropositionalVariable> {
    describe(
        (one_of('A'..='Z'), digit0)
            .map(|(letter, index)| PropositionalVariable(format!("{letter}{index}"))),
        "propositional variable",
    )
    .parse_next(input)
}

fn spaced<'a, T>(
    parser: impl Parser<Input<'a>, T, ContextError>,
) -> impl Parser<Input<'a>, T, ContextError> {
    delimited(space0, parser, space0)
}

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
                    if let Some(p) = result_any.downcast_ref::<Proposition>() {
                        let tree_display = p.get_tree().to_string();
                        tree_display
                            .trim_end()
                            .split('\n')
                            .enumerate()
                            .map(|(i, line)| {
                                format!(
                                    "{}{}",
                                    indent(if i == 0 {
                                        0
                                    } else {
                                        unsafe { INDENTATION + INDENT_STEP + 1 }
                                    }),
                                    line
                                )
                            })
                            .collect::<Vec<_>>()
                            .join("\n")
                    } else {
                        format!("{:?}", result)
                    }
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

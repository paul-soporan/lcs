use std::{any::Any, collections::BTreeSet, fmt::Debug};

use colored::Colorize;
use winnow::{
    ascii::{digit0, space0},
    combinator::{
        alt, delimited, eof, preceded, separated, separated_foldr1, separated_pair, terminated,
    },
    error::{ContextError, ErrMode, StrContext, StrContextValue},
    token::one_of,
    PResult, Parser, Stateful,
};

use crate::{
    explanation::{Explain, Explanation},
    markdown::Markdown,
    propositional_logic::{
        normal_forms::Literal,
        types::{LogicalConsequence, LogicalEquivalence, Proposition, PropositionalVariable},
    },
};

#[derive(Debug)]
struct State {
    explanation: Explanation,
}

type Input<'a> = Stateful<&'a str, State>;

// fn make_parser<'a, T>(
//     parser: impl Parser<Input<'a>, T, ContextError>,
//     input: &'a str,
// ) -> ExplainedValue<Result<T, String>> {
//     let steps = Vec::new();
//     let state = State { steps };
//     let mut input = Stateful { input, state };

//     let result = terminated(
//         parser,
//         describe(
//             cut_err(
//                 eof.void()
//                     .context(StrContext::Expected(StrContextValue::Description(
//                         "end of input",
//                     ))),
//             ),
//             "end of input",
//         ),
//     )
//     .parse_next(&mut input);

//     ExplainedValue {
//         value: result.map_err(|e| e.to_string()),
//         steps: input.state.steps,
//     }
// }

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

pub fn parse_clause_set(
    input: &str,
    explanation: &mut Explanation,
) -> Result<BTreeSet<BTreeSet<Literal>>, String> {
    final_parser(clause_set, "clause set")(input, explanation)
}

pub fn parse_clause(
    input: &str,
    explanation: &mut Explanation,
) -> Result<BTreeSet<Literal>, String> {
    final_parser(clause, "clause")(input, explanation)
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
    explanation: &mut Explanation,
) -> Result<LogicalConsequence, String> {
    final_parser(logical_consequence, "logical consequence")(input, explanation)
}

pub fn parse_logical_equivalence(
    input: &str,
    explanation: &mut Explanation,
) -> Result<LogicalEquivalence, String> {
    final_parser(logical_equivalence, "logical equivalence")(input, explanation)
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

pub fn parse_proposition(
    input: &str,
    explanation: &mut Explanation,
) -> Result<Proposition, String> {
    final_parser(proposition, "proposition")(input, explanation)
}

fn proposition(input: &mut Input) -> PResult<Proposition> {
    describe(equivalence, "proposition").parse_next(input)
}

fn equivalence(input: &mut Input) -> PResult<Proposition> {
    describe(
        separated_foldr1(
            implication,
            spaced(describe('⇔', "equivalence logical connective")),
            |left, _, right| Proposition::Equivalence(Box::new(left), Box::new(right)),
        ),
        "equivalence or formula without equivalences",
    )
    .parse_next(input)
}

fn implication(input: &mut Input) -> PResult<Proposition> {
    describe(
        separated_foldr1(
            conjunction_or_disjunction,
            spaced(describe('⇒', "implication logical connective")),
            |left, _, right| Proposition::Implication(Box::new(left), Box::new(right)),
        ),
        "implication or formula without implications or equivalences",
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
            |left, sep, right| match (sep, right) {
                ('∧', Proposition::Conjunction(mut propositions)) => {
                    propositions.insert(0, left);
                    Proposition::Conjunction(propositions)
                }

                ('∨', Proposition::Disjunction(mut propositions)) => {
                    propositions.insert(0, left);
                    Proposition::Disjunction(propositions)
                }

                ('∧', right) => Proposition::Conjunction(vec![left, right]),

                ('∨', right) => Proposition::Disjunction(vec![left, right]),

                _ => unreachable!("Invalid logical connective"),
            },
        ),
        "conjunction or disjunction or formula without binary/n-ary logical connectives",
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
        .map(|p| Proposition::Negation(Box::new(p))),
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

fn describe<'a, T: Any>(
    mut parser: impl Parser<Input<'a>, T, ContextError>,
    what: &'static str,
) -> impl FnMut(&mut Input<'a>) -> PResult<T>
where
    T: Debug,
{
    move |input| {
        let input_str = input.input;

        let subexplanation = input.state.explanation.subexplanation(|| {
            format!(
                "Trying to parse {} at the beginning of '{}'",
                what.magenta().markdown(),
                input_str.cyan().markdown()
            )
        });

        let mut next_input = Input {
            input: input.input,
            state: State {
                explanation: subexplanation.clone(),
            },
        };

        let result = parser.parse_next(&mut next_input);

        next_input.state.explanation.with_subexplanation(
            || "Result",
            |explanation| match &result {
                Ok(result) => {
                    let result_any = result as &dyn Any;
                    if let Some(term) = result_any.downcast_ref::<Proposition>() {
                        explanation.use_tree(term.get_tree());
                    } else {
                        explanation.step(|| format!("{:?}", result));
                    }
                }
                Err(e) => explanation.step(|| match e {
                    ErrMode::Backtrack(_) => "Backtrack".yellow().markdown(),
                    ErrMode::Cut(e) => format!(
                        "Fatal parsing error: {}",
                        e.to_string().replace("\n", "; ").red().markdown()
                    ),
                    ErrMode::Incomplete(_) => unimplemented!(),
                }),
            },
        );

        let _ = std::mem::replace(subexplanation, next_input.state.explanation);
        input.input = next_input.input;

        result
    }
}

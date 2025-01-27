use std::fmt::Display;

use colored::Colorize;
use indexmap::IndexMap;

use crate::{evaluate::TruthValue, explanation::Explanation, markdown::Markdown};

use super::parser::{Formula, Term};

#[derive(Debug)]
pub struct Function<D> {
    pub name: String,
    pub arity: usize,
    pub function: fn(&[D]) -> D,
}

#[derive(Debug)]
pub struct Predicate<D> {
    pub name: String,
    pub arity: usize,
    pub predicate: fn(&[D]) -> bool,
}

#[derive(Debug)]
pub struct Interpretation<D> {
    pub functions: IndexMap<String, Function<D>>,
    pub predicates: IndexMap<String, Predicate<D>>,
    pub constants: IndexMap<String, D>,
}

impl<D: Display> Display for Interpretation<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<pre>")?;

        for (name, function) in &self.functions {
            writeln!(f, "I({}) = '{}'", name, function.name)?;
        }

        for (name, predicate) in &self.predicates {
            writeln!(f, "I({}) = '{}'", name, predicate.name)?;
        }

        for (name, constant) in &self.constants {
            writeln!(f, "I({}) = '{}'", name, constant)?;
        }

        writeln!(f, "</pre>")
    }
}

#[derive(Debug)]
pub struct Assignment<D> {
    pub interpretation: Interpretation<D>,
    pub variables: IndexMap<String, D>,
}

impl<D: Display> Display for Assignment<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<pre>")?;

        for (variable, value) in &self.variables {
            writeln!(f, "σ<sub>I</sub>({}) = '{}'", variable, value)?;
        }

        writeln!(f, "</pre>")
    }
}

impl Term {
    pub fn evaluate<D: Clone + Display>(
        &self,
        assignment: &Assignment<D>,
        explanation: &mut Explanation,
    ) -> D {
        explanation.step(format!(
            "υ<sub>σ<sub>I</sub></sub>({})",
            self.to_relaxed_syntax(None).green().markdown()
        ));

        let result = match self {
            Term::Variable(variable) => {
                explanation.step(format!("σ<sub>I</sub>({})", variable.0.blue().markdown()));

                assignment.variables[&variable.0].clone()
            }
            Term::Constant(constant) => {
                explanation.step(format!("I({})", constant.0.blue().markdown()));

                assignment.interpretation.constants[&constant.0].clone()
            }
            Term::FunctionApplication {
                function,
                arguments,
                ..
            } => {
                let function = explanation.with_subexplanation("", |explanation| {
                    explanation.step(format!("I({})", function.magenta().markdown()));

                    let function = assignment.interpretation.functions.get(function).expect(
                        format!(
                            "Function {} is not defined in the interpretation.",
                            function
                        )
                        .as_str(),
                    );

                    explanation.step(format!("'{}'", function.name.magenta().markdown()));

                    function
                });

                let arguments = arguments
                    .iter()
                    .map(|argument| argument.evaluate(assignment, explanation.subexplanation("")))
                    .collect::<Vec<_>>();

                explanation.merge_subexplanations(|subexplanations| match subexplanations {
                    [function, rest @ ..] => format!("{}({})", function, rest.join(", ")),
                    _ => unimplemented!(),
                });

                (function.function)(&arguments)
            }
        };

        explanation.step(format!("'{}'", result.to_string().red().markdown()));

        result
    }
}

impl Formula {
    pub fn evaluate<D: Clone + Display>(
        &self,
        assignment: &Assignment<D>,
        explanation: &mut Explanation,
    ) -> TruthValue {
        explanation.step(format!(
            "υ<sub>σ<sub>I</sub></sub>({})",
            self.to_relaxed_syntax(None).green().markdown()
        ));

        let result = match self {
            Formula::Tautology => TruthValue(true),
            Formula::Contradiction => TruthValue(false),
            Formula::PredicateApplication {
                predicate,
                arguments,
                ..
            } => {
                let predicate = explanation.with_subexplanation("", |explanation| {
                    explanation.step(format!("I({})", predicate.magenta().markdown()));

                    let predicate = assignment.interpretation.predicates.get(predicate).expect(
                        format!(
                            "Predicate {} is not defined in the interpretation.",
                            predicate
                        )
                        .as_str(),
                    );

                    explanation.step(format!("'{}'", predicate.name.magenta().markdown()));

                    predicate
                });

                let arguments = arguments
                    .iter()
                    .map(|argument| argument.evaluate(assignment, explanation.subexplanation("")))
                    .collect::<Vec<_>>();

                explanation.merge_subexplanations(|subexplanations| match subexplanations {
                    [predicate, rest @ ..] => format!("{}({})", predicate, rest.join(", ")),
                    _ => unimplemented!(),
                });

                TruthValue((predicate.predicate)(&arguments))
            }

            Formula::Negation(formula) => {
                let value = formula.evaluate(assignment, explanation);
                TruthValue(!value.0)
            }

            Formula::Conjunction(left, right) => {
                let left = left.evaluate(assignment, explanation);
                let right = right.evaluate(assignment, explanation);
                TruthValue(left.0 && right.0)
            }

            Formula::Disjunction(left, right) => {
                let left = left.evaluate(assignment, explanation);
                let right = right.evaluate(assignment, explanation);
                TruthValue(left.0 || right.0)
            }

            Formula::Implication(left, right) => {
                let left = left.evaluate(assignment, explanation);
                let right = right.evaluate(assignment, explanation);
                TruthValue(!left.0 || right.0)
            }

            Formula::Equivalence(left, right) => {
                let left = left.evaluate(assignment, explanation);
                let right = right.evaluate(assignment, explanation);
                TruthValue(left.0 == right.0)
            }

            Formula::UniversalQuantification(_, _) | Formula::ExistentialQuantification(_, _) => {
                unimplemented!()
            }
        };

        explanation.step(format!("'{}'", result.to_string().red().markdown()));

        result
    }
}

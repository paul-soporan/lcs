use std::collections::{BTreeMap, BTreeSet, HashSet};

use colored::Colorize;
use indexmap::IndexSet;
use replace_with::replace_with_or_abort;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{Clause, ClauseSet, IntLiteral},
        evaluate::{Interpretation, TruthValue},
    },
};

use super::{
    resolution::apply_resolution_step,
    solve::{Solve, SolverResult},
};

#[derive(Debug)]
pub struct DpResult {
    value: bool,
    satisfiable: bool,
    engine: DpEngine,
}

impl SolverResult for DpResult {
    fn value(&self) -> bool {
        self.value
    }

    fn step_count(&self) -> usize {
        0
    }

    fn flip_value(&mut self) {
        self.value = !self.value;
    }

    fn build_interpretation(&self, explanation: &mut impl Explain) -> Option<Interpretation> {
        if self.satisfiable {
            Some(self.engine.build_satisfying_interpretation(explanation))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct DpSolver {}

impl DpSolver {
    pub fn new() -> Self {
        Self {}
    }
}

impl Solve for DpSolver {
    type Result = DpResult;

    fn solve(&self, clause_set: ClauseSet, explanation: &mut impl Explain) -> DpResult {
        let mut engine = DpEngine::new(clause_set);
        let value = engine.apply_dp(explanation);

        DpResult {
            value,
            satisfiable: value,
            engine,
        }
    }
}

#[derive(Debug)]
struct DpEngine {
    clauses: IndexSet<Clause>,
    required_literals: HashSet<IntLiteral>,
}

impl DpEngine {
    fn new(clause_set: ClauseSet) -> Self {
        Self {
            clauses: clause_set.clauses,
            required_literals: HashSet::new(),
        }
    }

    fn apply_dp(&mut self, explanation: &mut impl Explain) -> bool {
        let result = explanation.with_subexplanation(
            || "Applying the DP algorithm",
            |explanation| loop {
                let explanation = explanation.subexplanation(|| "DP step");

                explanation.with_subexplanation(
                    || "Current clauses",
                    |explanation| {
                        for (i, clause) in self.clauses.iter().enumerate() {
                            explanation.step(|| {
                                format!(
                                    "{} {}",
                                    format!("({})", i).to_string().magenta().markdown(),
                                    clause.to_string().blue().markdown()
                                )
                            });
                        }
                    },
                );

                if self.clauses.is_empty() {
                    explanation.step(|| {
                        format!(
                            "No clauses left, therefore the formula is {}",
                            "satisfiable".green().markdown()
                        )
                    });
                    return true;
                }

                for clause in &self.clauses {
                    if clause.0.is_empty() {
                        explanation.step(|| {
                            format!(
                                "Found an empty clause, therefore the formula is {}",
                                "unsatisfiable".red().markdown()
                            )
                        });
                        return false;
                    }
                }

                if apply_one_literal_rule(
                    &mut self.clauses,
                    &mut self.required_literals,
                    explanation,
                ) {
                    continue;
                }

                if apply_pure_literal_rule(
                    &mut self.clauses,
                    &mut self.required_literals,
                    explanation,
                ) {
                    continue;
                }

                match apply_resolution_step(&mut self.clauses, explanation) {
                    Some(result) => return result,
                    None => continue,
                }
            },
        );

        explanation.step(|| {
            format!(
                "Result: {}",
                if result {
                    "satisfiable".green().markdown()
                } else {
                    "unsatisfiable".red().markdown()
                },
            )
        });

        result
    }

    pub fn build_satisfying_interpretation(
        &self,
        explanation: &mut impl Explain,
    ) -> Interpretation {
        let clauses = BTreeSet::from_iter(self.clauses.clone());
        let mut interpretation = Interpretation::default();

        explanation.with_subexplanation(|| "Building a satisfying truth valuation", |explanation| {
            for literal in &self.required_literals {
                let literal = literal.to_literal();

                interpretation
                    .0
                    .insert(literal.0.clone(), TruthValue(literal.1));

                explanation.step(|| format!(
                    "Adding {} to the truth valuation",
                    literal.to_string().green().markdown(),
                ));
            }

            'clause: for clause in clauses {
                let explanation = explanation.subexplanation(|| format!(
                    "Checking clause {}",
                    clause.to_string().blue().markdown()
                ));

                for literal in clause.0 {
                    let explanation = explanation.subexplanation(|| format!(
                        "Checking literal {}",
                        literal.to_string().blue().markdown()
                    ));

                    let literal = literal.to_literal();

                    let existing = interpretation.0.get(&literal.0);
                    match existing {
                        Some(value) => {
                            if value.0 == literal.1 {
                                explanation.step(|| "Literal evaluates to true according to the truth valuation, skipping clause");
                                continue 'clause;
                            } else {
                                explanation.step(|| "Literal evaluates to false according to the truth valuation, skipping it");
                                continue;
                            }
                        }
                        None => {
                            explanation
                                .step(|| "Literal is not in the truth valuation, adding it");

                            interpretation
                                .0
                                .insert(literal.0.clone(), TruthValue(literal.1));

                            continue 'clause;
                        }
                    }
                }
            }

            explanation.step(|| format!(
                "Result: {}",
                interpretation.to_string().green().markdown()
            ));
        });

        interpretation
    }
}

pub(super) fn apply_one_literal_rule<T>(
    clauses: &mut T,
    required_literals: &mut HashSet<IntLiteral>,
    explanation: &mut impl Explain,
) -> bool
where
    T: IntoIterator<Item = Clause> + FromIterator<Clause>,
    for<'a> &'a T: IntoIterator<Item = &'a Clause>,
{
    explanation.with_subexplanation(
        || "Trying to apply the one literal rule",
        |explanation| match find_one_literal(&*clauses, explanation) {
            Some(literal) => {
                required_literals.insert(literal);

                replace_with_or_abort(clauses, |clauses| {
                    clauses
                        .into_iter()
                        .enumerate()
                        .filter_map(|(i, mut clause)| {
                            if clause.0.contains(&literal) {
                                explanation.step(|| {
                                    format!(
                                        "Removing clause {} because it contains {}",
                                        format!("({})", i).to_string().magenta().markdown(),
                                        literal.to_string().green().markdown()
                                    )
                                });

                                return None;
                            }

                            let complement = literal.complement();

                            if clause.0.remove(&complement) {
                                explanation.with_subexplanation(
                                    || {
                                        format!(
                                            "Deleting {} from {}",
                                            complement.to_string().red().markdown(),
                                            format!("({})", i).to_string().magenta().markdown(),
                                        )
                                    },
                                    |explanation| {
                                        explanation.step(|| {
                                            format!(
                                                "Result: {}",
                                                clause.to_string().blue().markdown(),
                                            )
                                        });
                                    },
                                );
                            }

                            Some(clause)
                        })
                        .collect()
                });

                true
            }
            None => false,
        },
    )
}

fn find_one_literal(
    clauses: impl IntoIterator<Item = &Clause>,
    explanation: &mut impl Explain,
) -> Option<IntLiteral> {
    explanation.with_subexplanation(
        || "Looking for a one literal clause",
        |explanation| {
            for clause in clauses {
                if clause.0.len() == 1 {
                    explanation.step(|| {
                        format!(
                            "Found a one literal clause: {}",
                            clause.to_string().green().markdown()
                        )
                    });
                    return Some(clause.0.iter().next().copied().unwrap());
                }
            }

            explanation.step(|| "No one literal clause found");
            None
        },
    )
}

pub(super) fn apply_pure_literal_rule<T>(
    clauses: &mut T,
    required_literals: &mut HashSet<IntLiteral>,
    explanation: &mut impl Explain,
) -> bool
where
    T: IntoIterator<Item = Clause> + FromIterator<Clause>,
    for<'a> &'a T: IntoIterator<Item = &'a Clause>,
{
    explanation.with_subexplanation(
        || "Trying to apply the pure literal rule",
        |explanation| match find_pure_literal(&*clauses, explanation) {
            Some(literal) => {
                required_literals.insert(literal);

                replace_with_or_abort(clauses, |clauses| {
                    clauses
                        .into_iter()
                        .enumerate()
                        .filter_map(|(i, clause)| {
                            if clause.0.contains(&literal) {
                                explanation.step(|| {
                                    format!(
                                        "Removing clause {} because it contains {}",
                                        format!("({})", i).to_string().magenta().markdown(),
                                        literal.to_string().green().markdown()
                                    )
                                });
                                None
                            } else {
                                Some(clause)
                            }
                        })
                        .collect()
                });

                true
            }
            None => false,
        },
    )
}

fn find_pure_literal(
    clauses: impl IntoIterator<Item = &Clause>,
    explanation: &mut impl Explain,
) -> Option<IntLiteral> {
    explanation.with_subexplanation(
        || "Looking for a pure literal",
        |explanation| {
            let mut literals = BTreeMap::new();

            for clause in clauses {
                for literal in &clause.0 {
                    let entry = literals
                        .entry(literal.abs())
                        .or_insert_with(|| BTreeSet::new());
                    entry.insert(literal);
                }
            }

            for occurrences in literals.values() {
                if occurrences.len() == 1 {
                    let literal = occurrences.first().copied().unwrap();
                    explanation.step(|| {
                        format!(
                            "Found a pure literal: {}",
                            literal.to_string().green().markdown()
                        )
                    });
                    return Some(literal.clone());
                }
            }

            explanation.step(|| "No pure literal found");
            None
        },
    )
}

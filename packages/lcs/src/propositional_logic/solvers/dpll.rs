use std::collections::HashSet;

use colored::Colorize;
use nohash_hasher::IntSet;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{ClauseSet, IntLiteral},
        evaluate::{Interpretation, TruthValue},
    },
};

use super::{
    dp::{apply_one_literal_rule, apply_pure_literal_rule},
    solve::{Clause, Solve, SolverResult},
};

#[derive(Debug)]
pub struct DpllResult {
    value: bool,
    satisfiable: bool,
    engine: DpllEngine,
}

impl DpllResult {
    pub fn split_count(&self) -> usize {
        self.engine.split_count
    }
}

impl SolverResult for DpllResult {
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

#[derive(Debug, Clone, Copy)]
pub enum DpllBranchingHeuristic {
    First,
    Random,
    Maxo,
}

#[derive(Debug)]
pub struct DpllSolver {
    branching_heuristic: DpllBranchingHeuristic,
}

impl DpllSolver {
    pub fn new(branching_heuristic: DpllBranchingHeuristic) -> Self {
        Self {
            branching_heuristic,
        }
    }
}

impl Solve for DpllSolver {
    type Result = DpllResult;

    fn solve(&self, clause_set: ClauseSet, explanation: &mut impl Explain) -> DpllResult {
        let mut engine = DpllEngine::new(clause_set, self.branching_heuristic);
        let value = engine.apply_dpll(explanation);

        DpllResult {
            value,
            satisfiable: value,
            engine,
        }
    }
}

#[derive(Debug)]
struct DpllEngine {
    // For DPLL, clauses are stored in a Vec - no need for fast search and no risk of duplicates.
    clauses: Vec<Clause>,
    branching_heuristic: DpllBranchingHeuristic,
    required_literals: HashSet<IntLiteral>,
    split_count: usize,
}

impl DpllEngine {
    fn new(clause_set: ClauseSet, branching_heuristic: DpllBranchingHeuristic) -> Self {
        Self {
            clauses: Vec::from_iter(clause_set.clauses),
            branching_heuristic,
            required_literals: HashSet::new(),
            split_count: 0,
        }
    }

    fn choose_literal(&self) -> Option<IntLiteral> {
        match self.branching_heuristic {
            DpllBranchingHeuristic::First => self.clauses[0].0.iter().next().copied(),
            DpllBranchingHeuristic::Random => {
                unimplemented!()
            }
            DpllBranchingHeuristic::Maxo => {
                unimplemented!()
            }
        }
    }

    fn apply_split(&mut self, explanation: &mut impl Explain) -> bool {
        let literal = self.choose_literal().unwrap();

        self.split_count += 1;

        explanation.with_subexplanation(
            || format!("Splitting on {}", literal.to_string().green().markdown()),
            |explanation| {
                let clauses = self.clauses.clone();
                let literals = self.required_literals.clone();

                let positive_literal_clause = Clause(IntSet::from_iter([literal]));
                let positive_literal_clause_string = positive_literal_clause.to_string();

                self.clauses.push(positive_literal_clause);
                self.required_literals.insert(literal);

                let positive_literal_result = self.apply_dpll(explanation.subexplanation(|| {
                    format!(
                        "Branch with clause {}",
                        positive_literal_clause_string.green().markdown()
                    )
                }));
                if positive_literal_result {
                    explanation.step(|| {
                        format!(
                            "Result: {}; no need to check the other branch",
                            "satisfiable".green().markdown()
                        )
                    });
                    return true;
                }

                let negative_literal_clause = Clause(IntSet::from_iter([literal.complement()]));
                let negative_literal_clause_string = negative_literal_clause.to_string();

                self.clauses = clauses;
                self.required_literals = literals;

                self.clauses.push(negative_literal_clause);
                self.required_literals.insert(literal.complement());

                let result = self.apply_dpll(explanation.subexplanation(|| {
                    format!(
                        "Branch with clause {}",
                        negative_literal_clause_string.red().markdown()
                    )
                }));

                explanation.step(|| {
                    format!(
                        "Result: {}",
                        if result {
                            "satisfiable".green().markdown()
                        } else {
                            "unsatisfiable".red().markdown()
                        }
                    )
                });

                result
            },
        )
    }

    fn apply_dpll(&mut self, explanation: &mut impl Explain) -> bool {
        let result = explanation.with_subexplanation(
            || "Applying the DPLL algorithm",
            |explanation| loop {
                let explanation = explanation.subexplanation(|| "DPLL step");

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

                return self.apply_split(explanation);
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
        let mut interpretation = Interpretation::default();

        explanation.with_subexplanation(
            || "Building a satisfying truth valuation",
            |explanation| {
                for literal in &self.required_literals {
                    let literal = literal.to_literal();

                    interpretation
                        .0
                        .insert(literal.0.clone(), TruthValue(literal.1));

                    explanation.step(|| {
                        format!(
                            "Adding {} to the truth valuation",
                            literal.to_string().green().markdown(),
                        )
                    });
                }

                explanation
                    .step(|| format!("Result: {}", interpretation.to_string().green().markdown()));
            },
        );

        interpretation
    }
}

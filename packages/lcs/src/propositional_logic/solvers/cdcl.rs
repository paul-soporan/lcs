use std::collections::HashSet;

use colored::Colorize;
use itertools::Itertools;
use nohash_hasher::IntSet;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{Clause, ClauseSet, IntLiteral},
        evaluate::{Interpretation, TruthValue},
    },
};

use super::{
    dp::apply_one_literal_rule,
    dpll::{choose_literal, BranchingHeuristic},
    solve::{Solve, SolverResult},
};

#[derive(Debug)]
pub struct CdclResult {
    value: bool,
    satisfiable: bool,
    engine: CdclEngine,
}

impl CdclResult {
    pub fn split_count(&self) -> usize {
        self.engine.split_count
    }
}

impl SolverResult for CdclResult {
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
pub struct CdclSolver {
    branching_heuristic: BranchingHeuristic,
}

impl CdclSolver {
    pub fn new(branching_heuristic: BranchingHeuristic) -> Self {
        Self {
            branching_heuristic,
        }
    }
}

impl Solve for CdclSolver {
    type Result = CdclResult;

    fn solve(&self, clause_set: ClauseSet, explanation: &mut impl Explain) -> CdclResult {
        let mut engine = CdclEngine::new(clause_set, self.branching_heuristic);
        let value = engine.apply_cdcl(explanation);

        CdclResult {
            value,
            satisfiable: value,
            engine,
        }
    }
}

#[derive(Debug)]
struct CdclFrame {
    chosen_literal: IntLiteral,
    clauses: Vec<Clause>,
    assignments: HashSet<IntLiteral>,
}

#[derive(Debug)]
struct CdclEngine {
    // For CDCL, clauses are stored in a Vec - no need for fast search and no risk of duplicates.
    clauses: Vec<Clause>,
    history: Vec<CdclFrame>,
    branching_heuristic: BranchingHeuristic,
    initial_literal_count: usize,
    required_literals: HashSet<IntLiteral>,
    split_count: usize,
}

impl CdclEngine {
    fn new(clause_set: ClauseSet, branching_heuristic: BranchingHeuristic) -> Self {
        Self {
            clauses: Vec::from_iter(clause_set.clauses),
            history: Vec::new(),
            initial_literal_count: clause_set.variable_count,
            branching_heuristic,
            required_literals: HashSet::with_capacity(clause_set.variable_count),
            split_count: 0,
        }
    }

    fn apply_cdcl(&mut self, explanation: &mut impl Explain) -> bool {
        let result = explanation.with_subexplanation(
            || "Applying the CDCL algorithm",
            |explanation| loop {
                let explanation = explanation.subexplanation(|| "CDCL step");

                explanation.with_subexplanation(
                    || {
                        format!(
                            "Decision level {}",
                            self.history.len().to_string().blue().markdown(),
                        )
                    },
                    |explanation| {
                        if !self.history.is_empty() {
                            explanation.step(|| {
                                format!(
                                    "Current assignment: {}",
                                    self.history
                                        .last()
                                        .unwrap()
                                        .assignments
                                        .iter()
                                        .map(|literal| literal.to_string())
                                        .join(", ")
                                        .green()
                                        .markdown(),
                                )
                            });
                        }
                    },
                );

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

                let conflicting_literal = apply_one_literal_rule(
                    &mut self.clauses,
                    &mut self.required_literals,
                    explanation.subexplanation(|| "Applying unit propagation"),
                );

                match conflicting_literal {
                    Some(literal) => {
                        if self.history.is_empty() {
                            explanation.step(|| {
                                format!(
                                    "Found an empty clause, therefore the formula is {}",
                                    "unsatisfiable".red().markdown()
                                )
                            });

                            return false;
                        }

                        explanation.step(|| {
                            format!(
                                "Found a conflict with {}",
                                literal.to_string().red().markdown()
                            )
                        });

                        let complement = literal.complement();
                        let mut learned_clause = Clause(IntSet::default());

                        while let Some(CdclFrame {
                            chosen_literal,
                            clauses,
                            assignments,
                        }) = self.history.pop()
                        {
                            learned_clause.0.insert(chosen_literal.complement());

                            if !assignments.contains(&complement) {
                                explanation.step(|| {
                                    format!(
                                        "Learned new clause: {}",
                                        learned_clause.to_string().red().markdown()
                                    )
                                });

                                explanation.step(|| {
                                    format!(
                                        "Jumping back to decision level {}",
                                        self.history.len().to_string().blue().markdown()
                                    )
                                });

                                self.clauses = clauses;
                                self.clauses.push(learned_clause);
                                self.required_literals = assignments;

                                break;
                            }
                        }
                    }

                    None => {
                        if self.clauses.is_empty() {
                            explanation.step(|| {
                                format!(
                                    "No clauses left, therefore the formula is {}",
                                    "satisfiable".green().markdown()
                                )
                            });
                            return true;
                        }

                        let literal = choose_literal(
                            &self.clauses,
                            self.initial_literal_count,
                            self.branching_heuristic,
                        );
                        explanation.step(|| {
                            format!(
                                "Choosing {} to add to assignment",
                                literal.to_string().green().markdown()
                            )
                        });
                        self.history.push(CdclFrame {
                            chosen_literal: literal,
                            clauses: self.clauses.clone(),
                            assignments: self.required_literals.clone(),
                        });

                        self.clauses.push(Clause(IntSet::from_iter([literal])));
                    }
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

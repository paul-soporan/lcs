use std::{collections::HashSet, ops::Neg};

use colored::Colorize;
use nohash_hasher::IntSet;
use rand::Rng;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{Clause, ClauseSet, IntLiteral},
        evaluate::{Interpretation, TruthValue},
    },
};

use super::{
    dp::{apply_one_literal_rule, apply_pure_literal_rule},
    solve::{Solve, SolverResult},
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
    MaxOccurrences,
    MaxOccurrencesMinSize,
    MaxOccurrencesAndComplementMaxOccurrencesMinSize,
    JeroslawWang,
    MaxUnitPropagations,
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
    initial_literal_count: usize,
    required_literals: HashSet<IntLiteral>,
    split_count: usize,
}

impl DpllEngine {
    fn new(clause_set: ClauseSet, branching_heuristic: DpllBranchingHeuristic) -> Self {
        Self {
            clauses: Vec::from_iter(clause_set.clauses),
            initial_literal_count: clause_set.variable_count,
            branching_heuristic,
            required_literals: HashSet::with_capacity(clause_set.variable_count),
            split_count: 0,
        }
    }

    fn choose_literal(&self) -> Option<IntLiteral> {
        type Scores<T> = (T, Vec<(T, T)>);

        let maxo = |clauses: &[&Clause]| {
            let mut max_count = 0;
            let mut occurrences = vec![(0, 0); self.initial_literal_count];

            for clause in clauses {
                for literal in &clause.0 {
                    let value = (literal.abs_value().get() - 1) as usize;

                    if literal.is_positive() {
                        occurrences[value].0 += 1;
                        max_count = max_count.max(occurrences[value].0);
                    } else {
                        occurrences[value].1 += 1;
                        max_count = max_count.max(occurrences[value].1);
                    }
                }
            }

            (max_count, occurrences)
        };

        let moms = |clauses: &[Clause]| {
            let mut minimum_clause_size = usize::MAX;
            let mut minimum_size_clauses = Vec::new();

            for clause in clauses {
                if clause.0.len() < minimum_clause_size {
                    minimum_size_clauses.clear();
                    minimum_size_clauses.push(clause);

                    minimum_clause_size = clause.0.len();
                } else if clause.0.len() == minimum_clause_size {
                    minimum_size_clauses.push(clause);
                }
            }

            maxo(&minimum_size_clauses)
        };

        fn choose_max_score<T: PartialEq>(
            (max_count, occurrences): Scores<T>,
        ) -> Option<IntLiteral> {
            for (i, count) in occurrences.into_iter().enumerate() {
                if count.0 == max_count {
                    return Some(IntLiteral::new((i + 1) as i32));
                }
                if count.1 == max_count {
                    return Some(IntLiteral::new(-((i + 1) as i32)));
                }
            }

            // There will always be at least one clause with at least one literal.
            unreachable!()
        }

        match self.branching_heuristic {
            DpllBranchingHeuristic::First => self.clauses[0].0.iter().next().copied(),
            DpllBranchingHeuristic::Random => {
                // TODO: Initialize the random number generator once and reuse it.
                let mut rng = rand::rng();

                let random_clause_index = rng.random_range(..self.clauses.len());
                let random_clause = &self.clauses[random_clause_index];

                let random_literal_index = rng.random_range(..random_clause.0.len());
                // TODO: Find a way to access the nth element in constant time.
                random_clause.0.iter().nth(random_literal_index).copied()
            }
            DpllBranchingHeuristic::MaxOccurrences => {
                choose_max_score(maxo(&self.clauses.iter().collect::<Vec<_>>()))
            }
            DpllBranchingHeuristic::MaxOccurrencesMinSize => choose_max_score(moms(&self.clauses)),
            DpllBranchingHeuristic::MaxOccurrencesAndComplementMaxOccurrencesMinSize => {
                let (_, mut mams) = maxo(&self.clauses.iter().collect::<Vec<_>>());
                let (_, moms) = moms(&self.clauses);

                let mut max_score = 0;
                for (i, count) in mams.iter_mut().enumerate() {
                    count.0 += moms[i].1;
                    count.1 += moms[i].0;

                    max_score = max_score.max(count.0).max(count.1);
                }

                choose_max_score((max_score, mams))
            }
            DpllBranchingHeuristic::JeroslawWang => {
                let mut scores = vec![(0f32, 0f32); self.initial_literal_count];

                let mut max_score = 0f32;
                for clause in &self.clauses {
                    for literal in &clause.0 {
                        let value = (literal.abs_value().get() - 1) as usize;

                        let delta = (clause.0.len() as f32).neg().exp2();

                        if literal.is_positive() {
                            scores[value].0 += delta;
                            max_score = max_score.max(scores[value].0);
                        } else {
                            scores[value].1 += delta;
                            max_score = max_score.max(scores[value].1);
                        }
                    }
                }

                choose_max_score((max_score, scores))
            }
            DpllBranchingHeuristic::MaxUnitPropagations => {
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

                if apply_one_literal_rule(
                    &mut self.clauses,
                    &mut self.required_literals,
                    explanation,
                ) {
                    return false;
                }

                if self.clauses.is_empty() {
                    explanation.step(|| {
                        format!(
                            "No clauses left, therefore the formula is {}",
                            "satisfiable".green().markdown()
                        )
                    });
                    return true;
                }

                let literal_count = self.initial_literal_count - self.required_literals.len();

                if apply_pure_literal_rule(
                    &mut self.clauses,
                    &mut self.required_literals,
                    literal_count,
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

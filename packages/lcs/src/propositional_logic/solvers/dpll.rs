use std::{fmt::Display, ops::Neg};

use colored::Colorize;
use nohash_hasher::IntSet;
use rand::Rng;
use serde::{Deserialize, Serialize};
use strum::EnumIter;

use crate::{
    explanation::{DiscardedExplanation, Explain},
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DpllStats {
    pub decision_count: usize,
    pub unit_propagation_count: usize,
    pub pure_literal_count: usize,
}

impl SolverResult for DpllResult {
    type Stats = DpllStats;

    fn value(&self) -> bool {
        self.value
    }

    fn flip_value(&mut self) {
        self.value = !self.value;
    }

    fn stats(&self) -> Self::Stats {
        DpllStats {
            decision_count: self.engine.decision_count,
            unit_propagation_count: self.engine.unit_propagation_count,
            pure_literal_count: self.engine.pure_literal_count,
        }
    }

    fn build_interpretation(&self, explanation: &mut impl Explain) -> Option<Interpretation> {
        if self.satisfiable {
            Some(self.engine.build_satisfying_interpretation(explanation))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, EnumIter)]
pub enum DpllBranchingHeuristic {
    First,
    Random,
    MaxOccurrences,
    MaxOccurrencesMinSize,
    MaxOccurrencesAndComplementMaxOccurrencesMinSize,
    JeroslawWang,
    MaxUnitPropagations,
    GreedyMaxUnitPropagations,
    SelectiveMaxUnitPropagations,
}

impl Display for DpllBranchingHeuristic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                DpllBranchingHeuristic::First => "first",
                DpllBranchingHeuristic::Random => "random",
                DpllBranchingHeuristic::MaxOccurrences => "maxo",
                DpllBranchingHeuristic::MaxOccurrencesMinSize => "moms",
                DpllBranchingHeuristic::MaxOccurrencesAndComplementMaxOccurrencesMinSize => {
                    "mams"
                }
                DpllBranchingHeuristic::JeroslawWang => "jw",
                DpllBranchingHeuristic::MaxUnitPropagations => "up",
                DpllBranchingHeuristic::GreedyMaxUnitPropagations => "gup",
                DpllBranchingHeuristic::SelectiveMaxUnitPropagations => "sup",
            }
        )
    }
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
    branching_heuristic: DpllBranchingHeuristic,
    initial_literal_count: usize,

    // For DPLL, clauses are stored in a Vec - no need for fast search and no risk of duplicates.
    clauses: Vec<Clause>,
    assignments: IntSet<IntLiteral>,

    // Stats
    decision_count: usize,
    unit_propagation_count: usize,
    pure_literal_count: usize,
}

impl DpllEngine {
    fn new(clause_set: ClauseSet, branching_heuristic: DpllBranchingHeuristic) -> Self {
        Self {
            branching_heuristic,
            initial_literal_count: clause_set.variable_count,

            clauses: Vec::from_iter(clause_set.clauses),
            assignments: IntSet::with_capacity_and_hasher(
                clause_set.variable_count,
                Default::default(),
            ),

            decision_count: 0,
            unit_propagation_count: 0,
            pure_literal_count: 0,
        }
    }

    fn apply_split(&mut self, explanation: &mut impl Explain) -> bool {
        let literal = choose_literal(
            &self.clauses,
            &self.assignments,
            self.initial_literal_count,
            self.branching_heuristic,
        );

        self.decision_count += 1;

        explanation.with_subexplanation(
            || format!("Splitting on {}", literal.to_string().green().markdown()),
            |explanation| {
                let clauses = self.clauses.clone();
                let assignments = self.assignments.clone();

                let positive_literal_clause = Clause(IntSet::from_iter([literal]));
                let positive_literal_clause_string = positive_literal_clause.to_string();

                self.clauses.push(positive_literal_clause);

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
                self.assignments = assignments;

                self.clauses.push(negative_literal_clause);

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

                let assignment_count = self.assignments.len();

                let conflicting_literal =
                    apply_one_literal_rule(&mut self.clauses, &mut self.assignments, explanation);

                self.unit_propagation_count += self.assignments.len() - assignment_count;

                if conflicting_literal.is_some() {
                    explanation.step(|| {
                        format!(
                            "Found an empty clause, therefore the formula is {}",
                            "unsatisfiable".red().markdown()
                        )
                    });

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

                let literal_count = self.initial_literal_count - self.assignments.len();

                if apply_pure_literal_rule(
                    &mut self.clauses,
                    &mut self.assignments,
                    literal_count,
                    explanation,
                ) {
                    self.pure_literal_count += 1;
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
                for literal in &self.assignments {
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

pub(super) fn choose_literal(
    clauses: &[Clause],
    assignments: &IntSet<IntLiteral>,
    initial_literal_count: usize,
    branching_heuristic: DpllBranchingHeuristic,
) -> IntLiteral {
    let maxo = |clauses: &[&Clause]| {
        let mut max_count = 0;
        let mut occurrences = vec![(0, 0); initial_literal_count];

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

    let count_unit_propagations = |literal: IntLiteral, greedy: bool| {
        let mut literals = IntSet::default();

        let mut clauses = clauses.to_vec();
        clauses.push(Clause(IntSet::from_iter([literal])));

        let conflicting_literal =
            apply_one_literal_rule(&mut clauses, &mut literals, &mut DiscardedExplanation);

        if greedy {
            if conflicting_literal.is_some() || clauses.is_empty() {
                return None;
            }
        }

        return Some(literals.len());
    };

    let max_unit_propagations = |greedy: bool| {
        let mut visited = vec![(false, false); initial_literal_count];

        let mut max_score = 0;
        let mut best_literal = None;
        for clause in clauses {
            for &literal in &clause.0 {
                let value = (literal.abs_value().get() - 1) as usize;
                let visited = if literal.is_positive() {
                    &mut visited[value].0
                } else {
                    &mut visited[value].1
                };

                if !*visited {
                    *visited = true;

                    let score = match count_unit_propagations(literal, greedy) {
                        None => return literal,
                        Some(score) => score,
                    };

                    if max_score < score {
                        max_score = score;
                        best_literal = Some(literal);
                    }
                }
            }
        }

        best_literal.unwrap()
    };

    match branching_heuristic {
        DpllBranchingHeuristic::First => clauses[0].0.iter().next().copied().unwrap(),
        DpllBranchingHeuristic::Random => {
            // TODO: Initialize the random number generator once and reuse it.
            let mut rng = rand::rng();

            let unassigned_literals = (1..=initial_literal_count as i32)
                .filter_map(|i| {
                    let literal = IntLiteral::new(i);
                    if assignments.contains(&literal) || assignments.contains(&literal.complement())
                    {
                        None
                    } else {
                        Some(literal)
                    }
                })
                .collect::<Vec<_>>();

            let random_literal_index = rng.random_range(..unassigned_literals.len());
            let random_literal = unassigned_literals[random_literal_index];

            if rng.random_bool(0.5) {
                random_literal
            } else {
                random_literal.complement()
            }
        }
        DpllBranchingHeuristic::MaxOccurrences => {
            choose_max_score(maxo(&clauses.iter().collect::<Vec<_>>())).unwrap()
        }
        DpllBranchingHeuristic::MaxOccurrencesMinSize => choose_max_score(moms(&clauses)).unwrap(),
        DpllBranchingHeuristic::MaxOccurrencesAndComplementMaxOccurrencesMinSize => {
            let (_, mut mams) = maxo(&clauses.iter().collect::<Vec<_>>());
            let (_, moms) = moms(&clauses);

            let mut max_score = 0;
            for (i, count) in mams.iter_mut().enumerate() {
                count.0 += moms[i].1;
                count.1 += moms[i].0;

                max_score = max_score.max(count.0).max(count.1);
            }

            choose_max_score((max_score, mams)).unwrap()
        }
        DpllBranchingHeuristic::JeroslawWang => {
            let mut scores = vec![(0f32, 0f32); initial_literal_count];

            let mut max_score = 0f32;
            for clause in clauses {
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

            choose_max_score((max_score, scores)).unwrap()
        }
        DpllBranchingHeuristic::MaxUnitPropagations => max_unit_propagations(false),
        DpllBranchingHeuristic::GreedyMaxUnitPropagations => max_unit_propagations(true),
        DpllBranchingHeuristic::SelectiveMaxUnitPropagations => {
            let maxo = choose_literal(
                clauses,
                assignments,
                initial_literal_count,
                DpllBranchingHeuristic::MaxOccurrences,
            );
            let moms = choose_literal(
                clauses,
                assignments,
                initial_literal_count,
                DpllBranchingHeuristic::MaxOccurrencesMinSize,
            );
            let mams = choose_literal(
                clauses,
                assignments,
                initial_literal_count,
                DpllBranchingHeuristic::MaxOccurrencesAndComplementMaxOccurrencesMinSize,
            );
            let jw = choose_literal(
                clauses,
                assignments,
                initial_literal_count,
                DpllBranchingHeuristic::JeroslawWang,
            );

            let literals = IntSet::from_iter([maxo, moms, mams, jw]);

            let mut max_score = 0;
            let mut best_literal = None;

            for literal in literals {
                let score = match count_unit_propagations(literal, true) {
                    None => return literal,
                    Some(score) => score,
                };

                if max_score < score {
                    max_score = score;
                    best_literal = Some(literal);
                }
            }

            best_literal.unwrap()
        }
    }
}

pub(super) type Scores<T> = (T, Vec<(T, T)>);

pub(super) fn choose_max_score<T: PartialEq>(
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

    None
}

use std::{
    collections::{HashSet, VecDeque},
    fmt::Display,
    ops::Neg,
};

use colored::Colorize;
use itertools::Itertools;
use nohash_hasher::{IntMap, IntSet};
use strum::EnumIter;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{Clause, ClauseSet, IntLiteral},
        evaluate::{Interpretation, TruthValue},
    },
};

use super::{
    dpll::choose_max_score,
    solve::{Solve, SolverResult},
};

#[derive(Debug)]
pub struct CdclResult {
    value: bool,
    satisfiable: bool,
    engine: CdclEngine,
}

impl CdclResult {
    pub fn decision_count(&self) -> usize {
        self.engine.decision_count
    }

    pub fn conflict_count(&self) -> usize {
        self.engine.conflict_count
    }

    pub fn propagation_count(&self) -> usize {
        self.engine.propagation_count
    }
}

impl SolverResult for CdclResult {
    fn value(&self) -> bool {
        self.value
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumIter)]
pub enum CdclBranchingHeuristic {
    First,
    JeroslawWang,
    ChaffVsids,
    MiniSatVsids,
}

impl Display for CdclBranchingHeuristic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CdclBranchingHeuristic::First => "first",
                CdclBranchingHeuristic::JeroslawWang => "jw",
                CdclBranchingHeuristic::ChaffVsids => "chaff-vsids",
                CdclBranchingHeuristic::MiniSatVsids => "minisat-vsids",
            }
        )
    }
}

#[derive(Debug)]
pub struct CdclSolver {
    branching_heuristic: CdclBranchingHeuristic,
}

impl CdclSolver {
    pub fn new(branching_heuristic: CdclBranchingHeuristic) -> Self {
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
struct WatchedClause {
    clause: Clause,
    first_watcher: IntLiteral,
    second_watcher: IntLiteral,
}

#[derive(Debug)]
struct AssignmentEntry {
    literal: IntLiteral,
    implicant: Option<Clause>,
}

#[derive(Debug)]
struct CdclEngine {
    // For CDCL, clauses are stored in a Vec - no need for fast search and no risk of duplicates.
    clauses: Vec<WatchedClause>,
    watchers: IntMap<IntLiteral, IntSet<usize>>,
    decision_level: usize,
    assignments: IntSet<IntLiteral>,
    unit_propagate: IntSet<IntLiteral>,
    assignment_stack: Vec<AssignmentEntry>,
    variable_levels: Vec<usize>,
    branching_heuristic: CdclBranchingHeuristic,
    initial_literal_count: usize,

    activity_scores: Vec<(f32, f32)>,

    // Stats
    decision_count: usize,
    conflict_count: usize,
    propagation_count: usize,
}

impl CdclEngine {
    fn new(clause_set: ClauseSet, branching_heuristic: CdclBranchingHeuristic) -> Self {
        let mut engine = Self {
            clauses: Vec::with_capacity(clause_set.clauses.len()),
            watchers: IntMap::default(),
            decision_level: 0,
            assignments: IntSet::with_capacity_and_hasher(
                clause_set.variable_count,
                Default::default(),
            ),
            unit_propagate: IntSet::with_capacity_and_hasher(
                clause_set.variable_count,
                Default::default(),
            ),
            assignment_stack: Vec::with_capacity(clause_set.variable_count),
            variable_levels: vec![0; clause_set.variable_count],
            initial_literal_count: clause_set.variable_count,
            branching_heuristic,

            activity_scores: if matches!(
                branching_heuristic,
                CdclBranchingHeuristic::ChaffVsids | CdclBranchingHeuristic::MiniSatVsids
            ) {
                vec![(0.0, 0.0); clause_set.variable_count]
            } else {
                Vec::new()
            },

            decision_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        };

        clause_set.clauses.into_iter().for_each(|clause| {
            engine.add_clause(clause);
        });

        engine
    }

    fn add_clause(&mut self, clause: Clause) -> bool {
        let index = self.clauses.len();

        let mut iter = clause
            .0
            .iter()
            .filter(|literal| !self.assignments.contains(&literal.complement()))
            .take(2);

        let first_watcher = iter.next().copied().unwrap();
        let second_watcher = match iter.next() {
            Some(literal) => *literal,
            None => {
                self.unit_propagate.insert(first_watcher);
                self.assignments.insert(first_watcher);
                self.assignment_stack.push(AssignmentEntry {
                    literal: first_watcher,
                    implicant: Some(clause.clone()),
                });
                self.variable_levels[first_watcher.abs_value().get() as usize - 1] =
                    self.decision_level;

                match self
                    .assignment_stack
                    .iter()
                    .rev()
                    .find(|entry| clause.0.contains(&entry.literal.complement()))
                    .map(|entry| entry.literal.complement())
                {
                    Some(literal) => literal,
                    None => {
                        return false;
                    }
                }
            }
        };

        self.watchers
            .entry(first_watcher)
            .or_insert_with(IntSet::default)
            .insert(index);
        self.watchers
            .entry(second_watcher)
            .or_insert_with(IntSet::default)
            .insert(index);

        self.clauses.push(WatchedClause {
            clause,
            first_watcher,
            second_watcher,
        });

        return true;
    }

    fn explain_clauses(&self, explanation: &mut impl Explain) {
        explanation.with_subexplanation(
            || "Current clauses",
            |explanation| {
                for (i, clause) in self.clauses.iter().enumerate() {
                    explanation.step(|| {
                        format!(
                            "{} {{{}}} (watchers: {}, {})",
                            format!("({})", i).to_string().magenta().markdown(),
                            clause
                                .clause
                                .0
                                .iter()
                                .map(|literal| {
                                    if self.assignments.contains(literal) {
                                        literal.to_string().green().markdown()
                                    } else if self.assignments.contains(&literal.complement()) {
                                        literal.to_string().red().markdown()
                                    } else {
                                        literal.to_string()
                                    }
                                })
                                .join(", "),
                            clause.first_watcher.to_string().green().markdown(),
                            clause.second_watcher.to_string().green().markdown(),
                        )
                    });
                }
            },
        );
    }

    fn explain_assignment_stack(&self, explanation: &mut impl Explain) {
        explanation.step(|| {
            format!(
                "Assignment stack: {}",
                self.assignment_stack
                    .iter()
                    .map(|entry| format!(
                        "{}:{}:{}",
                        entry.literal.to_string().green().markdown(),
                        self.variable_levels[entry.literal.abs_value().get() as usize - 1]
                            .to_string()
                            .blue()
                            .markdown(),
                        entry
                            .implicant
                            .as_ref()
                            .map(|clause| clause.to_string().red().markdown())
                            .unwrap_or_else(|| "None".to_string().red().markdown())
                    ))
                    .join(", ")
                    .green()
                    .markdown()
            )
        });
    }

    fn unit_propagation(&mut self, explanation: &mut impl Explain) -> Option<Clause> {
        explanation.with_subexplanation(
            || "Applying unit propagation",
            |explanation| {
                self.explain_assignment_stack(explanation);

                explanation.step(|| {
                    format!(
                        "Unit propagating: {}",
                        self.unit_propagate
                            .iter()
                            .map(|literal| literal.to_string())
                            .join(", ")
                            .green()
                            .markdown()
                    )
                });

                let mut queue = VecDeque::from_iter(self.unit_propagate.iter().copied());
                self.unit_propagate.clear();

                while let Some(literal) = queue.pop_front() {
                    let explanation = explanation.subexplanation(|| {
                        format!("Unit literal: {}", literal.to_string().green().markdown())
                    });

                    self.propagation_count += 1;

                    explanation.step(|| {
                        format!(
                            "Queue: {}",
                            queue
                                .iter()
                                .map(|literal| literal.to_string())
                                .join(", ")
                                .green()
                                .markdown()
                        )
                    });

                    self.explain_clauses(explanation);

                    let complement = literal.complement();
                    if let Some(clause_indices) = self.watchers.get(&complement).cloned() {
                        'outer: for i in clause_indices {
                            let clause = &mut self.clauses[i];
                            let (other, complement_ref) = if clause.first_watcher == complement {
                                (clause.second_watcher, &mut clause.first_watcher)
                            } else {
                                (clause.first_watcher, &mut clause.second_watcher)
                            };

                            if self.assignments.contains(&other) {
                                continue;
                            }

                            for &literal in &clause.clause.0 {
                                if literal == complement || literal == other {
                                    continue;
                                }

                                if !self.assignments.contains(&literal.complement()) {
                                    *complement_ref = literal;

                                    self.watchers
                                        .entry(literal)
                                        .or_insert_with(IntSet::default)
                                        .insert(i);

                                    self.watchers.entry(complement).and_modify(|c| {
                                        c.remove(&i);
                                    });

                                    continue 'outer;
                                }
                            }

                            if self.assignments.contains(&other.complement()) {
                                return Some(clause.clause.clone());
                            }

                            self.assignments.insert(other);
                            self.assignment_stack.push(AssignmentEntry {
                                literal: other,
                                implicant: Some(clause.clause.clone()),
                            });
                            self.variable_levels[other.abs_value().get() as usize - 1] =
                                self.decision_level;

                            queue.push_back(other);
                        }
                    }
                }

                None
            },
        )
    }

    fn analyze_conflict(
        &mut self,
        conflict_clause: Clause,
        explanation: &mut impl Explain,
    ) -> (Clause, usize) {
        explanation.with_subexplanation(
            || "Analyzing conflict",
            |explanation| {
                let mut learned_clause = conflict_clause.clone();

                explanation.step(|| {
                    format!(
                        "Conflict clause: {}",
                        learned_clause.to_string().red().markdown()
                    )
                });

                self.explain_assignment_stack(explanation);

                let mut seen = HashSet::new();
                let mut counter = 0;

                for literal in &learned_clause.0 {
                    if seen.contains(&literal.abs()) {
                        continue;
                    }
                    seen.insert(literal.abs());

                    if self.variable_levels[literal.abs_value().get() as usize - 1]
                        == self.decision_level
                    {
                        counter += 1;
                    }
                }

                let mut assignment_stack_iter = self.assignment_stack.iter().rev().peekable();

                loop {
                    let explanation = explanation.subexplanation(|| "Loop iteration");

                    explanation.step(|| {
                        format!(
                            "Learned clause: {}",
                            learned_clause.to_string().red().markdown()
                        )
                    });

                    let assignment_entry = assignment_stack_iter.next().unwrap();
                    if assignment_entry.implicant.is_none() {
                        break;
                    }

                    if self.branching_heuristic == CdclBranchingHeuristic::MiniSatVsids {
                        learned_clause.0.iter().for_each(|literal| {
                            let index = literal.abs_value().get() as usize - 1;

                            if literal.is_positive() {
                                self.activity_scores[index].0 += 1.0;
                            } else {
                                self.activity_scores[index].1 += 1.0;
                            }
                        });
                    }

                    if learned_clause.0.contains(&assignment_entry.literal)
                        || learned_clause
                            .0
                            .contains(&assignment_entry.literal.complement())
                    {
                        let mut resolvent = Clause::default();
                        for &literal in &learned_clause.0 {
                            if literal.abs() != assignment_entry.literal.abs() {
                                resolvent.0.insert(literal);
                            }
                        }

                        let implicant = assignment_entry.implicant.clone().unwrap();

                        explanation.step(|| {
                            format!(
                                "Implicant clause: {}",
                                implicant.to_string().red().markdown()
                            )
                        });

                        for &literal in &implicant.0 {
                            if literal.abs() != assignment_entry.literal.abs() {
                                resolvent.0.insert(literal);
                            }
                        }

                        explanation.step(|| {
                            format!("Resolvent: {}", resolvent.to_string().red().markdown())
                        });

                        learned_clause = resolvent;

                        for literal in &implicant.0 {
                            if seen.contains(&literal.abs()) {
                                continue;
                            }
                            seen.insert(literal.abs());

                            if self.variable_levels[literal.abs_value().get() as usize - 1]
                                == self.decision_level
                            {
                                counter += 1;
                            }
                        }

                        counter -= 1;
                    }

                    if learned_clause
                        .0
                        .iter()
                        .filter(|literal| {
                            self.variable_levels[literal.abs_value().get() as usize - 1]
                                == self.decision_level
                        })
                        .count()
                        == 1
                    {
                        break;
                    }

                    if assignment_stack_iter.peek().unwrap().implicant.is_none() {
                        break;
                    }

                    if counter == 0 {
                        break;
                    }
                }

                if matches!(
                    self.branching_heuristic,
                    CdclBranchingHeuristic::ChaffVsids | CdclBranchingHeuristic::MiniSatVsids
                ) {
                    learned_clause.0.iter().for_each(|literal| {
                        let index = literal.abs_value().get() as usize - 1;

                        if literal.is_positive() {
                            self.activity_scores[index].0 += 1.0;
                        } else {
                            self.activity_scores[index].1 += 1.0;
                        }
                    });

                    self.activity_scores.iter_mut().for_each(|score| {
                        score.0 *= 0.95;
                        score.1 *= 0.95;
                    });
                }

                let backjump_level = learned_clause
                    .0
                    .iter()
                    .map(|literal| self.variable_levels[literal.abs_value().get() as usize - 1])
                    .filter(|&level| level < self.decision_level)
                    .max()
                    .unwrap_or(0);

                (learned_clause, backjump_level)
            },
        )
    }

    fn backjump(&mut self, target_level: usize, explanation: &mut impl Explain) {
        explanation.with_subexplanation(
            || format!("Backjumping to decision level {}", target_level),
            |explanation| {
                explanation.step(|| {
                    format!(
                        "Current decision level: {}",
                        self.decision_level.to_string().blue().markdown()
                    )
                });

                self.explain_assignment_stack(explanation);

                while self.variable_levels[self
                    .assignment_stack
                    .last()
                    .map(|entry| entry.literal.abs_value().get() as usize - 1)
                    .unwrap_or(0)]
                    > target_level
                {
                    let assignment_entry = self.assignment_stack.pop().unwrap();
                    explanation.step(|| {
                        format!(
                            "Removing {} from assignment stack because it is at decision level {}",
                            assignment_entry.literal.to_string().green().markdown(),
                            self.variable_levels
                                [assignment_entry.literal.abs_value().get() as usize - 1]
                                .to_string()
                                .blue()
                                .markdown(),
                        )
                    });

                    self.assignments.remove(&assignment_entry.literal);
                    self.assignments
                        .remove(&assignment_entry.literal.complement());
                    self.variable_levels[assignment_entry.literal.abs_value().get() as usize - 1] =
                        0;
                }

                self.decision_level = target_level;
            },
        );
    }

    fn choose_literal(&self) -> IntLiteral {
        match self.branching_heuristic {
            CdclBranchingHeuristic::First => {
                let literal = (1..=self.initial_literal_count as i32)
                    .find_map(|i| {
                        let literal = IntLiteral::new(i);

                        if !self.assignments.contains(&literal)
                            && !self.assignments.contains(&literal.complement())
                        {
                            Some(literal)
                        } else {
                            None
                        }
                    })
                    .unwrap();

                literal
            }

            CdclBranchingHeuristic::JeroslawWang => {
                let mut scores = vec![(0f32, 0f32); self.initial_literal_count];

                let mut max_score = 0f32;
                'outer: for clause in &self.clauses {
                    let mut unset_literals = Vec::with_capacity(clause.clause.0.len());

                    for literal in &clause.clause.0 {
                        if self.assignments.contains(literal) {
                            continue 'outer;
                        }

                        if self.assignments.contains(&literal.complement()) {
                            continue;
                        }

                        unset_literals.push(literal);
                    }

                    for literal in unset_literals.iter() {
                        let value = (literal.abs_value().get() - 1) as usize;

                        let delta = (unset_literals.len() as f32).neg().exp2();

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

            CdclBranchingHeuristic::ChaffVsids | CdclBranchingHeuristic::MiniSatVsids => {
                let mut max_score = -1.0;
                let mut max_score_literal = None;
                for (i, &score) in self.activity_scores.iter().enumerate() {
                    let literal = IntLiteral::new(i as i32 + 1);

                    if self.assignments.contains(&literal)
                        || self.assignments.contains(&literal.complement())
                    {
                        continue;
                    }

                    if max_score < score.0 {
                        max_score = score.0;
                        max_score_literal = Some(literal);
                    }

                    if max_score < score.1 {
                        max_score = score.1;
                        max_score_literal = Some(literal.complement());
                    }
                }

                max_score_literal.unwrap()
            }
        }
    }

    fn apply_cdcl(&mut self, explanation: &mut impl Explain) -> bool {
        let result = explanation.with_subexplanation(
            || "Applying the CDCL algorithm",
            |explanation| {

                // let unit_literal = self
                // .clauses
                // .iter()
                // .filter(|clause| clause.clause.0.len() == 1)
                // .map(|clause| clause.clause.0.iter().next().unwrap())
                // .next()
                // .copied();
                // self.unit_propagate.insert();

                loop {
                    let explanation = explanation.subexplanation(|| "CDCL step");

                    let conflict_clause = self.unit_propagation( explanation);

                    explanation.with_subexplanation(
                        || {
                            format!(
                                "Decision level {}",
                                self.decision_level.to_string().blue().markdown(),
                            )
                        },
                        |explanation| {
                            explanation.step(|| {
                                format!(
                                    "Current assignment: {}",
                                    self.assignments
                                        .iter()
                                        .map(|literal| literal.to_string())
                                        .join(", ")
                                        .green()
                                        .markdown(),
                                )
                            });
                        },
                    );

                    self.explain_clauses(explanation);

                    match conflict_clause {
                        Some(conflict_clause) => {
                            self.conflict_count += 1;

                            if self.decision_level == 0 {
                                explanation.step(|| {
                                    format!(
                                        "Found a conflict at decision level 0, therefore the formula is {}",
                                        "unsatisfiable".red().markdown()
                                    )
                                });

                                return false;
                            }

                            explanation.step(|| {
                                format!(
                                    "Conflict clause: {}",
                                    conflict_clause.to_string().red().markdown()
                                )
                            });

                            let (learned_clause, backjump_level) =
                                self.analyze_conflict(conflict_clause, explanation);

                            explanation.step(|| {
                                format!(
                                    "Learned new clause: {}",
                                    learned_clause.to_string().red().markdown()
                                )
                            });

                            self.backjump(backjump_level, explanation);

                            if learned_clause.0.len() == 1 {
                                let literal = learned_clause.0.iter().next().copied().unwrap();

                                self.assignments.insert(literal);
                                self.assignment_stack.push(AssignmentEntry {
                                    literal,
                                    implicant: None,
                                });
                                self.variable_levels[literal.abs_value().get() as usize - 1] =
                                    self.decision_level;
                                self.unit_propagate.insert(
                                    literal,
                                );
                            } else {
                                if !self.add_clause(learned_clause) {
                                    return false;
                                }
                            }
                        }

                        None => {
                            if self.assignments.len() == self.initial_literal_count {
                                explanation.step(|| {
                                    format!(
                                        "All variables have been assigned, therefore the formula is {}",
                                        "satisfiable".green().markdown()
                                    )
                                });

                                return true;
                            }

                            // let literal = (1..=self.initial_literal_count as i32)
                            //     .find_map(|i| {
                            //         let literal = IntLiteral::new(i);

                            //         if !self.assignments.contains(&literal)
                            //             && !self.assignments.contains(&literal.complement())
                            //         {
                            //             Some(literal)
                            //         } else {
                            //             None
                            //         }
                            //     })
                            //     .unwrap();


                            let literal = self.choose_literal();
                            explanation.step(|| {
                                format!(
                                    "Choosing {} to add to assignment",
                                    literal.to_string().green().markdown()
                                )
                            });

                            self.decision_count += 1;

                            self.decision_level += 1;

                            self.unit_propagate.insert(literal);
                            self.assignments.insert(literal);
                            self.assignment_stack.push(AssignmentEntry {
                                literal,
                                implicant: None,
                            });
                            self.variable_levels[literal.abs_value().get() as usize - 1] =
                                self.decision_level;
                        }
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

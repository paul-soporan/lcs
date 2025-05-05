use colored::Colorize;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{dimacs::ClauseSet, evaluate::Interpretation},
};

use super::solve::{Clause, Solve, SolverResult};

#[derive(Debug)]
pub struct ResolutionResult {
    value: bool,
    step_count: usize,
}

impl SolverResult for ResolutionResult {
    fn value(&self) -> bool {
        self.value
    }

    fn step_count(&self) -> usize {
        self.step_count
    }

    fn flip_value(&mut self) {
        self.value = !self.value;
    }

    fn build_interpretation(&self, _: &mut impl Explain) -> Option<Interpretation> {
        unimplemented!()
    }
}

#[derive(Debug)]
pub struct ResolutionSolver {}

impl ResolutionSolver {
    pub fn new() -> Self {
        Self {}
    }
}

impl Solve for ResolutionSolver {
    type Result = ResolutionResult;

    fn solve(&self, clause_set: ClauseSet, explanation: &mut impl Explain) -> ResolutionResult {
        let mut engine = ResolutionEngine::new(clause_set);
        let value = engine.apply_resolution(explanation);

        ResolutionResult {
            value,
            step_count: 0,
        }
    }
}

#[derive(Debug)]
struct ResolutionEngine {
    clauses: IndexSet<Clause>,
}

impl ResolutionEngine {
    fn new(clause_set: ClauseSet) -> Self {
        Self {
            clauses: clause_set.clauses,
        }
    }

    fn apply_resolution(&mut self, explanation: &mut impl Explain) -> bool {
        let result =
            explanation.with_subexplanation("Applying the resolution algorithm", |explanation| {
                loop {
                    explanation.with_subexplanation("Current clauses", |explanation| {
                        for (i, clause) in self.clauses.iter().enumerate() {
                            explanation.step(format!(
                                "{} {}",
                                format!("({})", i).to_string().magenta().markdown(),
                                clause.to_string().blue().markdown()
                            ));
                        }
                    });

                    if self.clauses.is_empty() {
                        explanation.step(format!(
                            "The formula has no clauses, therefore it is {}",
                            "satisfiable".green().markdown()
                        ));
                        return true;
                    }

                    for clause in &self.clauses {
                        if clause.0.is_empty() {
                            explanation.step(format!(
                                "Found an empty clause, therefore the formula is {}",
                                "unsatisfiable".red().markdown()
                            ));
                            return false;
                        }
                    }

                    match apply_resolution_step(&mut self.clauses, explanation) {
                        Some(result) => return result,
                        None => continue,
                    }
                }
            });

        explanation.step(format!(
            "Result: {}",
            if result {
                "satisfiable".green().markdown()
            } else {
                "unsatisfiable".red().markdown()
            },
        ));

        result
    }
}

pub(super) fn apply_resolution_step(
    clauses: &mut IndexSet<Clause>,
    explanation: &mut impl Explain,
) -> Option<bool> {
    explanation.with_subexplanation("Resolution step", |explanation| {
        match find_new_resolvent(clauses, explanation) {
            Some(resolvent) => {
                if resolvent.0.is_empty() {
                    explanation.step("Found an empty resolvent, the formula is unsatisfiable");
                    return Some(false);
                }

                clauses.insert(resolvent);

                None
            }
            None => {
                explanation.step("No new resolvent found, the formula is satisfiable");

                Some(true)
            }
        }
    })
}

fn find_new_resolvent(
    clauses: &IndexSet<Clause>,
    explanation: &mut impl Explain,
) -> Option<Clause> {
    explanation.with_subexplanation("Attempting to find a new resolvent", |explanation| {
        for (i, clause1) in clauses.iter().enumerate().sorted_by(|a, b| a.1.cmp(&b.1)) {
            for (j, clause2) in clauses
                .iter()
                .skip(i + 1)
                .enumerate()
                .sorted_by(|a, b| a.1.cmp(&b.1))
            {
                'literals: for literal in &clause1.0 {
                    if clause2.0.contains(&literal.complement()) {
                        let resolvent = Clause(
                            clause1
                                .0
                                .union(&clause2.0)
                                .filter(|l| l.abs() != literal.abs())
                                .cloned()
                                .collect(),
                        );

                        for literal in &resolvent.0 {
                            if resolvent.0.contains(&literal.complement()) {
                                continue 'literals;
                            }
                        }

                        if !clauses.contains(&resolvent) {
                            explanation.step(format!(
                                "Found a new resolvent: {} from {} and {}",
                                resolvent.to_string().blue().markdown(),
                                format!("({})", i).to_string().magenta().markdown(),
                                format!("({})", i + j + 1).to_string().magenta().markdown(),
                            ));
                            return Some(resolvent);
                        }
                    }
                }
            }
        }

        explanation.step("No new resolvent found");

        None
    })
}

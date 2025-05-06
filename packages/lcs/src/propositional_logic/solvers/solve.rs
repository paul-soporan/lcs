use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        dimacs::{Clause, ClauseSet, IntLiteral},
        evaluate::Interpretation,
        normal_forms::{ConjunctiveNormalForm, NegationNormalForm},
        types::{LogicalConsequence, Proposition},
    },
};
use colored::Colorize;
use indexmap::IndexSet;

pub trait SolverResult {
    fn value(&self) -> bool;
    fn step_count(&self) -> usize;

    fn flip_value(&mut self);

    fn build_interpretation(&self, explanation: &mut impl Explain) -> Option<Interpretation>;
}

pub trait Solve {
    type Result: SolverResult;

    fn solve(&self, clauses: ClauseSet, explanation: &mut impl Explain) -> Self::Result;

    fn check_clause_set_satisfiability(
        &self,
        clause_set: ClauseSet,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        self.solve(clause_set, explanation)
    }

    fn check_satisfiability(
        &self,
        proposition: impl Into<Proposition>,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let proposition = proposition.into();
        let proposition_string = proposition.to_string();

        explanation.with_subexplanation(
            || {
                format!(
                    "Creating a satisfiability solver for {}",
                    proposition_string.blue().markdown()
                )
            },
            |explanation| {
                let nnf = NegationNormalForm::from_proposition(proposition, explanation);
                let cnf = ConjunctiveNormalForm::from_negation_normal_form(nnf, explanation);

                let mut variables = IndexSet::new();

                let clauses = cnf
                    .0
                    .into_iter()
                    .map(|clause| {
                        Clause(
                            clause
                                .into_iter()
                                .map(|literal| {
                                    let abs =
                                        variables.get_index_of(&literal.0).unwrap_or_else(|| {
                                            variables.insert(literal.0.clone());
                                            variables.len() - 1
                                        }) + 1;

                                    IntLiteral::new(if literal.1 {
                                        abs as i32
                                    } else {
                                        -(abs as i32)
                                    })
                                })
                                .collect(),
                        )
                    })
                    .collect::<IndexSet<_>>();

                let clause_set = ClauseSet {
                    variable_count: variables.len(),
                    clause_count: clauses.len(),
                    clauses,
                };

                self.check_clause_set_satisfiability(clause_set, explanation)
            },
        )
    }

    fn check_validity(
        &self,
        proposition: impl Into<Proposition>,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let proposition = proposition.into();

        explanation.with_subexplanation(
            || {
                format!(
                    "Creating a validity solver for {}",
                    proposition.to_string().blue().markdown()
                )
            },
            |explanation| {
                let negated_proposition = proposition.negated();

                let mut result =
                    self.check_satisfiability(negated_proposition.clone(), explanation);

                explanation.step(|| {
                    format!(
                        "{} is {}, therefore {} is {}",
                        negated_proposition.to_string().blue().markdown(),
                        if result.value() {
                            "satisfiable".green().markdown()
                        } else {
                            "unsatisfiable".red().markdown()
                        },
                        proposition.to_string().blue().markdown(),
                        if !result.value() {
                            "valid".green().markdown()
                        } else {
                            "invalid".red().markdown()
                        },
                    )
                });

                result.flip_value();

                result
            },
        )
    }

    fn check_logical_consequence(
        &self,
        consequence: LogicalConsequence,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let mut propositions = consequence.premises.clone();
        propositions.push(consequence.conclusion.negated());

        let proposition = Proposition::Conjunction(propositions);

        explanation.with_subexplanation(
            || {
                format!(
                    "Creating a logical consequence solver for {}",
                    consequence.to_string().blue().markdown()
                )
            },
            |explanation| {
                let mut result = self.check_satisfiability(proposition.clone(), explanation);

                explanation.step(|| {
                    format!(
                        "{} is {}, therefore {} is {}",
                        proposition.to_string().blue().markdown(),
                        if result.value() {
                            "satisfiable".green().markdown()
                        } else {
                            "unsatisfiable".red().markdown()
                        },
                        consequence.to_string().blue().markdown(),
                        if !result.value() {
                            "true".green().markdown()
                        } else {
                            "false".red().markdown()
                        },
                    )
                });

                result.flip_value();

                result
            },
        )
    }
}

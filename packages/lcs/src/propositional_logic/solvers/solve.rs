use std::{collections::BTreeSet, fmt::Display};

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{
        evaluate::Interpretation,
        normal_forms::{ConjunctiveNormalForm, Literal, NegationNormalForm},
        types::{LogicalConsequence, Proposition},
    },
};
use colored::Colorize;
use indexmap::IndexSet;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Clause(pub BTreeSet<Literal>);

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.0.len() < other.0.len() {
            Some(std::cmp::Ordering::Less)
        } else if self.0.len() > other.0.len() {
            Some(std::cmp::Ordering::Greater)
        } else {
            return self.0.partial_cmp(&other.0);
        }
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0.len() < other.0.len() {
            std::cmp::Ordering::Less
        } else if self.0.len() > other.0.len() {
            std::cmp::Ordering::Greater
        } else {
            return self.0.cmp(&other.0);
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let literals = self
            .0
            .iter()
            .map(|literal| literal.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        write!(f, "{{{}}}", literals)
    }
}

pub trait SolverResult {
    fn value(&self) -> bool;
    fn step_count(&self) -> usize;

    fn flip_value(&mut self);

    fn build_interpretation(&self, explanation: &mut impl Explain) -> Option<Interpretation>;
}

pub trait Solve {
    type Result: SolverResult;

    fn solve(clauses: IndexSet<Clause>, explanation: &mut impl Explain) -> Self::Result;

    fn check_cnf_satisfiability(
        cnf: ConjunctiveNormalForm,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let clauses = cnf.0.into_iter().map(Clause).collect();

        Self::solve(clauses, explanation)
    }

    fn check_satisfiability(
        proposition: impl Into<Proposition>,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let proposition = proposition.into();

        explanation.with_subexplanation(
            format!(
                "Creating a satisfiability solver for {}",
                proposition.to_string().blue().markdown()
            ),
            |explanation| {
                let nnf = NegationNormalForm::from_proposition(proposition, explanation);
                let cnf = ConjunctiveNormalForm::from_negation_normal_form(nnf, explanation);

                Self::check_cnf_satisfiability(cnf, explanation)
            },
        )
    }

    fn check_validity(
        proposition: impl Into<Proposition>,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let proposition = proposition.into();

        explanation.with_subexplanation(
            format!(
                "Creating a validity solver for {}",
                proposition.to_string().blue().markdown()
            ),
            |explanation| {
                let negated_proposition = proposition.negated();

                let mut result =
                    Self::check_satisfiability(negated_proposition.clone(), explanation);

                explanation.step(format!(
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
                ));

                result.flip_value();

                result
            },
        )
    }

    fn check_logical_consequence(
        consequence: LogicalConsequence,
        explanation: &mut impl Explain,
    ) -> Self::Result {
        let mut propositions = consequence.premises.clone();
        propositions.push(consequence.conclusion.negated());

        let proposition = Proposition::Conjunction(propositions);

        explanation.with_subexplanation(
            format!(
                "Creating a logical consequence solver for {}",
                consequence.to_string().blue().markdown()
            ),
            |explanation| {
                let mut result = Self::check_satisfiability(proposition.clone(), explanation);

                explanation.step(format!(
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
                ));

                result.flip_value();

                result
            },
        )
    }
}

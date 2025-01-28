use std::fmt::Display;

use colored::Colorize;
use indexmap::IndexMap;
use itertools::Itertools;

use crate::{explanation::Explanation, markdown::Markdown};

use super::types::{Term, Variable};

#[derive(Debug, Clone)]
pub struct Substitution {
    pub name: String,
    pub mapping: IndexMap<Variable, Term>,
}

impl Substitution {
    pub fn single(variable: Variable, term: Term) -> Substitution {
        Substitution {
            name: format!("{{{}}} ← {}", variable, term),
            mapping: [(variable, term)].iter().cloned().collect(),
        }
    }

    pub fn without(&self, variable: &Variable) -> Substitution {
        let mut new_substitution = self.clone();
        new_substitution.mapping.shift_remove(variable);

        if self.mapping.contains_key(variable) {
            new_substitution.name = format!(
                "{} ∖ {{{} ← {}}}",
                self.name,
                variable,
                self.mapping[variable].to_relaxed_syntax(None)
            );
        }

        new_substitution
    }

    pub fn compose(&self, other: &Substitution, explanation: &mut Explanation) -> Substitution {
        let mut new_substitution = Substitution {
            name: format!("{}{}", self.name, other.name),
            mapping: IndexMap::new(),
        };

        explanation.with_subexplanation("", |explanation| {
            for (variable, term) in &self.mapping {
                explanation.with_subexplanation("", |explanation| {
                    let new_term = term.with_substitution(other, explanation.subexplanation(""));

                    explanation.merge_subexplanations(|subexplanations| {
                        format!("{} ← {}", variable, subexplanations[0])
                    });

                    if new_term != Term::Variable(variable.clone()) {
                        new_substitution.mapping.insert(variable.clone(), new_term);
                    }
                });
            }

            explanation.merge_subexplanations(|subexplanations| {
                format!("{{{}}}", subexplanations.join(", "))
            });
        });

        explanation.with_subexplanation("", |explanation| {
            for (variable, term) in &other.mapping {
                if !self.mapping.contains_key(variable) {
                    explanation.with_subexplanation("", |explanation| {
                        explanation.step(format!(
                            "{} ← {}",
                            variable,
                            term.to_relaxed_syntax(None)
                        ));

                        new_substitution
                            .mapping
                            .insert(variable.clone(), term.clone());
                    });
                }
            }

            explanation.merge_subexplanations(|subexplanations| {
                format!("{{{}}}", subexplanations.join(", "))
            });
        });

        explanation.merge_subexplanations(|subexplanations| {
            format!(
                "{} = {}",
                new_substitution.name.magenta().markdown(),
                subexplanations.join(" ∪ ")
            )
        });

        new_substitution
    }

    pub fn to_relaxed_syntax(&self) -> String {
        let mut components = self
            .mapping
            .iter()
            .map(|(variable, term)| format!("{} ← {}", variable, term.to_relaxed_syntax(None)));

        format!("{{{}}}", components.join(", "))
    }
}

impl Display for Substitution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut components = self
            .mapping
            .iter()
            .map(|(variable, term)| format!("{} ← {}", variable, term));

        write!(f, "{{{}}}", components.join(", "))
    }
}

// impl Mul for Substitution {
//     type Output = Substitution;

//     fn mul(self, other: Substitution) -> Substitution {
//         self.compose(&other)
//     }
// }

// impl Mul for &Substitution {
//     type Output = Substitution;

//     fn mul(self, other: &Substitution) -> Substitution {
//         self.compose(&other)
//     }
// }

// impl Mul<&Substitution> for Substitution {
//     type Output = Substitution;

//     fn mul(self, other: &Substitution) -> Substitution {
//         self.compose(other)
//     }
// }

// impl Mul<Substitution> for &Substitution {
//     type Output = Substitution;

//     fn mul(self, other: Substitution) -> Substitution {
//         self.compose(&other)
//     }
// }

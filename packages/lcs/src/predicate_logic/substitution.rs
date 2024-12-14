use std::{fmt::Display, ops::Mul};

use indexmap::IndexMap;
use itertools::Itertools;

use super::parser::{Signature, Term, Variable};

#[derive(Debug, Clone, Default)]
pub struct Substitution(pub IndexMap<Variable, Term>);

impl Substitution {
    pub fn without(&self, variable: &Variable) -> Substitution {
        let mut new_substitution = self.clone();
        new_substitution.0.shift_remove(variable);

        new_substitution
    }

    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut new_substitution = Substitution::default();

        for (variable, term) in &self.0 {
            let new_term = term.with_substitution(other);

            if new_term != Term::Variable(variable.clone()) {
                new_substitution.0.insert(variable.clone(), new_term);
            }
        }

        for (variable, term) in &other.0 {
            if !self.0.contains_key(variable) {
                new_substitution.0.insert(variable.clone(), term.clone());
            }
        }

        new_substitution
    }

    pub fn to_relaxed_syntax(&self, signature: &Signature) -> String {
        let mut components = self.0.iter().map(|(variable, term)| {
            format!("{}←{}", variable, term.to_relaxed_syntax(signature, None))
        });

        format!("{{{}}}", components.join(", "))
    }
}

impl Display for Substitution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut components = self
            .0
            .iter()
            .map(|(variable, term)| format!("{}←{}", variable, term));

        write!(f, "{{{}}}", components.join(", "))
    }
}

impl Mul for Substitution {
    type Output = Substitution;

    fn mul(self, other: Substitution) -> Substitution {
        self.compose(&other)
    }
}

impl Mul for &Substitution {
    type Output = Substitution;

    fn mul(self, other: &Substitution) -> Substitution {
        self.compose(&other)
    }
}

impl Mul<&Substitution> for Substitution {
    type Output = Substitution;

    fn mul(self, other: &Substitution) -> Substitution {
        self.compose(other)
    }
}

impl Mul<Substitution> for &Substitution {
    type Output = Substitution;

    fn mul(self, other: Substitution) -> Substitution {
        self.compose(&other)
    }
}

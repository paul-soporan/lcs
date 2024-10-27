use std::{collections::HashMap, fmt::Display};

use crate::ast::{
    AtomicProposition, BinaryOperation, CompoundProposition, Proposition, PropositionalVariable,
    UnaryOperation,
};

#[derive(Debug)]
pub struct Interpretation(pub HashMap<PropositionalVariable, bool>);

impl Interpretation {
    pub fn all<'a>(variables: &'a [&'a str]) -> impl Iterator<Item = Interpretation> + 'a {
        let n = variables.len();
        let interpretation_count = 1 << n;

        (0..interpretation_count).map(move |i| {
            let bit_string = format!("{:0n$b}", i);
            let mapping = bit_string.chars().map(|c| c == '1').collect::<Vec<bool>>();

            let mut interpretation = Interpretation(HashMap::new());
            for (variable, value) in variables.iter().zip(mapping) {
                interpretation
                    .0
                    .insert(PropositionalVariable(variable.to_string()), value);
            }
            interpretation
        })
    }
}

impl Display for Interpretation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut variables = self.0.keys().collect::<Vec<_>>();
        variables.sort_by_key(|v| &v.0);

        let variable_list = variables
            .iter()
            .map(|variable| {
                let prefix = if *self.0.get(variable).unwrap() {
                    ""
                } else {
                    "¬"
                };
                format!("{prefix}{variable}")
            })
            .collect::<Vec<_>>()
            .join(", ");

        write!(f, "{{{}}}", variable_list)
    }
}

pub trait Evaluate {
    fn evaluate(&self, interpretation: &Interpretation) -> bool;
}

impl Evaluate for PropositionalVariable {
    fn evaluate(&self, interpretation: &Interpretation) -> bool {
        *interpretation.0.get(self).unwrap()
    }
}

impl Evaluate for AtomicProposition {
    fn evaluate(&self, interpretation: &Interpretation) -> bool {
        match self {
            AtomicProposition::PropositionalVariable(p) => p.evaluate(interpretation),
            AtomicProposition::Invalid(_) => panic!("Invalid atomic proposition"),
        }
    }
}

impl Evaluate for CompoundProposition {
    fn evaluate(&self, interpretation: &Interpretation) -> bool {
        match self {
            CompoundProposition::UnaryOperation {
                operation,
                proposition,
            } => {
                let p = proposition.evaluate(interpretation);
                match operation {
                    UnaryOperation::Negation => !p,
                }
            }
            CompoundProposition::BinaryOperation {
                operation,
                left,
                right,
            } => {
                let l = left.evaluate(interpretation);
                let r = right.evaluate(interpretation);
                match operation {
                    BinaryOperation::Conjunction => l && r,
                    BinaryOperation::Disjunction => l || r,
                    BinaryOperation::Implication => !l || r,
                    BinaryOperation::Equivalence => l == r,
                }
            }
            CompoundProposition::Invalid(_) => panic!("Invalid compound proposition"),
        }
    }
}

impl Evaluate for Proposition {
    fn evaluate(&self, interpretation: &Interpretation) -> bool {
        match self {
            Proposition::Atomic(p) => p.evaluate(interpretation),
            Proposition::Compound(p) => p.evaluate(interpretation),
            Proposition::Invalid(_) => panic!("Invalid proposition"),
        }
    }
}

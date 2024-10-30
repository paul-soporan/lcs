use std::{collections::HashMap, fmt::Display};

use colored::Colorize;

use crate::ast::{
    BinaryOperation, CompoundProposition, Proposition, PropositionalVariable, UnaryOperation,
    VariableSet,
};

#[derive(Debug)]
pub struct Interpretation(pub HashMap<PropositionalVariable, TruthValue>);

impl Interpretation {
    pub fn generate_all<'a>(variables: VariableSet) -> impl Iterator<Item = Interpretation> + 'a {
        let n = variables.0.len();
        let interpretation_count = 1 << n;

        (0..interpretation_count).map(move |i| {
            let bit_string = format!("{:0n$b}", i);
            let mapping = bit_string.chars().map(|c| c == '1').collect::<Vec<bool>>();

            let mut interpretation = Interpretation(HashMap::new());
            for (variable, value) in variables.0.iter().zip(mapping) {
                interpretation.0.insert(variable.clone(), TruthValue(value));
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
                let prefix = if self.0.get(variable).unwrap().0 {
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

#[derive(Debug, Clone, Copy)]
pub struct TruthValue(pub bool);

impl Display for TruthValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "𝐓" } else { "𝟊" })
    }
}

#[derive(Debug)]
pub struct ExplainedValue<T> {
    pub value: T,
    pub steps: Vec<String>,
}

pub type Evaluation = ExplainedValue<TruthValue>;

pub trait Evaluate {
    fn evaluate(&self, interpretation: &Interpretation) -> Evaluation;
}

impl Evaluate for PropositionalVariable {
    fn evaluate(&self, interpretation: &Interpretation) -> Evaluation {
        let value = *interpretation.0.get(self).unwrap();
        Evaluation {
            value,
            steps: vec![format!(
                "{}{}{}",
                "I(".magenta(),
                self.0.to_string().cyan(),
                ")".magenta()
            )],
        }
    }
}

impl Evaluate for CompoundProposition {
    fn evaluate(&self, interpretation: &Interpretation) -> Evaluation {
        match self {
            CompoundProposition::UnaryOperation {
                operation,
                proposition,
            } => {
                let Evaluation { value, steps } = proposition.evaluate(interpretation);
                let value = match operation {
                    UnaryOperation::Negation => !value.0,
                };
                Evaluation {
                    value: TruthValue(value),
                    steps: steps
                        .iter()
                        .map(|s| format!("{}{s}{}", "Ɓ¬(".green(), ")".green()))
                        .collect(),
                }
            }
            CompoundProposition::BinaryOperation {
                operation,
                left,
                right,
            } => {
                let Evaluation {
                    value: TruthValue(l),
                    steps: l_steps,
                } = left.evaluate(interpretation);
                let Evaluation {
                    value: TruthValue(r),
                    steps: r_steps,
                } = right.evaluate(interpretation);

                let value = match operation {
                    BinaryOperation::Conjunction => l && r,
                    BinaryOperation::Disjunction => l || r,
                    BinaryOperation::Implication => !l || r,
                    BinaryOperation::Equivalence => l == r,
                };

                let operation = match operation {
                    BinaryOperation::Conjunction => "∧",
                    BinaryOperation::Disjunction => "∨",
                    BinaryOperation::Implication => "⇒",
                    BinaryOperation::Equivalence => "⇔",
                };

                let l_steps_len = l_steps.len();
                let r_steps_len = r_steps.len();
                let max_steps_len = l_steps_len.max(r_steps_len);

                // Pad each vector with its last element to make them the same length.
                let l_steps = l_steps
                    .iter()
                    .chain(std::iter::repeat(&l_steps[l_steps_len - 1]))
                    .take(max_steps_len);

                let r_steps = r_steps
                    .iter()
                    .chain(std::iter::repeat(&r_steps[r_steps_len - 1]))
                    .take(max_steps_len);

                let steps = l_steps
                    .zip(r_steps)
                    .map(|(l, r)| {
                        format!(
                            "{}{l}{}{r}{}",
                            format!("Ɓ{operation}(").green(),
                            ", ".green(),
                            ")".green()
                        )
                    })
                    .collect();

                Evaluation {
                    value: TruthValue(value),
                    steps,
                }
            }
        }
    }
}

impl Evaluate for Proposition {
    fn evaluate(&self, interpretation: &Interpretation) -> Evaluation {
        let Evaluation { value, mut steps } = match self {
            Proposition::Atomic(p) => p.evaluate(interpretation),
            Proposition::Compound(p) => p.evaluate(interpretation),
        };

        steps.insert(
            0,
            format!(
                "{}{}{}",
                "𑜆ᵢ(".yellow(),
                self.to_string().red(),
                ")".yellow()
            ),
        );
        steps.push(value.to_string().blue().to_string());

        Evaluation { value, steps }
    }
}

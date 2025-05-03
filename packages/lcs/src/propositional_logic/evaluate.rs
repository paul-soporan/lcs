use std::fmt::Display;

use colored::Colorize;
use indexmap::IndexMap;

use crate::propositional_logic::ast::{Proposition, PropositionalVariable, VariableSet};

#[derive(Debug, Default)]
pub struct Interpretation(pub IndexMap<PropositionalVariable, TruthValue>);

impl Interpretation {
    pub fn generate_all<'a>(variables: VariableSet) -> impl Iterator<Item = Interpretation> + 'a {
        let n = variables.0.len();
        let interpretation_count = 1 << n;

        (0..interpretation_count).map(move |i| {
            let bit_string = format!("{:0n$b}", i);
            let mapping = bit_string.chars().map(|c| c == '1').collect::<Vec<bool>>();

            let mut interpretation = Interpretation(IndexMap::new());
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
            .map(|&variable| {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl Proposition {
    pub fn evaluate(&self, interpretation: &Interpretation) -> Evaluation {
        let Evaluation { value, mut steps } = match self {
            Proposition::Tautology => Evaluation {
                value: TruthValue(true),
                steps: vec![],
            },
            Proposition::Contradiction => Evaluation {
                value: TruthValue(false),
                steps: vec![],
            },

            Proposition::Atomic(p) => Evaluation {
                value: *interpretation.0.get(p).unwrap(),
                steps: vec![format!(
                    "{}{}{}",
                    "I(".magenta(),
                    p.0.to_string().cyan(),
                    ")".magenta()
                )],
            },

            Proposition::Negation(p) => {
                let Evaluation { value, steps } = p.evaluate(interpretation);
                Evaluation {
                    value: TruthValue(!value.0),
                    steps: steps
                        .iter()
                        .map(|s| format!("{}{s}{}", "Ɓ¬(".green(), ")".green()))
                        .collect(),
                }
            }

            Proposition::Implication(left, right) | Proposition::Equivalence(left, right) => {
                let Evaluation {
                    value: TruthValue(l),
                    steps: l_steps,
                } = left.evaluate(interpretation);
                let Evaluation {
                    value: TruthValue(r),
                    steps: r_steps,
                } = right.evaluate(interpretation);

                let (value, operation) = match self {
                    Proposition::Implication(_, _) => (!l || r, "⇒"),
                    Proposition::Equivalence(_, _) => (l == r, "⇔"),
                    _ => unreachable!(),
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

            Proposition::Conjunction(propositions) | Proposition::Disjunction(propositions) => {
                let evaluations = propositions.iter().map(|p| p.evaluate(interpretation));

                let (value, operation) = match self {
                    Proposition::Conjunction(_) => (
                        evaluations.clone().fold(true, |acc, e| acc && e.value.0),
                        "∧",
                    ),
                    Proposition::Disjunction(_) => (
                        evaluations.clone().fold(false, |acc, e| acc || e.value.0),
                        "∨",
                    ),
                    _ => unreachable!(),
                };

                if propositions.is_empty() {
                    Evaluation {
                        value: TruthValue(value),
                        steps: vec![],
                    }
                } else {
                    let max_steps_len =
                        evaluations.clone().fold(0, |acc, e| acc.max(e.steps.len()));

                    // Pad each vector with its last element to make them the same length.
                    let steps = evaluations
                        .into_iter()
                        .map(|e| {
                            e.steps
                                .iter()
                                .chain(std::iter::repeat(&e.steps[e.steps.len() - 1]))
                                .take(max_steps_len)
                                .cloned()
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();

                    let mut final_steps = vec![];

                    for i in 0..steps[0].len() {
                        let s = steps
                            .iter()
                            .map(|step| step[i].clone())
                            .collect::<Vec<_>>()
                            .join(", ");

                        final_steps.push(format!(
                            "{}{}{}",
                            format!("Ɓ{operation}(").green(),
                            s,
                            ")".green()
                        ))
                    }

                    Evaluation {
                        value: TruthValue(value),
                        steps: final_steps,
                    }
                }
            }
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

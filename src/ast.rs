use std::{
    collections::BTreeSet,
    fmt::{Debug, Display},
    vec,
};

use colored::Colorize;

use crate::evaluate::{Evaluate, Evaluation, ExplainedValue, Interpretation, TruthValue};

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct PropositionalVariable(pub String);

#[derive(Debug)]
pub enum UnaryOperation {
    Negation,
}

#[derive(Debug)]
pub enum BinaryOperation {
    Conjunction,
    Disjunction,
    Implication,
    Equivalence,
}

#[derive(Debug)]
pub enum CompoundProposition {
    UnaryOperation {
        operation: UnaryOperation,
        proposition: Proposition,
    },
    BinaryOperation {
        operation: BinaryOperation,
        left: Proposition,
        right: Proposition,
    },
}

#[derive(Debug)]
pub enum Proposition {
    Atomic(PropositionalVariable),
    Compound(Box<CompoundProposition>),
}

#[derive(Debug)]
pub struct PropositionAttributes {
    pub valid: bool,
    pub satisfiable: bool,
}

impl From<PropositionalVariable> for Proposition {
    fn from(p: PropositionalVariable) -> Self {
        Proposition::Atomic(p)
    }
}

impl From<CompoundProposition> for Proposition {
    fn from(p: CompoundProposition) -> Self {
        Proposition::Compound(Box::new(p))
    }
}

#[derive(Debug)]
pub struct VariableSet(pub BTreeSet<PropositionalVariable>);

impl Display for VariableSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let variable_list = self
            .0
            .iter()
            .map(|variable| variable.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        write!(f, "{{{}}}", variable_list)
    }
}

impl Proposition {
    pub fn get_variables(&self) -> ExplainedValue<VariableSet> {
        let mut steps = vec![format!(
            "Collecting variables in {}",
            self.to_string().blue()
        )];

        match self {
            Proposition::Atomic(p) => {
                let mut variables = VariableSet(BTreeSet::new());
                variables.0.insert(p.clone());

                steps.push(format!("=> {}", variables.to_string().green()));

                ExplainedValue {
                    value: variables,
                    steps,
                }
            }
            Proposition::Compound(p) => {
                let p = p.as_ref();

                match p {
                    CompoundProposition::UnaryOperation { proposition, .. } => {
                        proposition.get_variables()
                    }
                    CompoundProposition::BinaryOperation { left, right, .. } => {
                        let ExplainedValue {
                            value: mut variables,
                            steps: left_steps,
                        } = left.get_variables();
                        let ExplainedValue {
                            value: right,
                            steps: right_steps,
                        } = right.get_variables();

                        let left_variable_set = variables.to_string().red();
                        let right_variable_set = right.to_string().yellow();

                        variables.0.extend(right.0);

                        let variable_set = variables.to_string().green();

                        steps.extend(left_steps.iter().map(|step| format!("  {step}")));
                        steps.extend(right_steps.iter().map(|step| format!("  {step}")));

                        steps.push(format!(
                            "=> {} = {} ∪ {}",
                            variable_set, left_variable_set, right_variable_set
                        ));

                        ExplainedValue {
                            value: variables,
                            steps,
                        }
                    }
                }
            }
        }
    }

    // pub fn is_valid(&self) -> bool {
    //     let variables = self.get_variables();
    //     Interpretation::generate_all(variables).all(|i| self.evaluate(&i))
    // }

    // pub fn is_satisfiable(&self) -> bool {
    //     let variables = self.get_variables();
    //     Interpretation::generate_all(variables).any(|i| self.evaluate(&i))
    // }

    pub fn get_attributes(&self) -> ExplainedValue<PropositionAttributes> {
        let ExplainedValue {
            value: variables,
            mut steps,
        } = self.get_variables();

        let mut valid = true;
        let mut satisfiable = false;

        steps.push(format!(
            "\nGenerating all interpretations for variable set: {}",
            variables.to_string().blue()
        ));

        Interpretation::generate_all(variables)
            .enumerate()
            .for_each(|(index, interpretation)| {
                steps.push(format!("  Interpretation {}:", index.to_string().yellow()));
                steps.push(format!("    Let I ≔ {}", interpretation.to_string().blue()));

                let Evaluation {
                    value: TruthValue(value),
                    steps: evaluation_steps,
                } = self.evaluate(&interpretation);

                steps.extend(evaluation_steps.iter().enumerate().map(|(i, step)| {
                    format!(
                        "      {step}{}",
                        if i == evaluation_steps.len() - 1 {
                            ""
                        } else {
                            " ="
                        }
                    )
                }));

                valid &= value;
                satisfiable |= value;
            });

        let attributes = PropositionAttributes { valid, satisfiable };
        ExplainedValue {
            value: attributes,
            steps,
        }
    }
}

impl Display for PropositionalVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for CompoundProposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CompoundProposition::UnaryOperation {
                    operation,
                    proposition,
                } => match operation {
                    UnaryOperation::Negation => format!("(¬{})", proposition),
                },
                CompoundProposition::BinaryOperation {
                    operation,
                    left,
                    right,
                } => {
                    match operation {
                        BinaryOperation::Conjunction => format!("({} ∧ {})", left, right),
                        BinaryOperation::Disjunction => format!("({} ∨ {})", left, right),
                        BinaryOperation::Implication => format!("({} ⇒ {})", left, right),
                        BinaryOperation::Equivalence => format!("({} ⇔ {})", left, right),
                    }
                }
            }
        )
    }
}

impl Display for Proposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Proposition::Atomic(p) => p.to_string(),
                Proposition::Compound(p) => p.to_string(),
            }
        )
    }
}

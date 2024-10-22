use crate::ast::{
    AtomicProposition, BinaryOperation, CompoundProposition, Invalid, Proposition, UnaryOperation,
};

pub struct Description {
    pub description: String,
    pub valid: bool,
}

pub trait Describe {
    fn describe(&self, indentation: usize, id: usize) -> Description;
}

impl Describe for AtomicProposition {
    fn describe(&self, indentation: usize, _: usize) -> Description {
        match self {
            AtomicProposition::PropositionalVariable(v) => Description {
                description: format!(
                    "{v} ∈ 𝓥 propositional variable\n{} => {v} ∈ 𝓟 atomic statement",
                    indent(indentation),
                ),
                valid: true,
            },
            AtomicProposition::Invalid(Invalid { input, .. }) => Description {
                description: format!(
                    "{input} ∉ 𝓥 and {input} not compound\n{} => {input} ∉ 𝓟",
                    indent(indentation),
                ),
                valid: false,
            },
        }
    }
}

impl Describe for CompoundProposition {
    fn describe(&self, indentation: usize, id: usize) -> Description {
        let next_indentation = indentation + 2;

        let (Description { description, valid }, operation) = match self {
            CompoundProposition::UnaryOperation {
                operation,
                proposition,
            } => {
                let operation = match operation {
                    UnaryOperation::Negation => "negation",
                };

                let Description { description, valid } =
                    proposition.describe(next_indentation, id + 1);

                (
                    Description {
                        description: format!("\n{}{}", indent(next_indentation), description),
                        valid,
                    },
                    operation,
                )
            }
            CompoundProposition::BinaryOperation {
                operation,
                left,
                right,
            } => {
                let operation = match operation {
                    BinaryOperation::Conjunction => "conjunction",
                    BinaryOperation::Disjunction => "disjunction",
                    BinaryOperation::Implication => "implication",
                    BinaryOperation::Equivalence => "equivalence",
                };

                let lhs = left.describe(next_indentation, id + 1);
                let rhs = right.describe(
                    next_indentation,
                    if let Proposition::Compound(_) = left {
                        id + 2
                    } else {
                        id + 1
                    },
                );

                let lhs_description =
                    format!("\n{}LHS: {}", indent(next_indentation), lhs.description);
                let rhs_description =
                    format!("\n{}RHS: {}", indent(next_indentation), rhs.description);

                (
                    Description {
                        description: format!("{}{}", lhs_description, rhs_description),
                        valid: lhs.valid && rhs.valid,
                    },
                    operation,
                )
            }
            CompoundProposition::Invalid(Invalid { input, reason }) => {
                return Description {
                    description: if let Some(reason) = reason {
                        format!("{}({input}) ∉ 𝓟 because {reason}", indent(indentation))
                    } else {
                        format!("{}({input}) ∉ 𝓟", indent(indentation))
                    } + format!("\n{}=> T{} ∉ 𝓟", indent(indentation), subscript(id))
                        .as_str(),
                    valid: false,
                };
            }
        };

        let mut final_description = format!(
            "{}T{} is the {operation} of:",
            indent(indentation),
            subscript(id)
        ) + description.as_str();

        let membership_symbol = if valid { "∈" } else { "∉" };

        final_description += format!(
            "\n{}=> T{} {membership_symbol} 𝓟{}",
            indent(indentation),
            subscript(id),
            if valid { " compound proposition" } else { "" }
        )
        .as_str();

        Description {
            description: final_description,
            valid,
        }
    }
}

impl Describe for Proposition {
    fn describe(&self, indentation: usize, id: usize) -> Description {
        match self {
            Proposition::Atomic(v) => v.describe(indentation + 2, id),
            Proposition::Compound(p) => {
                let Description { description, valid } = p.describe(indentation + 2, id);

                Description {
                    description: format!("Let T{} ≔ {p} \n{}", subscript(id), description),
                    valid,
                }
            }
            Proposition::Invalid(Invalid { input, reason }) => Description {
                description: if let Some(reason) = reason {
                    format!("{input} ∉ 𝓟 because {reason}")
                } else {
                    format!("{input} ∉ 𝓟")
                },
                valid: false,
            },
        }
    }
}

pub fn indent(indentation: usize) -> String {
    " ".repeat(indentation)
}

pub fn subscript(i: usize) -> String {
    let subscripts = vec!["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"];

    i.to_string()
        .chars()
        .map(|c| subscripts[c.to_digit(10).unwrap() as usize])
        .collect()
}

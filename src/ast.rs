use std::fmt::Display;

#[derive(Debug)]
pub struct Invalid {
    pub input: String,
    pub reason: Option<String>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PropositionalVariable(pub String);

#[derive(Debug)]
pub enum AtomicProposition {
    PropositionalVariable(PropositionalVariable),
    Invalid(Invalid),
}

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
    Invalid(Invalid),
}

#[derive(Debug)]
pub enum Proposition {
    Atomic(AtomicProposition),
    Compound(Box<CompoundProposition>),
    Invalid(Invalid),
}

impl Display for PropositionalVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for AtomicProposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AtomicProposition::PropositionalVariable(p) => p.to_string(),
                AtomicProposition::Invalid(Invalid { input, .. }) => input.to_string(),
            }
        )
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
                    UnaryOperation::Negation => format!("(¬ {})", proposition),
                },
                CompoundProposition::BinaryOperation {
                    operation,
                    left,
                    right,
                } => match operation {
                    BinaryOperation::Conjunction => format!("({} ∧ {})", left, right),
                    BinaryOperation::Disjunction => format!("({} ∨ {})", left, right),
                    BinaryOperation::Implication => format!("({} ⇒ {})", left, right),
                    BinaryOperation::Equivalence => format!("({} ⇔ {})", left, right),
                },
                CompoundProposition::Invalid(Invalid { input, .. }) => format!("({input})"),
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
                Proposition::Invalid(Invalid { input, .. }) => input.to_owned(),
            }
        )
    }
}

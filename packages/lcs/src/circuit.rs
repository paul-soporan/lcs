use std::{
    fmt::Display,
    ops::{Add, AddAssign},
};

use indexmap::IndexSet;

use crate::ast::{ConjunctiveNormalForm, DisjunctiveNormalForm, Literal};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Bit(pub String);

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Gate {
    Not(Component),
    And(Component, Component),
    Or(Component, Component),
}

impl Display for Gate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Gate::Not(component) => write!(f, "¬{}", component),
            Gate::And(left, right) => write!(f, "({} ∧ {})", left, right),
            Gate::Or(left, right) => write!(f, "({} ∨ {})", left, right),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Component {
    Input(Bit),
    Gate(Box<Gate>),
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Input(bit) => write!(f, "{}", bit),
            Component::Gate(gate) => write!(f, "{}", gate),
        }
    }
}

impl From<Bit> for Component {
    fn from(bit: Bit) -> Self {
        Component::Input(bit)
    }
}

impl From<Gate> for Component {
    fn from(gate: Gate) -> Self {
        Component::Gate(Box::new(gate))
    }
}

#[derive(Debug, Default)]
pub struct CircuitAttributes<'a> {
    pub depth: usize,
    pub inputs: IndexSet<&'a Bit>,
    pub gates: IndexSet<&'a Gate>,
}

impl AddAssign for CircuitAttributes<'_> {
    fn add_assign(&mut self, other: Self) {
        self.depth = self.depth.max(other.depth);
        self.inputs.extend(other.inputs);
        self.gates.extend(other.gates);
    }
}

impl Add for CircuitAttributes<'_> {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        self += other;
        self
    }
}

pub trait Analyze {
    fn get_attributes(&self) -> CircuitAttributes;
}

#[derive(Debug, Clone, Default)]
pub struct Circuit {
    pub components: Vec<Component>,
}

impl Analyze for Circuit {
    fn get_attributes(&self) -> CircuitAttributes {
        let mut attributes = CircuitAttributes::default();

        for component in &self.components {
            attributes += component.get_attributes();
        }

        attributes
    }
}

impl Analyze for Component {
    fn get_attributes(&self) -> CircuitAttributes {
        match self {
            Component::Input(input) => input.get_attributes(),
            Component::Gate(gate) => gate.get_attributes(),
        }
    }
}

impl Analyze for Gate {
    fn get_attributes(&self) -> CircuitAttributes {
        let mut attributes = CircuitAttributes::default();

        match self {
            Gate::Not(component) => {
                attributes += component.get_attributes();
            }
            Gate::And(left, right) | Gate::Or(left, right) => {
                attributes += left.get_attributes();
                attributes += right.get_attributes();
            }
        }

        attributes.depth += 1;
        attributes.gates.insert(self);

        attributes
    }
}

impl Analyze for Bit {
    fn get_attributes(&self) -> CircuitAttributes {
        CircuitAttributes {
            depth: 0,
            inputs: IndexSet::from([self]),
            gates: IndexSet::new(),
        }
    }
}

fn transform_conjunction(conjunction: &[Component]) -> Component {
    let n = conjunction.len();

    if n & 1 == 0 {
        let (left, right) = conjunction.split_at(n / 2);
        Gate::And(transform_conjunction(left), transform_conjunction(right)).into()
    } else {
        let (first, rest) = conjunction.split_first().unwrap();
        if rest.is_empty() {
            first.clone()
        } else {
            Gate::And(first.clone(), transform_conjunction(rest)).into()
        }
    }
}

fn transform_disjunction(disjunction: &[Component]) -> Component {
    let n = disjunction.len();

    if n & 1 == 0 {
        let (left, right) = disjunction.split_at(n / 2);
        Gate::Or(transform_disjunction(left), transform_disjunction(right)).into()
    } else {
        let (first, rest) = disjunction.split_first().unwrap();
        if rest.is_empty() {
            first.clone()
        } else {
            Gate::Or(first.clone(), transform_disjunction(rest)).into()
        }
    }
}

impl From<Literal> for Component {
    fn from(Literal(variable, value): Literal) -> Self {
        match value {
            true => Bit(variable.0).into(),
            false => Gate::Not(Bit(variable.0).into()).into(),
        }
    }
}

impl From<ConjunctiveNormalForm> for Component {
    fn from(cnf: ConjunctiveNormalForm) -> Self {
        transform_conjunction(
            &cnf.0
                .into_iter()
                .map(|clause| {
                    transform_disjunction(
                        &clause
                            .into_iter()
                            .map(|literal| literal.into())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
}

impl From<DisjunctiveNormalForm> for Component {
    fn from(cnf: DisjunctiveNormalForm) -> Self {
        transform_disjunction(
            &cnf.0
                .into_iter()
                .map(|clause| {
                    transform_conjunction(
                        &clause
                            .into_iter()
                            .map(|literal| literal.into())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }
}

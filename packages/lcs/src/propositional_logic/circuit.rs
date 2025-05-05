use std::{
    fmt::Display,
    ops::{Add, AddAssign},
};

use colored::Colorize;
use indexmap::IndexSet;

use crate::{
    explanation::{DiscardedExplanation, Explain},
    markdown::Markdown,
    propositional_logic::normal_forms::{ConjunctiveNormalForm, DisjunctiveNormalForm, Literal},
};

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
    Nand(Component, Component),
}

impl Display for Gate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Gate::Not(component) => write!(f, "¬{}", component),
            Gate::And(left, right) => write!(f, "({} ∧ {})", left, right),
            Gate::Or(left, right) => write!(f, "({} ∨ {})", left, right),
            Gate::Nand(left, right) => write!(f, "({} | {})", left, right),
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

pub fn into_nand_only_component(
    component: impl Into<Component>,
    explanation: &mut impl Explain,
) -> Component {
    let component = component.into();

    explanation.with_subexplanation(
        format!("Transforming {} into nand-only circuit", component.to_string().red().markdown()),
        |explanation| {
            let result = match component {
                Component::Gate(box gate) => match gate {
                    Gate::Or(left, right) => explanation.with_subexplanation("disjunction -> double-negated disjunction -> negation of conjunction of negations -> nand of negations", |explanation| {
                        Gate::Nand(
                            into_nand_only_component(Gate::Not(left), explanation.subexplanation("negation of lhs")),
                            into_nand_only_component(Gate::Not(right), explanation.subexplanation("negation of rhs")),
                        )
                        .into()
                    }),
                    Gate::And(left, right) => {
                        explanation.with_subexplanation("conjunction -> double-negated conjunction -> negated nand", |explanation| {
                            into_nand_only_component(Gate::Not(Gate::Nand(left, right).into()), explanation.subexplanation("negation of nand"))
                        })
                    }
                    Gate::Not(component) => match component {
                        Component::Input(bit) => explanation.with_subexplanation("negated atom -> nand", |_| {
                            Gate::Nand(bit.clone().into(), bit.into()).into()
                        }),
                        Component::Gate(box gate) => match gate {
                            Gate::Not(component) => explanation.with_subexplanation("double negated formula -> formula", |explanation| into_nand_only_component(component, explanation.subexplanation("inner formula"))),
                            Gate::And(left, right) => explanation.with_subexplanation("negated conjunction -> nand", |explanation| {
                                Gate::Nand(
                                    into_nand_only_component(left, explanation.subexplanation("lhs")),
                                    into_nand_only_component(right, explanation.subexplanation("rhs")),
                                )
                                .into()
                            }),
                            Gate::Or(left, right) => explanation.with_subexplanation("negated disjunction -> conjunction of negations", |explanation| {
                                into_nand_only_component(Gate::And(
                                    Gate::Not(left).into(),
                                    Gate::Not(right).into(),
                                ), explanation.subexplanation("conjunction of negations"))
                            }),
                            Gate::Nand(left, right) => explanation.with_subexplanation("negated nand -> conjunction -> double-negated conjunction -> negated nand", |explanation| {
                                let left = into_nand_only_component(left, explanation.subexplanation("lhs"));
                                let right = into_nand_only_component(right, explanation.subexplanation("rhs"));

                                let gate = Gate::Nand(left, right);

                                Gate::Nand(gate.clone().into(), gate.into()).into()
                            })
                        },
                    },
                    _ => unimplemented!(),
                },
                component => component,
            };

            explanation.step(format!("Result: {}", result.to_string().green().markdown()));

            result
        },
    )
}

#[derive(Debug, Default)]
pub struct CircuitAttributes<'a> {
    pub depth: usize,
    pub inputs: IndexSet<&'a Bit>,
    pub gates: IndexSet<&'a Gate>,
}

impl CircuitAttributes<'_> {
    pub fn transistor_count(&self) -> usize {
        self.gates.iter().fold(0, |acc, gate| {
            acc + match gate {
                Gate::Not(_) => 1,
                Gate::Nand(_, _) => 2,
                Gate::And(_, _) | Gate::Or(_, _) => 3,
            }
        })
    }
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

impl Circuit {
    pub fn into_nand_only(self) -> Self {
        Self {
            components: self
                .components
                .into_iter()
                .map(|component| into_nand_only_component(component, &mut DiscardedExplanation))
                .collect(),
        }
    }
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
            Gate::Nand(left, right) => {
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

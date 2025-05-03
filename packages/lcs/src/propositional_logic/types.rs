use std::{
    fmt::{Debug, Display},
    hash::Hash,
    usize, vec,
};

use colored::{Color, Colorize};
use indexmap::{IndexMap, IndexSet};
use termtree::Tree;

use crate::{
    markdown::Markdown,
    propositional_logic::{
        evaluate::{Evaluation, ExplainedValue, Interpretation, TruthValue},
        normal_forms::{ConjunctiveNormalForm, DisjunctiveNormalForm, Literal},
    },
};

#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub struct PropositionalVariable(pub String);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Proposition {
    Tautology,
    Contradiction,
    Atomic(PropositionalVariable),
    Negation(Box<Proposition>),
    Implication(Box<Proposition>, Box<Proposition>),
    Equivalence(Box<Proposition>, Box<Proposition>),
    Conjunction(Vec<Proposition>),
    Disjunction(Vec<Proposition>),
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

#[derive(Debug, Clone)]
pub struct VariableSet(pub IndexSet<PropositionalVariable>);

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
    pub fn symbol(&self) -> &str {
        match self {
            Proposition::Tautology => "⊤",
            Proposition::Contradiction => "⊥",
            Proposition::Atomic(p) => &p.0,
            Proposition::Negation(_) => "¬",
            Proposition::Implication(_, _) => "⇒",
            Proposition::Equivalence(_, _) => "⇔",
            Proposition::Conjunction(_) => "∧",
            Proposition::Disjunction(_) => "∨",
        }
    }

    pub fn is_compound(&self) -> bool {
        match self {
            Proposition::Tautology | Proposition::Contradiction | Proposition::Atomic(_) => false,
            Proposition::Negation(_)
            | Proposition::Implication(_, _)
            | Proposition::Equivalence(_, _)
            | Proposition::Conjunction(_)
            | Proposition::Disjunction(_) => true,
        }
    }

    pub fn negated(&self) -> Self {
        Proposition::Negation(Box::new(self.clone()))
    }

    pub fn get_tree(&self) -> Tree<String> {
        let symbol = self.symbol().to_owned();

        match self {
            Proposition::Tautology | Proposition::Contradiction | Proposition::Atomic(_) => {
                Tree::new(symbol)
            }
            Proposition::Negation(p) => Tree::new(symbol).with_leaves(vec![p.get_tree()]),
            Proposition::Implication(left, right) | Proposition::Equivalence(left, right) => {
                Tree::new(symbol).with_leaves(vec![left.get_tree(), right.get_tree()])
            }
            Proposition::Conjunction(propositions) | Proposition::Disjunction(propositions) => {
                Tree::new(symbol).with_leaves(propositions.iter().map(|p| p.get_tree()))
            }
        }
    }

    pub fn get_variables(&self) -> ExplainedValue<VariableSet> {
        let mut steps = vec![format!(
            "Collecting variables in {}",
            self.to_string().blue()
        )];

        match self {
            Proposition::Tautology | Proposition::Contradiction => ExplainedValue {
                value: VariableSet(IndexSet::new()),
                steps,
            },
            Proposition::Atomic(p) => {
                let mut variables = VariableSet(IndexSet::new());
                variables.0.insert(p.clone());

                steps.push(format!("=> {}", variables.to_string().green()));

                ExplainedValue {
                    value: variables,
                    steps,
                }
            }
            Proposition::Negation(p) => p.get_variables(),
            Proposition::Implication(left, right) | Proposition::Equivalence(left, right) => {
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
            Proposition::Conjunction(propositions) | Proposition::Disjunction(propositions) => {
                let variables = propositions.iter().map(|p| p.get_variables().value.0).fold(
                    IndexSet::new(),
                    |mut acc, set| {
                        acc.extend(set);
                        acc
                    },
                );

                ExplainedValue {
                    value: VariableSet(variables),
                    steps,
                }
            }
        }
    }

    pub fn get_subformulas(&self) -> IndexSet<&Self> {
        let mut subformulas = match self {
            Proposition::Negation(p) => p.get_subformulas(),
            Proposition::Implication(left, right) | Proposition::Equivalence(left, right) => {
                let mut subformulas = left.get_subformulas();
                subformulas.extend(right.get_subformulas());

                subformulas
            }
            Proposition::Conjunction(propositions) | Proposition::Disjunction(propositions) => {
                let mut subformulas = IndexSet::new();

                for proposition in propositions {
                    subformulas.extend(proposition.get_subformulas());
                }

                subformulas
            }
            _ => IndexSet::new(),
        };

        subformulas.insert(self);

        subformulas
    }

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

impl Display for Proposition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Proposition::Tautology => '⊤'.to_string(),
                Proposition::Contradiction => '⊥'.to_string(),
                Proposition::Atomic(p) => p.to_string(),
                Proposition::Negation(p) => format!("(¬{})", p),
                Proposition::Implication(left, right) => format!("({} ⇒ {})", left, right),
                Proposition::Equivalence(left, right) => format!("({} ⇔ {})", left, right),
                Proposition::Conjunction(propositions) => {
                    let propositions = propositions
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>();

                    match propositions.len() {
                        0 => '⊤'.to_string(),
                        1 => propositions[0].clone(),
                        _ => format!("({})", propositions.join(" ∧ ")),
                    }
                }
                Proposition::Disjunction(propositions) => {
                    let propositions = propositions
                        .iter()
                        .map(|p| p.to_string())
                        .collect::<Vec<_>>();

                    match propositions.len() {
                        0 => '⊥'.to_string(),
                        1 => propositions[0].clone(),
                        _ => format!("({})", propositions.join(" ∨ ")),
                    }
                }
            }
        )
    }
}

#[derive(Debug)]
pub struct TruthTable {
    pub columns: IndexMap<Proposition, Vec<TruthValue>>,
    pub highlighted_columns: IndexSet<Proposition>,
    pub highlighted_rows: IndexSet<usize>,
    pub hidden_columns: IndexSet<Proposition>,
    pub column_labels: IndexMap<Proposition, String>,
}

impl TruthTable {
    pub fn new(propositions: &[&Proposition]) -> Self {
        let mut truth_table = TruthTable {
            columns: IndexMap::new(),
            highlighted_columns: IndexSet::new(),
            highlighted_rows: IndexSet::new(),
            hidden_columns: IndexSet::new(),
            column_labels: IndexMap::new(),
        };

        let mut variables = VariableSet(IndexSet::new());
        let mut subformulas = IndexSet::new();

        for p in propositions {
            variables.0.extend(p.get_variables().value.0);
            subformulas.extend(p.get_subformulas());
        }

        subformulas.sort_by(|a, b| a.is_compound().cmp(&b.is_compound()));

        let interpretations = Interpretation::generate_all(variables);

        for interpretation in interpretations {
            for p in &subformulas {
                let ExplainedValue { value, .. } = p.evaluate(&interpretation);

                truth_table
                    .columns
                    .entry((*p).clone())
                    .or_insert(vec![])
                    .push(value);
            }
        }

        truth_table
    }

    pub fn get_attributes(&self, proposition: &Proposition) -> PropositionAttributes {
        let mut valid = true;
        let mut satisfiable = false;

        for i in self.columns[proposition].iter() {
            valid &= i.0;
            satisfiable |= i.0;
        }

        PropositionAttributes { valid, satisfiable }
    }
}

impl Display for TruthTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let subformulas = self
            .columns
            .keys()
            .filter(|&key| !self.hidden_columns.contains(key))
            .collect::<Vec<_>>();

        for &p in &subformulas {
            write!(
                f,
                "|{}",
                self.column_labels
                    .get(p)
                    .map(|label| label.to_owned())
                    .unwrap_or_else(|| p.to_string())
                    .blue()
                    .markdown()
            )?;
        }
        writeln!(f, "|")?;

        for _ in 0..subformulas.len() {
            write!(f, "|:-:")?;
        }
        writeln!(f, "|")?;

        let row_size = self.columns.values().next().unwrap().len();

        for i in 0..row_size {
            for &p in &subformulas {
                write!(f, "|{}", {
                    format!("{}", self.columns[p][i])
                        .color({
                            if self.highlighted_columns.contains(p)
                                || self.highlighted_rows.contains(&i)
                            {
                                Color::Red
                            } else {
                                Color::Black
                            }
                        })
                        .markdown()
                })?;
            }
            writeln!(f, "|")?;
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct LogicalEquivalence {
    pub left: Proposition,
    pub right: Proposition,
}

impl LogicalEquivalence {
    pub fn check(&self) -> ExplainedValue<bool> {
        let mut truth_table = TruthTable::new(&[&self.left, &self.right]);

        truth_table.highlighted_columns.insert(self.left.clone());
        truth_table.highlighted_columns.insert(self.right.clone());

        ExplainedValue {
            value: truth_table.columns[&self.left] == truth_table.columns[&self.right],
            steps: vec![format!("{truth_table}")],
        }
    }
}

#[derive(Debug, Clone)]
pub struct LogicalConsequence {
    pub premises: Vec<Proposition>,
    pub conclusion: Proposition,
}

impl LogicalConsequence {
    pub fn check(&self) -> ExplainedValue<bool> {
        let mut truth_table = TruthTable::new(
            &[
                self.premises.iter().collect::<Vec<_>>().as_slice(),
                &[&self.conclusion],
            ]
            .concat(),
        );

        let mut value = true;

        'outer: for i in 0..truth_table.columns[&self.premises[0]].len() {
            for premise in &self.premises {
                if !truth_table.columns[premise][i].0 {
                    continue 'outer;
                }
            }

            truth_table.highlighted_rows.insert(i);

            if !truth_table.columns[&self.conclusion][i].0 {
                value &= false;
            }
        }

        ExplainedValue {
            value,
            steps: vec![format!("{truth_table}")],
        }
    }
}

impl Display for LogicalConsequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ⊨ {}",
            self.premises
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.conclusion.to_string()
        )
    }
}

#[derive(Debug)]
pub struct TruthFunction<const N: usize>(pub fn(&[TruthValue; N]) -> TruthValue);

impl<const N: usize> TruthFunction<N> {
    // pub fn get_truth_table(&self) -> TruthTable {
    //     let binding = (0..N)
    //         .map(|i| PropositionalVariable(format!("A{i}")).into())
    //         .collect::<Vec<_>>();

    //     let variables = binding.iter().collect::<Vec<_>>();

    //     TruthTable::new(variables.as_slice())
    // }

    pub fn get_disjunctive_normal_form(&self) -> DisjunctiveNormalForm {
        let variables = (0..N)
            .map(|i| PropositionalVariable((('A' as u8 + i as u8) as char).to_string()))
            .collect::<IndexSet<_>>();

        let interpretations = Interpretation::generate_all(VariableSet(variables));

        DisjunctiveNormalForm(
            interpretations
                .filter_map(|interpretation| {
                    let binding = interpretation.0.values().copied().collect::<Vec<_>>();
                    let output = self.0(binding.as_slice().try_into().unwrap());

                    output.0.then(|| {
                        interpretation
                            .0
                            .into_iter()
                            .map(|(variable, value)| Literal(variable, value.0))
                            .collect()
                    })
                })
                .collect(),
        )
    }

    pub fn get_conjunctive_normal_form(&self) -> ConjunctiveNormalForm {
        let variables = (0..N)
            .map(|i| PropositionalVariable((('A' as u8 + i as u8) as char).to_string()))
            .collect::<IndexSet<_>>();

        let interpretations = Interpretation::generate_all(VariableSet(variables));

        ConjunctiveNormalForm(
            interpretations
                .filter_map(|interpretation| {
                    let binding = interpretation.0.values().copied().collect::<Vec<_>>();
                    let output = self.0(binding.as_slice().try_into().unwrap());

                    (!output.0).then(|| {
                        interpretation
                            .0
                            .into_iter()
                            .map(|(variable, value)| Literal(variable, !value.0))
                            .collect()
                    })
                })
                .collect(),
        )
    }
}

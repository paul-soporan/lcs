use std::collections::HashMap;

use indexmap::IndexSet;
use itertools::Itertools;
use ordermap::OrderMap;

use crate::ast::{ConjunctiveNormalForm, DisjunctiveNormalForm, Literal, PropositionalVariable};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment(pub OrderMap<PropositionalVariable, bool>);

impl Assignment {
    fn get_variables(&self) -> IndexSet<&PropositionalVariable> {
        self.0.keys().collect()
    }

    fn encode_variable(&self, variable: &PropositionalVariable) -> char {
        self.0
            .get(variable)
            .map(|&value| if value { '1' } else { '0' })
            .unwrap_or('*')
    }
}

fn is_prime_implicant(cnf: &ConjunctiveNormalForm, assignment: &Assignment) -> bool {
    let mut new_clauses = Vec::new();
    let mut critical_variables = IndexSet::new();

    for clause in cnf.0.iter() {
        let mut exists_true_literal = false;

        let mut mapped_clause = Vec::new();

        let mut mapped_to_1 = Vec::new();

        for Literal(variable, value) in clause {
            let encoding = assignment.encode_variable(&variable);
            if encoding == '*' {
                mapped_clause.push((variable, value));
            } else {
                let implicant_value = encoding == '1';
                let literal_value = implicant_value == *value;

                if literal_value {
                    exists_true_literal = true;
                    mapped_to_1.push(variable);
                }
            }
        }

        if !exists_true_literal {
            return false;
        }

        match mapped_to_1.len() {
            0 => new_clauses.push(mapped_clause),
            1 => {
                critical_variables.insert(mapped_to_1[0]);
            }
            _ => (),
        }
    }

    for clause in new_clauses {
        let mut t: HashMap<PropositionalVariable, (bool, bool)> = HashMap::new();

        for (variable, value) in clause {
            let entry = t.entry(variable.clone()).or_default();
            if *value {
                entry.0 = true;
            } else {
                entry.1 = true;
            }
        }

        for (_, (true_value, false_value)) in t {
            if !true_value || !false_value {
                return false;
            }
        }
    }

    let implicant_variables = assignment.get_variables();

    implicant_variables.is_subset(&critical_variables)
}

fn get_prime_implicants(cnf: &ConjunctiveNormalForm) -> IndexSet<Assignment> {
    let mut prime_implicants = IndexSet::new();

    let mut variables = IndexSet::new();
    for clause in &cnf.0 {
        for Literal(variable, _) in clause {
            variables.insert(variable);
        }
    }

    let product = (0..variables.len())
        .map(|_| ['0', '1', '*'].iter())
        .multi_cartesian_product();

    for s in product {
        let implicant = Assignment(
            variables
                .iter()
                .enumerate()
                .filter_map(|(i, &v)| {
                    let value = match s[i] {
                        '0' => false,
                        '1' => true,
                        _ => return None,
                    };
                    Some((v.clone(), value))
                })
                .collect(),
        );

        if is_prime_implicant(&cnf, &implicant) {
            prime_implicants.insert(implicant);
        }
    }

    prime_implicants
}

pub fn get_bcf(cnf: &ConjunctiveNormalForm) -> DisjunctiveNormalForm {
    let prime_implicants = get_prime_implicants(cnf);

    DisjunctiveNormalForm(
        prime_implicants
            .iter()
            .map(|implicant| {
                implicant
                    .0
                    .iter()
                    .map(|(variable, &value)| Literal(variable.clone(), value))
                    .collect()
            })
            .collect(),
    )
}

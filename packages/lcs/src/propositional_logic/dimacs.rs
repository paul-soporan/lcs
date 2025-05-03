use std::{
    collections::{BTreeSet, HashSet},
    str::FromStr,
};

use super::{
    normal_forms::{ConjunctiveNormalForm, Literal},
    types::PropositionalVariable,
};

#[derive(Debug)]
pub struct DimacsCnf {
    pub variable_count: usize,
    pub clause_count: usize,
    pub cnf: ConjunctiveNormalForm,
}

impl FromStr for DimacsCnf {
    type Err = String;

    fn from_str(data: &str) -> Result<Self, Self::Err> {
        parse_dimacs_cnf(data)
    }
}

fn parse_dimacs_cnf(data: &str) -> Result<DimacsCnf, String> {
    let mut variables = HashSet::new();

    let mut variable_count = None;
    let mut clause_count = None;
    let mut cnf = ConjunctiveNormalForm(BTreeSet::new());

    for line in data.lines() {
        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        let components = line.split_whitespace().collect::<Vec<_>>();
        if components[0] == "p" {
            if components.len() != 4 || components[1] != "cnf" {
                return Err(format!("Invalid DIMACS header: {}", line));
            }

            variable_count = Some(components[2].parse().unwrap());
            clause_count = Some(components[3].parse().unwrap());
        } else {
            if components.last() != Some(&"0") {
                return Err(format!("Invalid clause termination: {}", line));
            }

            let clause = components
                .iter()
                .take(components.len() - 1)
                .map(|&literal| {
                    let n = literal.parse::<i32>().unwrap();
                    if n == 0 {
                        panic!("Unexpected zero in clause: {}", line);
                    }

                    if n < 0 {
                        let variable = PropositionalVariable(format!("P{}", -n));
                        variables.insert(variable.clone());

                        Literal(variable, false)
                    } else {
                        let variable = PropositionalVariable(format!("P{}", n));
                        variables.insert(variable.clone());

                        Literal(variable, true)
                    }
                })
                .collect::<BTreeSet<_>>();

            cnf.0.insert(clause);
        }
    }

    let variable_count = if let Some(count) = variable_count {
        if variables.len() != count {
            return Err(format!(
                "Expected {} variables, found {}",
                count,
                variables.len()
            ));
        }

        count
    } else {
        variables.len()
    };

    let clause_count = if let Some(count) = clause_count {
        if cnf.0.len() != count {
            return Err(format!("Expected {} clauses, found {}", count, cnf.0.len()));
        }

        count
    } else {
        cnf.0.len()
    };

    Ok(DimacsCnf {
        variable_count,
        clause_count,
        cnf,
    })
}

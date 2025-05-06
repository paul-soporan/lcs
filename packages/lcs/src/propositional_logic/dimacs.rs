use std::{
    collections::HashSet,
    fmt::Display,
    hash::{Hash, Hasher},
    num::NonZeroI32,
    str::FromStr,
};

use indexmap::IndexSet;
use itertools::Itertools;
use nohash_hasher::IntSet;

use super::{normal_forms::Literal, types::PropositionalVariable};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct IntLiteral(NonZeroI32);

impl IntLiteral {
    pub fn new(value: i32) -> Self {
        IntLiteral(NonZeroI32::new(value).expect("Value cannot be zero"))
    }

    pub fn abs_value(&self) -> NonZeroI32 {
        self.0.abs()
    }

    pub fn abs(&self) -> Self {
        IntLiteral(self.0.abs())
    }

    pub fn complement(&self) -> Self {
        IntLiteral(-self.0)
    }

    pub fn is_positive(&self) -> bool {
        self.0.get() > 0
    }

    pub fn is_negative(&self) -> bool {
        self.0.get() < 0
    }

    pub fn to_literal(&self) -> Literal {
        Literal::from(*self)
    }
}

impl Hash for IntLiteral {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        hasher.write_i32(self.0.get())
    }
}

impl nohash_hasher::IsEnabled for IntLiteral {}

impl Display for IntLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_positive() {
            write!(f, "P{}", self.0)
        } else {
            write!(f, "¬P{}", -self.0)
        }
    }
}

impl From<IntLiteral> for Literal {
    fn from(literal: IntLiteral) -> Self {
        Literal(
            PropositionalVariable(format!("P{}", literal.abs_value())),
            literal.is_positive(),
        )
    }
}

// IntSet is a HashSet that uses the NoHashHasher.
// Therefore, iteration order is deterministic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause(pub IntSet<IntLiteral>);

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.0.len() < other.0.len() {
            Some(std::cmp::Ordering::Less)
        } else if self.0.len() > other.0.len() {
            Some(std::cmp::Ordering::Greater)
        } else {
            return self.0.iter().partial_cmp(&other.0);
        }
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.0.len() < other.0.len() {
            std::cmp::Ordering::Less
        } else if self.0.len() > other.0.len() {
            std::cmp::Ordering::Greater
        } else {
            return self.0.iter().cmp(&other.0);
        }
    }
}

impl Hash for Clause {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        for literal in &self.0 {
            literal.hash(hasher);
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let literals = self.0.iter().map(|literal| literal.to_string()).join(", ");

        write!(f, "{{{}}}", literals)
    }
}

#[derive(Debug)]
pub struct ClauseSet {
    pub clauses: IndexSet<Clause>,
    pub variable_count: usize,
}

impl FromStr for ClauseSet {
    type Err = String;

    fn from_str(data: &str) -> Result<Self, Self::Err> {
        parse_dimacs_cnf(data)
    }
}

fn parse_dimacs_cnf(data: &str) -> Result<ClauseSet, String> {
    let mut variables = HashSet::new();

    let mut variable_count = None;
    let mut clause_count = None;
    let mut clauses = IndexSet::new();

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

            let clause = Clause(
                components
                    .iter()
                    .take(components.len() - 1)
                    .map(|&literal| {
                        let n = literal.parse::<i32>().unwrap();
                        if n == 0 {
                            panic!("Unexpected zero in clause: {}", line);
                        }

                        variables.insert(n.abs());

                        IntLiteral::new(n)
                    })
                    .collect(),
            );

            clauses.insert(clause);
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

    if let Some(count) = clause_count {
        if clauses.len() != count {
            return Err(format!(
                "Expected {} clauses, found {}",
                count,
                clauses.len()
            ));
        }
    }

    for variable in variables {
        if variable > variable_count as i32 {
            return Err(format!("Invalid variable number: {}", variable));
        }
    }

    Ok(ClauseSet {
        clauses,
        variable_count,
    })
}

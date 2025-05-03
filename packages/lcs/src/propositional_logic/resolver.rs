use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
};

use colored::Colorize;
use indexmap::IndexSet;
use itertools::Itertools;
use replace_with::replace_with_or_abort;

use crate::{
    explanation::Explanation,
    markdown::Markdown,
    propositional_logic::{
        ast::{LogicalConsequence, Proposition},
        evaluate::{Interpretation, TruthValue},
        normal_forms::{ConjunctiveNormalForm, Literal, NegationNormalForm},
    },
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Clause(pub BTreeSet<Literal>);

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.0.len() < other.0.len() {
            Some(std::cmp::Ordering::Less)
        } else if self.0.len() > other.0.len() {
            Some(std::cmp::Ordering::Greater)
        } else {
            return self.0.partial_cmp(&other.0);
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
            return self.0.cmp(&other.0);
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let literals = self
            .0
            .iter()
            .map(|literal| literal.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        write!(f, "{{{}}}", literals)
    }
}

pub struct Resolver {
    clauses: IndexSet<Clause>,
    result_mapper: Box<dyn Fn(bool, &mut Explanation) -> bool>,
    required_literals: BTreeSet<Literal>,
}

impl Resolver {
    pub fn is_satisfiable(
        proposition: impl Into<Proposition>,
        explanation: &mut Explanation,
    ) -> Resolver {
        let proposition = proposition.into();

        explanation.with_subexplanation(
            format!(
                "Creating a satisfiability resolver for {}",
                proposition.to_string().blue().markdown()
            ),
            |explanation| {
                let nnf = NegationNormalForm::from_proposition(proposition, explanation);
                let cnf = ConjunctiveNormalForm::from_negation_normal_form(nnf, explanation);

                Self::new(cnf.0.into_iter().map(Clause).collect())
            },
        )
    }

    pub fn is_valid(
        proposition: impl Into<Proposition>,
        explanation: &mut Explanation,
    ) -> Resolver {
        let proposition = proposition.into();

        explanation.with_subexplanation(
            format!(
                "Creating a validity resolver for {}",
                proposition.to_string().blue().markdown()
            ),
            |explanation| {
                let negated_proposition = proposition.negated();

                Self::is_satisfiable(negated_proposition.clone(), explanation).with_result_mapper(
                    move |result, explanation| {
                        explanation.step(format!(
                            "{} is {}, therefore {} is {}",
                            negated_proposition.to_string().blue().markdown(),
                            if result {
                                "satisfiable".green().markdown()
                            } else {
                                "unsatisfiable".red().markdown()
                            },
                            proposition.to_string().blue().markdown(),
                            if !result {
                                "valid".green().markdown()
                            } else {
                                "invalid".red().markdown()
                            },
                        ));
                        !result
                    },
                )
            },
        )
    }

    pub fn check_logical_consequence(
        consequence: LogicalConsequence,
        explanation: &mut Explanation,
    ) -> Resolver {
        let mut propositions = consequence.premises.clone();
        propositions.push(consequence.conclusion.negated());

        let proposition = Proposition::Conjunction(propositions);

        explanation.with_subexplanation(
            format!(
                "Creating a logical consequence resolver for {}",
                consequence.to_string().blue().markdown()
            ),
            |explanation| {
                Self::is_satisfiable(proposition.clone(), explanation).with_result_mapper(
                    move |result, explanation| {
                        explanation.step(format!(
                            "{} is {}, therefore {} is {}",
                            proposition.to_string().blue().markdown(),
                            if result {
                                "satisfiable".green().markdown()
                            } else {
                                "unsatisfiable".red().markdown()
                            },
                            consequence.to_string().blue().markdown(),
                            if !result {
                                "true".green().markdown()
                            } else {
                                "false".red().markdown()
                            },
                        ));

                        !result
                    },
                )
            },
        )
    }

    pub fn new(clauses: BTreeSet<Clause>) -> Self {
        Self {
            clauses: IndexSet::from_iter(clauses),
            result_mapper: Box::new(|result, _| result),
            required_literals: BTreeSet::new(),
        }
    }

    pub fn with_result_mapper(
        mut self,
        result_mapper: impl Fn(bool, &mut Explanation) -> bool + 'static,
    ) -> Self {
        self.result_mapper = Box::new(result_mapper);
        self
    }

    fn find_new_resolvent(&self, explanation: &mut Explanation) -> Option<Clause> {
        explanation.with_subexplanation("Attempting to find a new resolvent", |explanation| {
            for (i, clause1) in self.clauses.iter().enumerate().sorted_by(|a, b| a.1.cmp(&b.1)) {
                for (j, clause2) in self.clauses.iter().skip(i + 1).enumerate().sorted_by(|a, b| a.1.cmp(&b.1)) {
                    'literals: for literal in &clause1.0 {
                        if clause2.0.contains(&literal.complement()) {
                            let resolvent = Clause(
                                clause1
                                    .0
                                    .union(&clause2.0)
                                    .filter(|l| l.0 != literal.0)
                                    .cloned()
                                    .collect::<BTreeSet<_>>(),
                            );

                            for literal in &resolvent.0 {
                                let complement = literal.complement();
                                if resolvent.0.contains(&complement) {
                                    explanation.step(format!(
                                        "Discarding redundant resolvent: {} - contains both {} and {}",
                                        resolvent.to_string().blue().markdown(),
                                        literal.to_string().green().markdown(),
                                        complement.to_string().red().markdown()
                                    ));
                                    continue 'literals;
                                }
                            }

                            if !self.clauses.contains(&resolvent) {
                                explanation.step(format!(
                                    "Found a new resolvent: {} from {} and {}",
                                    resolvent.to_string().blue().markdown(),
                                    format!("({})", i).to_string().magenta().markdown(),
                                    format!("({})", i + j + 1).to_string().magenta().markdown(),
                                ));
                                return Some(resolvent);
                            }
                        }
                    }
                }
            }


            explanation.step("No new resolvent found");

            None
        })
    }

    fn apply_resolution_step(&mut self, explanation: &mut Explanation) -> Option<bool> {
        explanation.with_subexplanation("Resolution step", |explanation| {
            match self.find_new_resolvent(explanation) {
                Some(resolvent) => {
                    if resolvent.0.is_empty() {
                        explanation.step("Found an empty resolvent, the formula is unsatisfiable");
                        return Some(false);
                    }

                    self.clauses.insert(resolvent);

                    None
                }
                None => {
                    explanation.step("No new resolvent found, the formula is satisfiable");

                    Some(true)
                }
            }
        })
    }

    fn apply_resolution(&mut self, explanation: &mut Explanation) -> bool {
        let result =
            explanation.with_subexplanation("Applying the resolution algorithm", |explanation| {
                loop {
                    explanation.with_subexplanation("Current clauses", |explanation| {
                        for (i, clause) in self.clauses.iter().enumerate() {
                            explanation.step(format!(
                                "{} {}",
                                format!("({})", i).to_string().magenta().markdown(),
                                clause.to_string().blue().markdown()
                            ));
                        }
                    });

                    if self.clauses.is_empty() {
                        explanation.step(format!(
                            "The formula has no clauses, therefore it is {}",
                            "satisfiable".green().markdown()
                        ));
                        return true;
                    }

                    for clause in &self.clauses {
                        if clause.0.is_empty() {
                            explanation.step(format!(
                                "Found an empty clause, therefore the formula is {}",
                                "unsatisfiable".red().markdown()
                            ));
                            return false;
                        }
                    }

                    match self.apply_resolution_step(explanation) {
                        Some(result) => return result,
                        None => continue,
                    }
                }
            });

        explanation.step(format!(
            "Result: {}",
            if result {
                "satisfiable".green().markdown()
            } else {
                "unsatisfiable".red().markdown()
            },
        ));

        result
    }

    fn find_one_literal(&self, explanation: &mut Explanation) -> Option<Literal> {
        explanation.with_subexplanation("Looking for a one literal clause", |explanation| {
            for clause in &self.clauses {
                if clause.0.len() == 1 {
                    explanation.step(format!(
                        "Found a one literal clause: {}",
                        clause.to_string().green().markdown()
                    ));
                    return Some(clause.0.first().unwrap().clone());
                }
            }

            explanation.step("No one literal clause found");
            None
        })
    }

    fn apply_one_literal_rule(&mut self, explanation: &mut Explanation) -> bool {
        explanation.with_subexplanation("Trying to apply the one literal rule", |explanation| {
            match self.find_one_literal(explanation) {
                Some(literal) => {
                    self.required_literals.insert(literal.clone());

                    replace_with_or_abort(&mut self.clauses, |clauses| {
                        let mut new_clauses = IndexSet::new();

                        for (i, clause) in clauses.into_iter().enumerate() {
                            if clause.0.contains(&literal) {
                                explanation.step(format!(
                                    "Removing clause {} because it contains {}",
                                    format!("({})", i).to_string().magenta().markdown(),
                                    literal.to_string().green().markdown()
                                ));
                                continue;
                            }

                            let complement = literal.complement();

                            let new_clause = Clause(
                                clause
                                    .0
                                    .difference(&BTreeSet::from([complement.clone()]))
                                    .cloned()
                                    .collect(),
                            );

                            if new_clause != clause {
                                explanation.with_subexplanation(
                                    format!(
                                        "Deleting {} from {}",
                                        complement.to_string().red().markdown(),
                                        format!("({})", i).to_string().magenta().markdown(),
                                    ),
                                    |explanation| {
                                        explanation.step(format!(
                                            "Result: {}",
                                            new_clause.to_string().blue().markdown(),
                                        ));
                                    },
                                );
                            }

                            new_clauses.insert(new_clause);
                        }

                        new_clauses
                    });

                    true
                }
                None => false,
            }
        })
    }

    fn find_pure_literal(&self, explanation: &mut Explanation) -> Option<Literal> {
        explanation.with_subexplanation("Looking for a pure literal", |explanation| {
            let mut literals = BTreeMap::new();

            for clause in &self.clauses {
                for literal in &clause.0 {
                    let entry = literals
                        .entry(literal.0.clone())
                        .or_insert_with(|| BTreeSet::new());
                    entry.insert(literal);
                }
            }

            for occurrences in literals.values() {
                if occurrences.len() == 1 {
                    let literal = occurrences.first().unwrap();
                    explanation.step(format!(
                        "Found a pure literal: {}",
                        literal.to_string().green().markdown()
                    ));
                    return Some(literal.clone().clone());
                }
            }

            explanation.step("No pure literal found");
            None
        })
    }

    fn apply_pure_literal_rule(&mut self, explanation: &mut Explanation) -> bool {
        explanation.with_subexplanation("Trying to apply the pure literal rule", |explanation| {
            match self.find_pure_literal(explanation) {
                Some(literal) => {
                    self.required_literals.insert(literal.clone());

                    replace_with_or_abort(&mut self.clauses, |clauses| {
                        clauses
                            .into_iter()
                            .enumerate()
                            .filter_map(|(i, clause)| {
                                if clause.0.contains(&literal) {
                                    explanation.step(format!(
                                        "Removing clause {} because it contains {}",
                                        format!("({})", i).to_string().magenta().markdown(),
                                        literal.to_string().green().markdown()
                                    ));
                                    None
                                } else {
                                    Some(clause)
                                }
                            })
                            .collect()
                    });

                    true
                }
                None => false,
            }
        })
    }

    fn apply_dp(&mut self, explanation: &mut Explanation) -> bool {
        let result =
            explanation.with_subexplanation("Applying the DP algorithm", |explanation| loop {
                let explanation = explanation.subexplanation("DP step");

                explanation.with_subexplanation("Current clauses", |explanation| {
                    for (i, clause) in self.clauses.iter().enumerate() {
                        explanation.step(format!(
                            "{} {}",
                            format!("({})", i).to_string().magenta().markdown(),
                            clause.to_string().blue().markdown()
                        ));
                    }
                });

                if self.clauses.is_empty() {
                    explanation.step(format!(
                        "No clauses left, therefore the formula is {}",
                        "satisfiable".green().markdown()
                    ));
                    return true;
                }

                for clause in &self.clauses {
                    if clause.0.is_empty() {
                        explanation.step(format!(
                            "Found an empty clause, therefore the formula is {}",
                            "unsatisfiable".red().markdown()
                        ));
                        return false;
                    }
                }

                if self.apply_one_literal_rule(explanation) {
                    continue;
                }

                if self.apply_pure_literal_rule(explanation) {
                    continue;
                }

                match self.apply_resolution_step(explanation) {
                    Some(result) => return result,
                    None => continue,
                }
            });

        explanation.step(format!(
            "Result: {}",
            if result {
                "satisfiable".green().markdown()
            } else {
                "unsatisfiable".red().markdown()
            },
        ));

        result
    }

    fn apply_split(&mut self, explanation: &mut Explanation) -> bool {
        let literal = self.clauses[0].0.first().unwrap().clone();

        explanation.with_subexplanation(
            format!("Splitting on {}", literal.to_string().green().markdown()),
            |explanation| {
                let clauses = self.clauses.clone();
                let literals = self.required_literals.clone();

                let positive_literal_clause = Clause(BTreeSet::from([literal.clone()]));
                let positive_literal_explanation = format!(
                    "Branch with clause {}",
                    positive_literal_clause.to_string().green().markdown()
                );

                self.clauses.insert(positive_literal_clause);
                self.required_literals.insert(literal.clone());

                let positive_literal_result =
                    self.apply_dpll(explanation.subexplanation(positive_literal_explanation));
                if positive_literal_result {
                    explanation.step(format!(
                        "Result: {}; no need to check the other branch",
                        "satisfiable".green().markdown()
                    ));
                    return true;
                }

                let negative_literal_clause = Clause(BTreeSet::from([literal.complement()]));
                let negative_literal_explanation = format!(
                    "Branch with clause {}",
                    negative_literal_clause.to_string().red().markdown()
                );

                self.clauses = clauses;
                self.required_literals = literals;

                self.clauses.insert(negative_literal_clause);
                self.required_literals.insert(literal.complement());

                let result =
                    self.apply_dpll(explanation.subexplanation(negative_literal_explanation));

                explanation.step(format!(
                    "Result: {}",
                    if result {
                        "satisfiable".green().markdown()
                    } else {
                        "unsatisfiable".red().markdown()
                    }
                ));

                result
            },
        )
    }

    fn apply_dpll(&mut self, explanation: &mut Explanation) -> bool {
        let result =
            explanation.with_subexplanation("Applying the DPLL algorithm", |explanation| loop {
                let explanation = explanation.subexplanation("DPLL step");

                explanation.with_subexplanation("Current clauses", |explanation| {
                    for (i, clause) in self.clauses.iter().enumerate() {
                        explanation.step(format!(
                            "{} {}",
                            format!("({})", i).to_string().magenta().markdown(),
                            clause.to_string().blue().markdown()
                        ));
                    }
                });

                if self.clauses.is_empty() {
                    explanation.step(format!(
                        "No clauses left, therefore the formula is {}",
                        "satisfiable".green().markdown()
                    ));
                    return true;
                }

                for clause in &self.clauses {
                    if clause.0.is_empty() {
                        explanation.step(format!(
                            "Found an empty clause, therefore the formula is {}",
                            "unsatisfiable".red().markdown()
                        ));
                        return false;
                    }
                }

                if self.apply_one_literal_rule(explanation) {
                    continue;
                }

                if self.apply_pure_literal_rule(explanation) {
                    continue;
                }

                return self.apply_split(explanation);
            });

        explanation.step(format!(
            "Result: {}",
            if result {
                "satisfiable".green().markdown()
            } else {
                "unsatisfiable".red().markdown()
            },
        ));

        result
    }

    pub fn resolution(&mut self, explanation: &mut Explanation) -> bool {
        let result = self.apply_resolution(explanation);

        (self.result_mapper)(result, explanation)
    }

    pub fn dp(&mut self, explanation: &mut Explanation) -> bool {
        let result = self.apply_dp(explanation);

        (self.result_mapper)(result, explanation)
    }

    pub fn dpll(&mut self, explanation: &mut Explanation) -> bool {
        let result = self.apply_dpll(explanation);

        (self.result_mapper)(result, explanation)
    }

    pub fn build_satisfying_interpretation_dp(
        &self,
        explanation: &mut Explanation,
    ) -> Interpretation {
        let clauses = BTreeSet::from_iter(self.clauses.clone());
        let mut interpretation = Interpretation::default();

        explanation.with_subexplanation("Building a satisfying truth valuation", |explanation| {
            for literal in &self.required_literals {
                interpretation
                    .0
                    .insert(literal.0.clone(), TruthValue(literal.1));

                explanation.step(format!(
                    "Adding {} to the truth valuation",
                    literal.to_string().green().markdown(),
                ));
            }

            'clause: for clause in clauses {
                let explanation = explanation.subexplanation(format!(
                    "Checking clause {}",
                    clause.to_string().blue().markdown()
                ));

                for literal in clause.0 {
                    let explanation = explanation.subexplanation(format!(
                        "Checking literal {}",
                        literal.to_string().blue().markdown()
                    ));

                    let existing = interpretation.0.get(&literal.0);
                    match existing {
                        Some(value) => {
                            if value.0 == literal.1 {
                                explanation.step("Literal evaluates to true according to the truth valuation, skipping clause");
                                continue 'clause;
                            } else {
                                explanation.step("Literal evaluates to false according to the truth valuation, skipping it");
                                continue;
                            }
                        }
                        None => {
                            explanation
                                .step("Literal is not in the truth valuation, adding it");

                            interpretation
                                .0
                                .insert(literal.0.clone(), TruthValue(literal.1));

                            continue 'clause;
                        }
                    }
                }
            }

            explanation.step(format!(
                "Result: {}",
                interpretation.to_string().green().markdown()
            ));
        });

        interpretation
    }

    pub fn build_satisfying_interpretation_dpll(
        &self,
        explanation: &mut Explanation,
    ) -> Interpretation {
        let mut interpretation = Interpretation::default();

        explanation.with_subexplanation("Building a satisfying truth valuation", |explanation| {
            for literal in &self.required_literals {
                interpretation
                    .0
                    .insert(literal.0.clone(), TruthValue(literal.1));

                explanation.step(format!(
                    "Adding {} to the truth valuation",
                    literal.to_string().green().markdown(),
                ));
            }

            explanation.step(format!(
                "Result: {}",
                interpretation.to_string().green().markdown()
            ));
        });

        interpretation
    }
}

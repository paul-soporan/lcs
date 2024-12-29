use std::{collections::BTreeMap, fmt::Display};

use colored::Colorize;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{explanation::Explanation, markdown::Markdown};

use super::{
    parser::{Formula, Signature, Term, Variable},
    substitution::Substitution,
};

pub struct ProofSituation {
    pub knowledge_base: IndexSet<Formula>,
    pub goal: Option<Formula>,
}

impl ProofSituation {
    pub fn prove(mut self, signature: &Signature) {
        println!("{}", self);

        let mut preserve_goal = false;

        if let Some(goal) = self.goal.clone() {
            if self.knowledge_base.contains(&goal) {
                println!("- The goal is trivially true.");

                return;
            }

            match goal {
                Formula::UniversalQuantification(variable, formula) => {
                    let new_goal = formula.with_substitution(
                        &Substitution::single(
                            variable.clone(),
                            Term::Variable(Variable(variable.0 + "0")),
                        ),
                        signature,
                        &mut Explanation::default(),
                    );

                    return ProofSituation {
                        knowledge_base: self.knowledge_base,
                        goal: Some(new_goal),
                    }
                    .prove(signature);
                }
                Formula::Implication(hypothesis, conclusion) => {
                    let mut new_knowledge_base = self.knowledge_base.clone();
                    new_knowledge_base.insert(*hypothesis);

                    return ProofSituation {
                        knowledge_base: new_knowledge_base,
                        goal: Some(*conclusion),
                    }
                    .prove(signature);
                }
                Formula::Negation(_) => {
                    preserve_goal = true;
                }
                _ => {}
            }
        }

        for formula in &self.knowledge_base {
            if self
                .knowledge_base
                .contains(&Formula::Negation(Box::new(formula.clone())))
            {
                println!("- Proof by contradiction.");

                return;
            }

            match formula {
                Formula::UniversalQuantification(variable, formula) => {
                    if let Some(goal) = self.goal.clone() {
                        let mut variables_by_scope = BTreeMap::new();
                        goal.get_symbols("", &mut variables_by_scope);
                        let goal_variables = variables_by_scope
                            .get("")
                            .unwrap()
                            .keys()
                            .cloned()
                            .collect_vec();
                        let mut knowledge_base = self.knowledge_base.clone();

                        for goal_variable in goal_variables {
                            knowledge_base.insert(formula.with_substitution(
                                &Substitution::single(
                                    variable.clone(),
                                    Term::Variable(goal_variable),
                                ),
                                signature,
                                &mut Explanation::default(),
                            ));
                        }

                        if knowledge_base != self.knowledge_base {
                            return ProofSituation {
                                knowledge_base,
                                goal: Some(goal),
                            }
                            .prove(signature);
                        }
                    }
                }
                Formula::Implication(box hypothesis, box conclusion) => {
                    if let Some(goal) = self.goal.clone() {
                        if conclusion == &goal && !preserve_goal {
                            let mut knowledge_base = self.knowledge_base.clone();

                            // knowledge_base.shift_remove(hypothesis);

                            return ProofSituation {
                                knowledge_base,
                                goal: Some(hypothesis.clone()),
                            }
                            .prove(signature);
                        }
                    }

                    if self.knowledge_base.contains(hypothesis)
                        && !self.knowledge_base.contains(conclusion)
                    {
                        self.knowledge_base.insert(conclusion.clone());

                        return self.prove(signature);
                    }
                }
                _ => {}
            }
        }

        if let Some(goal) = self.goal.clone() {
            let negated = match goal {
                Formula::Negation(box goal) => goal,
                goal => Formula::Negation(Box::new(goal)),
            };

            self.knowledge_base.insert(negated.clone());

            ProofSituation {
                knowledge_base: self.knowledge_base,
                goal: None,
            }
            .prove(signature)
        }
    }
}

impl Display for ProofSituation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<pre>")?;
        writeln!(f, "Knowledge Base:")?;
        writeln!(
            f,
            "{}",
            self.knowledge_base
                .iter()
                .map(|formula| format!("\n- {}", formula))
                .join("")
                .red()
                .markdown()
        )?;
        write!(f, " ⊢ ")?;
        writeln!(
            f,
            "{}",
            match &self.goal {
                Some(goal) => goal.to_string().green().markdown(),
                None => "None".green().markdown(),
            }
        )?;
        writeln!(f, "</pre>")
    }
}

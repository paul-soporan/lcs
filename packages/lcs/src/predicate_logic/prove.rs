use std::fmt::Display;

use colored::Colorize;
use indexmap::{indexset, IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    explanation::{DiscardedExplanation, Explain},
    markdown::Markdown,
};

use super::{
    substitution::Substitution,
    types::{Formula, Term, Variable},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofSituation {
    pub knowledge_base: IndexSet<Formula>,
    pub goal: Formula,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofResult {
    Proven,
    Contradiction,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofNode {
    Trivial,
    Proof(Proof),
    And(Proof, Proof),
    Or(Proof, Proof),
    Case(Proof, Proof),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    pub rule: String,
    pub node: ProofNode,
    pub result: ProofResult,

    pub announcement: String,
    pub inputs: IndexSet<Formula>,
    pub outputs: IndexSet<Formula>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    pub situation: ProofSituation,
    pub result: ProofResult,
    pub next_step: Option<Box<ProofStep>>,
}

impl Proof {
    pub fn trim(&self) -> Proof {
        let (proof, _) = self.trim_impl();
        proof
    }

    fn trim_impl(&self) -> (Proof, IndexSet<Formula>) {
        fn trim_knowledge_base(proof: &mut Proof, unused_formulas: &IndexSet<Formula>) {
            proof
                .situation
                .knowledge_base
                .retain(|formula| !unused_formulas.contains(formula));

            if let Some(step) = &mut proof.next_step {
                match &mut step.node {
                    ProofNode::Proof(proof) => {
                        trim_knowledge_base(proof, unused_formulas);
                    }
                    ProofNode::And(left, right)
                    | ProofNode::Or(left, right)
                    | ProofNode::Case(left, right) => {
                        trim_knowledge_base(left, unused_formulas);
                        trim_knowledge_base(right, unused_formulas);
                    }
                    _ => {}
                }
            }
        }

        match &self.next_step {
            None => (self.clone(), indexset! {}),
            Some(step) => match &step.node {
                ProofNode::Trivial => (self.clone(), step.inputs.clone()),

                ProofNode::Proof(proof) => {
                    let (mut proof, inputs) = proof.trim_impl();
                    if inputs.intersection(&step.outputs).count() == 0 {
                        trim_knowledge_base(&mut proof, &step.outputs);

                        (proof, inputs)
                    } else {
                        let mut trimmed_step = step.clone();
                        trimmed_step.node = ProofNode::Proof(proof);

                        (
                            Proof {
                                situation: self.situation.clone(),
                                result: self.result,
                                next_step: Some(trimmed_step),
                            },
                            inputs.union(&step.inputs).cloned().collect(),
                        )
                    }
                }

                ProofNode::And(left, right) => {
                    let (left_proof, left_inputs) = left.trim_impl();
                    let (right_proof, right_inputs) = right.trim_impl();

                    let mut all_inputs = step.inputs.clone();
                    all_inputs.extend(left_inputs);
                    all_inputs.extend(right_inputs);

                    let mut trimmed_step = step.clone();
                    trimmed_step.node = ProofNode::And(left_proof, right_proof);

                    (
                        Proof {
                            situation: self.situation.clone(),
                            result: self.result,
                            next_step: Some(trimmed_step),
                        },
                        all_inputs,
                    )
                }

                ProofNode::Or(left, right) => {
                    let (left_proof, left_inputs) = left.trim_impl();
                    let (right_proof, right_inputs) = right.trim_impl();

                    let mut all_inputs = step.inputs.clone();
                    all_inputs.extend(left_inputs);
                    all_inputs.extend(right_inputs);

                    let mut trimmed_step = step.clone();
                    trimmed_step.node = ProofNode::Or(left_proof, right_proof);

                    (
                        Proof {
                            situation: self.situation.clone(),
                            result: self.result,
                            next_step: Some(trimmed_step),
                        },
                        all_inputs,
                    )
                }

                ProofNode::Case(left, right) => {
                    let (left_proof, left_inputs) = left.trim_impl();
                    let (right_proof, right_inputs) = right.trim_impl();

                    let mut all_inputs = step.inputs.clone();
                    all_inputs.extend(left_inputs);
                    all_inputs.extend(right_inputs);

                    let mut trimmed_step = step.clone();
                    trimmed_step.node = ProofNode::Case(left_proof, right_proof);

                    (
                        Proof {
                            situation: self.situation.clone(),
                            result: self.result,
                            next_step: Some(trimmed_step),
                        },
                        all_inputs,
                    )
                }
            },
        }
    }

    pub fn describe(&self, formula_labels: &IndexMap<Formula, String>) -> String {
        let mut formula_labels = formula_labels.clone();

        let mut description = "We know the following:".to_owned();

        let mut assumption_count = 0;
        let mut goal_count = 0;

        let mut label_assumption = |formula: &Formula, labels: &mut IndexMap<Formula, String>| {
            labels.entry(formula.clone()).or_insert_with(|| {
                assumption_count += 1;
                format!("A{}", assumption_count)
            });
        };
        let mut label_goal = |formula: &Formula, labels: &mut IndexMap<Formula, String>| {
            labels.entry(formula.clone()).or_insert_with(|| {
                goal_count += 1;
                format!("G{}", goal_count)
            });
        };

        fn pretty_label(label: &str, definition: bool) -> String {
            format!("({})", label)
                .color(if definition { "magenta" } else { "yellow" })
                .markdown()
        }

        let labeled_formula = |formula: &Formula, labels: &IndexMap<Formula, String>| {
            format!(
                "\n    {}    {}",
                formula.to_string().green().markdown(),
                pretty_label(&labels[formula], true)
            )
        };

        for formula in &self.situation.knowledge_base {
            label_assumption(formula, &mut formula_labels);

            description.push_str(&labeled_formula(formula, &formula_labels));
        }

        label_goal(&self.situation.goal, &mut formula_labels);

        description.push_str("\nWe want to prove:");
        description.push_str(&labeled_formula(&self.situation.goal, &formula_labels));

        description.push_str("\n\n");

        let is_goal = |formula: &Formula, step: &ProofStep| match &step.node {
            ProofNode::Proof(proof) => formula == &proof.situation.goal,
            ProofNode::And(left, right)
            | ProofNode::Or(left, right)
            | ProofNode::Case(left, right) => {
                formula == &left.situation.goal || formula == &right.situation.goal
            }
            _ => false,
        };

        let mut interpolate_values =
            |step: &ProofStep, mut formula_labels: &mut IndexMap<Formula, String>| {
                let mut announcement = step.announcement.clone();

                for output in &step.outputs {
                    if is_goal(output, step) {
                        label_goal(output, &mut formula_labels);
                    } else {
                        label_assumption(output, &mut formula_labels);
                    }
                }

                if announcement.contains("%I1") {
                    announcement = announcement.replace(
                        "%I1",
                        &formula_labels
                            .get(&step.inputs[0])
                            .map(|label| pretty_label(label, false))
                            .unwrap_or_else(|| step.inputs[0].to_string()),
                    );
                }
                if announcement.contains("%I2") {
                    announcement = announcement.replace(
                        "%I2",
                        &formula_labels
                            .get(&step.inputs[1])
                            .map(|label| pretty_label(label, false))
                            .unwrap_or_else(|| step.inputs[1].to_string()),
                    );
                }
                if announcement.contains("%O1") {
                    announcement = announcement.replace(
                        " %O1",
                        &format!(":{}\n", labeled_formula(&step.outputs[0], &formula_labels)),
                    );
                } else {
                    announcement += "\n";
                }

                if announcement.contains("%O2") {
                    announcement = announcement.replace(
                        " %O2",
                        &format!("{}\n", labeled_formula(&step.outputs[1], &formula_labels)),
                    );
                }

                announcement += "\n";

                announcement
            };

        fn describe_proof(
            proof: &Proof,
            indent: usize,
            interpolate_values: &mut dyn FnMut(
                &ProofStep,
                &mut IndexMap<Formula, String>,
            ) -> String,
            labels: &mut IndexMap<Formula, String>,
        ) -> String {
            let mut description = String::new();

            if let Some(step) = &proof.next_step {
                description.push_str(&interpolate_values(step, labels));

                match &step.node {
                    ProofNode::Proof(proof) => {
                        description += &describe_proof(proof, 0, interpolate_values, labels);
                    }
                    ProofNode::Case(left, right) => {
                        description.push_str(&format!(
                            "Case {} {}:\n",
                            step.outputs[0].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[0]], true)
                        ));
                        description +=
                            &describe_proof(left, indent + 2, interpolate_values, labels);

                        description.push_str(&format!(
                            "Case {} {}:\n",
                            step.outputs[1].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[1]], true)
                        ));
                        description +=
                            &describe_proof(right, indent + 2, interpolate_values, labels);

                        if left.result == ProofResult::Contradiction
                            && right.result == ProofResult::Contradiction
                        {
                            description.push_str(&format!(
                                "Both cases lead to a contradiction. Therefore, we get a contradiction.\n",
                            ));
                        }
                    }
                    ProofNode::And(left, right) => {
                        description.push_str(&format!(
                            "Proving {} {}:\n",
                            step.outputs[0].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[0]], true)
                        ));
                        description +=
                            &describe_proof(left, indent + 2, interpolate_values, labels);

                        description.push_str(&format!(
                            "Proving {} {}:\n",
                            step.outputs[1].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[1]], true)
                        ));
                        description +=
                            &describe_proof(right, indent + 2, interpolate_values, labels);
                    }
                    ProofNode::Or(left, right) => {
                        description.push_str(&format!(
                            "Proving {} {}:\n",
                            step.outputs[0].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[0]], true)
                        ));
                        description +=
                            &describe_proof(left, indent + 2, interpolate_values, labels);

                        description.push_str(&format!(
                            "Proving {} {}:\n",
                            step.outputs[1].to_string().green().markdown(),
                            pretty_label(&labels[&step.outputs[1]], true)
                        ));
                        description +=
                            &describe_proof(right, indent + 2, interpolate_values, labels);
                    }
                    _ => {}
                }
            }

            description
                .split('\n')
                .map(|line| {
                    if line.is_empty() {
                        line.to_owned()
                    } else {
                        " ".repeat(indent) + line
                    }
                })
                .join("\n")
        }

        description += &describe_proof(self, 0, &mut interpolate_values, &mut formula_labels);

        format!("\n<pre>{}</pre>", description)
    }

    pub fn explain(&self, explanation: &mut impl Explain) {
        explanation.with_subexplanation(
            || "Proof situation",
            |explanation| {
                explanation.with_subexplanation(
                    || "Knowledge Base",
                    |explanation| {
                        for formula in &self.situation.knowledge_base {
                            explanation.step(|| formula.to_string().magenta().markdown());
                        }
                    },
                );

                explanation.with_subexplanation(
                    || "Goal",
                    |explanation| {
                        explanation.step(|| {
                            format!("⊢ {}", self.situation.goal.to_string().green().markdown())
                        });
                    },
                );
            },
        );

        explanation.step(|| {
            format!(
                "Result: {}",
                match self.result {
                    ProofResult::Proven => "Proven".green().markdown(),
                    ProofResult::Contradiction => "Contradiction".red().markdown(),
                    ProofResult::Unknown => "Unknown".yellow().markdown(),
                }
            )
        });

        explanation.with_subexplanation(
            || "Next step",
            |explanation| match &self.next_step {
                Some(next_step) => {
                    explanation.step(|| format!("Rule: {}", next_step.rule.red().markdown()));

                    explanation.with_subexplanation(
                        || "Inputs",
                        |explanation| {
                            for formula in &next_step.inputs {
                                explanation.step(|| formula.to_string().magenta().markdown());
                            }
                        },
                    );
                    explanation.with_subexplanation(
                        || "Outputs",
                        |explanation| {
                            for formula in &next_step.outputs {
                                explanation.step(|| formula.to_string().green().markdown());
                            }
                        },
                    );

                    match &next_step.node {
                        ProofNode::Trivial => {
                            explanation.step(|| {
                                format!(
                                    "Trivial: {}",
                                    match next_step.result {
                                        ProofResult::Proven => "Local".green().markdown(),
                                        ProofResult::Contradiction =>
                                            "Contradiction".red().markdown(),
                                        ProofResult::Unknown => "Unknown".yellow().markdown(),
                                    }
                                )
                            });
                        }
                        ProofNode::Proof(next_proof) => {
                            next_proof.explain(explanation);
                        }
                        ProofNode::And(left_proof, right_proof) => explanation.with_subexplanation(
                            || "And node",
                            |explanation| {
                                left_proof.explain(explanation);
                                right_proof.explain(explanation);
                            },
                        ),
                        ProofNode::Or(left_proof, right_proof) => explanation.with_subexplanation(
                            || "Or node",
                            |explanation| {
                                left_proof.explain(explanation);
                                right_proof.explain(explanation);
                            },
                        ),
                        ProofNode::Case(left_proof, right_proof) => explanation
                            .with_subexplanation(
                                || "Case node",
                                |explanation| {
                                    left_proof.explain(explanation);
                                    right_proof.explain(explanation);
                                },
                            ),
                    }
                }
                None => {}
            },
        )
    }
}

fn negated_formula(formula: &Formula) -> Formula {
    Formula::Negation(Box::new(formula.clone()))
}

fn is_formula_simpler(left: &Formula, right: &Formula) -> bool {
    if matches!(left, Formula::PredicateApplication { .. })
        && matches!(
            right,
            Formula::Conjunction { .. }
                | Formula::Disjunction { .. }
                | Formula::Implication { .. }
                | Formula::Equivalence { .. }
        )
    {
        return true;
    }

    false
}

impl ProofSituation {
    pub fn build_proof(&self) -> Proof {
        match self.apply_rules() {
            Some(step) => {
                if let ProofNode::Proof(proof) = &step.node
                    && proof.situation == *self
                {
                    panic!("Infinitely recursive proof rules");
                } else {
                    Proof {
                        situation: self.clone(),
                        result: step.result,
                        next_step: Some(Box::new(step)),
                    }
                }
            }
            None => Proof {
                situation: self.clone(),
                result: ProofResult::Unknown,
                next_step: None,
            },
        }
    }

    fn apply_rules(&self) -> Option<ProofStep> {
        self.use_local()
            .or_else(|| self.use_contradiction())
            .or_else(|| self.simplify_goal())
            .or_else(|| self.use_suffices_to_prove())
            .or_else(|| self.use_modus_ponens())
            .or_else(|| self.use_conjunction())
            .or_else(|| self.use_negation())
            .or_else(|| self.use_cases())
            .or_else(|| self.use_universal_quantifier())
            .or_else(|| self.proof_by_contradiction())
            .or_else(|| self.use_contrapositive())
            .or_else(|| self.reduce_implication())
    }

    fn use_local(&self) -> Option<ProofStep> {
        if self.knowledge_base.contains(&self.goal) {
            return Some(ProofStep {
                rule: "local".to_string(),
                result: ProofResult::Proven,
                node: ProofNode::Trivial,
                announcement: "%I1 is what we had to prove.".to_string(),
                inputs: indexset! {self.goal.clone()},
                outputs: indexset! {},
            });
        }

        None
    }

    fn use_contradiction(&self) -> Option<ProofStep> {
        for (formula_index, formula) in self.knowledge_base.iter().enumerate() {
            let negated = negated_formula(formula);
            let negated_index = self.knowledge_base.get_index_of(&negated);

            if let Some(negated_index) = negated_index {
                return Some(ProofStep {
                    rule: "contradiction".to_string(),
                    result: ProofResult::Contradiction,
                    node: ProofNode::Trivial,
                    announcement: "%I1 is in contradiction with %I2.".to_string(),
                    inputs: if formula_index < negated_index {
                        indexset! {negated, formula.clone()}
                    } else {
                        indexset! {formula.clone(), negated}
                    },
                    outputs: indexset! {},
                });
            }
        }

        None
    }

    fn simplify_goal(&self) -> Option<ProofStep> {
        match &self.goal {
            Formula::Conjunction(box left, box right) => {
                let left_proof = ProofSituation {
                    knowledge_base: self.knowledge_base.clone(),
                    goal: left.clone(),
                }
                .build_proof();
                let right_proof = ProofSituation {
                    knowledge_base: self.knowledge_base.clone(),
                    goal: right.clone(),
                }
                .build_proof();

                return Some(ProofStep {
                    rule: "⊢ ∧".to_string(),
                    result: match (left_proof.result, right_proof.result) {
                        (ProofResult::Proven, ProofResult::Proven) => ProofResult::Proven,
                        (ProofResult::Contradiction, _) | (_, ProofResult::Contradiction) => {
                            ProofResult::Contradiction
                        }
                        _ => ProofResult::Unknown,
                    },
                    node: ProofNode::And(left_proof, right_proof),
                    announcement: "To prove %I1, prove %O1 and prove %O2".to_string(),
                    inputs: indexset! {self.goal.clone()},
                    outputs: indexset! {left.clone(), right.clone()},
                });
            }

            Formula::Disjunction(box left, box right) => {
                let left_proof = ProofSituation {
                    knowledge_base: self.knowledge_base.clone(),
                    goal: left.clone(),
                }
                .build_proof();
                let right_proof = ProofSituation {
                    knowledge_base: self.knowledge_base.clone(),
                    goal: right.clone(),
                }
                .build_proof();

                return Some(ProofStep {
                    rule: "⊢ ∨".to_string(),
                    result: match (left_proof.result, right_proof.result) {
                        (ProofResult::Contradiction, ProofResult::Contradiction) => {
                            ProofResult::Contradiction
                        }
                        (ProofResult::Proven, _) | (_, ProofResult::Proven) => ProofResult::Proven,
                        _ => ProofResult::Unknown,
                    },
                    node: ProofNode::Or(left_proof, right_proof),
                    announcement: "To prove %I1, prove %O1 or prove %O2".to_string(),
                    inputs: indexset! {self.goal.clone()},
                    outputs: indexset! {left.clone(), right.clone()},
                });
            }

            Formula::Implication(box hypothesis, box conclusion) => {
                let mut knowledge_base = self.knowledge_base.clone();
                knowledge_base.insert(hypothesis.clone());

                let next_proof = ProofSituation {
                    knowledge_base,
                    goal: conclusion.clone(),
                }
                .build_proof();

                return Some(ProofStep {
                    rule: "⊢⇒".to_string(),
                    result: next_proof.result,
                    node: ProofNode::Proof(next_proof),
                    announcement: "To prove %I1, assume %O1 and show %O2".to_string(),
                    inputs: indexset! {self.goal.clone()},
                    outputs: indexset! {hypothesis.clone(), conclusion.clone()},
                });
            }

            Formula::UniversalQuantification(variable, formula) => {
                let arbitrary_variable_name = variable.0.clone() + "0";

                let next_goal = formula.with_substitution(
                    &Substitution::single(
                        variable.clone(),
                        Term::Variable(Variable(arbitrary_variable_name.clone())),
                    ),
                    &mut DiscardedExplanation,
                );

                let next_proof = ProofSituation {
                    knowledge_base: self.knowledge_base.clone(),
                    goal: next_goal.clone(),
                }
                .build_proof();

                return Some(ProofStep {
                    rule: "⊢ ∀".to_string(),
                    result: next_proof.result,
                    node: ProofNode::Proof(next_proof),
                    announcement: format!(
                        "To prove %I1, take {} arbitrary but fixed, and prove %O1",
                        arbitrary_variable_name.magenta().markdown()
                    )
                    .to_string(),
                    inputs: indexset! {self.goal.clone()},
                    outputs: indexset! {next_goal},
                });
            }

            _ => {}
        };

        None
    }

    fn reduce_implication(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Implication(hypothesis, conclusion) => {
                    let disjunction = Formula::Disjunction(
                        Box::new(Formula::Negation(hypothesis.clone())),
                        conclusion.clone(),
                    );

                    if !self.knowledge_base.contains(&disjunction) {
                        let mut knowledge_base = self.knowledge_base.clone();
                        knowledge_base.insert(disjunction.clone());

                        let next_proof = ProofSituation {
                            knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "⊢⇒ ⊢".to_string(),
                            result: next_proof.result,
                            node: ProofNode::Proof(next_proof),
                            announcement: "Since we know %I1, we know %O1".to_owned(),
                            inputs: indexset! {formula.clone()},
                            outputs: indexset! {disjunction},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_suffices_to_prove(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Implication(box hypothesis, box conclusion) => {
                    if conclusion == &self.goal && is_formula_simpler(hypothesis, conclusion) {
                        let mut knowledge_base = self.knowledge_base.clone();
                        knowledge_base.shift_remove(formula);

                        let next_proof = ProofSituation {
                            knowledge_base,
                            goal: hypothesis.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "⇒⊢".to_string(),
                            result: next_proof.result,
                            node: ProofNode::Proof(next_proof),
                            announcement:
                                "To prove %I1, since we know %I2, it suffices to prove %O1"
                                    .to_owned(),
                            inputs: indexset! {self.goal.clone(), formula.clone()},
                            outputs: indexset! {hypothesis.clone()},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_universal_quantifier(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::UniversalQuantification(variable, box subformula) => {
                    let goal_variables = self.goal.get_free_root_variables();
                    let mut knowledge_base = self.knowledge_base.clone();

                    let free_variables = self.knowledge_base.iter().fold(
                        goal_variables,
                        |mut variables, formula| {
                            variables.extend(formula.get_free_root_variables());
                            variables
                        },
                    );

                    for free_variable in free_variables {
                        let next_formula = subformula.with_substitution(
                            &Substitution::single(variable.clone(), Term::Variable(free_variable)),
                            &mut DiscardedExplanation,
                        );

                        if self.knowledge_base.contains(&next_formula) {
                            continue;
                        }

                        knowledge_base.insert(next_formula.clone());

                        let next_proof = ProofSituation {
                            knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "∀ ⊢".to_string(),
                            result: next_proof.result,
                            node: ProofNode::Proof(next_proof),
                            announcement: "Since we know %I1, in particular, we know %O1"
                                .to_owned(),
                            inputs: indexset! {formula.clone()},
                            outputs: indexset! {next_formula},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_contrapositive(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Implication(box hypothesis, box conclusion) => {
                    let negated_conclusion = Formula::Negation(Box::new(conclusion.clone()));
                    let negated_hypothesis = Formula::Negation(Box::new(hypothesis.clone()));

                    let contrapositive = Formula::Implication(
                        Box::new(negated_conclusion),
                        Box::new(negated_hypothesis),
                    );

                    if !self.knowledge_base.contains(&contrapositive) {
                        let mut knowledge_base = self.knowledge_base.clone();
                        knowledge_base.insert(contrapositive.clone());

                        let next_proof = ProofSituation {
                            knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "contrapositive".to_string(),
                            result: next_proof.result,
                            node: ProofNode::Proof(next_proof),
                            announcement: "Since we know %I1, by contraposition, we know %O1"
                                .to_owned(),
                            inputs: indexset! {formula.clone()},
                            outputs: indexset! {contrapositive},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_cases(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Disjunction(box left, box right) => {
                    if !self.knowledge_base.contains(left) && !self.knowledge_base.contains(right) {
                        let mut knowledge_base = self.knowledge_base.clone();
                        knowledge_base.shift_remove(formula);

                        let mut left_knowledge_base = knowledge_base.clone();
                        left_knowledge_base.insert(left.clone());

                        let left_proof = ProofSituation {
                            knowledge_base: left_knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        let mut right_knowledge_base = knowledge_base.clone();
                        right_knowledge_base.insert(right.clone());

                        let right_proof = ProofSituation {
                            knowledge_base: right_knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "∨ ⊢".to_string(),
                            result: match (left_proof.result, right_proof.result) {
                                (ProofResult::Contradiction, ProofResult::Contradiction) => {
                                    ProofResult::Contradiction
                                }
                                (ProofResult::Unknown, _) | (_, ProofResult::Unknown) => {
                                    ProofResult::Unknown
                                }
                                _ => ProofResult::Proven,
                            },
                            node: ProofNode::Case(left_proof, right_proof),
                            announcement: "We prove by cases:".to_owned(),
                            inputs: indexset! {formula.clone()},
                            outputs: indexset! {left.clone(), right.clone()},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_modus_ponens(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Implication(box hypothesis, box conclusion) => {
                    if !self.knowledge_base.contains(conclusion) {
                        if self.knowledge_base.contains(hypothesis) {
                            let mut knowledge_base = self.knowledge_base.clone();
                            knowledge_base.insert(conclusion.clone());

                            let next_proof = ProofSituation {
                                knowledge_base,
                                goal: self.goal.clone(),
                            }
                            .build_proof();

                            return Some(ProofStep {
                                rule: "modus ponens".to_string(),
                                result: next_proof.result,
                                node: ProofNode::Proof(next_proof),
                                announcement: "From %I1 and %I2, by modus ponens, we get %O1"
                                    .to_owned(),
                                inputs: indexset! {formula.clone(), hypothesis.clone()},
                                outputs: indexset! {conclusion.clone()},
                            });
                        }

                        match hypothesis {
                            Formula::Conjunction(box left, box right) => {
                                if self.knowledge_base.contains(left)
                                    && self.knowledge_base.contains(right)
                                {
                                    let mut knowledge_base = self.knowledge_base.clone();
                                    knowledge_base.insert(hypothesis.clone());

                                    let next_proof = ProofSituation {
                                        knowledge_base,
                                        goal: self.goal.clone(),
                                    }
                                    .build_proof();

                                    return Some(ProofStep {
                                        rule: "modus ponens preparation".to_string(),
                                        result: next_proof.result,
                                        node: ProofNode::Proof(next_proof),
                                        announcement: "Since we know both %I1 and %I2, we know their conjunction %O1"
                                            .to_owned(),
                                        inputs: indexset! {left.clone(), right.clone()},
                                        outputs: indexset! {hypothesis.clone()},
                                    });
                                }
                            }
                            _ => {}
                        }
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_conjunction(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Conjunction(box left, box right) => {
                    if !self.knowledge_base.contains(left) || !self.knowledge_base.contains(right) {
                        let mut knowledge_base = self.knowledge_base.clone();
                        knowledge_base.insert(left.clone());
                        knowledge_base.insert(right.clone());

                        let next_proof = ProofSituation {
                            knowledge_base,
                            goal: self.goal.clone(),
                        }
                        .build_proof();

                        return Some(ProofStep {
                            rule: "∧ ⊢".to_string(),
                            result: next_proof.result,
                            node: ProofNode::Proof(next_proof),
                            announcement: "Since we know %I1, we know both %O1 and %O2".to_owned(),
                            inputs: indexset! {formula.clone()},
                            outputs: indexset! {left.clone(), right.clone()},
                        });
                    }
                }

                _ => {}
            }
        }

        None
    }

    fn use_negation(&self) -> Option<ProofStep> {
        for formula in &self.knowledge_base {
            match formula {
                Formula::Negation(box negated_formula) => match negated_formula {
                    Formula::Negation(box double_negated_formula) => {
                        if !self.knowledge_base.contains(double_negated_formula) {
                            let mut knowledge_base = self.knowledge_base.clone();
                            knowledge_base.insert(double_negated_formula.clone());

                            let next_proof = ProofSituation {
                                knowledge_base,
                                goal: self.goal.clone(),
                            }
                            .build_proof();

                            return Some(ProofStep {
                                rule: "¬¬ ⊢".to_string(),
                                result: next_proof.result,
                                node: ProofNode::Proof(next_proof),
                                announcement:
                                    "Since we know %I1, by the law of double negation, we know %O1"
                                        .to_owned(),
                                inputs: indexset! {formula.clone()},
                                outputs: indexset! {double_negated_formula.clone()},
                            });
                        }
                    }

                    Formula::Conjunction(left, right) => {
                        let disjunction = Formula::Disjunction(
                            Box::new(Formula::Negation(left.clone())),
                            Box::new(Formula::Negation(right.clone())),
                        );

                        if !self.knowledge_base.contains(&disjunction) {
                            let mut knowledge_base = self.knowledge_base.clone();
                            knowledge_base.insert(disjunction.clone());

                            let next_proof = ProofSituation {
                                knowledge_base,
                                goal: self.goal.clone(),
                            }
                            .build_proof();

                            return Some(ProofStep {
                                rule: "¬∧ ⊢".to_string(),
                                result: next_proof.result,
                                node: ProofNode::Proof(next_proof),
                                announcement: "Since we know %I1, by De Morgan's laws, we know %O1"
                                    .to_owned(),
                                inputs: indexset! {formula.clone()},
                                outputs: indexset! {disjunction},
                            });
                        }
                    }

                    Formula::Disjunction(left, right) => {
                        let conjunction = Formula::Conjunction(
                            Box::new(Formula::Negation(left.clone())),
                            Box::new(Formula::Negation(right.clone())),
                        );

                        if !self.knowledge_base.contains(&conjunction) {
                            let mut knowledge_base = self.knowledge_base.clone();
                            knowledge_base.insert(conjunction.clone());

                            let next_proof = ProofSituation {
                                knowledge_base,
                                goal: self.goal.clone(),
                            }
                            .build_proof();

                            return Some(ProofStep {
                                rule: "¬∨ ⊢".to_string(),
                                result: next_proof.result,
                                node: ProofNode::Proof(next_proof),
                                announcement: "Since we know %I1, by De Morgan's laws, we know %O1"
                                    .to_owned(),
                                inputs: indexset! {formula.clone()},
                                outputs: indexset! {conjunction},
                            });
                        }
                    }

                    _ => {}
                },

                _ => {}
            }
        }

        None
    }

    fn proof_by_contradiction(&self) -> Option<ProofStep> {
        if self.goal == Formula::Contradiction {
            return None;
        }

        let negated_goal = negated_formula(&self.goal);

        let mut knowledge_base = self.knowledge_base.clone();
        knowledge_base.insert(negated_goal.clone());

        let proof = ProofSituation {
            knowledge_base,
            goal: Formula::Contradiction,
        }
        .build_proof();

        Some(ProofStep {
            rule: "proof by contradiction".to_string(),
            result: match proof.result {
                ProofResult::Proven => ProofResult::Contradiction,
                ProofResult::Contradiction => ProofResult::Proven,
                ProofResult::Unknown => ProofResult::Unknown,
            },
            node: ProofNode::Proof(proof),
            announcement: "We prove %I1 by contradiction:\nAssume %O1".to_owned(),
            inputs: indexset! {self.goal.clone()},
            outputs: indexset! {negated_goal},
        })
    }
}

impl Display for ProofSituation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "\n<pre>")?;
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
        writeln!(f, "{}", self.goal.to_string().green().markdown())?;
        writeln!(f, "</pre>")
    }
}

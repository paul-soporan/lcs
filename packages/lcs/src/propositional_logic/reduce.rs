use colored::Colorize;

use crate::{
    explanation::Explanation,
    markdown::Markdown,
    propositional_logic::{
        ast::{BinaryOperation, CompoundProposition, NaryOperation, Proposition, UnaryOperation},
        simplify::law,
    },
};

pub fn reduce_proposition(proposition: Proposition, explanation: &mut Explanation) -> Proposition {
    match proposition {
        Proposition::Tautology => {
            explanation.step(format!(
                "Tautology: {}",
                proposition.to_string().red().markdown()
            ));

            proposition
        }
        Proposition::Contradiction => {
            explanation.step(format!(
                "Contradiction: {}",
                proposition.to_string().red().markdown()
            ));

            proposition
        }
        Proposition::Atomic(p) => {
            explanation.step(format!(
                "Positive literal: {}",
                p.to_string().red().markdown()
            ));

            p.into()
        }
        Proposition::Compound(box CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition: Proposition::Atomic(p),
        }) => {
            explanation.step(format!(
                "Negative literal: {}",
                format!("¬{p}").red().markdown()
            ));

            CompoundProposition::UnaryOperation {
                operation: UnaryOperation::Negation,
                proposition: p.into(),
            }
            .into()
        }
        Proposition::Compound(box p) => explanation.with_subexplanation(
            format!("Reducing proposition: {}", p.to_string().blue().markdown()),
            |explanation| {
                let result = match p {
                    CompoundProposition::UnaryOperation {
                        operation,
                        proposition,
                    } => CompoundProposition::UnaryOperation {
                        operation,
                        proposition: reduce_proposition(
                            proposition,
                            explanation.subexplanation("Negation"),
                        ),
                    }
                    .into(),
                    CompoundProposition::NaryOperation {
                        operation,
                        propositions,
                    } => CompoundProposition::NaryOperation {
                        propositions: explanation.with_subexplanation(
                            match operation {
                                NaryOperation::Conjunction => "Conjunction",
                                NaryOperation::Disjunction => "Disjunction",
                            },
                            |explanation| {
                                propositions
                                    .into_iter()
                                    .map(|p| reduce_proposition(p, explanation))
                                    .collect()
                            },
                        ),
                        operation,
                    }
                    .into(),
                    CompoundProposition::BinaryOperation {
                        operation,
                        left,
                        right,
                    } => match operation {
                        BinaryOperation::Equivalence => {
                            reduce_equivalence(left, right, explanation)
                        }
                        BinaryOperation::Implication => {
                            reduce_implication(left, right, explanation)
                        }
                    },
                };

                explanation.step(format!("Result: {}", result.to_string().red().markdown()));

                result
            },
        ),
    }
}

pub fn reduce_equivalence(
    left: Proposition,
    right: Proposition,
    explanation: &mut Explanation,
) -> Proposition {
    explanation.step(law("(F ⇔ G) ∼ (F ⇒ G) ∧ (G ⇒ F)"));

    reduce_proposition(
        CompoundProposition::NaryOperation {
            operation: NaryOperation::Conjunction,
            propositions: vec![
                CompoundProposition::BinaryOperation {
                    operation: BinaryOperation::Implication,
                    left: left.clone(),
                    right: right.clone(),
                }
                .into(),
                CompoundProposition::BinaryOperation {
                    operation: BinaryOperation::Implication,
                    left: right,
                    right: left,
                }
                .into(),
            ],
        }
        .into(),
        explanation,
    )
}

pub fn reduce_implication(
    left: Proposition,
    right: Proposition,
    explanation: &mut Explanation,
) -> Proposition {
    explanation.step(law("(F ⇒ G) ∼ (¬F ∨ G)"));

    reduce_proposition(
        CompoundProposition::NaryOperation {
            operation: NaryOperation::Disjunction,
            propositions: vec![
                CompoundProposition::UnaryOperation {
                    operation: UnaryOperation::Negation,
                    proposition: left,
                }
                .into(),
                right,
            ],
        }
        .into(),
        explanation,
    )
}

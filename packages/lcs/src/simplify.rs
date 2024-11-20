use colored::Colorize;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    ast::{CompoundProposition, NaryOperation, Proposition, UnaryOperation},
    explanation::Explanation,
    markdown::Markdown,
};

pub fn law(equivalence: &str) -> String {
    format!("Applying {equivalence}").green().markdown()
}

pub fn simplify_proposition<T: Into<Proposition>>(
    proposition: T,
    explanation: &mut Explanation,
) -> Proposition {
    let proposition = proposition.into();

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
            format!(
                "Simplifying proposition: {}",
                p.to_string().blue().markdown()
            ),
            |explanation| {
                let result = match p {
                    CompoundProposition::UnaryOperation {
                        operation,
                        proposition,
                    } => match operation {
                        UnaryOperation::Negation => {
                            simplify_negation(proposition, explanation.subexplanation("Negation"))
                        }
                    },
                    CompoundProposition::NaryOperation {
                        operation,
                        propositions,
                    } => match operation {
                        NaryOperation::Conjunction => {
                            match simplify_conjunction(
                                propositions,
                                explanation.subexplanation("Conjunction"),
                                true,
                            ) {
                                None => Proposition::Contradiction,
                                Some(propositions) => match propositions.len() {
                                    1 => propositions.into_iter().next().unwrap(),
                                    _ => CompoundProposition::NaryOperation {
                                        operation: NaryOperation::Conjunction,
                                        propositions,
                                    }
                                    .into(),
                                },
                            }
                        }
                        NaryOperation::Disjunction => {
                            match simplify_disjunction(
                                propositions,
                                explanation.subexplanation("Disjunction"),
                                true,
                            ) {
                                None => Proposition::Tautology,
                                Some(propositions) => match propositions.len() {
                                    1 => propositions.into_iter().next().unwrap(),
                                    _ => CompoundProposition::NaryOperation {
                                        operation: NaryOperation::Disjunction,
                                        propositions,
                                    }
                                    .into(),
                                },
                            }
                        }
                    },
                    proposition => proposition.into(),
                };

                explanation.step(format!("Result: {}", result.to_string().red().markdown()));

                result
            },
        ),
    }
}

pub fn simplify_conjunction<T: Into<Proposition> + From<Proposition>>(
    propositions: Vec<T>,
    explanation: &mut Explanation,
    simplify_components: bool,
) -> Option<Vec<T>> {
    let mut simplified = IndexSet::new();

    let propositions = propositions
        .into_iter()
        .enumerate()
        .flat_map(|(i, p)| {
            let proposition = match simplify_components {
                true => simplify_proposition(
                    p,
                    explanation.subexplanation(format!(
                        "Component {}",
                        format!("#{i}").magenta().markdown()
                    )),
                ),
                false => p.into(),
            };

            match proposition {
                Proposition::Compound(box CompoundProposition::NaryOperation {
                    operation: NaryOperation::Conjunction,
                    propositions,
                }) => propositions.into_iter(),
                _ => vec![proposition].into_iter(),
            }
        })
        .sorted();

    'outer: for p in propositions {
        match p {
            Proposition::Contradiction => {
                explanation.step(law("F ∧ ⊥ ∼ ⊥"));
                return None;
            }
            Proposition::Tautology => {
                explanation.step(law("F ∧ ⊤ ∼ F"));
                continue;
            }
            p => {
                if let Proposition::Compound(box CompoundProposition::NaryOperation {
                    operation: NaryOperation::Disjunction,
                    propositions,
                }) = &p
                {
                    for p in propositions {
                        if simplified.contains(p) {
                            explanation.step(law("F ∧ (F ∨ G) ∼ F"));
                            continue 'outer;
                        }
                    }
                }

                if simplified.contains(&simplify_proposition(
                    CompoundProposition::UnaryOperation {
                        operation: UnaryOperation::Negation,
                        proposition: p.clone(),
                    },
                    &mut Explanation::default(),
                )) {
                    explanation.step(law("F ∧ ¬F ∼ ⊥"));
                    return None;
                }

                if !simplified.insert(p) {
                    explanation.step(law("F ∧ F ∼ F"));
                }
            }
        }
    }

    Some(simplified.into_iter().map(|p| p.into()).collect())
}

pub fn simplify_disjunction<T: Into<Proposition> + From<Proposition>>(
    propositions: Vec<T>,
    explanation: &mut Explanation,
    simplify_components: bool,
) -> Option<Vec<T>> {
    let mut simplified = IndexSet::new();

    let propositions = propositions
        .into_iter()
        .enumerate()
        .flat_map(|(i, p)| {
            let proposition = match simplify_components {
                true => simplify_proposition(
                    p,
                    explanation.subexplanation(format!(
                        "Component {}",
                        format!("#{i}").magenta().markdown()
                    )),
                ),
                false => p.into(),
            };

            match proposition {
                Proposition::Compound(box CompoundProposition::NaryOperation {
                    operation: NaryOperation::Disjunction,
                    propositions,
                }) => propositions.into_iter(),
                _ => vec![proposition].into_iter(),
            }
        })
        .sorted();

    'outer: for p in propositions {
        match p {
            Proposition::Tautology => {
                explanation.step(law("F ∨ ⊤ ∼ ⊤"));
                return None;
            }
            Proposition::Contradiction => {
                explanation.step(law("F ∨ ⊥ ∼ F"));
                continue;
            }
            p => {
                if let Proposition::Compound(box CompoundProposition::NaryOperation {
                    operation: NaryOperation::Conjunction,
                    propositions,
                }) = &p
                {
                    for p in propositions {
                        if simplified.contains(p) {
                            explanation.step(law("F ∨ (F ∧ G) ∼ F"));
                            continue 'outer;
                        }
                    }
                }

                if simplified.contains(&simplify_proposition(
                    CompoundProposition::UnaryOperation {
                        operation: UnaryOperation::Negation,
                        proposition: p.clone(),
                    },
                    &mut Explanation::default(),
                )) {
                    explanation.step(law("F ∨ ¬F ∼ ⊤"));
                    return None;
                }

                if !simplified.insert(p) {
                    explanation.step(law("F ∨ F ∼ F"));
                }
            }
        }
    }

    Some(simplified.into_iter().map(|p| p.into()).collect())
}

pub fn simplify_negation<T: Into<Proposition>>(
    negated_proposition: T,
    explanation: &mut Explanation,
) -> Proposition {
    match simplify_proposition(
        negated_proposition,
        explanation.subexplanation("Negated proposition"),
    ) {
        Proposition::Tautology => {
            explanation.step(law("¬⊤ ∼ ⊥"));
            Proposition::Contradiction
        }
        Proposition::Contradiction => {
            explanation.step(law("¬⊥ ∼ ⊤"));
            Proposition::Tautology
        }
        Proposition::Compound(box CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition,
        }) => {
            explanation.step(law("¬(¬F) ∼ F"));
            proposition
        }
        proposition => CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition,
        }
        .into(),
    }
}

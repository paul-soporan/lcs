use colored::Colorize;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    explanation::{DiscardedExplanation, Explain},
    markdown::Markdown,
    propositional_logic::types::Proposition,
};

pub fn law(equivalence: &str) -> String {
    format!("Applying {equivalence}").green().markdown()
}

pub fn simplify_proposition(
    proposition: &Proposition,
    explanation: &mut impl Explain,
) -> Proposition {
    match proposition {
        Proposition::Tautology => {
            explanation.step(|| format!("Tautology: {}", proposition.to_string().red().markdown()));

            proposition.clone()
        }
        Proposition::Contradiction => {
            explanation.step(|| {
                format!(
                    "Contradiction: {}",
                    proposition.to_string().red().markdown()
                )
            });

            proposition.clone()
        }
        Proposition::Atomic(p) => {
            explanation.step(|| format!("Positive literal: {}", p.to_string().red().markdown()));

            proposition.clone()
        }
        Proposition::Negation(box Proposition::Atomic(p)) => {
            explanation.step(|| format!("Negative literal: {}", format!("¬{p}").red().markdown()));

            proposition.clone()
        }
        p => explanation.with_subexplanation(
            || {
                format!(
                    "Simplifying proposition: {}",
                    p.to_string().blue().markdown()
                )
            },
            |explanation| {
                let result = match p {
                    Proposition::Negation(proposition) => {
                        simplify_negation(proposition, explanation.subexplanation(|| "Negation"))
                    }

                    Proposition::Conjunction(propositions) => {
                        match simplify_conjunction(
                            propositions,
                            explanation.subexplanation(|| "Conjunction"),
                            true,
                        ) {
                            None => Proposition::Contradiction,
                            Some(propositions) => match propositions.len() {
                                1 => propositions.into_iter().next().unwrap(),
                                _ => Proposition::Conjunction(propositions),
                            },
                        }
                    }
                    Proposition::Disjunction(propositions) => {
                        match simplify_disjunction(
                            propositions,
                            explanation.subexplanation(|| "Disjunction"),
                            true,
                        ) {
                            None => Proposition::Tautology,
                            Some(propositions) => match propositions.len() {
                                1 => propositions.into_iter().next().unwrap(),
                                _ => Proposition::Disjunction(propositions),
                            },
                        }
                    }

                    proposition => proposition.clone(),
                };

                explanation.step(|| format!("Result: {}", result.to_string().red().markdown()));

                result
            },
        ),
    }
}

pub fn simplify_conjunction<T: Clone + From<Proposition> + Into<Proposition>>(
    propositions: &[T],
    explanation: &mut impl Explain,
    simplify_components: bool,
) -> Option<Vec<T>> {
    let mut simplified = IndexSet::new();

    let propositions = propositions
        .into_iter()
        .enumerate()
        .flat_map(|(i, p)| {
            let proposition = match simplify_components {
                true => simplify_proposition(
                    &p.clone().into(),
                    explanation.subexplanation(|| {
                        format!("Component {}", format!("#{i}").magenta().markdown())
                    }),
                ),
                false => p.clone().into(),
            };

            match proposition {
                Proposition::Conjunction(propositions) => propositions.into_iter(),
                _ => vec![proposition].into_iter(),
            }
        })
        .sorted();

    'outer: for p in propositions {
        match p {
            Proposition::Contradiction => {
                explanation.step(|| law("F ∧ ⊥ ∼ ⊥"));
                return None;
            }
            Proposition::Tautology => {
                explanation.step(|| law("F ∧ ⊤ ∼ F"));
                continue;
            }
            p => {
                if let Proposition::Disjunction(propositions) = &p {
                    for p in propositions {
                        if simplified.contains(p) {
                            explanation.step(|| law("F ∧ (F ∨ G) ∼ F"));
                            continue 'outer;
                        }
                    }
                }

                if simplified.contains(&simplify_proposition(
                    &p.negated(),
                    &mut DiscardedExplanation,
                )) {
                    explanation.step(|| law("F ∧ ¬F ∼ ⊥"));
                    return None;
                }

                if !simplified.insert(p) {
                    explanation.step(|| law("F ∧ F ∼ F"));
                }
            }
        }
    }

    Some(simplified.into_iter().map(|p| p.into()).collect())
}

pub fn simplify_disjunction<T: Clone + From<Proposition> + Into<Proposition>>(
    propositions: &[T],
    explanation: &mut impl Explain,
    simplify_components: bool,
) -> Option<Vec<T>> {
    let mut simplified = IndexSet::new();

    let propositions = propositions
        .into_iter()
        .enumerate()
        .flat_map(|(i, p)| {
            let proposition = match simplify_components {
                true => simplify_proposition(
                    &p.clone().into(),
                    explanation.subexplanation(|| {
                        format!("Component {}", format!("#{i}").magenta().markdown())
                    }),
                ),
                false => p.clone().into(),
            };

            match proposition {
                Proposition::Disjunction(propositions) => propositions.into_iter(),
                _ => vec![proposition].into_iter(),
            }
        })
        .sorted();

    'outer: for p in propositions {
        match p {
            Proposition::Tautology => {
                explanation.step(|| law("F ∨ ⊤ ∼ ⊤"));
                return None;
            }
            Proposition::Contradiction => {
                explanation.step(|| law("F ∨ ⊥ ∼ F"));
                continue;
            }
            p => {
                if let Proposition::Conjunction(propositions) = &p {
                    for p in propositions {
                        if simplified.contains(p) {
                            explanation.step(|| law("F ∨ (F ∧ G) ∼ F"));
                            continue 'outer;
                        }
                    }
                }

                if simplified.contains(&simplify_proposition(
                    &p.negated(),
                    &mut DiscardedExplanation,
                )) {
                    explanation.step(|| law("F ∨ ¬F ∼ ⊤"));
                    return None;
                }

                if !simplified.insert(p) {
                    explanation.step(|| law("F ∨ F ∼ F"));
                }
            }
        }
    }

    Some(simplified.into_iter().map(|p| p.into()).collect())
}

pub fn simplify_negation(
    negated_proposition: &Proposition,
    explanation: &mut impl Explain,
) -> Proposition {
    match simplify_proposition(
        negated_proposition,
        explanation.subexplanation(|| "Negated proposition"),
    ) {
        Proposition::Tautology => {
            explanation.step(|| law("¬⊤ ∼ ⊥"));
            Proposition::Contradiction
        }
        Proposition::Contradiction => {
            explanation.step(|| law("¬⊥ ∼ ⊤"));
            Proposition::Tautology
        }
        Proposition::Negation(box proposition) => {
            explanation.step(|| law("¬(¬F) ∼ F"));
            proposition
        }
        proposition => proposition.negated(),
    }
}

use colored::Colorize;

use crate::{
    explanation::Explain,
    markdown::Markdown,
    propositional_logic::{simplify::law, types::Proposition},
};

pub fn reduce_proposition(
    proposition: &Proposition,
    explanation: &mut impl Explain,
) -> Proposition {
    match proposition {
        Proposition::Tautology => {
            explanation.step(format!(
                "Tautology: {}",
                proposition.to_string().red().markdown()
            ));

            proposition.clone()
        }
        Proposition::Contradiction => {
            explanation.step(format!(
                "Contradiction: {}",
                proposition.to_string().red().markdown()
            ));

            proposition.clone()
        }
        Proposition::Atomic(p) => {
            explanation.step(format!(
                "Positive literal: {}",
                p.to_string().red().markdown()
            ));

            proposition.clone()
        }
        Proposition::Negation(box Proposition::Atomic(p)) => {
            explanation.step(format!(
                "Negative literal: {}",
                format!("¬{p}").red().markdown()
            ));

            proposition.clone()
        }
        p => explanation.with_subexplanation(
            format!("Reducing proposition: {}", p.to_string().blue().markdown()),
            |explanation| {
                let result = match p {
                    Proposition::Negation(proposition) => Proposition::Negation(Box::new(
                        reduce_proposition(proposition, explanation.subexplanation("Negation")),
                    )),

                    Proposition::Conjunction(propositions) => {
                        explanation.with_subexplanation("Conjunction", |explanation| {
                            Proposition::Conjunction(
                                propositions
                                    .into_iter()
                                    .map(|p| reduce_proposition(p, explanation))
                                    .collect(),
                            )
                        })
                    }
                    Proposition::Disjunction(propositions) => {
                        explanation.with_subexplanation("Disjunction", |explanation| {
                            Proposition::Disjunction(
                                propositions
                                    .into_iter()
                                    .map(|p| reduce_proposition(p, explanation))
                                    .collect(),
                            )
                        })
                    }

                    Proposition::Implication(left, right) => {
                        reduce_implication(left, right, explanation)
                    }
                    Proposition::Equivalence(left, right) => {
                        reduce_equivalence(left, right, explanation)
                    }

                    _ => unreachable!(),
                };

                explanation.step(format!("Result: {}", result.to_string().red().markdown()));

                result
            },
        ),
    }
}

pub fn reduce_equivalence(
    left: &Proposition,
    right: &Proposition,
    explanation: &mut impl Explain,
) -> Proposition {
    explanation.step(law("(F ⇔ G) ∼ (F ⇒ G) ∧ (G ⇒ F)"));

    reduce_proposition(
        &Proposition::Conjunction(vec![
            Proposition::Implication(Box::new(left.clone()), Box::new(right.clone())),
            Proposition::Implication(Box::new(right.clone()), Box::new(left.clone())),
        ]),
        explanation,
    )
}

pub fn reduce_implication(
    left: &Proposition,
    right: &Proposition,
    explanation: &mut impl Explain,
) -> Proposition {
    explanation.step(law("(F ⇒ G) ∼ (¬F ∨ G)"));

    reduce_proposition(
        &Proposition::Disjunction(vec![
            Proposition::Negation(Box::new(left.clone())),
            right.clone(),
        ]),
        explanation,
    )
}

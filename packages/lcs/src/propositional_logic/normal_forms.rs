use std::{collections::BTreeSet, fmt::Display};

use colored::Colorize;
use itertools::Itertools;
use maplit::btreeset;

use crate::{
    explanation::Explanation,
    markdown::Markdown,
    propositional_logic::{
        reduce::reduce_proposition,
        simplify::{law, simplify_conjunction, simplify_disjunction, simplify_proposition},
        types::{Proposition, PropositionalVariable},
    },
};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Literal(pub PropositionalVariable, pub bool);

impl Literal {
    pub fn complement(&self) -> Self {
        Literal(self.0.clone(), !self.1)
    }
}

impl From<Literal> for Proposition {
    fn from(Literal(variable, value): Literal) -> Self {
        let proposition = variable.into();

        if value {
            proposition
        } else {
            Proposition::Negation(Box::new(proposition))
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 {
            write!(f, "{}", self.0)
        } else {
            write!(f, "¬{}", self.0)
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum NegationNormalForm {
    Literal(Literal),
    Conjunction(BTreeSet<NegationNormalForm>),
    Disjunction(BTreeSet<NegationNormalForm>),
}

impl From<Literal> for NegationNormalForm {
    fn from(value: Literal) -> Self {
        NegationNormalForm::Literal(value)
    }
}

impl NegationNormalForm {
    pub fn from_proposition(proposition: Proposition, explanation: &mut Explanation) -> Self {
        explanation.with_subexplanation(
            format!(
                "Computing NNF for proposition: {}",
                proposition.to_string().blue().markdown()
            ),
            |explanation| {
                let result = match simplify_proposition(
                    &reduce_proposition(&proposition, explanation),
                    explanation,
                ) {
                    Proposition::Tautology => unimplemented!(),
                    Proposition::Contradiction => unimplemented!(),
                    Proposition::Atomic(p) => Literal(p, true).into(),

                    Proposition::Conjunction(propositions) => explanation.with_subexplanation(
                        "Conjunction",
                        |explanation| {
                            let propositions = propositions
                                .into_iter()
                                .enumerate()
                                .map(|(i, p)| {
                                    NegationNormalForm::from_proposition(
                                        p,
                                        explanation.subexplanation(format!(
                                            "Component {}",
                                            format!("#{i}").magenta().markdown()
                                        )),
                                    )
                                })
                                .collect::<Vec<_>>();
                            match simplify_conjunction(&propositions, explanation, true)
                            {
                                None => NegationNormalForm::Disjunction(btreeset! {}),
                                Some(propositions) => NegationNormalForm::Conjunction(
                                    propositions.into_iter().collect(),
                                ),
                            }
                        },
                    ),
                    Proposition::Disjunction(propositions) => explanation.with_subexplanation(
                        "Disjunction",
                        |explanation| {
                            let propositions = propositions
                                .into_iter()
                                .enumerate()
                                .map(|(i, p)| {
                                    NegationNormalForm::from_proposition(
                                        p,
                                        explanation.subexplanation(format!(
                                            "Component {}",
                                            format!("#{i}").magenta().markdown()
                                        )),
                                    )
                                })
                                .collect::<Vec<_>>();
                            match simplify_disjunction(&propositions, explanation, true)
                            {
                                None => NegationNormalForm::Conjunction(btreeset! {}),
                                Some(propositions) => NegationNormalForm::Disjunction(
                                    propositions.into_iter().collect(),
                                ),
                            }
                        },
                    ),

                    Proposition::Negation(box proposition) => match proposition {
                        Proposition::Atomic(p) => Literal(p, false).into(),

                        Proposition::Conjunction(propositions) => {
                            explanation.step(law("¬(F ∧ G) ∼ ¬F ∨ ¬G"));

                            let propositions = propositions
                                .into_iter()
                                .map(|proposition| proposition.negated())
                                .collect::<Vec<_>>();

                            match simplify_disjunction(
                                &propositions.clone(),
                                explanation.subexplanation(format!(
                                    "Simplifying resulting disjunction: {}",
                                    Proposition::Disjunction(propositions)
                                        .to_string()
                                        .red()
                                        .markdown()
                                )),
                                true,
                            ) {
                                None => NegationNormalForm::Conjunction(btreeset! {}),
                                Some(propositions) => explanation.with_subexplanation(
                                    "Disjunction",
                                    |explanation| {
                                        NegationNormalForm::Disjunction(
                                            propositions
                                                .into_iter()
                                                .enumerate()
                                                .map(|(i, p)| {
                                                    NegationNormalForm::from_proposition(
                                                        p,
                                                        explanation.subexplanation(format!(
                                                            "Component {}",
                                                            format!("#{}", i)
                                                                .magenta()
                                                                .markdown()
                                                        )),
                                                    )
                                                })
                                                .collect(),
                                        )
                                    },
                                ),
                            }
                        }

                        Proposition::Disjunction(propositions) => {
                            explanation.step(law("¬(F ∨ G) ∼ ¬F ∧ ¬G"));

                            let propositions = propositions
                                .into_iter()
                                .map(|proposition| proposition.negated())
                                .collect::<Vec<_>>();

                            match simplify_conjunction(
                                &propositions.clone(),
                                explanation.subexplanation(format!(
                                    "Simplifying resulting conjunction: {}",
                                    Proposition::Conjunction(propositions)
                                        .to_string()
                                        .red()
                                        .markdown()
                                )),
                                true,
                            ) {
                                None => NegationNormalForm::Disjunction(btreeset! {}),
                                Some(propositions) => explanation.with_subexplanation(
                                    "Conjunction",
                                    |explanation| {
                                        NegationNormalForm::Conjunction(
                                            propositions
                                                .into_iter()
                                                .enumerate()
                                                .map(|(i, p)| {
                                                    NegationNormalForm::from_proposition(
                                                        p,
                                                        explanation.subexplanation(format!(
                                                            "Component {}",
                                                            format!("#{}", i)
                                                                .magenta()
                                                                .markdown()
                                                        )),
                                                    )
                                                })
                                                .collect(),
                                        )
                                    },
                                ),
                            }
                        }

                        Proposition::Implication(_, _) | Proposition::Equivalence(_, _) => {
                            unreachable!(
                                "Implications and equivalences should have been reduced."
                            )
                        }

                        Proposition::Negation(_) => {
                            unreachable!("Double negation should have been simplified.")
                        }

                        Proposition::Tautology | Proposition::Contradiction => unreachable!(
                            "Negations of tautologies and contradictions should have been simplified."
                        ),
                    },

                    Proposition::Implication(_, _) | Proposition::Equivalence(_, _) => {
                        unreachable!("Implications and equivalences should have been reduced.")
                    }
                };

                explanation.step(format!("NNF: {}", result.to_string().red().markdown()));

                result
            },
        )
    }
}

impl From<Proposition> for NegationNormalForm {
    fn from(value: Proposition) -> Self {
        NegationNormalForm::from_proposition(value, &mut Explanation::default())
    }
}

impl From<NegationNormalForm> for Proposition {
    fn from(value: NegationNormalForm) -> Self {
        match value {
            NegationNormalForm::Literal(literal) => literal.into(),
            NegationNormalForm::Conjunction(propositions) => {
                Proposition::Conjunction(propositions.into_iter().map(|nnf| nnf.into()).collect())
            }
            NegationNormalForm::Disjunction(propositions) => {
                Proposition::Disjunction(propositions.into_iter().map(|nnf| nnf.into()).collect())
            }
        }
    }
}

impl Display for NegationNormalForm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Proposition::from(self.clone()).fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct DisjunctiveNormalForm(pub BTreeSet<BTreeSet<Literal>>);

impl DisjunctiveNormalForm {
    pub fn from_negation_normal_form(
        nnf: NegationNormalForm,
        explanation: &mut Explanation,
    ) -> Self {
        explanation.with_subexplanation(
            format!(
                "Computing DNF for proposition: {}",
                nnf.to_string().blue().markdown()
            ),
            |explanation| {
                let clauses = match nnf {
                    NegationNormalForm::Literal(literal) => {
                        return DisjunctiveNormalForm(btreeset! {btreeset! {literal}})
                    }
                    NegationNormalForm::Conjunction(propositions) => {
                        explanation.with_subexplanation("Conjunction", |explanation| {
                            let mut literals = btreeset! {};
                            let mut disjunctions = btreeset! {};

                            for (i, proposition) in propositions.into_iter().enumerate() {
                                explanation.with_subexplanation(format!("Component {}", format!("#{i}").magenta().markdown()), |explanation| {
                                    match proposition {
                                        NegationNormalForm::Literal(literal) => {
                                            explanation.step(format!(
                                                "Literal: {}",
                                                literal.to_string().blue().markdown()
                                            ));
                                            literals.insert(literal);
                                        }
                                        NegationNormalForm::Disjunction(propositions) => {
                                            explanation.with_subexplanation("Disjunction", |explanation| {
                                                let cnf = ConjunctiveNormalForm::from_negation_normal_form(
                                                    NegationNormalForm::Disjunction(propositions),
                                                    explanation,
                                                );

                                                for clause in cnf.0 {
                                                    disjunctions.insert(clause);
                                                }
                                            })
                                        }
                                        NegationNormalForm::Conjunction(_) => unreachable!("Nested conjunctions should have been simplified.")

                                    }
                                });
                            }

                            disjunctions.extend(literals.into_iter().map(|literal| btreeset! {literal}));

                            explanation.step(format!(
                                "Conjunction: {}",
                                ConjunctiveNormalForm(disjunctions.clone())
                                    .to_string()
                                    .blue()
                                    .markdown()
                            ));

                            explanation.step(law("F ∧ (G ∨ H) ∼ (F ∧ G) ∨ (F ∧ H)"));

                            disjunctions
                                .into_iter()
                                .map(|clause| clause.into_iter().collect::<Vec<_>>())
                                .collect::<Vec<_>>()
                                .into_iter()
                                .multi_cartesian_product()
                                .map(|clause| {
                                    // clause.splice(0..0, literals.clone());
                                    clause.into_iter().collect::<BTreeSet<_>>()
                                })
                                .collect::<BTreeSet<_>>()
                            })
                    }
                    NegationNormalForm::Disjunction(propositions) => explanation
                        .with_subexplanation("Disjunction", |explanation| {
                            let mut clauses = btreeset! {};

                            for (i, proposition) in propositions.into_iter().enumerate() {
                                explanation.with_subexplanation(
                                    format!("Component {}", format!("#{i}").magenta().markdown()),
                                    |explanation| match proposition {
                                        NegationNormalForm::Literal(literal) => {
                                            explanation.step(format!(
                                                "Literal: {}",
                                                literal.to_string().blue().markdown()
                                            ));
                                            clauses.insert(btreeset! {literal});
                                        }
                                        NegationNormalForm::Conjunction(propositions) => {
                                            explanation.with_subexplanation("Conjunction", |explanation| {
                                                let dnf =
                                                    DisjunctiveNormalForm::from_negation_normal_form(
                                                        NegationNormalForm::Conjunction(propositions),
                                                        explanation,
                                                    );
                                                for clause in dnf.0 {
                                                    clauses.insert(clause);
                                                }
                                            })
                                        }
                                        NegationNormalForm::Disjunction(_) => unreachable!("Nested disjunctions should have been simplified.")
                                    },
                                )
                            }

                            clauses
                        }),
                };

                let disjunction = clauses
                    .into_iter()
                    .map(|clause| {
                        NegationNormalForm::Conjunction(
                            clause
                                .into_iter()
                                .map(NegationNormalForm::Literal)
                                .collect(),
                        )
                    })
                    .collect::<Vec<_>>();

                let disjunction = simplify_disjunction(
                    &disjunction.clone(),
                    explanation.subexplanation(format!(
                        "Simplifying resulting disjunction: {}",
                        NegationNormalForm::Disjunction(disjunction.into_iter().collect())
                            .to_string()
                            .red()
                            .markdown()
                    )),
                    true,
                );

                let result = match disjunction {
                    None => DisjunctiveNormalForm(btreeset! {btreeset! {}}),
                    Some(propositions) => DisjunctiveNormalForm(
                        propositions
                            .into_iter()
                            .map(|nnf| match nnf {
                                NegationNormalForm::Conjunction(propositions) => propositions
                                    .into_iter()
                                    .map(|nnf| match nnf {
                                        NegationNormalForm::Literal(literal) => literal,
                                        _ => unreachable!(),
                                    })
                                    .collect(),
                                p => btreeset! {match p {
                                    NegationNormalForm::Literal(literal) => literal,
                                    _ => unreachable!(),
                                }},
                            })
                            .collect(),
                    ),
                };

                explanation.step(format!("DNF: {}", result.to_string().red().markdown()));

                result
            },
        )
    }
}

impl From<NegationNormalForm> for DisjunctiveNormalForm {
    fn from(value: NegationNormalForm) -> Self {
        DisjunctiveNormalForm::from_negation_normal_form(value, &mut Explanation::default())
    }
}

impl From<DisjunctiveNormalForm> for Proposition {
    fn from(value: DisjunctiveNormalForm) -> Self {
        Proposition::Disjunction(
            value
                .0
                .into_iter()
                .map(|conjunction| {
                    Proposition::Conjunction(
                        conjunction
                            .into_iter()
                            .map(|literal| literal.into())
                            .collect(),
                    )
                })
                .collect(),
        )
    }
}

impl Display for DisjunctiveNormalForm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Proposition::from(self.clone()).fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct ConjunctiveNormalForm(pub BTreeSet<BTreeSet<Literal>>);

impl ConjunctiveNormalForm {
    pub fn from_negation_normal_form(
        nnf: NegationNormalForm,
        explanation: &mut Explanation,
    ) -> Self {
        explanation.with_subexplanation(
            format!(
                "Computing CNF for proposition: {}",
                nnf.to_string().blue().markdown()
            ),
            |explanation| {
                let clauses = match nnf {
                    NegationNormalForm::Literal(literal) => {
                        return ConjunctiveNormalForm(btreeset! {btreeset! {literal}})
                    }
                    NegationNormalForm::Conjunction(propositions) => explanation
                        .with_subexplanation("Conjunction", |explanation| {
                            let mut clauses = btreeset! {};

                            for (i, proposition) in propositions.into_iter().enumerate() {
                                explanation.with_subexplanation(format!("Component {}", format!("#{i}").magenta().markdown()), |explanation| {
                                    match proposition {
                                        NegationNormalForm::Literal(literal) => {
                                            explanation.step(format!(
                                                "Literal: {}",
                                                literal.to_string().blue().markdown()
                                            ));
                                            clauses.insert(btreeset! {literal});
                                        }
                                        NegationNormalForm::Disjunction(propositions) => explanation
                                            .with_subexplanation("Disjunction", |explanation| {
                                                let dnf: ConjunctiveNormalForm =
                                                    ConjunctiveNormalForm::from_negation_normal_form(
                                                        NegationNormalForm::Disjunction(propositions),
                                                        explanation,
                                                    );
                                                for clause in dnf.0 {
                                                    clauses.insert(clause);
                                                }
                                            }),
                                        NegationNormalForm::Conjunction(_) => unreachable!("Nested conjunctions should have been simplified."),
                                    }
                                });
                            }

                            clauses
                        }),
                    NegationNormalForm::Disjunction(propositions) => {
                        explanation.with_subexplanation("Disjunction", |explanation| {
                            let mut literals = btreeset! {};
                            let mut conjunctions = btreeset! {};

                            for (i, proposition) in propositions.into_iter().enumerate() {
                                explanation.with_subexplanation(
                                    format!("Component {}", format!("#{i}").magenta().markdown()),
                                    |explanation| match proposition {
                                        NegationNormalForm::Literal(literal) => {
                                            explanation.step(format!(
                                                "Literal: {}",
                                                literal.to_string().blue().markdown()
                                            ));
                                            literals.insert(literal);
                                        }
                                        NegationNormalForm::Conjunction(propositions) => {
                                            explanation.with_subexplanation("Conjunction", |explanation| {
                                                let dnf = DisjunctiveNormalForm::from_negation_normal_form(
                                                    NegationNormalForm::Conjunction(propositions),
                                                    explanation,
                                                );
                                                for clause in dnf.0 {
                                                    conjunctions.insert(clause);
                                                }
                                            })
                                        }
                                        NegationNormalForm::Disjunction(_) => unreachable!("Nested disjunctions should have been simplified."),
                                    },
                                )
                            }

                            conjunctions.extend(literals.into_iter().map(|literal| btreeset! {literal}));

                            explanation.step(format!(
                                "Disjunction: {}",
                                DisjunctiveNormalForm(conjunctions.clone())
                                    .to_string()
                                    .blue()
                                    .markdown()
                            ));

                            explanation.step(law("F ∨ (G ∧ H) ∼ (F ∨ G) ∧ (F ∨ H)"));

                            conjunctions
                                .into_iter()
                                .map(|clause| clause.into_iter().collect::<Vec<_>>())
                                .collect::<Vec<_>>()
                                .into_iter()
                                .multi_cartesian_product()
                                .map(|clause| {
                                    // clause.splice(0..0, literals.clone());
                                    clause.into_iter().collect::<BTreeSet<_>>()
                                })
                                .collect::<BTreeSet<_>>()
                        })
                    }
                };

                let conjunction = clauses
                    .into_iter()
                    .map(|clause| {
                        NegationNormalForm::Disjunction(
                            clause
                                .into_iter()
                                .map(NegationNormalForm::Literal)
                                .collect(),
                        )
                    })
                    .collect::<Vec<_>>();

                let conjunction = simplify_conjunction(
                    &conjunction.clone(),
                    explanation.subexplanation(format!(
                        "Simplifying resulting conjunction: {}",
                        NegationNormalForm::Conjunction(conjunction.into_iter().collect())
                            .to_string()
                            .red()
                            .markdown()
                    )),
                    true,
                );

                let result = match conjunction {
                    None => ConjunctiveNormalForm(btreeset! {btreeset! {}}),
                    Some(propositions) => ConjunctiveNormalForm(
                        propositions
                            .into_iter()
                            .map(|nnf| match nnf {
                                NegationNormalForm::Disjunction(propositions) => propositions
                                    .into_iter()
                                    .map(|nnf| match nnf {
                                        NegationNormalForm::Literal(literal) => literal,
                                        _ => unreachable!(),
                                    })
                                    .collect(),
                                p => btreeset! {match p {
                                    NegationNormalForm::Literal(literal) => literal,
                                    _ => unreachable!(),
                                }},
                            })
                            .collect(),
                    ),
                };

                explanation.step(format!("CNF: {}", result.to_string().red().markdown()));

                result
            },
        )
    }
}

impl From<NegationNormalForm> for ConjunctiveNormalForm {
    fn from(value: NegationNormalForm) -> Self {
        ConjunctiveNormalForm::from_negation_normal_form(value, &mut Explanation::default())
    }
}

impl From<ConjunctiveNormalForm> for Proposition {
    fn from(value: ConjunctiveNormalForm) -> Self {
        Proposition::Conjunction(
            value
                .0
                .into_iter()
                .map(|clause| {
                    Proposition::Disjunction(
                        clause.into_iter().map(|literal| literal.into()).collect(),
                    )
                })
                .collect(),
        )
    }
}

impl Display for ConjunctiveNormalForm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Proposition::from(self.clone()).fmt(f)
    }
}

impl From<ConjunctiveNormalForm> for DisjunctiveNormalForm {
    fn from(value: ConjunctiveNormalForm) -> Self {
        DisjunctiveNormalForm::from(NegationNormalForm::from(Proposition::from(value)))
    }
}

impl From<DisjunctiveNormalForm> for ConjunctiveNormalForm {
    fn from(value: DisjunctiveNormalForm) -> Self {
        ConjunctiveNormalForm::from(NegationNormalForm::from(Proposition::from(value)))
    }
}

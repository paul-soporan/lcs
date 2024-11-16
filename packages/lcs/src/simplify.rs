use indexmap::IndexSet;

use crate::ast::{CompoundProposition, NaryOperation, Proposition, UnaryOperation};

pub fn simplify_proposition(proposition: Proposition) -> Proposition {
    if let Proposition::Compound(p) = proposition {
        match *p {
            CompoundProposition::NaryOperation {
                operation,
                propositions,
            } => match operation {
                NaryOperation::Conjunction => simplify_conjunction(propositions),
                NaryOperation::Disjunction => simplify_disjunction(propositions),
            },
            CompoundProposition::UnaryOperation {
                operation,
                proposition,
            } => match operation {
                UnaryOperation::Negation => simplify_negation(proposition),
            },
            _ => Proposition::Compound(p),
        }
    } else {
        proposition
    }
}

fn simplify_conjunction(propositions: Vec<Proposition>) -> Proposition {
    let mut simplified = IndexSet::new();
    for p in propositions {
        match simplify_proposition(p) {
            Proposition::Contradiction => return Proposition::Contradiction,
            Proposition::Tautology => continue,
            p => {
                if simplified.contains(&Proposition::from(CompoundProposition::UnaryOperation {
                    operation: UnaryOperation::Negation,
                    proposition: p.clone(),
                })) {
                    return Proposition::Contradiction;
                }

                simplified.insert(p);
            }
        }
    }

    CompoundProposition::NaryOperation {
        operation: NaryOperation::Conjunction,
        propositions: Vec::from_iter(simplified),
    }
    .into()
}

fn simplify_disjunction(propositions: Vec<Proposition>) -> Proposition {
    let mut simplified = IndexSet::new();
    for p in propositions {
        match simplify_proposition(p) {
            Proposition::Tautology => return Proposition::Tautology,
            Proposition::Contradiction => continue,
            p => {
                if simplified.contains(&Proposition::from(CompoundProposition::UnaryOperation {
                    operation: UnaryOperation::Negation,
                    proposition: p.clone(),
                })) {
                    return Proposition::Tautology;
                }

                simplified.insert(p);
            }
        }
    }

    CompoundProposition::NaryOperation {
        operation: NaryOperation::Disjunction,
        propositions: Vec::from_iter(simplified),
    }
    .into()
}

fn simplify_negation(proposition: Proposition) -> Proposition {
    match simplify_proposition(proposition) {
        Proposition::Tautology => Proposition::Contradiction,
        Proposition::Contradiction => Proposition::Tautology,
        Proposition::Compound(box CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition,
        }) => proposition,
        proposition => CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition,
        }
        .into(),
    }
}
//

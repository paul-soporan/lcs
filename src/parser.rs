use crate::ast::{
    AtomicProposition, BinaryOperation, CompoundProposition, Invalid, Proposition,
    PropositionalVariable, UnaryOperation,
};
use unicode_segmentation::UnicodeSegmentation;

pub fn proposition(input: &str) -> Proposition {
    if let Some(p) = compound_proposition(input) {
        Proposition::Compound(Box::new(p))
    } else if let Some(p) = atomic_proposition(input) {
        Proposition::Atomic(p)
    } else {
        Proposition::Invalid(Invalid {
            input: input.to_owned(),
            reason: negation(input)
                .or_else(|| operation(input))
                .and_then(|p| match p {
                    CompoundProposition::Invalid(_) => None,
                    _ => Some("compound propositions must be parenthesized".to_owned()),
                }),
        })
    }
}

fn compound_proposition(input: &str) -> Option<CompoundProposition> {
    input
        .strip_prefix('(')
        .and_then(|input| match input.strip_suffix(')') {
            Some(input) => operation(input),
            None => panic!("Expected closing parenthesis"),
        })
}

fn operation(input: &str) -> Option<CompoundProposition> {
    let mut paren_stack = 0;

    let operator = input.grapheme_indices(true).find(|&(_, c)| {
        if paren_stack == 0 && "∧∨⇒⇔".contains(c) {
            return true;
        }

        match c {
            "(" => paren_stack += 1,
            ")" => paren_stack -= 1,
            _ => (),
        }

        return false;
    });

    let (pos, op) = match operator {
        Some((pos, op)) => (pos, op),
        None => {
            let neg = negation(input);
            if neg.is_some() {
                return neg;
            }

            return Some(CompoundProposition::Invalid(Invalid {
                input: input.to_owned(),
                reason: {
                    let p = proposition(input);
                    match p {
                        Proposition::Invalid(_) => None,
                        _ => Some(
                            "propositions can't be formed by parenthesizing other propositions"
                                .to_owned(),
                        ),
                    }
                },
            }));
        }
    };

    let lhs = &input[..pos];
    let rhs = &input[pos + op.len() + 1..];

    let left = proposition(lhs.trim());
    let right = proposition(rhs.trim());

    Some(CompoundProposition::BinaryOperation {
        operation: match op {
            "∧" => BinaryOperation::Conjunction,
            "∨" => BinaryOperation::Disjunction,
            "⇒" => BinaryOperation::Implication,
            "⇔" => BinaryOperation::Equivalence,
            _ => unreachable!("Invalid operator"),
        },
        left,
        right,
    })
}

fn negation(input: &str) -> Option<CompoundProposition> {
    input
        .strip_prefix('¬')
        .map(|input| CompoundProposition::UnaryOperation {
            operation: UnaryOperation::Negation,
            proposition: proposition(input),
        })
}

// TODO: Support indices
fn atomic_proposition(input: &str) -> Option<AtomicProposition> {
    if let Some(c) = input.chars().next()
        && c.is_alphanumeric()
    {
        if c.is_uppercase() {
            Some(AtomicProposition::PropositionalVariable(
                PropositionalVariable(c.to_string()),
            ))
        } else {
            Some(AtomicProposition::Invalid(Invalid {
                input: input.to_owned(),
                reason: None,
            }))
        }
    } else {
        None
    }
}

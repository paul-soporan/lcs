#![feature(let_chains)]

use std::io;

use describe::{subscript, Describe, Description};
use parser::proposition;

mod ast;
mod describe;
mod parser;

fn describe(input: &str, expected: Option<bool>, i: Option<usize>) {
    let result = proposition(input);

    let first_id = 1;
    let Description { description, valid } = result.describe(2, first_id);

    if let Some(expected) = expected {
        assert_eq!(valid, expected);
    }

    let mark = if valid { "✅" } else { "❌" };
    let is = if valid { "is" } else { "is not" };

    if let Some(i) = i {
        let exercise_letter = ('a' as u8 + i as u8) as char;
        println!("({exercise_letter}):\n");
    }

    println!("  {}\n", description);
    println!("  Conclusion: {mark} T{} {is} a well formed propositional formula (wff) as defined by the syntax of the language of propositional logic.\n\n", subscript(first_id));
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();

    let input = input.trim();
    if input.is_empty() {
        let test_cases = [
            ("(((P ⇒ Q) ∨ S) ⇔ T)", true),
            ("((P ⇒ (Q ∧ (S ⇒ T))))", false),
            ("(¬(B(¬Q)) ∧ R)", false),
            ("(P ∧ ((¬Q) ∧ (¬(¬(Q ⇔ (¬R))))))", true),
            ("((P ∨ Q) ⇒ ¬(P ∨ Q)) ∧ (P ∨ (¬(¬Q)))", false),
        ];

        for (i, &(input, expected)) in test_cases.iter().enumerate() {
            describe(input, Some(expected), Some(i));
        }
    } else {
        describe(input, None, None);
    }
}

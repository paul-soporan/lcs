#![feature(let_chains)]
#![feature(anonymous_lifetime_in_impl_trait)]

use ast::{BinaryOperation, CompoundProposition};
use colored::Colorize;
use evaluate::{Evaluate, Evaluation, ExplainedValue, Interpretation};
use parser::parse;

mod ast;
mod evaluate;
mod parser;

fn get_letter(i: usize) -> char {
    (b'a' + i as u8) as char
}

fn exercise_1() {
    println!("Exercise 1)\n");

    let parts = [
        "((P ∧ Q) ⇒ R)",
        "((¬P) ⇒ S)",
        "((¬Q) ⇒ T)",
        "(¬R)",
        "(U ⇒ (¬(S ∨ T)))",
    ];

    let mut parts = parts
        .iter()
        .map(|part| parse(part).unwrap())
        .collect::<Vec<_>>();

    println!();

    let rest = parts.split_off(1);
    let first = parts.pop().unwrap();

    let p = rest.into_iter().fold(first, |acc, part| {
        CompoundProposition::BinaryOperation {
            operation: BinaryOperation::Conjunction,
            left: acc,
            right: part,
        }
        .into()
    });

    println!("Proposition: {}\n", p.to_string().blue());

    let interpretation = Interpretation::generate_all(p.get_variables().value)
        .nth(6)
        .unwrap();

    println!("Let I ≔ {}\n", interpretation.to_string().blue());

    let ExplainedValue { value, steps } = p.evaluate(&interpretation);

    for step in steps {
        println!("{}", step);
    }

    println!(
        "=> The value of the proposition under interpretation I is {}.\n",
        value.to_string().magenta()
    );
}

fn exercise_2() {
    println!("Exercise 2)\n");

    let test_cases = [
        "(((P ⇒ Q) ∨ S) ⇔ T)",
        "((P ⇒ (Q ∧ (S ⇒ T))))",
        "(¬(B(¬Q)) ∧ R)",
        "((P ⇒ Q) ∧ ((¬Q) ∧ P))",
        "((P ⇒ Q) ⇒ (Q ⇒ P))",
        "((¬(P ∨ Q)) ∧ (¬Q))",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("{})\n", get_letter(i));

        println!("Input: {}\n", input.blue());

        let result = parse(input);
        println!();

        match result {
            Ok(p) => {
                println!("Abstract syntax tree:\n  {}\n", format!("{p:#?}").blue());

                let ExplainedValue {
                    value: variables,
                    steps,
                } = p.get_variables();

                for step in steps {
                    println!("{}", step);
                }

                println!(
                    "\nGenerating 3 interpretations for variable set: {}",
                    variables.to_string().blue()
                );

                let interpretations = Interpretation::generate_all(variables).take(3);
                for (i, interpretation) in interpretations.enumerate() {
                    println!(
                        "  Interpretation {}:\n    Let I ≔ {}",
                        i.to_string().yellow(),
                        interpretation.to_string().blue()
                    );
                    let Evaluation { value, steps } = p.evaluate(&interpretation);

                    for step in steps {
                        println!("      {}", step);
                    }
                    println!(
                        "    => The value of the proposition under interpretation I is {}.",
                        value.to_string().magenta()
                    );
                }
            }
            Err(_) => {
                println!("Parsing error; nothing to analyze\n");
            }
        }

        println!();
    }
}

fn exercise_3() {
    println!("Exercise 3)\n");

    let test_cases = [
        "((P ⇒ Q) ∧ ((¬Q) ∧ (¬P)))",
        "((P ⇒ Q) ⇒ ((Q ⇒ S) ⇒ ((P ∨ Q) ⇒ R)))",
        "((¬(P ⇒ Q)) ⇔ ((P ∨ R) ∧ ((¬P) ⇒ Q)))",
        "((P ⇔ Q) ⇔ (¬(P ⇒ (¬Q))))",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("{})\n", get_letter(i));

        println!("Input: {}\n", input.blue());

        let result = parse(input);
        println!();

        match result {
            Ok(p) => {
                println!("Abstract syntax tree:\n  {}\n", format!("{p:#?}").blue());

                let ExplainedValue {
                    value: attributes,
                    steps,
                } = p.get_attributes();

                for step in steps {
                    println!("{}", step);
                }

                println!("\n=> {}\n", format!("{attributes:#?}",).cyan());
            }
            Err(_) => {
                println!("Parsing error; nothing to analyze\n");
            }
        }

        println!();
    }
}

fn main() {
    exercise_1();
    exercise_2();
    exercise_3();
}

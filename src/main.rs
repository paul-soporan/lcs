#![feature(let_chains)]
#![feature(anonymous_lifetime_in_impl_trait)]
#![feature(box_patterns)]

use ast::{LogicalConsequence, PropositionalVariable, TruthTable};
use colored::Colorize;
use evaluate::ExplainedValue;
use indexmap::{indexmap, IndexMap};
use markdown::Markdown;
use parser::{parse_logical_consequence, parse_logical_equivalence, parse_proposition};

mod ast;
mod evaluate;
mod markdown;
mod parser;

fn get_letter(i: usize) -> char {
    (b'a' + i as u8) as char
}

fn exercise_1() {
    println!("# Exercise 1");

    let test_cases = ["P ∧ Q ⇒ R¬B ∨ G", "P ⇒ ¬¬¬¬¬B ⇔ Q ∧ S"];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));
        println!("Input: {}", input.blue().markdown());

        let ExplainedValue {
            value: result,
            steps,
        } = parse_proposition(input);

        println!("<pre>");
        for step in steps {
            println!("{}", step);
        }
        println!("</pre>");

        println!(
            "Proposition {} a well-formed formula.\n",
            if result.is_ok() {
                "is".green().markdown()
            } else {
                "is not".red().markdown()
            }
        );

        if let Ok(proposition) = result {
            println!(
                "Proposition converted to strong syntax: {}",
                proposition.to_string().blue().markdown()
            );

            println!("<pre>{}</pre>", proposition.get_tree());
        }
    }
}

fn exercise_2() {
    println!("# Exercise 2");

    let test_cases = [
        "(P ⇒ Q) ∧ ¬Q ∧ ¬P",
        "(P ⇒ Q) ⇒ ((Q ⇒ S) ⇒ ((P ∨ Q) ⇒ R))",
        "¬(P ⇒ Q) ⇔ ((P ∨ R) ∧ (¬P ⇒ Q))",
        "(P ⇔ Q) ⇔ (¬(P ⇒ ¬Q))",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));
        println!("Proposition: {}", input.blue().markdown());

        let ExplainedValue { value: result, .. } = parse_proposition(input);

        let proposition = result.unwrap();

        let truth_table = TruthTable::new(&[&proposition]);
        println!("{}", truth_table);

        let attributes = truth_table.get_attributes(&proposition);
        println!("<pre>{attributes:#?}</pre>");
    }
}

fn exercise_3() {
    println!("# Exercise 3");

    let test_cases: IndexMap<&str, &[&str]> = indexmap! {
        "Reduction Laws" => [
            "(F ⇔ G) ∼ (F ⇒ G) ∧ (G ⇒ F)",
            "(F ⇒ G) ∼ (¬F ∨ G)",
        ].as_slice(),

        "Commutative Laws" => [
            "F ∨ G ∼ G ∨ F",
            "F ∧ G ∼ G ∧ F",

            "F ⇔ G ∼ G ⇔ F",
        ].as_slice(),

        "Associative Laws" => [
            "(F ∨ G) ∨ H ∼ F ∨ (G ∨ H)",
            "(F ∧ G) ∧ H ∼ F ∧ (G ∧ H)",
            "(F ⇔ G) ⇔ H ∼ F ⇔ (G ⇔ H)",
        ].as_slice(),

        "Distributive Laws" => [
            "F ∨ (G ∧ H) ∼ (F ∨ G) ∧ (F ∨ H)",
            "F ∧ (G ∨ H) ∼ (F ∧ G) ∨ (F ∧ H)",

            "(F ∨ G) ⇒ H ∼ (F ⇒ H) ∧ (G ⇒ H)",
            "(F ∧ G) ⇒ H ∼ (F ⇒ H) ∨ (G ⇒ H)",
            "F ⇒ (G ∨ H) ∼ (F ⇒ G) ∨ (F ⇒ H)",
            "F ⇒ (G ∧ H) ∼ (F ⇒ G) ∧ (F ⇒ H)",
            "(F ∧ G) ⇒ H ∼ F ⇒ (G ⇒ H)",
        ].as_slice(),

        "Laws of “True” and “False”" => [
            "¬⊤ ∼ ⊥",
            "¬⊥ ∼ ⊤",
            "F ∨ ⊥ ∼ F",
            "F ∧ ⊤ ∼ F",
            "F ∨ ⊤ ∼ ⊤",
            "F ∧ ⊥ ∼ ⊥",
            "⊥ ⇒ F ∼ ⊤",
            "F ⇒ ⊤ ∼ ⊤",
        ].as_slice(),

        "Idempocy rules" => [
            "F ∧ F ∼ F",
            "F ∨ F ∼ F",
        ].as_slice(),

        "Absorption Laws" => [
            "F ∨ (F ∧ G) ∼ F",
            "F ∧ (F ∨ G) ∼ F",
        ].as_slice(),

        "“Annihilation” Laws" => [
            "F ∨ ¬F ∼ ⊤",
            "F ∧ ¬F ∼ ⊥",

            "F ⇒ F ∼ ⊤",
        ].as_slice(),

        "Negation Laws" => [
            "¬(¬F) ∼ F",
            "¬(F ∨ G) ∼ ¬F ∧ ¬G",
            "¬(F ∧ G) ∼ ¬F ∨ ¬G",

            "¬(F ⇒ G) ∼ F ∧ (¬G)",
            "¬(F ⇔ G) ∼ F ⇔ (¬G)",
        ].as_slice(),

        "Other Laws" => [
            "F ⇒ G ∼ F ⇔ (F ∧ G)",
            "F ⇒ G ∼ G ⇔ (F ∨ G)",
        ].as_slice(),
    };

    for (group_name, inputs) in test_cases {
        println!("## {group_name}");
        for (i, input) in inputs.iter().enumerate() {
            println!("### {})", get_letter(i));
            println!("Logical equivalence: {}", input.blue().markdown());

            let equivalence = parse_logical_equivalence(input).value.unwrap();

            let ExplainedValue { value, steps } = equivalence.check();
            for step in steps {
                println!("{}", step);
            }

            println!(
                "=> Logical equivalence {}.",
                if value {
                    "holds".green().markdown()
                } else {
                    "doesn't hold".red().markdown()
                }
            );
        }
    }
}

fn exercise_4() {
    println!("# Exercise 4");

    let test_cases = ["Q ∨ R, Q ⇒ ¬P, ¬(R ∧ P) ⊨ ¬P", "P ⇒ Q, Q ⊨ P ∧ Q"];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));
        println!("Logical consequence: {}\n", input.blue().markdown());

        let consequence = parse_logical_consequence(input).value.unwrap();

        let ExplainedValue { value, steps } = consequence.check();
        for step in steps {
            println!("{}", step);
        }

        println!(
            "=> Logical consequence {}.\n",
            if value {
                "holds".green().markdown()
            } else {
                "doesn't hold".red().markdown()
            }
        );
    }
}

fn exercise_5() {
    println!("# Exercise 5");

    let parts = ["A ∧ W ⇒ P", "¬A ⇒ I", "¬W ⇒ M", "¬P", "E ⇒ ¬(I ∨ M)"];

    let premises = parts.map(|part| parse_proposition(part).value.unwrap());

    let logical_consequence = LogicalConsequence {
        premises: premises.to_vec(),
        conclusion: PropositionalVariable("E".to_owned()).into(),
    };

    let ExplainedValue { value, steps } = logical_consequence.check();
    for step in steps {
        println!("{}", step);
    }

    println!(
        "=> Logical consequence is {}.\n",
        if value {
            "E".green().markdown()
        } else {
            "¬E".red().markdown()
        }
    );
}

fn main() {
    exercise_1();
    exercise_2();
    exercise_3();
    exercise_4();
    exercise_5();
}

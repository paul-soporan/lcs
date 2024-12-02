use std::collections::BTreeSet;

use colored::Colorize;
use lcs::ast::{LogicalConsequence, Proposition, PropositionalVariable};
use lcs::explanation::Explanation;
use lcs::markdown::Markdown;
use lcs::normal_forms::ConjunctiveNormalForm;
use lcs::parser::{parse_clause, parse_clause_set, parse_proposition};
use lcs::resolver::Resolver;

fn get_letter(i: usize) -> char {
    (b'a' + i as u8) as char
}

fn exercise_1() {
    println!("# Exercise 1");

    let parts = ["A ∧ W ⇒ P", "¬A ⇒ I", "¬W ⇒ M", "¬P", "E ⇒ ¬(I ∨ M)"];

    let premises = parts.map(|part| parse_proposition(part).value.unwrap());

    let consequence = LogicalConsequence {
        premises: premises.to_vec(),
        conclusion: PropositionalVariable("E".to_owned()).into(),
    };

    println!(
        "- **Logical consequence:** {}",
        consequence.to_string().blue().markdown()
    );

    let mut explanation = Explanation::default();

    explanation.with_subexplanation(
        format!(
            "Checking logical consequence {}",
            consequence.to_string().blue().markdown()
        ),
        |explanation| {
            let mut resolution_resolver =
                Resolver::check_logical_consequence(consequence.clone(), explanation);
            let mut dp_resolver = Resolver::check_logical_consequence(
                consequence.clone(),
                &mut Explanation::default(),
            );

            let consequence_resolution =
                resolution_resolver.resolution(explanation.subexplanation("Resolution"));
            let consequence_dp = dp_resolver.dp(explanation.subexplanation("DP"));

            let consequence_truth_table = consequence.check().value;

            if (consequence_resolution != consequence_dp)
                || (consequence_dp != consequence_truth_table)
            {
                panic!("Different logical consequence results");
            }

            println!(
                "- **Logical consequence is:** {}",
                match consequence_resolution {
                    true => "true".green().markdown(),
                    false => "false".red().markdown(),
                }
            );
        },
    );

    println!("{}", explanation);
}

fn exercise_2() {
    println!("# Exercise 2");

    let test_cases = [
        "{{A, ¬B, C}, {B, C}, {¬A, C}, {B, ¬C}, {¬B}}",
        "{{A, ¬B}, {A, C}, {¬B, C}, {¬A, B}, {B, ¬C}, {¬A, ¬C}}",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!(
            "- **Clause set:** {}",
            input.to_string().magenta().markdown()
        );

        let clause_set = parse_clause_set(input).value.unwrap();
        let cnf = ConjunctiveNormalForm(clause_set);

        println!("- **Formula:** {}", cnf.to_string().blue().markdown());

        let mut explanation = Explanation::default();

        explanation.with_subexplanation(
            format!(
                "Checking satisfiability for {}",
                cnf.to_string().blue().markdown()
            ),
            |explanation| {
                let mut resolution_resolver = Resolver::is_satisfiable(cnf.clone(), explanation);
                let mut dp_resolver =
                    Resolver::is_satisfiable(cnf.clone(), &mut Explanation::default());

                let satisfiable_resolution =
                    resolution_resolver.resolution(explanation.subexplanation("Resolution"));
                let satisfiable_dp = dp_resolver.dp(explanation.subexplanation("DP"));

                let satisfiable_truth_table =
                    Proposition::from(cnf).get_attributes().value.satisfiable;

                if (satisfiable_resolution != satisfiable_dp)
                    || (satisfiable_dp != satisfiable_truth_table)
                {
                    panic!("Different satisfiability results");
                }

                println!(
                    "- **Result:** {}",
                    match satisfiable_resolution {
                        true => "satisfiable".green().markdown(),
                        false => "unsatisfiable".red().markdown(),
                    }
                );

                if satisfiable_resolution {
                    let interpretation = dp_resolver.build_satisfying_interpretation(explanation);

                    println!(
                        "- **Satisfying truth valuation:** {}",
                        interpretation.to_string().green().markdown()
                    );
                }
            },
        );

        println!("{}", explanation);
    }
}

fn exercise_3() {
    println!("# Exercise 3");

    let clauses = [
        "{P, Q, ¬R}",
        "{¬P, R}",
        "{P, ¬Q, S}",
        "{¬P, ¬Q, ¬R}",
        "{P, ¬S}",
    ];

    let clause_set = clauses
        .iter()
        .map(|clause| parse_clause(clause).value.unwrap())
        .collect::<BTreeSet<_>>();

    let cnf = ConjunctiveNormalForm(clause_set);

    println!("- **Formula:** {}", cnf.to_string().blue().markdown());

    let mut explanation = Explanation::default();

    explanation.with_subexplanation(
        format!(
            "Checking satisfiability for {}",
            cnf.to_string().blue().markdown()
        ),
        |explanation| {
            let mut resolution_resolver = Resolver::is_satisfiable(cnf.clone(), explanation);
            let mut dp_resolver =
                Resolver::is_satisfiable(cnf.clone(), &mut Explanation::default());

            let satisfiable_resolution =
                resolution_resolver.resolution(explanation.subexplanation("Resolution"));
            let satisfiable_dp = dp_resolver.dp(explanation.subexplanation("DP"));

            let satisfiable_truth_table = Proposition::from(cnf).get_attributes().value.satisfiable;

            if (satisfiable_resolution != satisfiable_dp)
                || (satisfiable_dp != satisfiable_truth_table)
            {
                panic!("Different satisfiability results");
            }

            println!(
                "- **Result:** {}",
                match satisfiable_resolution {
                    true => "satisfiable".green().markdown(),
                    false => "unsatisfiable".red().markdown(),
                }
            );

            if satisfiable_resolution {
                let interpretation = dp_resolver.build_satisfying_interpretation(explanation);

                println!(
                    "- **Satisfying truth valuation:** {}",
                    interpretation.to_string().green().markdown()
                );
            }
        },
    );

    println!("{}", explanation);
}

fn exercise_4() {
    println!("# Exercise 4");

    let formula = "((P1 ⇒ (P2 ∨ P3)) ∧ (¬P1 ⇒ (P3 ∨ P4)) ∧ (P3 ⇒ (¬P6)) ∧ (¬P3 ⇒ (P4 ⇒ P1)) ∧ (¬(P2 ∧ P5)) ∧ (P2 ⇒ P5)) ⇒ ¬(P3 ⇒ P6)";

    println!("- **Formula:** {}", formula.magenta().markdown());

    let proposition = parse_proposition(formula).value.unwrap();

    let mut explanation = Explanation::default();

    explanation.with_subexplanation(
        format!("Checking validity for {}", formula.blue().markdown()),
        |explanation| {
            let mut resolution_resolver = Resolver::is_valid(proposition.clone(), explanation);
            let mut dp_resolver =
                Resolver::is_valid(proposition.clone(), &mut Explanation::default());

            let valid_resolution =
                resolution_resolver.resolution(explanation.subexplanation("Resolution"));
            let valid_dp = dp_resolver.dp(explanation.subexplanation("DP"));

            let valid_truth_table = Proposition::from(proposition.clone())
                .get_attributes()
                .value
                .valid;

            if (valid_resolution != valid_dp) || (valid_dp != valid_truth_table) {
                panic!("Different validity results");
            }

            println!(
                "- **Result:** {}",
                match valid_resolution {
                    true => "valid".green().markdown(),
                    false => "invalid".red().markdown(),
                }
            );
        },
    );

    println!("{}", explanation);
}

fn main() {
    exercise_1();
    exercise_2();
    exercise_3();
    exercise_4();
}

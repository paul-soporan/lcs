use colored::Colorize;
use indexmap::{indexmap, IndexMap};
use itertools::Itertools;
use lcs::{
    markdown::Markdown,
    propositional_logic::{
        bcf::get_bcf,
        circuit::{Analyze, Circuit, Component},
        evaluate::TruthValue,
        types::{Proposition, TruthFunction, TruthTable},
    },
};

use crate::homework::utils::get_letter;

fn print_circuit_attributes(circuit: &Circuit) {
    let attributes = circuit.get_attributes();
    println!(
        "- Depth: {}",
        attributes.depth.to_string().blue().markdown()
    );
    println!(
        "- Inputs({}): {}",
        attributes.inputs.len().to_string().blue().markdown(),
        attributes
            .inputs
            .iter()
            .map(|label| label.0.magenta().markdown())
            .join(", ")
    );
    println!(
        "- Gates({}):\n{}",
        attributes.gates.len().to_string().blue().markdown(),
        attributes
            .gates
            .iter()
            .map(|gate| format!("  - {}", gate.to_string().green().markdown()))
            .join("\n")
    );
}

fn process_test_cases(test_cases: &IndexMap<&str, TruthFunction<3>>) {
    let mut original_dnf_circuit = Circuit::default();
    let mut original_cnf_circuit = Circuit::default();
    let mut simplified_circuit = Circuit::default();

    let mut propositions = IndexMap::new();

    println!("## Functions\n");

    for (i, (function_name, function)) in test_cases.iter().enumerate() {
        println!("### {}) {function_name}", get_letter(i));

        let dnf = function.get_disjunctive_normal_form();
        println!(
            "- Original proposition (Disjunctive Normal Form): {}",
            Proposition::from(dnf.clone())
                .to_string()
                .magenta()
                .markdown()
        );
        let original_dnf_component = Component::from(dnf);
        original_dnf_circuit.components.push(original_dnf_component);

        let cnf = function.get_conjunctive_normal_form();
        println!(
            "- Original proposition (Conjunctive Normal Form): {}",
            Proposition::from(cnf.clone()).to_string().red().markdown()
        );
        let original_cnf_component = Component::from(cnf.clone());
        original_cnf_circuit.components.push(original_cnf_component);

        let bcf = get_bcf(&cnf);

        propositions.insert(function_name, Proposition::from(bcf.clone()));
        println!(
            "- Simplified proposition: {}",
            Proposition::from(bcf.clone()).to_string().blue().markdown()
        );
        let simplified_component = Component::from(bcf);
        println!(
            "- Transformed proposition: {}",
            simplified_component.to_string().green().markdown()
        );

        simplified_circuit.components.push(simplified_component);

        println!();
    }

    let mut truth_table = TruthTable::new(&propositions.values().collect::<Vec<_>>());
    for key in truth_table.columns.keys() {
        if !matches!(key, Proposition::Atomic(_)) && !propositions.values().contains(key) {
            truth_table.hidden_columns.insert(key.clone());
        } else {
            let label = propositions
                .iter()
                .find(|(_, value)| *value == key)
                .and_then(|(key, _)| Some(key));

            if let Some(label) = label {
                truth_table
                    .column_labels
                    .insert(key.clone(), label.to_string());
            }
        }
    }

    println!("## Truth Table\n");
    println!("{truth_table}");

    println!("## Original DNF Circuit");
    print_circuit_attributes(&original_dnf_circuit);

    println!();

    println!("## Original CNF Circuit");
    print_circuit_attributes(&original_cnf_circuit);

    println!();

    println!("## Simplified Circuit");
    print_circuit_attributes(&simplified_circuit);
}

fn exercise_3() {
    println!("# Exercise 3\n");

    fn args_to_decimal(args: &[TruthValue]) -> u32 {
        u32::from_str_radix(
            &args
                .iter()
                .map(|&TruthValue(value)| char::from_digit(value as u32, 10).unwrap())
                .collect::<String>(),
            2,
        )
        .unwrap()
    }

    let test_cases: IndexMap<_, TruthFunction<3>> = indexmap! {
        "prime" => TruthFunction(|args| {
            TruthValue([2, 3, 5, 7].contains(&args_to_decimal(args)))
        }),
        "square" => TruthFunction(|args| {
            TruthValue([0, 1, 4].contains(&args_to_decimal(args)))
        }),
        "even" => TruthFunction(|args| TruthValue(!args[2].0)),
    };

    process_test_cases(&test_cases);
}

fn exercise_4() {
    println!("# Exercise 4");

    let test_cases: IndexMap<_, TruthFunction<3>> = indexmap! {
        "sum" => TruthFunction(|[bit1, bit2, carry_in]| TruthValue(bit1.0 ^ bit2.0 ^ carry_in.0)),
        "carry_out" => TruthFunction(|[bit1, bit2, carry_in]| {
            TruthValue((bit1.0 & bit2.0) | (bit1.0 & carry_in.0) | (bit2.0 & carry_in.0))
        }),
    };

    process_test_cases(&test_cases);
}

pub fn run() {
    exercise_3();
    exercise_4();
}

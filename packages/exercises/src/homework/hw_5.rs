use colored::Colorize;
use indexmap::{indexmap, IndexMap};
use itertools::Itertools;
use lcs::{
    explanation::Explanation,
    markdown::Markdown,
    propositional_logic::{
        bcf::get_bcf,
        circuit::{into_nand_only_component, Analyze, Circuit, Component},
        evaluate::TruthValue,
        normal_forms::{ConjunctiveNormalForm, DisjunctiveNormalForm, NegationNormalForm},
        parser::parse_proposition,
        types::{LogicalEquivalence, Proposition, TruthFunction, TruthTable},
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
        "- Transistor count: {}",
        attributes.transistor_count().to_string().blue().markdown()
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
    let mut nand_only_circuit = Circuit::default();

    let mut propositions = IndexMap::new();

    println!("## Functions\n");

    for (i, (function_name, function)) in test_cases.iter().enumerate() {
        println!("### {}) {function_name}", get_letter(i));

        println!("- Building DNF and CNF from specification table");

        let dnf = function.get_disjunctive_normal_form();
        println!(
            "- Original DNF: {}",
            Proposition::from(dnf.clone())
                .to_string()
                .magenta()
                .markdown()
        );
        let original_dnf_component = Component::from(dnf);
        original_dnf_circuit.components.push(original_dnf_component);

        let cnf = function.get_conjunctive_normal_form();
        println!(
            "- Original CNF: {}",
            Proposition::from(cnf.clone()).to_string().red().markdown()
        );
        let original_cnf_component = Component::from(cnf.clone());
        original_cnf_circuit.components.push(original_cnf_component);

        println!("- Simplifying DNF and CNF using the Blake Canonical Form");

        let simplified_dnf = get_bcf(&cnf);

        propositions.insert(function_name, Proposition::from(simplified_dnf.clone()));
        println!(
            "- Simplified DNF: {}",
            Proposition::from(simplified_dnf.clone())
                .to_string()
                .blue()
                .markdown()
        );

        let simplified_cnf = ConjunctiveNormalForm::from(simplified_dnf.clone());

        println!(
            "- Simplified CNF: {}",
            Proposition::from(simplified_cnf.clone())
                .to_string()
                .blue()
                .markdown()
        );

        let dnf_component = Component::from(simplified_dnf);
        let cnf_component = Component::from(simplified_cnf);

        let component = if dnf_component.get_attributes().transistor_count()
            < cnf_component.get_attributes().transistor_count()
        {
            println!("- Choosing DNF - fewer transistors");
            dnf_component
        } else {
            println!("- Choosing CNF - fewer transistors");
            cnf_component
        };

        println!("- Transforming n-ary gates into binary gates using associativity");

        println!(
            "- Transformed: {}",
            component.to_string().green().markdown()
        );

        simplified_circuit.components.push(component.clone());

        let mut explanation = Explanation::default();

        let nand_only_component = into_nand_only_component(component, &mut explanation);
        println!(
            "- Nand-only proposition: {}",
            nand_only_component.to_string().green().markdown()
        );

        println!("{}", explanation);

        nand_only_circuit.components.push(nand_only_component);

        println!();
    }

    let mut truth_table = TruthTable::new(&propositions.values().collect::<Vec<_>>());
    let variables = truth_table
        .columns
        .keys()
        .filter(|p| matches!(p, Proposition::Atomic(_)))
        .collect::<Vec<_>>();
    let arguments_str = variables.iter().map(|p| p.to_string()).join(", ");

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
                    .insert(key.clone(), format!("{label}({arguments_str})"));
            }
        }
    }

    println!("## Specification Table\n");
    println!("{truth_table}");

    println!("## Original DNF Circuit");
    print_circuit_attributes(&original_dnf_circuit);

    println!();

    println!("## Original CNF Circuit");
    print_circuit_attributes(&original_cnf_circuit);

    println!();

    println!("## Simplified Circuit");
    print_circuit_attributes(&simplified_circuit);

    println!("## Nand-Only Simplified Circuit");
    print_circuit_attributes(&nand_only_circuit);
}

fn exercise_2() {
    println!("# Exercise 2\n");

    println!("## Specification 1\n");

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

    println!("## Specification 2\n");

    let test_cases: IndexMap<_, TruthFunction<3>> = indexmap! {
        "sum" => TruthFunction(|[bit1, bit2, carry_in]| TruthValue(bit1.0 ^ bit2.0 ^ carry_in.0)),
        "carry_out" => TruthFunction(|[bit1, bit2, carry_in]| {
            TruthValue((bit1.0 & bit2.0) | (bit1.0 & carry_in.0) | (bit2.0 & carry_in.0))
        }),
    };

    process_test_cases(&test_cases);
}

fn check_equivalence<T: Clone + Into<Proposition>>(transformed: &T, original: &Proposition) {
    assert!(
        LogicalEquivalence {
            left: transformed.clone().into(),
            right: original.clone()
        }
        .check()
        .value
    )
}

fn exercise_3() {
    println!("# Exercise 3");

    let test_cases = [
        "(P ⇒ Q) ∧ ¬Q ∧ ¬P",
        "(P ⇒ Q) ⇒ ((Q ⇒ S) ⇒ ((P ∨ Q) ⇒ R))",
        "¬(P ⇒ Q) ⇔ ((P ∨ Q) ∧ (¬P ⇒ Q))",
        "(P ⇔ Q) ⇔ (¬(P ⇒ ¬Q))",
        "(¬P ⇒ (Q ∧ R)) ⇒ ((Q ∨ ¬R) ⇔ P)",
        "(P ∨ ¬Q ∨ (R ⇔ S)) ⇔ (S ∧ Q)",
        "(P ⇔ (P ∧ Q)) ⇒ ¬Q",
        "¬(¬P ∨ Q ∨ R) ∨ (Q ⇒ (P ∨ ¬R))",
        "(¬P ∨ Q ∨ R) ∧ (P ∨ ¬R) ∧ (¬Q ∨ ¬R) ∧ ¬(P ∧ R)",
        "((P1 ⇒ (P2 ∨ P3)) ∧ (¬P1 ⇒ (P3 ∨ P4)) ∧ (P3 ⇒ (¬P6)) ∧ (¬P3 ⇒ (P4 ⇒ P1)) ∧ (¬(P2 ∧ P5)) ∧ (P2 ⇒ P5)) ⇒ ¬(P3 ⇒ P6)",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Original:** {}", input.to_string().red().markdown());

        let p = parse_proposition(input, &mut Explanation::default()).unwrap();

        let mut explanation = Explanation::default();

        let nnf = NegationNormalForm::from_proposition(p.clone(), &mut explanation);
        check_equivalence(&nnf, &p);
        println!("- **NNF:** {}", nnf.to_string().magenta().markdown());

        let dnf = DisjunctiveNormalForm::from_negation_normal_form(nnf.clone(), &mut explanation);
        check_equivalence(&dnf, &p);
        println!("- **DNF:** {}", dnf.to_string().blue().markdown());

        let cnf = ConjunctiveNormalForm::from_negation_normal_form(nnf, &mut explanation);
        check_equivalence(&cnf, &p);
        println!("- **CNF:** {}", cnf.to_string().blue().markdown());

        let bcf = get_bcf(&cnf);
        check_equivalence(&bcf, &p);
        println!("- **BCF:** {}", bcf.to_string().green().markdown());

        println!("{}", explanation);
    }
}

pub fn run() {
    exercise_2();
    exercise_3();
}

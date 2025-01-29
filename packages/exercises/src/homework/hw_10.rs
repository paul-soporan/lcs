use as_variant::as_variant;
use colored::Colorize;
use indexmap::{indexmap, indexset, IndexMap};
use itertools::Itertools;
use lcs::{
    explanation::Explanation,
    markdown::Markdown,
    predicate_logic::{
        parser::{parse_expression, Signature},
        prove::{Proof, ProofSituation},
        types::{Expression, Formula, PredicateSymbol},
    },
    propositional_logic::{
        ast::{BinaryOperation, CompoundProposition, NaryOperation, Proposition},
        parser::parse_proposition,
    },
};

fn write_proof(proof: &Proof, labels: &IndexMap<Formula, String>) {
    let trimmed_proof = proof.trim();
    println!("- **Proof:**\n{}", trimmed_proof.describe(labels));

    let explanation = &mut Explanation::default();
    proof.explain(explanation);
    println!("- **Original proof tree**:\n{}", explanation.to_string());

    if trimmed_proof != *proof {
        let explanation = &mut Explanation::default();
        trimmed_proof.explain(explanation);
        println!("- **Trimmed proof tree**:\n{}", explanation.to_string());
    } else {
        println!(
            "- **Trimmed proof tree**: {}",
            "unchanged".yellow().markdown()
        );
    }
}

fn exercise_1() {
    println!("# Exercise 1");

    println!("## a)");

    let mut explanation = Explanation::default();

    let signature = Signature {
        functions: indexmap! {},
        predicates: indexmap! {
            "≺".to_owned() => PredicateSymbol::Infix,
        },
        is_constant_fn: |_| false,
        static_constants: indexset! {},
    };

    let transitivity = as_variant!(
        parse_expression(
            "∀x∀y∀z(x ≺ y ∧ y ≺ z ⇒ x ≺ z)",
            &signature,
            &mut explanation,
        )
        .unwrap(),
        Expression::Formula
    )
    .unwrap();

    let irreflexivity = as_variant!(
        parse_expression("∀x¬(x ≺ x)", &signature, &mut explanation).unwrap(),
        Expression::Formula
    )
    .unwrap();

    let asymmetry = as_variant!(
        parse_expression("∀x∀y(x ≺ y ⇒ ¬(y ≺ x))", &signature, &mut explanation).unwrap(),
        Expression::Formula
    )
    .unwrap();

    let labels = indexmap! {
        transitivity.clone() => "transitivity".to_owned(),
        asymmetry.clone() => "asymmetry".to_owned(),
        irreflexivity.clone() => "irreflexivity".to_owned(),
    };

    let proof_situation = ProofSituation {
        knowledge_base: indexset![transitivity, asymmetry],
        goal: irreflexivity,
    };

    let proof = proof_situation.build_proof();

    write_proof(&proof, &labels);

    println!("## b)");
    println!(
        "- Predicates satisfying **(transitivity)**, **(asymmetry)**, and **(irreflexivity)**:"
    );
    println!("  - In the domain of numbers: **<**, **>**");
    println!("  - In the domain of sets: **⊂ (strict inclusion)**");
}

fn exercise_2() {
    println!("# Exercise 2");

    println!("## a)");

    let mut explanation = Explanation::default();

    let signature = Signature {
        functions: indexmap! {},
        predicates: indexmap! {
            "≈".to_owned() => PredicateSymbol::Infix,
        },
        is_constant_fn: |_| false,
        static_constants: indexset! {},
    };

    let transitivity = as_variant!(
        parse_expression(
            "∀x∀y∀z(x ≈ y ∧ y ≈ z ⇒ x ≈ z)",
            &signature,
            &mut explanation,
        )
        .unwrap(),
        Expression::Formula
    )
    .unwrap();

    let symmetry = as_variant!(
        parse_expression("∀x∀y(x ≈ y ⇒ y ≈ x)", &signature, &mut explanation).unwrap(),
        Expression::Formula
    )
    .unwrap();

    let reflexivity = as_variant!(
        parse_expression("∀x(x ≈ x)", &signature, &mut explanation).unwrap(),
        Expression::Formula
    )
    .unwrap();

    let double_transitivity = as_variant!(
        parse_expression(
            "∀x∀y∀z∀u(x ≈ y ∧ x ≈ z ∧ y ≈ u ⇒ z ≈ u)",
            &signature,
            &mut explanation,
        )
        .unwrap(),
        Expression::Formula
    )
    .unwrap();

    let labels = indexmap! {
        transitivity.clone() => "transitivity".to_owned(),
        symmetry.clone() => "symmetry".to_owned(),
        reflexivity.clone() => "reflexivity".to_owned(),
        double_transitivity.clone() => "double transitivity".to_owned(),
    };

    let proof_situation = ProofSituation {
        knowledge_base: indexset![transitivity, symmetry, reflexivity],
        goal: double_transitivity,
    };

    let proof = proof_situation.build_proof();

    write_proof(&proof, &labels);

    println!("## b)");
    println!("- Predicates satisfying **(transitivity)**, **(symmetry)**, **(reflexivity)**, and therefore **(double transitivity)**:");
    println!("  - In the domain of numbers: **=**");
    println!("  - In the domain of integers: **≡ (mod n), where n is an integer**");
    println!("  - In the domain of sets: **= (set equality)**");
    println!("  - In the domain of lines: **'parallel or equal'**");
}

fn exercise_3() {
    println!("# Exercise 3");

    let parts = ["A ∧ W ⇒ P", "¬A ⇒ I", "¬W ⇒ M", "¬P", "E ⇒ ¬(I ∨ M)"];

    let premises = parts
        .map(|part| parse_proposition(part, &mut Explanation::default()).unwrap())
        .map(|proposition| proposition_to_formula(proposition));

    let proof_situation = ProofSituation {
        knowledge_base: premises.into_iter().collect(),
        goal: proposition_to_formula(parse_proposition("¬E", &mut Explanation::default()).unwrap()),
    };

    let proof = proof_situation.build_proof();

    write_proof(&proof, &indexmap! {});
}

pub fn run() {
    exercise_1();
    exercise_2();
    exercise_3();
}

fn proposition_to_formula(proposition: Proposition) -> Formula {
    match proposition {
        Proposition::Atomic(variable) => Formula::PredicateApplication {
            predicate: variable.0,
            arguments: vec![],
            symbol: PredicateSymbol::Prefix(vec![0]),
        },
        Proposition::Compound(p) => match *p {
            CompoundProposition::UnaryOperation { proposition, .. } => {
                Formula::Negation(Box::new(proposition_to_formula(proposition)))
            }
            CompoundProposition::BinaryOperation {
                operation,
                left,
                right,
            } => match operation {
                BinaryOperation::Implication => Formula::Implication(
                    Box::new(proposition_to_formula(left)),
                    Box::new(proposition_to_formula(right)),
                ),
                BinaryOperation::Equivalence => Formula::Equivalence(
                    Box::new(proposition_to_formula(left)),
                    Box::new(proposition_to_formula(right)),
                ),
            },
            CompoundProposition::NaryOperation {
                operation,
                propositions,
            } => {
                let formulas = propositions
                    .into_iter()
                    .map(proposition_to_formula)
                    .collect_vec();

                match operation {
                    NaryOperation::Conjunction => Formula::Conjunction(
                        Box::new(formulas[0].clone()),
                        Box::new(formulas[1].clone()),
                    ),
                    NaryOperation::Disjunction => Formula::Disjunction(
                        Box::new(formulas[0].clone()),
                        Box::new(formulas[1].clone()),
                    ),
                }
            }
        },
        _ => unimplemented!(),
    }
}

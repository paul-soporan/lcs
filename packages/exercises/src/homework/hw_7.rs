use std::collections::BTreeSet;

use colored::Colorize;
use indexmap::{indexmap, indexset};
use lcs::{
    explanation::{Explain, Explanation},
    markdown::Markdown,
    predicate_logic::{
        parser::Signature,
        strict_parser::parse_expression_strict,
        types::{Expression, FunctionSymbol, PredicateSymbol},
    },
    propositional_logic::{
        normal_forms::ConjunctiveNormalForm,
        parser::{parse_clause, parse_clause_set, parse_proposition},
        solvers::{
            dp::DpSolver,
            dpll::{DpllBranchingHeuristic, DpllSolver},
            resolution::ResolutionSolver,
            solve::{Solve, SolverResult},
        },
        types::{LogicalConsequence, Proposition, PropositionalVariable},
    },
};

use crate::homework::utils::get_letter;

fn subexercise_1() {
    println!("## Exercise 1");

    let parts = ["A ∧ W ⇒ P", "¬A ⇒ I", "¬W ⇒ M", "¬P", "E ⇒ ¬(I ∨ M)"];

    let premises = parts.map(|part| parse_proposition(part, &mut Explanation::default()).unwrap());

    let consequence = LogicalConsequence {
        premises: premises.to_vec(),
        conclusion: PropositionalVariable("E".to_owned()).into(),
    };

    println!(
        "- **Logical consequence:** {}",
        consequence.to_string().blue().markdown()
    );

    let mut explanation = Explanation::default();

    let resolution_solver = ResolutionSolver::new();
    let dp_solver = DpSolver::new();
    let dpll_solver = DpllSolver::new(DpllBranchingHeuristic::First);

    explanation.with_subexplanation(
        || {
            format!(
                "Checking logical consequence {}",
                consequence.to_string().blue().markdown()
            )
        },
        |explanation| {
            let resolution_result = resolution_solver.check_logical_consequence(
                consequence.clone(),
                explanation.subexplanation(|| "Resolution"),
            );
            let dp_result = dp_solver.check_logical_consequence(
                consequence.clone(),
                explanation.subexplanation(|| "DP"),
            );
            let dpll_result = dpll_solver.check_logical_consequence(
                consequence.clone(),
                explanation.subexplanation(|| "DPLL"),
            );

            let consequence_resolution = resolution_result.value();
            let consequence_dp = dp_result.value();
            let consequence_dpll = dpll_result.value();

            let consequence_truth_table = consequence.check().value;

            if (consequence_resolution != consequence_dp)
                || (consequence_dp != consequence_truth_table)
                || (consequence_dpll != consequence_truth_table)
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

fn subexercise_2() {
    println!("## Exercise 2");

    let test_cases = [
        "{{A, ¬B, C}, {B, C}, {¬A, C}, {B, ¬C}, {¬B}}",
        "{{A, ¬B}, {A, C}, {¬B, C}, {¬A, B}, {B, ¬C}, {¬A, ¬C}}",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("### {})", get_letter(i));

        println!(
            "- **Clause set:** {}",
            input.to_string().magenta().markdown()
        );

        let clause_set = parse_clause_set(input, &mut Explanation::default()).unwrap();
        let cnf = ConjunctiveNormalForm(clause_set);

        println!("- **Formula:** {}", cnf.to_string().blue().markdown());

        let mut explanation = Explanation::default();

        let resolution_solver = ResolutionSolver::new();
        let dp_solver = DpSolver::new();
        let dpll_solver = DpllSolver::new(DpllBranchingHeuristic::First);

        let cnf_string = cnf.to_string();

        explanation.with_subexplanation(
            || {
                format!(
                    "Checking satisfiability for {}",
                    cnf_string.blue().markdown()
                )
            },
            |explanation| {
                let resolution_result = resolution_solver
                    .check_satisfiability(cnf.clone(), explanation.subexplanation(|| "Resolution"));
                let dp_result = dp_solver
                    .check_satisfiability(cnf.clone(), explanation.subexplanation(|| "DP"));
                let dpll_result = dpll_solver
                    .check_satisfiability(cnf.clone(), explanation.subexplanation(|| "DPLL"));

                let satisfiable_resolution = resolution_result.value();
                let satisfiable_dp = dp_result.value();
                let satisfiable_dpll = dpll_result.value();

                let satisfiable_truth_table =
                    Proposition::from(cnf).get_attributes().value.satisfiable;

                if (satisfiable_resolution != satisfiable_dp)
                    || (satisfiable_dp != satisfiable_truth_table)
                    || (satisfiable_dpll != satisfiable_truth_table)
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
                    let interpretation = dpll_result.build_interpretation(explanation).unwrap();

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

fn subexercise_3() {
    println!("## Exercise 3");

    let clauses = [
        "{P, Q, ¬R}",
        "{¬P, R}",
        "{P, ¬Q, S}",
        "{¬P, ¬Q, ¬R}",
        "{P, ¬S}",
    ];

    let clause_set = clauses
        .iter()
        .map(|clause| parse_clause(clause, &mut Explanation::default()).unwrap())
        .collect::<BTreeSet<_>>();

    let cnf = ConjunctiveNormalForm(clause_set);

    println!("- **Formula:** {}", cnf.to_string().blue().markdown());

    let mut explanation = Explanation::default();

    let resolution_solver = ResolutionSolver::new();
    let dp_solver = DpSolver::new();
    let dpll_solver = DpllSolver::new(DpllBranchingHeuristic::First);

    let cnf_string = cnf.to_string();

    explanation.with_subexplanation(
        || {
            format!(
                "Checking satisfiability for {}",
                cnf_string.blue().markdown()
            )
        },
        |explanation| {
            let resolution_result = resolution_solver
                .check_satisfiability(cnf.clone(), explanation.subexplanation(|| "Resolution"));
            let dp_result =
                dp_solver.check_satisfiability(cnf.clone(), explanation.subexplanation(|| "DP"));
            let dpll_result = dpll_solver
                .check_satisfiability(cnf.clone(), explanation.subexplanation(|| "DPLL"));

            let satisfiable_resolution = resolution_result.value();
            let satisfiable_dp = dp_result.value();
            let satisfiable_dpll = dpll_result.value();

            let satisfiable_truth_table = Proposition::from(cnf).get_attributes().value.satisfiable;

            if (satisfiable_resolution != satisfiable_dp)
                || (satisfiable_dp != satisfiable_truth_table)
                || (satisfiable_dpll != satisfiable_truth_table)
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
                let interpretation = dpll_result.build_interpretation(explanation).unwrap();

                println!(
                    "- **Satisfying truth valuation:** {}",
                    interpretation.to_string().green().markdown()
                );
            }
        },
    );

    println!("{}", explanation);
}

fn subexercise_4() {
    println!("## Exercise 4");

    let formula = "((P1 ⇒ (P2 ∨ P3)) ∧ (¬P1 ⇒ (P3 ∨ P4)) ∧ (P3 ⇒ (¬P6)) ∧ (¬P3 ⇒ (P4 ⇒ P1)) ∧ (¬(P2 ∧ P5)) ∧ (P2 ⇒ P5)) ⇒ ¬(P3 ⇒ P6)";

    println!("- **Formula:** {}", formula.magenta().markdown());

    let proposition = parse_proposition(formula, &mut Explanation::default()).unwrap();

    let mut explanation = Explanation::default();

    let resolution_solver = ResolutionSolver::new();
    let dp_solver = DpSolver::new();
    let dpll_solver = DpllSolver::new(DpllBranchingHeuristic::First);

    explanation.with_subexplanation(
        || format!("Checking validity for {}", formula.blue().markdown()),
        |explanation| {
            let resolution_result = resolution_solver.check_validity(
                proposition.clone(),
                explanation.subexplanation(|| "Resolution"),
            );
            let dp_result =
                dp_solver.check_validity(proposition.clone(), explanation.subexplanation(|| "DP"));
            let dpll_result = dpll_solver
                .check_validity(proposition.clone(), explanation.subexplanation(|| "DPLL"));

            let valid_resolution = resolution_result.value();
            let valid_dp = dp_result.value();
            let valid_dpll = dpll_result.value();

            let valid_truth_table = Proposition::from(proposition.clone())
                .get_attributes()
                .value
                .valid;

            if (valid_resolution != valid_dp)
                || (valid_dp != valid_truth_table)
                || (valid_dpll != valid_truth_table)
            {
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

fn exercise_1() {
    println!("# Exercise 1");

    subexercise_1();
    subexercise_2();
    subexercise_3();
    subexercise_4();
}

fn exercise_3() {
    println!("# Exercise 3");

    let signature = Signature {
        functions: indexmap! {
            "f".to_owned() => FunctionSymbol::new().prefix_arity(2),
            "g".to_owned() => FunctionSymbol::new().prefix_arity(1),
            "h".to_owned() => FunctionSymbol::new().prefix_arity(3),
        },
        predicates: indexmap! {
            "P".to_owned() => PredicateSymbol::Prefix(vec![2]),
            "Q".to_owned() => PredicateSymbol::Prefix(vec![2]),
            "R".to_owned() => PredicateSymbol::Prefix(vec![3]),
        },
        static_constants: indexset! {
            "a".to_owned(),
            "b".to_owned(),
            "c".to_owned()
        },
        is_constant_fn: |_| false,
    };

    let test_cases = [
        "c",
        "h",
        "(P ∧ Q)",
        "P(f(x, a), g(h(c, a, g(y, z)))",
        "f(g(f(a, h(b, g(x, y)))), Q(a, x))",
        "∀x((P(x, y) ∨ (R(f(x, y), g(f(y, z)), a))) ⇒ (P(a, b) ⇔ ∃yP(x, y)))",
        "(R(x, y, c) ∧ ∀aR(a, a, a))",
        "(h(x, y, c) ∨ ∃xQ(x, x))",
        "P(x, y) ⇔ ∃xR(x, y, z)",
    ];

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Input:** {}", input.magenta().markdown());

        let mut explanation = Explanation::default();

        let expression = parse_expression_strict(input, &signature, &mut explanation);

        println!("{}", explanation);

        match expression {
            Ok(expression) => {
                println!("- **{}**", "Valid expression".green().markdown());
                println!(
                    "- **Expression type:** {}",
                    match expression {
                        Expression::Term(_) => "term".green().markdown(),
                        Expression::Formula(_) => "formula".magenta().markdown(),
                    }
                );

                println!("- **Abstract syntax tree:**\n<pre>{:#?}</pre>", expression);
                println!(
                    "- **More natural-looking syntax tree:**\n<pre>{}</pre>",
                    expression.get_tree()
                );
            }
            Err(error) => {
                println!("- **{}**", "Invalid expression".red().markdown());

                let error = error.trim();
                if !error.is_empty() {
                    println!("- **Parsing Error:** {}", error.red().markdown());
                } else {
                    println!("- **Parsing Error**");
                }
            }
        }
    }
}

pub fn run() {
    exercise_1();
    exercise_3();
}

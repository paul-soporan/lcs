use std::collections::BTreeMap;

use colored::Colorize;
use indexmap::{indexmap, IndexSet};
use itertools::Itertools;
use lcs::{
    explanation::Explanation,
    markdown::Markdown,
    predicate_logic::{
        latex::get_interpolation_for_latex,
        parser::{parse_expression, Signature},
        types::{Associativity, Expression, FunctionSymbol, PredicateSymbol},
    },
};

use crate::homework::utils::get_letter;

fn get_common_math_signature() -> Signature {
    Signature {
        functions: indexmap! {
            "+".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 2).prefix_arity(1),
            "-".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 2).prefix_arity(1),

            "*".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 2),
            "/".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 2),

            "^".to_owned() => FunctionSymbol::new().infix(Associativity::Right, 3),

            "√".to_owned() => FunctionSymbol::new().prefix_arity(1),

            "[][]".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 5),
        },
        predicates: indexmap! {
            "=".to_owned() => PredicateSymbol::Infix,
            "<".to_owned() => PredicateSymbol::Infix,
            "⩽".to_owned() => PredicateSymbol::Infix,
            ">".to_owned() => PredicateSymbol::Infix,
            "⩾".to_owned() => PredicateSymbol::Infix,

            "∈".to_owned() => PredicateSymbol::Infix,

            "P".to_owned() => PredicateSymbol::Prefix(vec![2]),
            "Q".to_owned() => PredicateSymbol::Prefix(vec![3, 2]),
            "R".to_owned() => PredicateSymbol::Prefix(vec![3]),
        },
        is_constant_fn: |name| {
            if name == "ℕ" || name == "ℝ" {
                return true;
            }

            if name.chars().clone().all(|c| c.is_ascii_digit()) {
                return true;
            }

            let mut chars = name.chars();
            let first_char = chars.next().unwrap();

            if first_char == '-' && chars.all(|c| c.is_ascii_digit()) {
                return true;
            }

            false
        },
        static_constants: IndexSet::new(),
    }
}

fn exercise_1() {
    println!("# Exercise 1");

    let test_cases = [
        r"4",
        r"(8 x-5)+7 \geq(3-5 x \Leftrightarrow y>8 z)",
        r"\neg\left(x-y<x^{2}+y \sqrt{z}\right) \wedge\left(\exists z\left((5+1) * y=5 \frac{x}{y^{2}}\right)\right)",
        r"\forall x\left(\frac{x+1}{x^{2}+5}>\frac{x^{3}+5 x+11}{1+\frac{x-8}{x^{4}-1}}\right)",
        r"\neg P(x, y) \Leftrightarrow(\forall x \exists y \forall z((P(y, z) \vee Q(x, y, z)) \Rightarrow(R(x, z, y) \vee \neg P(x, z))))",
    ];

    let common_math_signature = get_common_math_signature();

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Input:** $${input}$$");

        println!("- **LaTeX:** {}", input.magenta().markdown());

        let template = get_interpolation_for_latex(input);

        println!("- **1-dimensional syntax:** {}", template.blue().markdown());

        let input = template.as_str();

        let result = parse_expression(input, &common_math_signature, &mut Explanation::default());

        match result {
            Ok(expression) => {
                println!("- **{}**", "Valid expression".green().markdown());

                println!(
                    "- **Expression type:** {}",
                    match expression {
                        Expression::Term(_) => "term",
                        Expression::Formula(_) => "formula",
                    }
                    .magenta()
                    .markdown()
                );

                println!(
                    "- **Strict syntax:** {}",
                    expression.to_string().green().markdown()
                );

                let mut variables_by_scope = BTreeMap::new();
                let symbols = expression.get_symbols(&mut variables_by_scope);

                println!(
                    "- **Functions:** {}",
                    format!("{:?}", symbols.functions).red().markdown()
                );
                println!(
                    "- **Predicates:** {}",
                    format!("{:?}", symbols.predicates).blue().markdown()
                );
                println!(
                    "- **Constants:** {}",
                    format!(
                        "{{{}}}",
                        symbols
                            .constants
                            .iter()
                            .map(|constant| constant.to_string())
                            .join(", ")
                    )
                    .green()
                    .markdown()
                );

                if variables_by_scope.is_empty() {
                    println!("- **Variables: {}**", "{}".red().markdown());
                } else {
                    println!("- **Variables:**");
                }

                for (scope, variables) in variables_by_scope.iter() {
                    println!(
                        "  - **Scope {}:**",
                        if scope.is_empty() { "." } else { scope }
                            .magenta()
                            .markdown()
                    );
                    println!(
                        "    - **Bound variables:** {}",
                        format!(
                            "{{{}}}",
                            variables
                                .into_iter()
                                .filter(|(_, bound)| **bound)
                                .map(|(name, _)| name)
                                .join(", ")
                        )
                        .red()
                        .markdown()
                    );
                    println!(
                        "    - **Free variables:** {}",
                        format!(
                            "{{{}}}",
                            variables
                                .into_iter()
                                .filter(|(_, bound)| !**bound)
                                .map(|(name, _)| name)
                                .join(", ")
                        )
                        .green()
                        .markdown()
                    );
                }
            }
            Err(_) => {
                println!("- **{}**", "Invalid expression".red().markdown());
            }
        }
    }
}

fn exercise_2() {
    println!("# Exercise 2");

    let test_cases = [
        r"\underset{x, y, z \in \mathbb{R}}{\forall} \underset{k, l \in \mathbb{N}}{\exists}(x, y, z \leqslant k \Rightarrow x+y+z \leqslant l)",
        r"\begin{array}{r}
\underset{x<y<z<1}{\forall} \quad \underset{-1 \leqslant \delta \leqslant 1}{\exists} \underset{-|\delta|<\varepsilon_{1}, \varepsilon_{2}<|\delta|}{\forall}\left(z-y<\varepsilon_{1} \Rightarrow y-x<\varepsilon_{2} \Rightarrow\right. \\
\left.z-x \geqslant \varepsilon_{1}+\varepsilon_{2}+|\delta|\right)
\end{array}",
        r"\underset{x \in \mathbb{N}}{\exists!}\left(x^{2}=7\right)",
    ];

    let common_math_signature = get_common_math_signature();

    for (i, input) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Input:** $${input}$$");

        println!("- **LaTeX:** {}", input.magenta().markdown());

        let template = get_interpolation_for_latex(input);

        println!("- **1-dimensional syntax:** {}", template.blue().markdown());

        let input = template.as_str();

        let expression =
            parse_expression(input, &common_math_signature, &mut Explanation::default()).unwrap();

        println!(
            "- **Strict syntax:** {}",
            expression.to_string().green().markdown()
        );

        let symbols = expression.get_symbols(&mut BTreeMap::new());

        println!(
            "- **Functions:** {}",
            format!("{:?}", symbols.functions).red().markdown()
        );
        println!(
            "- **Predicates:** {}",
            format!("{:?}", symbols.predicates).blue().markdown()
        );
    }
}

pub fn run() {
    exercise_1();
    exercise_2();
}

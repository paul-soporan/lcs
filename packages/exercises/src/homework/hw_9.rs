use std::{
    collections::BTreeSet,
    fmt::Display,
    ops::{Add, Mul},
};

use as_variant::as_variant;
use colored::Colorize;
use indexmap::{indexmap, indexset};
use itertools::Itertools;
use lcs::{
    explanation::Explanation,
    markdown::Markdown,
    predicate_logic::{
        evaluate::{Assignment, Function, Interpretation, Predicate},
        parser::{parse_expression, parse_substitution, Signature},
        substitution::Substitution,
        types::{Associativity, Expression, FunctionSymbol, PredicateSymbol, Term},
    },
};
use maplit::btreeset;

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
        static_constants: indexset! {},
    }
}

fn exercise_1() {
    println!("# Exercise 1");

    let substitutions = [
        ("x", "{x←z+2}"),
        ("(x + y)", "{x←z+2,y←x+y}"),
        ("(xy)", "{x←z+2,y←y+5}"),
        (
            "(¬P(x, y) ⇔ (∀x∃y∀z((P(y, z)∨Q(x, y, z)) ⇒ (R(x, z, y)∨¬P(x, z)))))",
            "{x←(y+z),y←xy,z←(x+c)}",
        ),
    ];

    for (i, &(input, substitution)) in substitutions.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Expression:** {}", input.red().markdown());
        println!("- **Substitution:** {}", substitution.blue().markdown());

        let signature = get_common_math_signature();

        let mut expression =
            parse_expression(input, &signature, &mut Explanation::default()).unwrap();
        let substitution =
            parse_substitution(substitution, &signature, &mut Explanation::default()).unwrap();

        let mut explanation = Explanation::default();

        expression.apply_substitution(&substitution, &mut explanation);

        println!(
            "- **Result:** {}",
            expression.to_relaxed_syntax().green().markdown()
        );

        println!("- **Explanation:**\n{}", explanation.to_string());
    }
}

fn exercise_2() {
    println!("# Exercise 2");

    let common_math_signature = get_common_math_signature();

    let mut theta = parse_substitution(
        "{x ← x + 5, y ← 2x + 3, z ← y + u}",
        &common_math_signature,
        &mut Explanation::default(),
    )
    .unwrap();

    theta.name = "θ".to_owned();

    let mut sigma = parse_substitution(
        "{x ← 3x + 3, z ← u + v, v ← x + 2y}",
        &common_math_signature,
        &mut Explanation::default(),
    )
    .unwrap();

    sigma.name = "σ".to_owned();

    let mut lambda = parse_substitution(
        "{y ← x + v, u ← 3y, v ← 4z}",
        &common_math_signature,
        &mut Explanation::default(),
    )
    .unwrap();

    lambda.name = "λ".to_owned();

    println!("## a)");

    let explanation = &mut Explanation::default();

    println!(
        "- **θσ =** {}",
        (theta.compose(&sigma, explanation))
            .to_relaxed_syntax()
            .green()
            .markdown()
    );

    println!("- **Explanation:**\n{}", explanation.to_string());

    let explanation = &mut Explanation::default();

    println!(
        "- **θλ =** {}",
        theta
            .compose(&lambda, explanation)
            .to_relaxed_syntax()
            .green()
            .markdown()
    );

    println!("- **Explanation:**\n{}", explanation.to_string());

    let explanation = &mut Explanation::default();

    println!(
        "- **θ(σλ) =** {}",
        theta
            .compose(&sigma.compose(&lambda, explanation), explanation)
            .to_relaxed_syntax()
            .green()
            .markdown()
    );

    println!("- **Explanation:**\n{}", explanation.to_string());

    let explanation = &mut Explanation::default();

    println!(
        "- **(θσ)λ =** {}",
        theta
            .compose(&sigma, explanation)
            .compose(&lambda, explanation)
            .to_relaxed_syntax()
            .green()
            .markdown()
    );

    println!("- **Explanation:**\n{}", explanation.to_string());

    println!("## b)");

    let mut f = parse_expression(
        "(P(x, y + z) ⇒ (Q(uv, x + y) ∧ P(x, y)))",
        &common_math_signature,
        &mut Explanation::default(),
    )
    .unwrap();

    let mut g = parse_expression(
        "∃v(P(x, y + z) ⇒ (Q(uv, x + y) ∧ P(x, y)))",
        &common_math_signature,
        &mut Explanation::default(),
    )
    .unwrap();

    let explanation = &mut Explanation::default();

    f.apply_substitution(&theta, explanation);

    println!("- **F<sub>θ</sub>:**\n{}", explanation.to_string());

    let explanation = &mut Explanation::default();

    g.apply_substitution(&sigma, explanation);

    println!("- **G<sub>σ</sub>:**\n{}", explanation.to_string());
}

fn exercise_3() {
    println!("# Exercise 3");

    let signature = Signature {
        functions: indexmap! {
            "f".to_owned() => FunctionSymbol::new().prefix_arity(1),
            "g".to_owned() => FunctionSymbol::new().prefix_arity(1),
            "∗".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 1),
        },
        predicates: indexmap! {
            "p".to_owned() => PredicateSymbol::Prefix(vec![4]),
        },
        is_constant_fn: |_| false,
        static_constants: indexset! {},
    };

    let mut theta = parse_substitution(
        "{x ← f(g(y)), y ← u, z ← f(y)}",
        &signature,
        &mut Explanation::default(),
    )
    .unwrap();

    theta.name = "θ".to_owned();

    let mut sigma = parse_substitution(
        "{u ← y, y ← f(a), x ← g(u)}",
        &signature,
        &mut Explanation::default(),
    )
    .unwrap();

    sigma.name = "σ".to_owned();

    let mut e = parse_expression(
        "p(x, f(y), g(u), z)",
        &signature,
        &mut Explanation::default(),
    )
    .unwrap();

    let explanation = &mut Explanation::default();

    let theta_sigma = theta.compose(&sigma, explanation);

    println!("- **Computing θσ:** {}", explanation);

    let explanation = &mut Explanation::default();

    e.clone().apply_substitution(&theta_sigma, explanation);

    println!("- **Computing E<sub>(θσ)</sub>:** {}", explanation);

    let explanation = &mut Explanation::default();

    e.apply_substitution(&theta, explanation);

    println!("- **Computing E<sub>θ</sub>:** {}", explanation);

    let explanation = &mut Explanation::default();

    e.apply_substitution(&sigma, explanation);

    println!(
        "- **Computing (E<sub>θ</sub>)<sub>σ</sub>:** {}",
        explanation
    );

    println!("- **Conclusion:** E<sub>(θσ)</sub> = (E<sub>θ</sub>)<sub>σ</sub>");
}

fn exercise_4() {
    println!("# Exercise 4");

    let common_math_signature = get_common_math_signature();

    let cases = [
        ("y + 1", "x", "∃y(x = 2y)"),
        ("y + 1", "y", "∀y(x = 2y)"),
        ("vw", "x", "∃y(x < vx ⇒ (∃w(w < v)))"),
        ("vw", "v", "∃y(x < vx ⇒ (∃w(w < v)))"),
        ("vw", "w", "∃y(x < vx ⇒ (∃w(w < v)))"),
    ];

    for (i, (term, variable, formula)) in cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        println!("- **Term:** {}", term.red().markdown());
        println!("- **Variable:** {}", variable.blue().markdown());
        println!("- **Formula:** {}", formula.magenta().markdown());

        let term = as_variant!(
            parse_expression(term, &common_math_signature, &mut Explanation::default()).unwrap(),
            Expression::Term
        )
        .unwrap();

        let variable = as_variant!(
            as_variant!(
                parse_expression(
                    variable,
                    &common_math_signature,
                    &mut Explanation::default()
                )
                .unwrap(),
                Expression::Term
            )
            .unwrap(),
            Term::Variable
        )
        .unwrap();

        let mut formula = as_variant!(
            parse_expression(formula, &common_math_signature, &mut Explanation::default()).unwrap(),
            Expression::Formula
        )
        .unwrap();

        let mut explanation = Explanation::default();

        let is_substitutable = formula.is_substitutable(&term, &variable, &mut explanation);

        println!(
            "- **Substitutable:** {}",
            if is_substitutable {
                "Yes".green().markdown()
            } else {
                "No".red().markdown()
            }
        );

        println!("- **Explanation:**\n{}", explanation.to_string());

        if is_substitutable {
            let substitution = Substitution {
                name: "σ".to_owned(),
                mapping: indexmap! { variable => term },
            };

            let mut explanation = Explanation::default();

            formula.apply_substitution(&substitution, &mut explanation);

            println!("- **Result:**\n{}", explanation.to_string());
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Polynomial(Vec<f32>);

impl Add for Polynomial {
    type Output = Polynomial;

    fn add(self, other: Polynomial) -> Polynomial {
        let mut result = vec![0.0; self.0.len().max(other.0.len())];

        for i in 0..result.len() {
            result[i] = self.0.get(i).unwrap_or(&0.0) + other.0.get(i).unwrap_or(&0.0);
        }

        Polynomial(result)
    }
}

impl Mul for Polynomial {
    type Output = Polynomial;

    fn mul(self, other: Polynomial) -> Polynomial {
        let mut result = vec![0.0; self.0.len() + other.0.len() - 1];

        for i in 0..self.0.len() {
            for j in 0..other.0.len() {
                result[i + j] += self.0[i] * other.0[j];
            }
        }

        Polynomial(result)
    }
}

impl Display for Polynomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut components = vec![];

        for (i, coefficient) in self.0.iter().enumerate() {
            if *coefficient == 0.0 {
                continue;
            }

            let mut component = match coefficient {
                1.0 if i > 1 => "".to_owned(),
                -1.0 if i > 1 => "-".to_owned(),
                _ => format!("{:.1}", coefficient),
            };

            if i > 0 {
                component += "X";

                if i > 1 {
                    component += &format!("<sup>{}</sup>", i);
                }
            }

            components.push(component);
        }

        components.reverse();

        if components.is_empty() {
            write!(f, "0")
        } else {
            write!(f, "{}", components.join(" + "))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum SetElement {
    Number(i32),
    Tuple(Box<SetElement>, Box<SetElement>),
    Set(Set),
}

impl Display for SetElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SetElement::Number(number) => write!(f, "{}", number),
            SetElement::Tuple(a, b) => write!(f, "({}, {})", a, b),
            SetElement::Set(set) => {
                write!(f, "{}", set)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Set(BTreeSet<SetElement>);

impl Display for Set {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, element) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", element)?;
        }

        write!(f, "}}")
    }
}

fn exercise_5() {
    println!("# Exercise 5");

    let signature = Signature {
        functions: indexmap! {
            "+".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 1),
            "−".to_owned() => FunctionSymbol::new().prefix_arity(1),
            "∗".to_owned() => FunctionSymbol::new().infix(Associativity::Left, 2)
        },
        predicates: indexmap! {
            "=".to_owned() => PredicateSymbol::Infix,
            "<".to_owned() => PredicateSymbol::Infix,
            "≤".to_owned() => PredicateSymbol::Infix,
        },
        is_constant_fn: |_| false,
        static_constants: indexset! {"0".to_owned(), "1".to_owned()},
    };

    let first_expression = as_variant!(
        parse_expression("(x + (−y)) ∗ z", &signature, &mut Explanation::default()).unwrap(),
        Expression::Term
    )
    .unwrap();
    let second_expression = as_variant!(
        parse_expression(
            "(x ∗ y + (−z)) ≤ (−z + 1) ∗ 0",
            &signature,
            &mut Explanation::default(),
        )
        .unwrap(),
        Expression::Formula
    )
    .unwrap();
    let third_expression = as_variant!(
        parse_expression(
            "(x ∗ (y + z)) = (x ∗ y) + (x ∗ z)",
            &signature,
            &mut Explanation::default(),
        )
        .unwrap(),
        Expression::Formula
    )
    .unwrap();

    let natural_numbers_assignment = Assignment::<u32> {
        interpretation: Interpretation {
            functions: indexmap! {
                "+".to_owned() => Function {
                    name: "+".to_owned(),
                    arity: 2,
                    function: |arguments| arguments[0] + arguments[1],
                },
                "−".to_owned() => Function {
                    name: "square".to_owned(),
                    arity: 1,
                    function: |arguments| arguments[0] * arguments[0],
                },
                "∗".to_owned() => Function {
                    name: "∗".to_owned(),
                    arity: 2,
                    function: |arguments| arguments[0] * arguments[1],
                },
            },
            constants: indexmap! {
                "0".to_owned() => 0,
                "1".to_owned() => 1,
            },
            predicates: indexmap! {
                "=".to_owned() => Predicate {
                    name: "=".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] == arguments[1],
                },
                "<".to_owned() => Predicate {
                    name: "<".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] < arguments[1],
                },
                "≤".to_owned() => Predicate {
                    name: "≤".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] <= arguments[1],
                },
            },
        },
        variables: indexmap! {
            "x".to_owned() => 1,
            "y".to_owned() => 2,
            "z".to_owned() => 3,
        },
    };

    let univariate_polynomials_over_reals_assignment = Assignment::<Polynomial> {
        interpretation: Interpretation {
            functions: indexmap! {
                "+".to_owned() => Function {
                    name: "+".to_owned(),
                    arity: 2,
                    function: |arguments: &[Polynomial]| arguments[0].clone() + arguments[1].clone(),
                },
                "−".to_owned() => Function {
                    name: "−".to_owned(),
                    arity: 1,
                    function: |arguments| arguments[0].clone() * Polynomial(vec![-1.0]),
                },
                "∗".to_owned() => Function {
                    name: "∗".to_owned(),
                    arity: 2,
                    function: |arguments| arguments[0].clone() * arguments[1].clone(),
                },
            },
            constants: indexmap! {
                "0".to_owned() => Polynomial(vec![]),
                "1".to_owned() => Polynomial(vec![1.0]),
            },
            predicates: indexmap! {
                "=".to_owned() => Predicate {
                    name: "=".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] == arguments[1],
                },
                "<".to_owned() => Predicate {
                    name: "degree_<".to_owned(),
                    arity: 2,
                    predicate: |arguments: &[Polynomial]| arguments[0].0.len() < arguments[1].0.len(),
                },
                "≤".to_owned() => Predicate {
                    name: "degree_≤".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0].0.len() <= arguments[1].0.len(),
                },
            },
        },
        variables: indexmap! {
            "x".to_owned() => Polynomial(vec![7.0]),
            "y".to_owned() => Polynomial(vec![0.0, 10.0]),
            "z".to_owned() => Polynomial(vec![5.3, 0.0, 1.0]),
        },
    };

    let sets_assignment = Assignment::<Set> {
        interpretation: Interpretation {
            functions: indexmap! {
                "+".to_owned() => Function {
                    name: "∪".to_owned(),
                    arity: 2,
                    function: |arguments: &[Set]| Set(arguments[0].0.union(&arguments[1].0).cloned().collect()),
                },
                "−".to_owned() => Function {
                    name: "powerset".to_owned(),
                    arity: 1,
                    function: |arguments| Set(arguments[0].0.iter().powerset()
                    .map(|set| SetElement::Set(Set(set.into_iter().cloned().collect()))).collect()),
                },
                "∗".to_owned() => Function {
                    name: "×".to_owned(),
                    arity: 2,
                    function: |arguments| {
                        Set(arguments[0].0.iter().cloned().cartesian_product(arguments[1].0.iter().cloned())
                        .map(|(a, b)| SetElement::Tuple(Box::new(a), Box::new(b))).collect())
                    },
                },
            },
            constants: indexmap! {
                "0".to_owned() => Set(btreeset! {}),
                "1".to_owned() => Set(btreeset! {SetElement::Number(1) }),
            },
            predicates: indexmap! {
                "=".to_owned() => Predicate {
                    name: "=".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] == arguments[1],
                },
                "<".to_owned() => Predicate {
                    name: "⊂".to_owned(),
                    arity: 2,
                    predicate: |arguments: &[Set]| arguments[0] != arguments[1] && arguments[0].0.is_subset(&arguments[1].0),
                },
                "≤".to_owned() => Predicate {
                    name: "⊆".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0].0.is_subset(&arguments[1].0),
                },
            },
        },
        variables: indexmap! {
            "x".to_owned() => Set(btreeset! { SetElement::Number(1), SetElement::Number(2) }),
            "y".to_owned() => Set(btreeset! { SetElement::Number(3), SetElement::Number(4), SetElement::Number(5) }),
            "z".to_owned() => Set(btreeset! { SetElement::Number(9), SetElement::Number(10) }),
        },
    };

    let strings_assignment = Assignment {
        interpretation: Interpretation {
            functions: indexmap! {
                "+".to_owned() => Function {
                    name: "concatenate".to_owned(),
                    arity: 2,
                    function: |arguments| format!("{}{}", arguments[0], arguments[1]),
                },
                "−".to_owned() => Function {
                    name: "reversed".to_owned(),
                    arity: 1,
                    function: |arguments| arguments[0].chars().rev().collect(),
                },
                "∗".to_owned() => Function {
                    name: "interleave".to_owned(),
                    arity: 2,
                    function: |arguments| {
                        let n = arguments[0].len().max(arguments[1].len());

                        (0..n)
                            .map(|i| {
                                format!(
                                    "{}{}",
                                    arguments[0].chars().nth(i).map(|c| c.to_string()).unwrap_or(String::new()),
                                    arguments[1].chars().nth(i).map(|c| c.to_string()).unwrap_or(String::new()),
                                )
                            })
                            .collect::<String>()
                    },
                },
            },
            constants: indexmap! {
                "0".to_owned() => "0".to_owned(),
                "1".to_owned() => "1".to_owned(),
            },
            predicates: indexmap! {
                "=".to_owned() => Predicate {
                    name: "=".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] == arguments[1],
                },
                "<".to_owned() => Predicate {
                    name: "<".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] < arguments[1],
                },
                "≤".to_owned() => Predicate {
                    name: "≤".to_owned(),
                    arity: 2,
                    predicate: |arguments| arguments[0] <= arguments[1],
                },
            },
        },
        variables: indexmap! {
            "x".to_owned() => "first".to_owned(),
            "y".to_owned() => "second".to_owned(),
            "z".to_owned() => "third".to_owned(),
        },
    };

    let mut explanation = Explanation::default();

    println!("## a) Universe of natural numbers");

    println!(
        "- **Interpretation:** {}",
        natural_numbers_assignment.interpretation
    );

    println!("- **Assignment:** {}", natural_numbers_assignment);

    first_expression.evaluate(
        &natural_numbers_assignment,
        explanation.subexplanation("First expression"),
    );

    second_expression.evaluate(
        &natural_numbers_assignment,
        explanation.subexplanation("Second expression"),
    );

    third_expression.evaluate(
        &natural_numbers_assignment,
        explanation.subexplanation("Third expression"),
    );

    println!(
        "- **Value under interpretation and variable assignment:**\n{}",
        explanation.to_string()
    );
    let mut explanation = Explanation::default();

    println!("## b) Universe of univariate polynomials over reals");

    println!(
        "- **Interpretation:** {}",
        univariate_polynomials_over_reals_assignment.interpretation
    );

    println!(
        "- **Assignment:** {}",
        univariate_polynomials_over_reals_assignment
    );

    first_expression.evaluate(
        &univariate_polynomials_over_reals_assignment,
        explanation.subexplanation("First expression"),
    );

    second_expression.evaluate(
        &univariate_polynomials_over_reals_assignment,
        explanation.subexplanation("Second expression"),
    );

    third_expression.evaluate(
        &univariate_polynomials_over_reals_assignment,
        explanation.subexplanation("Third expression"),
    );

    println!(
        "- **Value under interpretation and variable assignment:**\n{}",
        explanation.to_string()
    );

    let mut explanation = Explanation::default();

    println!("## c) Universe of sets");

    println!("- **Interpretation:** {}", sets_assignment.interpretation);

    println!("- **Assignment:** {}", sets_assignment);

    first_expression.evaluate(
        &sets_assignment,
        explanation.subexplanation("First expression"),
    );

    second_expression.evaluate(
        &sets_assignment,
        explanation.subexplanation("Second expression"),
    );

    third_expression.evaluate(
        &sets_assignment,
        explanation.subexplanation("Third expression"),
    );

    println!(
        "- **Value under interpretation and variable assignment:**\n{}",
        explanation.to_string()
    );

    let mut explanation = Explanation::default();

    println!("## d) Universe of strings");

    println!(
        "- **Interpretation:** {}",
        strings_assignment.interpretation
    );

    println!("- **Assignment:** {}", strings_assignment);

    first_expression.evaluate(
        &strings_assignment,
        explanation.subexplanation("First expression"),
    );

    second_expression.evaluate(
        &strings_assignment,
        explanation.subexplanation("Second expression"),
    );

    third_expression.evaluate(
        &strings_assignment,
        explanation.subexplanation("Third expression"),
    );

    println!(
        "- **Value under interpretation and variable assignment:**\n{}",
        explanation.to_string()
    );
}

pub fn run() {
    exercise_1();
    exercise_2();
    exercise_3();
    exercise_4();
    exercise_5();
}

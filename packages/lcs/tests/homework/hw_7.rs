use indexmap::{indexmap, IndexSet};
use lcs::{
    explanation::Explanation,
    predicate_logic::{
        parser::{parse_expression, Signature},
        types::{Constant, Expression, Formula, FunctionSymbol, PredicateSymbol, Term, Variable},
    },
};

#[test]
fn exercise_3() {
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
        static_constants: IndexSet::from_iter(["a".to_owned(), "b".to_owned(), "c".to_owned()]),
        is_constant_fn: |_| false,
    };

    let test_cases: [(&str, Result<Expression, Option<!>>); 9] = [
        (
            "c",
            Ok(Expression::Term(Term::Constant(Constant("c".to_owned())))),
        ),
        ("h", Err(None)),
        ("(P ∧ Q)", Err(None)),
        ("P(f(x, a), g(h(c, a, g(y, z)))", Err(None)),
        ("f(g(f(a, h(b, g(x, y)))), Q(a, x))", Err(None)),
        (
            "∀x((P(x, y) ∨ (R(f(x, y), g(f(y, z)), a))) ⇒ (P(a, b) ⇔ ∃yP(x, y)))",
            Err(None),
        ),
        (
            "(R(x, y, c) ∧ ∀aR(a, a, a))",
            Ok(Expression::Formula(Formula::Conjunction(
                Box::new(Formula::PredicateApplication {
                    predicate: "R".to_owned(),
                    arguments: vec![
                        Term::Variable(Variable("x".to_owned())),
                        Term::Variable(Variable("y".to_owned())),
                        Term::Constant(Constant("c".to_owned())),
                    ],
                    symbol: signature.predicates["R"].clone(),
                }),
                Box::new(Formula::UniversalQuantification(
                    Variable("a".to_owned()),
                    Box::new(Formula::PredicateApplication {
                        predicate: "R".to_owned(),
                        arguments: vec![
                            Term::Constant(Constant("a".to_owned())),
                            Term::Constant(Constant("a".to_owned())),
                            Term::Constant(Constant("a".to_owned())),
                        ],
                        symbol: signature.predicates["R"].clone(),
                    }),
                )),
            ))),
        ),
        ("(h(x, y, c) ∨ ∃xQ(x, x))", Err(None)),
        (
            "P(x, y) ⇔ ∃xR(x, y, z)",
            Ok(Expression::Formula(Formula::Equivalence(
                Box::new(Formula::PredicateApplication {
                    predicate: "P".to_owned(),
                    arguments: vec![
                        Term::Variable(Variable("x".to_owned())),
                        Term::Variable(Variable("y".to_owned())),
                    ],
                    symbol: signature.predicates["P"].clone(),
                }),
                Box::new(Formula::ExistentialQuantification(
                    Variable("x".to_owned()),
                    Box::new(Formula::PredicateApplication {
                        predicate: "R".to_owned(),
                        arguments: vec![
                            Term::Variable(Variable("x".to_owned())),
                            Term::Variable(Variable("y".to_owned())),
                            Term::Variable(Variable("z".to_owned())),
                        ],
                        symbol: signature.predicates["R"].clone(),
                    }),
                )),
            ))),
        ),
    ];

    for (i, (input, expected_result)) in test_cases.into_iter().enumerate() {
        let result =
            parse_expression(input, &signature, &mut Explanation::default()).map_err(|_| None);

        assert_eq!(
            result,
            expected_result,
            "Test case {}; Input: {}",
            i + 1,
            input
        );
    }
}

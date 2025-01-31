use colored::Colorize;
use lcs::{
    explanation::Explanation, markdown::Markdown,
    propositional_logic::strict_parser::parse_proposition_strict,
};

use crate::homework::utils::get_letter;

pub fn run() {
    let test_cases = [
        ("(((P ⇒ Q) ∨ S) ⇔ T)", true),
        ("((P ⇒ (Q ∧ (S ⇒ T))))", false),
        ("(¬(B(¬Q)) ∧ R)", false),
        ("(P ∧ ((¬Q) ∧ (¬(¬(Q ⇔ (¬R))))))", true),
        ("((P ∨ Q) ⇒ ¬(P ∨ Q)) ∧ (P ∨ (¬(¬Q)))", false),
    ];

    for (i, &(input, expected)) in test_cases.iter().enumerate() {
        println!("## {})", get_letter(i));

        let mut explanation = Explanation::default();

        let result = parse_proposition_strict(input, &mut explanation);

        println!("- **Input:** {}\n", input.green().markdown());
        println!("{explanation}");

        let valid = result.is_ok();

        assert_eq!(valid, expected);

        let mark = if valid { "✅" } else { "❌" };
        let is = if valid { "is" } else { "is not" };

        println!("- **Conclusion:** {mark} Input {is} a well formed propositional formula (wff) as defined by the syntax of the language of propositional logic.\n\n");
    }
}

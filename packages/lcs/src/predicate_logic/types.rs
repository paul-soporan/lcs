use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
};

use colored::Colorize;
use derive_more::derive::Display;
use itertools::Itertools;
use termtree::Tree;

use crate::{explanation::Explanation, markdown::Markdown};

use super::{parser::ExpressionSymbols, substitution::Substitution};

#[derive(Debug, Display, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(pub String);

#[derive(Debug, Display, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constant(pub String);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Associativity {
    None,
    Left,
    Right,
    Full,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InfixFunctionSymbol {
    pub associativity: Associativity,
    pub precedence: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionSymbol {
    pub prefix: Vec<usize>,
    pub infix: Option<InfixFunctionSymbol>,
}

impl FunctionSymbol {
    pub fn new() -> Self {
        Self {
            prefix: Vec::new(),
            infix: None,
        }
    }

    pub fn prefix_arity(mut self, arity: usize) -> Self {
        self.prefix.push(arity);

        self
    }

    pub fn infix(mut self, associativity: Associativity, precedence: usize) -> Self {
        self.infix = Some(InfixFunctionSymbol {
            associativity,
            precedence,
        });

        // Infix functions can also be used as prefix in order to be usable in strict syntax.
        self.prefix.push(2);

        self
    }

    // pub fn supports_arity(&self, arity: usize) -> bool {
    //     match self {
    //         FunctionSymbol::Prefix(arities) => arities.contains(&arity),
    //         FunctionSymbol::Infix { .. } => arity == 2,
    //     }
    // }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PredicateSymbol {
    /// Prefix-only predicates can have different arities, since there's no ambiguity.
    Prefix(Vec<usize>),
    /// Only binary predicates can be infix. Can also be used in prefix form, in order to be usable in strict syntax.
    Infix,
}

impl PredicateSymbol {
    pub fn supports_arity(&self, arity: usize) -> bool {
        match self {
            PredicateSymbol::Prefix(arities) => arities.contains(&arity),
            PredicateSymbol::Infix => arity == 2,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Variable(Variable),
    Constant(Constant),
    FunctionApplication {
        function: String,
        arguments: Vec<Term>,
        symbol: FunctionSymbol,
    },
}

impl Term {
    pub fn get_tree(&self) -> Tree<String> {
        match self {
            Term::Variable(v) => Tree::new(v.0.clone()),
            Term::Constant(c) => Tree::new(c.0.clone()),
            Term::FunctionApplication {
                function,
                arguments,
                ..
            } => Tree::new(function.clone()).with_leaves(arguments.iter().map(Term::get_tree)),
        }
    }

    pub fn contains_variable(&self, variable: &Variable) -> bool {
        match self {
            Term::Variable(v) => v == variable,
            Term::Constant(_) => false,
            Term::FunctionApplication { arguments, .. } => arguments
                .iter()
                .any(|argument| argument.contains_variable(variable)),
        }
    }

    pub fn apply_substitution(
        &mut self,
        substitution: &Substitution,
        explanation: &mut Explanation,
    ) {
        explanation.step(format!(
            "({})<sub>{}</sub>",
            self.to_relaxed_syntax(None).red().markdown(),
            substitution.name
        ));

        match self {
            Term::Variable(v) => {
                if let Some(term) = substitution.mapping.get(v) {
                    *self = term.clone()
                }
            }
            Term::Constant(_) => {}
            Term::FunctionApplication {
                function,
                arguments,
                ..
            } => {
                for argument in arguments {
                    argument.apply_substitution(substitution, explanation.subexplanation(""));
                }

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{}({})", function, subexplanations.join(", "))
                });
            }
        };

        explanation.step(self.to_relaxed_syntax(None).green().markdown());
    }

    pub fn with_substitution(
        &self,
        substitution: &Substitution,
        explanation: &mut Explanation,
    ) -> Term {
        let mut cloned = self.clone();
        cloned.apply_substitution(substitution, explanation);
        cloned
    }

    pub fn is_substitutable(&self, _: &Term, _: &Variable) -> bool {
        true
    }

    pub fn to_relaxed_syntax(&self, parent: Option<&FunctionSymbol>) -> String {
        match self {
            Term::Variable(v) => v.to_string(),
            Term::Constant(c) => c.to_string(),
            Term::FunctionApplication {
                function,
                arguments,
                symbol,
            } => {
                if let Some(infix) = &symbol.infix {
                    let expression = format!(
                        "{}{}{}",
                        arguments[0].to_relaxed_syntax(Some(symbol)),
                        match function.as_str() {
                            "[][]" => String::new(),
                            _ => format!(" {} ", function),
                        },
                        arguments[1].to_relaxed_syntax(Some(symbol))
                    );

                    if let Some(FunctionSymbol {
                        infix: Some(parent_infix),
                        ..
                    }) = parent
                    {
                        if parent_infix.precedence > infix.precedence {
                            return format!("({})", expression);
                        }
                    }

                    expression
                } else {
                    format!(
                        "{}({})",
                        function,
                        arguments
                            .iter()
                            .map(|term| term.to_relaxed_syntax(None))
                            .join(", ")
                    )
                }
            }
        }
    }

    pub fn relabel_variable(&mut self, old: &str, new: &str) {
        match self {
            Term::Variable(v) if v.0 == old => v.0 = new.to_owned(),
            Term::FunctionApplication { arguments, .. } => {
                for argument in arguments {
                    argument.relabel_variable(old, new);
                }
            }
            _ => {}
        }
    }

    pub fn get_symbols(
        &self,
        context: impl AsRef<str>,
        variables_by_scope: &mut BTreeMap<String, BTreeMap<Variable, bool>>,
    ) -> ExpressionSymbols {
        let context = context.as_ref();

        let mut symbols = ExpressionSymbols::default();
        // symbols.variables_by_scope = variables_by_scope;

        match self {
            Term::Variable(variable) => {
                let mut context = context.to_owned();

                let mut i = context.chars().count() as i32 - 1;
                while i >= 0 && ".¬∧∨⇒⇔01".contains(context.chars().nth(i as usize).unwrap())
                {
                    context.pop();
                    i -= 1;
                }

                let variable_context = context.to_owned();

                if i > 0 {
                    i -= 1;

                    while i >= 0 {
                        if let Some(parent_context) = variables_by_scope.get(&context) {
                            let parent_context = parent_context.clone();

                            let variable_context_entry = variables_by_scope
                                .entry(variable_context.to_owned())
                                .or_insert_with(BTreeMap::new);

                            for (variable, value) in parent_context {
                                if value {
                                    variable_context_entry.insert(variable.clone(), value);
                                } else {
                                    let _ =
                                        variable_context_entry.try_insert(variable.clone(), value);
                                }
                            }
                        }

                        context.pop();
                        i -= 1;
                    }
                }

                let variable_context_entry = variables_by_scope
                    .entry(variable_context.to_owned())
                    .or_insert_with(BTreeMap::new);
                let _ = variable_context_entry.try_insert(variable.clone(), false);
            }
            Term::Constant(constant) => {
                symbols.constants.insert(constant.clone());
            }
            Term::FunctionApplication {
                function,
                arguments,
                ..
            } => {
                symbols
                    .functions
                    .insert(format!("{function}/{}", arguments.len()));

                for argument in arguments {
                    symbols.extend(argument.get_symbols(context, variables_by_scope));
                }
            }
        };

        symbols
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(v) => write!(f, "{v}"),
            Term::Constant(c) => write!(f, "{c}"),
            Term::FunctionApplication {
                function,
                arguments,
                ..
            } => {
                write!(
                    f,
                    "{function}({})",
                    arguments.iter().map(|a| a.to_string()).join(", ")
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    PredicateApplication {
        predicate: String,
        arguments: Vec<Term>,
        symbol: PredicateSymbol,
    },
    Tautology,
    Contradiction,
    Negation(Box<Formula>),
    Conjunction(Box<Formula>, Box<Formula>),
    Disjunction(Box<Formula>, Box<Formula>),
    Implication(Box<Formula>, Box<Formula>),
    Equivalence(Box<Formula>, Box<Formula>),
    UniversalQuantification(Variable, Box<Formula>),
    ExistentialQuantification(Variable, Box<Formula>),
}

impl Formula {
    pub fn get_tree(&self) -> Tree<String> {
        match self {
            Formula::Tautology => Tree::new("⊤".to_owned()),
            Formula::Contradiction => Tree::new("⊥".to_owned()),
            Formula::PredicateApplication {
                predicate,
                arguments,
                ..
            } => Tree::new(predicate.clone()).with_leaves(arguments.iter().map(Term::get_tree)),
            Formula::Negation(formula) => {
                Tree::new("¬".to_owned()).with_leaves(vec![formula.get_tree()])
            }
            Formula::Conjunction(left, right)
            | Formula::Disjunction(left, right)
            | Formula::Implication(left, right)
            | Formula::Equivalence(left, right) => Tree::new(
                match self {
                    Formula::Conjunction(..) => "∧",
                    Formula::Disjunction(..) => "∨",
                    Formula::Implication(..) => "⇒",
                    Formula::Equivalence(..) => "⇔",
                    _ => unreachable!(),
                }
                .to_owned(),
            )
            .with_leaves(vec![left.get_tree(), right.get_tree()]),
            Formula::UniversalQuantification(variable, formula)
            | Formula::ExistentialQuantification(variable, formula) => Tree::new(
                match self {
                    Formula::UniversalQuantification(..) => "∀",
                    Formula::ExistentialQuantification(..) => "∃",
                    _ => unreachable!(),
                }
                .to_owned(),
            )
            .with_leaves(vec![Tree::new(variable.0.clone()), formula.get_tree()]),
        }
    }

    pub fn apply_substitution(
        &mut self,
        substitution: &Substitution,
        explanation: &mut Explanation,
    ) {
        explanation.step(format!(
            "({})<sub>{}</sub>",
            self.to_relaxed_syntax(None).red().markdown(),
            substitution.name
        ));

        match self {
            Formula::Tautology | Formula::Contradiction => {}
            Formula::PredicateApplication {
                predicate,
                arguments,
                ..
            } => {
                for argument in arguments {
                    argument.apply_substitution(substitution, explanation.subexplanation(""));
                }

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{predicate}({})", subexplanations.join(", "))
                });
            }
            Formula::Negation(f) => {
                f.apply_substitution(substitution, explanation.subexplanation(""));

                explanation
                    .merge_subexplanations(|subexplanations| format!("¬{}", subexplanations[0]));
            }
            Formula::Conjunction(left, right) => {
                left.apply_substitution(substitution, explanation.subexplanation(""));
                right.apply_substitution(substitution, explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{} ∧ {}", subexplanations[0], subexplanations[1])
                });
            }
            Formula::Disjunction(left, right) => {
                left.apply_substitution(substitution, explanation.subexplanation(""));
                right.apply_substitution(substitution, explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{} ∨ {}", subexplanations[0], subexplanations[1])
                });
            }
            Formula::Implication(left, right) => {
                left.apply_substitution(substitution, explanation.subexplanation(""));
                right.apply_substitution(substitution, explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{} ⇒ {}", subexplanations[0], subexplanations[1])
                });
            }
            Formula::Equivalence(left, right) => {
                left.apply_substitution(substitution, explanation.subexplanation(""));
                right.apply_substitution(substitution, explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("{} ⇔ {}", subexplanations[0], subexplanations[1])
                });
            }
            Formula::UniversalQuantification(v, f) => {
                f.apply_substitution(&substitution.without(v), explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("∀{}({})", v, subexplanations[0])
                });
            }
            Formula::ExistentialQuantification(v, f) => {
                f.apply_substitution(&substitution.without(v), explanation.subexplanation(""));

                explanation.merge_subexplanations(|subexplanations| {
                    format!("∃{}({})", v, subexplanations[0])
                });
            }
        }

        explanation.step(self.to_relaxed_syntax(None).green().markdown());
    }

    pub fn with_substitution(
        &self,
        substitution: &Substitution,
        explanation: &mut Explanation,
    ) -> Formula {
        let mut cloned = self.clone();
        cloned.apply_substitution(substitution, explanation);
        cloned
    }

    pub fn is_substitutable(
        &self,
        term: &Term,
        variable: &Variable,
        explanation: &mut Explanation,
    ) -> bool {
        explanation.step(format!(
            "Checking if {} is substitutable for {} in {}",
            term.to_relaxed_syntax(None).red().markdown(),
            variable.to_string().blue().markdown(),
            self.to_relaxed_syntax(None).green().markdown()
        ));

        match self {
            Formula::Tautology | Formula::Contradiction => {
                explanation.step("Tautology/contradiction -> substitutable".to_owned());
                true
            }
            Formula::PredicateApplication { .. } => {
                explanation.step("Predicate application -> substitutable".to_owned());
                true
            }
            Formula::Negation(f) => {
                f.is_substitutable(term, variable, explanation.subexplanation("Negation"))
            }
            Formula::Conjunction(left, right)
            | Formula::Disjunction(left, right)
            | Formula::Implication(left, right)
            | Formula::Equivalence(left, right) => {
                left.is_substitutable(term, variable, explanation.subexplanation("LHS"))
                    && right.is_substitutable(term, variable, explanation.subexplanation("RHS"))
            }
            Formula::UniversalQuantification(v, f) | Formula::ExistentialQuantification(v, f) => {
                if v == variable {
                    explanation.step(format!("{} is bound (protected) -> substitutable", v));
                    true
                } else {
                    let contains_variable = term.contains_variable(v);
                    if contains_variable {
                        explanation.step(format!("{} is free in term -> not substitutable ", v));

                        return false;
                    }

                    let is_substitutable_in_subformula = f.is_substitutable(
                        term,
                        variable,
                        explanation.subexplanation("Subformula of quantified formula"),
                    );

                    if is_substitutable_in_subformula {
                        explanation.step(
                            "Variable is substitutable in subformula -> substitutable".to_owned(),
                        );
                    } else {
                        explanation.step(
                            "Variable is not substitutable in subformula -> not substitutable"
                                .to_owned(),
                        );
                    }

                    is_substitutable_in_subformula
                }
            }
        }
    }

    pub fn to_relaxed_syntax(&self, parent: Option<&str>) -> String {
        match self {
            Formula::Tautology => "⊤".to_owned(),
            Formula::Contradiction => "⊥".to_owned(),
            Formula::PredicateApplication {
                predicate,
                arguments,
                symbol,
            } => {
                if arguments.is_empty() {
                    predicate.clone()
                } else if arguments.len() == 2 && matches!(symbol, PredicateSymbol::Infix) {
                    let expression = format!(
                        "{} {predicate} {}",
                        arguments[0].to_relaxed_syntax(None),
                        arguments[1].to_relaxed_syntax(None)
                    );

                    if let Some(parent) = parent {
                        if parent == "¬" {
                            return format!("({})", expression);
                        }
                    }

                    expression
                } else {
                    format!(
                        "{}({})",
                        predicate,
                        arguments
                            .iter()
                            .map(|term| term.to_relaxed_syntax(None))
                            .join(", ")
                    )
                }
            }
            Formula::Negation(f) => format!("¬{}", f.to_relaxed_syntax(Some("¬"))),
            Formula::Conjunction(left, right) => {
                let conjunction = format!(
                    "{} ∧ {}",
                    left.to_relaxed_syntax(Some("∧")),
                    right.to_relaxed_syntax(Some("∧"))
                );

                if parent == Some("¬") {
                    format!("({})", conjunction)
                } else {
                    conjunction
                }
            }
            Formula::Disjunction(left, right) => {
                let disjunction = format!(
                    "{} ∨ {}",
                    left.to_relaxed_syntax(Some("∨")),
                    right.to_relaxed_syntax(Some("∨"))
                );

                if parent == Some("¬") {
                    format!("({})", disjunction)
                } else {
                    disjunction
                }
            }
            Formula::Implication(left, right) => format!(
                "{} ⇒ {}",
                left.to_relaxed_syntax(Some("⇒")),
                right.to_relaxed_syntax(Some("⇒"))
            ),
            Formula::Equivalence(left, right) => format!(
                "{} ⇔ {}",
                left.to_relaxed_syntax(Some("⇔")),
                right.to_relaxed_syntax(Some("⇔"))
            ),
            Formula::UniversalQuantification(variable, formula) => {
                format!("∀{}({})", variable, formula.to_relaxed_syntax(Some("∀")))
            }
            Formula::ExistentialQuantification(variable, formula) => {
                format!("∃{}({})", variable, formula.to_relaxed_syntax(Some("∃")))
            }
        }
    }

    pub fn relabel_variable(&mut self, old: &str, new: &str) {
        match self {
            Formula::Tautology | Formula::Contradiction => {}
            Formula::PredicateApplication { arguments, .. } => {
                for argument in arguments {
                    argument.relabel_variable(old, new);
                }
            }
            Formula::Negation(f) => f.relabel_variable(old, new),
            Formula::Conjunction(left, right)
            | Formula::Disjunction(left, right)
            | Formula::Implication(left, right)
            | Formula::Equivalence(left, right) => {
                left.relabel_variable(old, new);
                right.relabel_variable(old, new);
            }
            Formula::UniversalQuantification(variable, f)
            | Formula::ExistentialQuantification(variable, f) => {
                if variable.0 == old {
                    variable.0 = new.to_owned();
                }
                f.relabel_variable(old, new);
            }
        }
    }

    pub fn get_symbols(
        &self,
        context: impl AsRef<str>,
        variables_by_scope: &mut BTreeMap<String, BTreeMap<Variable, bool>>,
    ) -> ExpressionSymbols {
        let context = context.as_ref();

        let mut symbols = ExpressionSymbols::default();

        match self {
            Formula::Tautology | Formula::Contradiction => {}
            Formula::PredicateApplication {
                predicate,
                arguments,
                ..
            } => {
                symbols
                    .predicates
                    .insert(format!("{predicate}/{}", arguments.len()));
                for argument in arguments {
                    symbols.extend(argument.get_symbols(context, variables_by_scope));
                }
            }
            Formula::Negation(formula) => {
                symbols.extend(formula.get_symbols(format!("{context}.¬"), variables_by_scope));
            }
            Formula::Conjunction(left, right) => {
                symbols.extend(left.get_symbols(format!("{context}.∧.0"), variables_by_scope));
                symbols.extend(right.get_symbols(format!("{context}.∧.1"), variables_by_scope));
            }
            Formula::Disjunction(left, right) => {
                symbols.extend(left.get_symbols(format!("{context}.∨.0"), variables_by_scope));
                symbols.extend(right.get_symbols(format!("{context}.∨.1"), variables_by_scope));
            }
            Formula::Implication(left, right) => {
                symbols.extend(left.get_symbols(format!("{context}.⇒.0"), variables_by_scope));
                symbols.extend(right.get_symbols(format!("{context}.⇒.1"), variables_by_scope));
            }
            Formula::Equivalence(left, right) => {
                symbols.extend(left.get_symbols(format!("{context}.⇔.0"), variables_by_scope));
                symbols.extend(right.get_symbols(format!("{context}.⇔.1"), variables_by_scope));
            }

            Formula::UniversalQuantification(variable, formula) => {
                let context = format!("{context}.∀");
                variables_by_scope
                    .entry(context.clone())
                    .or_insert_with(BTreeMap::new)
                    .insert(variable.clone(), true);

                let variable_context = context.clone();

                let mut context = context;

                let mut i = context.chars().count() as i32 - 1;

                while i >= 0 {
                    if let Some(parent_context) = variables_by_scope.get(&context) {
                        let parent_context = parent_context.clone();

                        let variable_context_entry = variables_by_scope
                            .entry(variable_context.to_owned())
                            .or_insert_with(BTreeMap::new);

                        for (variable, value) in parent_context {
                            if value {
                                variable_context_entry.insert(variable.clone(), value);
                            } else {
                                let _ = variable_context_entry.try_insert(variable.clone(), value);
                            }
                        }
                    }

                    context.pop();
                    i -= 1;
                }

                symbols.extend(formula.get_symbols(variable_context, variables_by_scope));
            }

            Formula::ExistentialQuantification(variable, formula) => {
                let context = format!("{context}.∃");
                variables_by_scope
                    .entry(context.clone())
                    .or_insert_with(BTreeMap::new)
                    .insert(variable.clone(), true);

                let variable_context = context.clone();

                let mut context = context;

                let mut i = context.chars().count() as i32 - 1;

                while i >= 0 {
                    if let Some(parent_context) = variables_by_scope.get(&context) {
                        let parent_context = parent_context.clone();

                        let variable_context_entry = variables_by_scope
                            .entry(variable_context.to_owned())
                            .or_insert_with(BTreeMap::new);

                        for (variable, value) in parent_context {
                            if value {
                                variable_context_entry.insert(variable.clone(), value);
                            } else {
                                let _ = variable_context_entry.try_insert(variable.clone(), value);
                            }
                        }
                    }

                    context.pop();
                    i -= 1;
                }

                symbols.extend(formula.get_symbols(variable_context, variables_by_scope));
            }
        };

        symbols
    }

    pub fn get_free_root_variables(&self) -> BTreeSet<Variable> {
        let mut variables_by_scope = BTreeMap::new();
        self.get_symbols("", &mut variables_by_scope);

        variables_by_scope
            .get("")
            .map(|variables| variables.keys().cloned().collect())
            .unwrap_or_default()
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Tautology => write!(f, "⊤"),
            Formula::Contradiction => write!(f, "⊥"),
            Formula::PredicateApplication {
                predicate,
                arguments,
                ..
            } => {
                if arguments.is_empty() {
                    write!(f, "{}", predicate)
                } else {
                    write!(
                        f,
                        "{predicate}({})",
                        arguments.iter().map(|a| a.to_string()).join(", ")
                    )
                }
            }
            Formula::Negation(formula) => write!(f, "¬{}", formula),
            Formula::Conjunction(left, right) => write!(f, "({} ∧ {})", left, right),
            Formula::Disjunction(left, right) => write!(f, "({} ∨ {})", left, right),
            Formula::Implication(left, right) => write!(f, "({} ⇒ {})", left, right),
            Formula::Equivalence(left, right) => write!(f, "({} ⇔ {})", left, right),
            Formula::UniversalQuantification(variable, formula) => {
                write!(f, "∀{variable}({formula})")
            }
            Formula::ExistentialQuantification(variable, formula) => {
                write!(f, "∃{variable}({formula})")
            }
        }
    }
}

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Term(Term),
    Formula(Formula),
}

impl Expression {
    pub fn get_tree(&self) -> Tree<String> {
        match self {
            Expression::Term(term) => term.get_tree(),
            Expression::Formula(formula) => formula.get_tree(),
        }
    }

    pub fn to_relaxed_syntax(&self) -> String {
        match self {
            Expression::Term(term) => term.to_relaxed_syntax(None),
            Expression::Formula(formula) => formula.to_relaxed_syntax(None),
        }
    }

    pub fn apply_substitution(
        &mut self,
        substitution: &Substitution,
        explanation: &mut Explanation,
    ) {
        match self {
            Expression::Term(term) => term.apply_substitution(substitution, explanation),
            Expression::Formula(formula) => formula.apply_substitution(substitution, explanation),
        }
    }

    pub fn get_symbols(
        &self,
        variables_by_scope: &mut BTreeMap<String, BTreeMap<Variable, bool>>,
    ) -> ExpressionSymbols {
        match self {
            Expression::Term(term) => term.get_symbols("".to_owned(), variables_by_scope),
            Expression::Formula(formula) => formula.get_symbols("".to_owned(), variables_by_scope),
        }
    }
}

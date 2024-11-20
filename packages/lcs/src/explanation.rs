use std::fmt::Display;

use enum_as_inner::EnumAsInner;
use ordermap::{set::MutableValues, OrderSet};
use termtree::Tree;

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, EnumAsInner)]
enum ExplanationComponent {
    Step(String),
    Explanation(Explanation),
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Explanation {
    description: String,
    components: OrderSet<ExplanationComponent>,
}

impl Explanation {
    pub fn new(description: impl Into<String>) -> Self {
        Self {
            description: description.into(),
            components: OrderSet::new(),
        }
    }

    pub fn step(&mut self, step: impl Into<String>) {
        self.components
            .insert(ExplanationComponent::Step(step.into()));
    }

    pub fn subexplanation(&mut self, description: impl Into<String>) -> &mut Self {
        let explanation = Explanation::new(description);
        self.components
            .insert(ExplanationComponent::Explanation(explanation));

        self.components
            .get_index_mut2(self.components.len() - 1)
            .unwrap()
            .as_explanation_mut()
            .unwrap()
    }

    pub fn with_subexplanation<T>(
        &mut self,
        description: impl Into<String>,
        function: impl FnOnce(&mut Explanation) -> T,
    ) -> T {
        let explanation = self.subexplanation(description);
        function(explanation)
    }

    pub fn get_tree(&self) -> Tree<String> {
        let mut leaves = vec![];

        for component in &self.components {
            match component {
                ExplanationComponent::Step(step) => {
                    leaves.push(Tree::new(step.clone()));
                }
                ExplanationComponent::Explanation(explanation) => {
                    leaves.push(explanation.get_tree());
                }
            }
        }

        Tree::new(self.description.clone()).with_leaves(leaves)
    }
}

impl Display for Explanation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "<pre>")?;
        write!(f, "{}", self.get_tree())?;
        writeln!(f, "</pre>")
    }
}

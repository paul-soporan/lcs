use std::fmt::Display;
use std::mem;

use enum_as_inner::EnumAsInner;
use termtree::Tree;

pub trait Explain {
    fn step<S: Into<String>>(&mut self, step_fn: impl FnOnce() -> S);
    fn subexplanation<S: Into<String>>(&mut self, description_fn: impl FnOnce() -> S) -> &mut Self;
    fn merge_subexplanations(&mut self, function: impl Fn(&[String]) -> String);

    fn with_subexplanation<T, S: Into<String>>(
        &mut self,
        description_fn: impl FnOnce() -> S,
        function: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let explanation = self.subexplanation(description_fn);
        function(explanation)
    }
}

#[derive(Debug)]
pub struct DiscardedExplanation;

impl Explain for DiscardedExplanation {
    fn step<S: Into<String>>(&mut self, _: impl FnOnce() -> S) {}

    fn subexplanation<S: Into<String>>(&mut self, _: impl FnOnce() -> S) -> &mut Self {
        self
    }

    fn merge_subexplanations(&mut self, _: impl Fn(&[String]) -> String) {}
}

#[derive(Debug)]
pub struct DebugExplanation;

impl Explain for DebugExplanation {
    fn step<S: Into<String>>(&mut self, step_fn: impl FnOnce() -> S) {
        println!("Step: {}\n", step_fn().into());
    }

    fn subexplanation<S: Into<String>>(&mut self, description_fn: impl FnOnce() -> S) -> &mut Self {
        println!("Subexplanation: {}\n", description_fn().into());
        self
    }

    fn merge_subexplanations(&mut self, _: impl Fn(&[String]) -> String) {}
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, EnumAsInner)]
enum ExplanationComponent {
    Step(String),
    Explanation(Explanation),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Explanation {
    description: String,
    components: Vec<ExplanationComponent>,
}

impl Explain for Explanation {
    fn step<S: Into<String>>(&mut self, step_fn: impl FnOnce() -> S) {
        let step = ExplanationComponent::Step(step_fn().into());

        if self.components.last() != Some(&step) {
            self.components.push(step);
        }
    }

    fn subexplanation<S: Into<String>>(&mut self, description_fn: impl FnOnce() -> S) -> &mut Self {
        let explanation = Explanation::new(description_fn());
        self.components
            .push(ExplanationComponent::Explanation(explanation));

        self.components
            .last_mut()
            .unwrap()
            .as_explanation_mut()
            .unwrap()
    }

    fn merge_subexplanations(&mut self, function: impl Fn(&[String]) -> String) {
        let mut subexplanations = vec![];

        for component in mem::take(&mut self.components) {
            match component {
                ExplanationComponent::Step(step) => self.step(|| step),
                ExplanationComponent::Explanation(explanation) => {
                    subexplanations.push(
                        explanation
                            .components
                            .into_iter()
                            .map(|component| match component {
                                ExplanationComponent::Step(step) => step,
                                ExplanationComponent::Explanation(_) => unimplemented!(),
                            })
                            .collect::<Vec<_>>(),
                    );
                }
            }
        }

        for i in 0..subexplanations
            .iter()
            .map(|steps| steps.len())
            .max()
            .unwrap_or(0)
        {
            let merged = function(
                subexplanations
                    .iter()
                    .map(|steps| {
                        steps
                            .get(i)
                            .cloned()
                            .unwrap_or_else(|| steps.last().cloned().unwrap_or(String::new()))
                    })
                    .collect::<Vec<_>>()
                    .as_slice(),
            );

            self.step(|| merged);
        }
    }
}

impl Explanation {
    pub fn new(description: impl Into<String>) -> Self {
        Self {
            description: description.into(),
            components: Vec::new(),
        }
    }

    pub fn use_tree(&mut self, tree: Tree<String>) {
        let subexplanation = self.subexplanation(|| tree.root);
        for leaf in tree.leaves {
            subexplanation.use_tree(leaf);
        }
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
        write!(f, "\n<pre>")?;
        write!(f, "{}", self.get_tree())?;
        writeln!(f, "</pre>")
    }
}

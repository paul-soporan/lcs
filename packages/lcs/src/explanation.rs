use std::fmt::Display;
use std::mem;

use enum_as_inner::EnumAsInner;
use termtree::Tree;

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

impl Explanation {
    pub fn new(description: impl Into<String>) -> Self {
        Self {
            description: description.into(),
            components: Vec::new(),
        }
    }

    pub fn step(&mut self, step: impl Into<String>) {
        let step = ExplanationComponent::Step(step.into());

        if self.components.last() != Some(&step) {
            self.components.push(step);
        }
    }

    pub fn subexplanation(&mut self, description: impl Into<String>) -> &mut Self {
        let explanation = Explanation::new(description);
        self.components
            .push(ExplanationComponent::Explanation(explanation));

        self.components
            .last_mut()
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

    pub fn merge_subexplanations(&mut self, function: impl Fn(&[String]) -> String) {
        let mut subexplanations = vec![];

        for component in mem::take(&mut self.components) {
            match component {
                ExplanationComponent::Step(step) => self.step(step),
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

            self.step(merged);
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

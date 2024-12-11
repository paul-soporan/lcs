use as_variant::as_variant;
use indexmap::IndexSet;
use unlatex::ast::Node;

pub fn get_interpolation_for_latex(input: &str) -> String {
    let root = unlatex::parse(input).unwrap();
    let nodes = match root {
        Node::Root { content, .. } => content,
        _ => unreachable!(),
    };

    get_interpolation_for_nodes(&nodes)
}

fn get_interpolation_for_nodes(nodes: &[Node]) -> String {
    let mut interpolation = String::new();

    let mut index = 0;

    while index < nodes.len() {
        if index + 1 < nodes.len() {
            let exponent_node = as_variant!(&nodes[index + 1], Node::Macro { content, args, .. } if content == "^" => &args[0]);
            if let Some(exponent_node) = exponent_node {
                let base_interpolation = get_interpolation_for_nodes(&[nodes[index].clone()]);
                let exponent_interpolation = get_interpolation_for_nodes(&[exponent_node.clone()]);

                interpolation += "(";
                interpolation += &base_interpolation;
                interpolation += ")";
                interpolation += "^";
                interpolation += "(";
                interpolation += &exponent_interpolation;
                interpolation += ")";

                index += 2;
                continue;
            }
        }

        match &nodes[index] {
            Node::WhiteSpace { .. } => {
                interpolation += " ";
                index += 1;
            }
            Node::String { content, .. } => {
                interpolation += &content.replace("_", "");
                index += 1;
            }
            Node::Group { content, .. }
            | Node::Argument { content, .. }
            | Node::Environment { content, .. } => {
                interpolation += &get_interpolation_for_nodes(content);
                index += 1;
            }
            Node::Macro { content, args, .. } => match content.as_str() {
                // Ignore formatting macros
                "quad" | "\\" => {
                    index += 1;
                }

                "left" | "right" => {
                    if matches!(&nodes[index + 1], Node::String { content, .. } if content == ".") {
                        index += 1;
                    }

                    index += 1;
                }

                "delta" => {
                    interpolation += "δ";
                    index += 1;
                }

                "varepsilon" => {
                    interpolation += "ε";
                    index += 1;
                }

                "leqslant" | "leq" => {
                    interpolation += "⩽";
                    index += 1;
                }

                "geqslant" | "geq" => {
                    interpolation += "⩾";
                    index += 1;
                }

                "neg" => {
                    interpolation += "¬";
                    index += 1;
                }

                "wedge" => {
                    interpolation += "∧";
                    index += 1;
                }

                "vee" => {
                    interpolation += "∨";
                    index += 1;
                }

                "Rightarrow" => {
                    interpolation += "⇒";
                    index += 1;
                }

                "Leftrightarrow" => {
                    interpolation += "⇔";
                    index += 1;
                }

                "forall" => {
                    interpolation += "∀";
                    index += 1;
                }

                "exists" => {
                    interpolation += "∃";
                    index += 1;
                }

                "in" => {
                    interpolation += "∈";
                    index += 1;
                }

                "mathbb" => {
                    let argument = get_interpolation_for_nodes(&[args[0].clone()]);

                    match argument.as_str() {
                        "N" => interpolation += "ℕ",
                        "Z" => interpolation += "ℤ",
                        "Q" => interpolation += "ℚ",
                        "R" => interpolation += "ℝ",
                        _ => unimplemented!("Unsupported mathbb argument: '{}'", argument),
                    }

                    index += 1;
                }

                "frac" => {
                    let numerator_interpolation = get_interpolation_for_nodes(&[args[0].clone()]);
                    let denominator_interpolation = get_interpolation_for_nodes(&[args[1].clone()]);

                    interpolation += "(";
                    interpolation += &numerator_interpolation;
                    interpolation += ")";
                    interpolation += "/";
                    interpolation += "(";
                    interpolation += &denominator_interpolation;
                    interpolation += ")";

                    index += 1;
                }

                "sqrt" => {
                    interpolation += "√(";
                    interpolation += &get_interpolation_for_nodes(args);
                    interpolation += ")";

                    index += 1;
                }

                "underset" => {
                    let bottom_nodes =
                        as_variant!(&nodes[index + 1], Node::Group { content, .. } => content)
                            .unwrap();

                    let bottom_interpolation = get_interpolation_for_nodes(bottom_nodes);
                    let variables = extract_variables(&bottom_interpolation);

                    let top_nodes =
                        as_variant!(&nodes[index + 2], Node::Group { content, .. } => content)
                            .unwrap();

                    match top_nodes.as_slice() {
                        [Node::Macro { content, .. }] => match content.as_str() {
                            "forall" => {
                                for variable in variables {
                                    interpolation += "∀";
                                    interpolation += &variable;
                                }

                                interpolation += &bottom_interpolation;
                                interpolation += "⇒";
                            }
                            "exists" => {
                                for variable in variables {
                                    interpolation += "∃";
                                    interpolation += &variable;
                                }

                                interpolation += "(";
                                interpolation += &bottom_interpolation;
                                interpolation += ")∧";
                            }
                            _ => unimplemented!("Unsupported underset top command"),
                        },
                        [Node::Macro {
                            content: quantifier,
                            ..
                        }, Node::String {
                            content: modifier, ..
                        }] if quantifier == "exists" && modifier == "!" => {
                            if variables.len() != 1 {
                                unimplemented!(
                                    "Unsupported uniqueness quantifier with multiple variables"
                                );
                            }

                            let variable = variables.first().unwrap();

                            interpolation += "∃!";
                            interpolation += variable;

                            interpolation += "(";
                            interpolation += &bottom_interpolation;
                            interpolation += ")∧";
                        }
                        _ => unimplemented!("Unsupported underset top node"),
                    }

                    index += 3;
                }

                macro_ => unimplemented!("Unsupported macro: {:#?}", macro_),
            },
            node => unimplemented!("Unsupported node: {:#?}", node),
        }
    }

    interpolation
}

fn extract_variables(expression: &str) -> IndexSet<String> {
    let mut variables = IndexSet::new();

    let mut chars = expression.chars().peekable();

    while let Some(c) = chars.peek() {
        if ('a'..='z').contains(&c) || ('α'..='ω').contains(&c) || ('Α'..='Ω').contains(&c) {
            let mut variable = c.to_string();

            while let Some(&c) = chars.peek() {
                if ('0'..='9').contains(&c) {
                    variable.push(c);
                    chars.next();
                } else {
                    break;
                }
            }

            variables.insert(variable);
        }

        chars.next();
    }

    variables
}

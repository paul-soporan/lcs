use indexmap::{indexmap, IndexMap, IndexSet};
use lcs::{
    explanation::{Explain, Explanation},
    predicate_logic::{
        parser::{parse_formula, Signature},
        prove::{ProofResult, ProofSituation},
        types::{Associativity, FunctionSymbol, PredicateSymbol},
    },
};
use serde::{Deserialize, Serialize};
use tsify::Tsify;
use wasm_bindgen::prelude::*;

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

#[derive(Serialize, Deserialize, Tsify)]
#[tsify(into_wasm_abi)]
pub struct ExplainedResult<T> {
    pub result: Result<T, String>,
    pub explanation: String,
}

#[derive(Serialize, Deserialize, Tsify)]
pub struct DetailedProof {
    pub result: String,
    pub description: String,
}

#[derive(Serialize, Deserialize, Tsify)]
#[tsify(from_wasm_abi)]
pub struct SimpleSignature {
    pub functions: Vec<(String, usize)>,
    pub predicates: Vec<(String, usize)>,
    pub constants: Vec<String>,
}

#[wasm_bindgen]
pub fn prove(
    knowledge_base: Vec<String>,
    goal: String,
    simple_signature: SimpleSignature,
) -> ExplainedResult<DetailedProof> {
    let mut signature = get_common_math_signature();

    for (name, arity) in simple_signature.functions {
        signature.functions.insert(
            name,
            if arity == 2 {
                FunctionSymbol::new().infix(Associativity::Left, 0)
            } else {
                FunctionSymbol::new().prefix_arity(arity)
            },
        );
    }

    for (name, arity) in simple_signature.predicates {
        signature.predicates.insert(
            name,
            if arity == 2 {
                PredicateSymbol::Infix
            } else {
                PredicateSymbol::Prefix(vec![arity])
            },
        );
    }

    signature.static_constants = simple_signature.constants.into_iter().collect();

    let mut explanation = Explanation::default();

    let knowledge_base =
        match explanation.with_subexplanation("Parsing knowledge base", |explanation| {
            knowledge_base
                .into_iter()
                .enumerate()
                .map(|(i, formula)| {
                    parse_formula(
                        &formula,
                        &signature,
                        explanation.subexplanation(format!("Formula #{i}")),
                    )
                })
                .collect::<Result<IndexSet<_>, _>>()
        }) {
            Ok(knowledge_base) => knowledge_base,
            Err(_) => {
                return ExplainedResult {
                    result: Err("Failed to parse knowledge base.".to_owned()),
                    explanation: explanation.to_string(),
                }
            }
        };

    let goal = match parse_formula(
        &goal,
        &signature,
        explanation.subexplanation("Parsing goal"),
    ) {
        Ok(goal) => goal,
        Err(_) => {
            return ExplainedResult {
                result: Err("Failed to parse goal.".to_owned()),
                explanation: explanation.to_string(),
            }
        }
    };

    let proof_situation = ProofSituation {
        knowledge_base,
        goal,
    };

    let proof = proof_situation.build_proof();

    let detailed_proof = explanation.with_subexplanation("Building proof tree", |explanation| {
        proof.explain(explanation.subexplanation("Original proof tree"));

        let trimmed_proof = proof.trim();

        trimmed_proof.explain(explanation.subexplanation("Trimmed proof tree"));

        let description = trimmed_proof.describe(&IndexMap::default());

        DetailedProof {
            result: match trimmed_proof.result {
                ProofResult::Proven => "proven".to_owned(),
                ProofResult::Contradiction => "contradiction".to_owned(),
                ProofResult::Unknown => "unknown".to_owned(),
            },
            description,
        }
    });

    ExplainedResult {
        result: Ok(detailed_proof),
        explanation: explanation.to_string(),
    }
}

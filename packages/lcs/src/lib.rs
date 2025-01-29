#![feature(box_patterns)]
#![feature(closure_lifetime_binder)]
#![feature(let_chains)]
#![feature(map_try_insert)]
#![feature(anonymous_lifetime_in_impl_trait)]

pub mod ast;
pub mod bcf;
pub mod circuit;
pub mod evaluate;
pub mod explanation;
pub mod markdown;
pub mod normal_forms;
pub mod parser;
pub mod predicate_logic;
pub mod reduce;
pub mod resolver;
pub mod simplify;

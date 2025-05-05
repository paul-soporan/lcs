use std::{fs, time::Instant};

use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::DimacsCnf,
        solvers::{
            dpll::DpllSolver,
            solve::{Solve, SolverResult},
        },
    },
};

pub fn run() {
    let data = fs::read_to_string("test.cnf").unwrap();
    let dimacs_cnf = data.parse::<DimacsCnf>().unwrap();

    let instant = Instant::now();

    let result = DpllSolver::check_cnf_satisfiability(dimacs_cnf.cnf, &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DPLL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Elapsed time: {:?}", elapsed);
}

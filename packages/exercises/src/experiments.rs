use std::{fs, time::Instant};

use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            dpll::{DpllBranchingHeuristic, DpllSolver},
            solve::{Solve, SolverResult},
        },
    },
};

pub fn run() {
    let data = fs::read_to_string("test.cnf").unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let instant = Instant::now();

    let solver = DpllSolver::new(DpllBranchingHeuristic::First);
    let result = solver.check_clause_set_satisfiability(clause_set, &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DPLL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Split count: {}", result.split_count());
    println!("Elapsed time: {:?}", elapsed);
}

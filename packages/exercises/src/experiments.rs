use std::{fs, time::Instant};

use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            cdcl::CdclSolver,
            dpll::{BranchingHeuristic, DpllSolver},
            solve::{Solve, SolverResult},
        },
    },
};

pub fn run() {
    let branching_heuristic = BranchingHeuristic::First;

    let data = fs::read_to_string("test.cnf").unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let instant = Instant::now();

    let solver = DpllSolver::new(branching_heuristic);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DPLL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Split count: {}", result.split_count());
    println!("Elapsed time: {:?}", elapsed);

    println!("-------------------------------------");

    let instant = Instant::now();

    let solver = CdclSolver::new(branching_heuristic);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "CDCL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Split count: {}", result.split_count());
    println!("Elapsed time: {:?}", elapsed);
}

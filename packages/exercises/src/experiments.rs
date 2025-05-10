use std::{fs, time::Instant};

use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            cdcl::{CdclBranchingHeuristic, CdclSolver},
            dpll::{DpllBranchingHeuristic, DpllSolver},
            solve::{Solve, SolverResult},
        },
    },
};

pub fn run() {
    let dpll_branching_heuristic = DpllBranchingHeuristic::First;

    let data = fs::read_to_string("test.cnf").unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let instant = Instant::now();

    let solver = DpllSolver::new(dpll_branching_heuristic);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DPLL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Decision count: {}", result.decision_count());
    println!("Elapsed time: {:?}", elapsed);

    println!("-------------------------------------");

    let instant = Instant::now();

    let cdcl_branching_heuristic = CdclBranchingHeuristic::First;

    let solver = CdclSolver::new(cdcl_branching_heuristic);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "CDCL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Decision count: {}", result.decision_count());
    println!("Conflict count: {}", result.conflict_count());
    println!("Propagation count: {}", result.propagation_count());
    println!("Elapsed time: {:?}", elapsed);
}

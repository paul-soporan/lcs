use std::{fs, time::Instant};

use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            cdcl::{CdclBranchingHeuristic, CdclRestartStrategy, CdclSolver},
            dp::DpSolver,
            dpll::{DpllBranchingHeuristic, DpllSolver},
            resolution::ResolutionSolver,
            solve::{Solve, SolverResult},
        },
    },
};

pub fn run() {
    let data = fs::read_to_string("test.cnf").unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let instant = Instant::now();

    let solver = ResolutionSolver::new();
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "Resolution result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Elapsed time: {:?}", elapsed);

    println!("-------------------------------------");

    let instant = Instant::now();

    let solver = DpSolver::new();
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DP result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    println!("Elapsed time: {:?}", elapsed);

    println!("-------------------------------------");

    let dpll_branching_heuristic = DpllBranchingHeuristic::First;

    let instant = Instant::now();

    let solver = DpllSolver::new(dpll_branching_heuristic);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "DPLL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    let stats = result.stats();
    println!("Decision count: {}", stats.decision_count);
    println!("Elapsed time: {:?}", elapsed);

    println!("-------------------------------------");

    let cdcl_branching_heuristic = CdclBranchingHeuristic::MiniSatVsids;

    let instant = Instant::now();

    let solver = CdclSolver::new(cdcl_branching_heuristic, CdclRestartStrategy::Luby);
    let result =
        solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

    let elapsed = instant.elapsed();

    println!(
        "CDCL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    let stats = result.stats();
    println!("Decision count: {}", stats.decision_count);
    println!("Conflict count: {}", stats.conflict_count);
    println!("Propagation count: {}", stats.propagation_count);
    println!("Restart count: {}", stats.restart_count);
    println!("Elapsed time: {:?}", elapsed);
}

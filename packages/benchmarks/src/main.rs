use std::{
    fs, process, thread,
    time::{Duration, Instant},
};

use fork::{fork, waitpid, Fork};
use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            dpll::{BranchingHeuristic, DpllSolver},
            solve::{Solve, SolverResult},
        },
    },
};

const TIMEOUT: u64 = 5;

fn bench() {
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
}

fn bench_process() {
    match fork() {
        Ok(Fork::Parent(pid)) => match waitpid(pid) {
            Ok(_) => println!("Child exited"),
            Err(_) => eprintln!("Failed to wait on child"),
        },
        Ok(Fork::Child) => {
            thread::spawn(move || {
                thread::sleep(Duration::from_secs(TIMEOUT));
                println!("Child process timed out");
                process::exit(0);
            });

            bench();
        }
        Err(_) => println!("Fork failed"),
    };
}

fn main() {
    bench_process();
}

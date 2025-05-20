# lcs

`lcs` is a full-featured logic library written in Rust, that includes various features for both propositional and first-order logic.

### Propositional logic

- parsing and pretty-printing
- evaluation
- normal form conversion
- different SAT solving algorithms (DPLL, CDCL, DP, resolution) with various heuristics
- simplifications
- circuit design

### Predicate logic

- parsing and pretty-printing
- evaluation
- substitution
- proof engine

## Examples

### SAT Solving

```rust
use lcs::{
    explanation::DiscardedExplanation,
    propositional_logic::{
        dimacs::ClauseSet,
        solvers::{
            cdcl::{CdclBranchingHeuristic, CdclRestartStrategy, CdclSolver},
            solve::{Solve, SolverResult},
        },
    },
};

fn main() {
    // DIMACS Input
    let data = std::fs::read_to_string("test.cnf").unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let solver = CdclSolver::new(CdclBranchingHeuristic::MiniSatVsids, CdclRestartStrategy::Luby);
    let result = solver.check_clause_set_satisfiability(clause_set, &mut DiscardedExplanation);

    println!(
        "CDCL result: {}",
        if result.value() { "SAT" } else { "UNSAT" }
    );
    let stats = result.stats();
    println!("Decision count: {}", stats.decision_count);
    println!("Conflict count: {}", stats.conflict_count);
    println!("Propagation count: {}", stats.propagation_count);
    println!("Restart count: {}", stats.restart_count);
}
```

## Benchmarks

The SAT solver benchmarks are documented in [./packages/benchmarks/README.md](./packages/benchmarks/README.md).

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

## Benchmarks

The SAT solver benchmarks are documented in [./packages/benchmarks/README.md](./packages/benchmarks/README.md).

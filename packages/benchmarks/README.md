# Benchmarks

## Overview

This folder contains benchmarks for SAT solving algorithms.

## Prerequisites

### Unix-based operating system

The benchmarking code uses Unix-specific features (`fork`) and can only be run on Unix-based operating systems (e.g. Linux, macOS).
If you are using Windows, you can use the [Windows Subsystem for Linux (WSL)](https://learn.microsoft.com/en-us/windows/wsl/install) to run the benchmarks.

### Rust

The benchmarks, just like the rest of the library, are written in Rust. To run them, you need to have Rust installed on your system. You can install Rust by following [these instructions](https://www.rust-lang.org/tools/install).

### Rust Nightly

The library uses features that are only available in the nightly (experimental) version of Rust. To install the nightly version, run the following command:

```sh
rustup install nightly
rustup default nightly
```

## Compiling the benchmarks

- Run `RUSTFLAGS="-C target-cpu=native" cargo build --release` to build the benchmarks in release mode, with all optimizations enabled.

## Executing the benchmarks in the paper

- Decide on the level of parallelism you want to use. The benchmarks are designed to run in parallel, and the number of threads can be controlled using the `RAYON_NUM_THREADS` environment variable. For example, on my 16-core, 32-thread machine, I ran the benchmarks with `RAYON_NUM_THREADS=64` as it was the optimal level of parallelism that did not cause context-switching overhead.
- Run `RAYON_NUM_THREADS=n ./target/release/benchmarks --paper-benchmarks` to execute the benchmarks used in the paper. Replace `n` with the level of parallelism you decided on.
- **Important:** Running the benchmarks will take at least 4 hours, depending on your machine, so you should let them run in the background. If you use most of your CPU threads, your PC will likely be unusable for other tasks while running the benchmarks.

## Executing specific benchmarks

To execute specific benchmarks, you can use the `RAYON_NUM_THREADS=n ./target/release/benchmarks path` command, which will execute all inputs with paths containing `path`.

## Results

The generated results will be saved in the `./output.json` file, with benchmarks from all categories aggregated together.

For comparison, my own results can be found in the `./results` folder, split by category into different files.

### Format

The results are saved in JSON format. In the JSON file, benchmarks are grouped by category (e.g. `uniform`, `flat`, `simple`), with an optional `sat` / `unsat` subcategory. Each benchmark has the filename of the input file as key, and results for each algorithm (e.g. `cdcl`, `dpll`, `dp`, `resolution`) as values. For `dpll` and `cdcl`, the results are further split by heuristic (e.g. `first`, `random`, `moms`).

Each algorithm benchmark can either:

- not appear in the results if its execution was not requested
- be `null` - benchmark execution timed out
- be an object with the following fields:
  - `max_memory_usage` - maximum memory usage in bytes
  - `mean_time` - mean time in seconds
  - `stats` - additional algorithm-specific statistics (e.g. `decision_count`, `conflict_count`), if available

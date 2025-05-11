use std::env;
use std::io::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process, thread,
    time::{Duration, Instant},
};

use average::{Estimate, Mean};
use fork::{fork, waitpid, Fork};
use lcs::propositional_logic::solvers::cdcl::{
    CdclBranchingHeuristic, CdclRestartStrategy, CdclSolver,
};
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
use memory_stats::memory_stats;
use os_pipe::pipe;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use serde_json::{json, Map};
use strum::IntoEnumIterator;
use tokio::fs;
use walkdir::{DirEntry, WalkDir};

const TIMEOUT_SECONDS: u64 = 30;
const RUN_COUNT: usize = 5;

#[derive(Clone)]
pub struct CancellationToken {
    cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    #[inline]
    pub fn should_cancel(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
}

#[derive(Clone)]
pub struct Canceller {
    cancelled: Arc<AtomicBool>,
}

impl Canceller {
    #[inline]
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }
}

#[inline]
pub fn cancellation_token() -> (Canceller, CancellationToken) {
    let cancelled = Arc::new(AtomicBool::new(false));
    (
        Canceller {
            cancelled: Arc::clone(&cancelled),
        },
        CancellationToken { cancelled },
    )
}

struct BenchConfig<'a, T: Solve> {
    path: PathBuf,
    expected_result: Option<bool>,
    get_solver: &'a dyn Fn() -> T,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
struct BenchResult<T> {
    mean_time: f64,
    max_memory_usage: usize,
    stats: T,
}

fn bench<T: Solve>(config: &BenchConfig<T>) -> BenchResult<<T::Result as SolverResult>::Stats> {
    let data = std::fs::read_to_string(&config.path).unwrap();
    let clause_set = data.parse::<ClauseSet>().unwrap();

    let solver = (config.get_solver)();

    let mut estimator = Mean::new();

    let (canceller, cancellation_token) = cancellation_token();

    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut max_memory_usage = 0;

        loop {
            let usage = memory_stats().expect("Failed to get memory stats");

            max_memory_usage = max_memory_usage.max(usage.physical_mem);

            thread::sleep(Duration::from_millis(30));

            if cancellation_token.should_cancel() {
                tx.send(max_memory_usage).unwrap();
                break;
            }
        }
    });

    let mut stats = None;

    for _ in 0..RUN_COUNT {
        let instant = Instant::now();

        let result =
            solver.check_clause_set_satisfiability(clause_set.clone(), &mut DiscardedExplanation);

        let elapsed = instant.elapsed();

        estimator.add(elapsed.as_secs_f64());

        if let Some(expected_result) = config.expected_result {
            assert_eq!(result.value(), expected_result);
        }

        stats = Some(result.stats());
    }

    canceller.cancel();
    let max_memory_usage = rx.recv().unwrap();

    BenchResult {
        mean_time: estimator.mean(),
        max_memory_usage,
        stats: stats.unwrap(),
    }
}

fn bench_process<T: Solve>(
    config: &BenchConfig<T>,
) -> Option<BenchResult<<T::Result as SolverResult>::Stats>> {
    let (mut reader, writer) = pipe().expect("Failed to create pipe");

    match fork() {
        Ok(Fork::Parent(pid)) => match waitpid(pid) {
            Ok(_) => {
                drop(writer);

                let mut result_str = String::new();
                reader
                    .read_to_string(&mut result_str)
                    .expect("Failed to read from pipe");

                return serde_json::from_str(&result_str).ok();
            }
            Err(_) => eprintln!("Failed to wait on child"),
        },
        Ok(Fork::Child) => {
            thread::spawn(move || {
                thread::sleep(Duration::from_secs(TIMEOUT_SECONDS));
                process::exit(0);
            });

            let result = bench(config);
            let json_result = serde_json::to_string(&result).unwrap();

            let mut writer = writer;
            writeln!(writer, "{}", json_result).expect("Failed to write to pipe");

            process::exit(0);
        }
        Err(_) => eprintln!("Fork failed"),
    };

    None
}

fn bench_file(file: &DirEntry, expected_result: Option<bool>) -> (&Path, serde_json::Value) {
    let dpll_results = Map::from_iter(DpllBranchingHeuristic::iter().map(|heuristic| {
        let config = BenchConfig {
            path: file.path().to_path_buf(),
            expected_result,
            get_solver: &|| DpllSolver::new(heuristic),
        };

        (
            heuristic.to_string(),
            serde_json::to_value(bench_process(&config)).unwrap(),
        )
    }));

    let cdcl_results = Map::from_iter(CdclBranchingHeuristic::iter().map(|heuristic| {
        let config = BenchConfig {
            path: file.path().to_path_buf(),
            expected_result,
            get_solver: &|| CdclSolver::new(heuristic, CdclRestartStrategy::None),
        };

        (
            heuristic.to_string(),
            serde_json::to_value(bench_process(&config)).unwrap(),
        )
    }));

    (
        file.path(),
        json!({
            "dpll": dpll_results,
            "cdcl": cdcl_results,
        }),
    )
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let current_dir = env::current_dir()?;

    let path_matcher = env::args().nth(1).unwrap_or_else(|| String::new());

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let inputs_dir = manifest_dir.join("inputs");

    let mut files = Vec::new();

    for entry in WalkDir::new(&inputs_dir) {
        let file = entry?;
        if file.file_type().is_dir() {
            continue;
        }

        let path = file.path();

        if !path.to_string_lossy().contains(&path_matcher) {
            continue;
        }

        if path.extension() != Some(OsStr::new("cnf")) {
            continue;
        }

        let path_str = path.to_string_lossy();

        let expected_result = if path_str.contains("unsat") {
            Some(false)
        } else if path_str.contains("sat") {
            Some(true)
        } else {
            None
        };

        files.push((file, expected_result));
    }

    let results = files
        .par_iter()
        .map(|(file, expected_result)| {
            println!(
                "Processing file: {}",
                file.path().strip_prefix(&current_dir).unwrap().display()
            );

            bench_file(file, expected_result.clone())
        })
        .collect::<Vec<_>>();

    let mut output = Map::new();

    for (path, result) in results {
        let components = path
            .parent()
            .unwrap()
            .strip_prefix(&inputs_dir)
            .unwrap()
            .components();

        let mut submap = &mut output;
        for component in components {
            let component = component.as_os_str().to_string_lossy();
            submap = submap
                .entry(component.to_string())
                .or_insert_with(|| json!({}))
                .as_object_mut()
                .unwrap();
        }

        submap.insert(
            path.file_name().unwrap().to_string_lossy().to_string(),
            json!(result),
        );
    }

    let output_path = manifest_dir.join("output.json");

    fs::write(&output_path, serde_json::to_string_pretty(&output)?).await?;

    println!(
        "Benchmark output written to {}",
        output_path.strip_prefix(current_dir)?.display()
    );

    Ok(())
}

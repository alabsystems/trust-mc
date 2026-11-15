// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![feature(exit_status_error)]
// Pre-existing patterns from upstream Kani tool crate
#![allow(
    clippy::unwrap_used,
    clippy::unnecessary_debug_formatting,
    clippy::unchecked_time_subtraction
)]

use crate::common::{AggrResult, Stats, aggregate_aggregates, krate_trimmed_path};
use clap::Parser;
use serde::Serialize;
use std::ffi::OsString;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;
mod common;

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
struct TimerArgs {
    /// Sets a custom config file
    #[arg(short, long, value_name = "FILE")]
    out_path: PathBuf,

    /// Ignore compiling the current directory
    #[arg(short, long)]
    skip_current: bool,

    /// The paths of additional paths to visit beyond the current subtree
    #[arg(short, long, value_name = "DIR")]
    also_visit: Vec<PathBuf>,

    /// The names or paths of files to ignore
    #[arg(short, long)]
    ignore: Vec<PathBuf>,
}

/// The number of untimed runs to do before starting timed runs.
/// We need at least one warm-up run to make sure crates are fetched & cached in
/// the local `.cargo/registry` folder. Otherwise the first run will be significantly slower.
const WARMUP_RUNS: usize = 1;
const TIMED_RUNS: usize = 10;

fn main() {
    let args = TimerArgs::parse();

    let (mut to_visit, mut res) = (vec![], vec![]);
    to_visit.extend(args.also_visit.into_iter().rev());
    if !args.skip_current {
        let current_directory = std::env::current_dir().expect("should be run in a directory");
        to_visit.push(current_directory);
    }

    let mut out_ser = serde_json::Serializer::pretty(File::create(&args.out_path).unwrap());
    let run_start = std::time::Instant::now();

    // recursively visit subdirectories to time the compiler on all rust projects
    while let Some(next) = to_visit.pop() {
        let next = next.canonicalize().unwrap();
        let path_to_toml = next.join("Cargo.toml");

        if path_to_toml.exists() && path_to_toml.is_file() {
            // in rust crate so we want to profile it
            println!("[!] profiling in {}", krate_trimmed_path(&next));
            let new_res = profile_on_crate(&next);
            new_res.serialize(&mut out_ser).unwrap();
            res.push(new_res);
        } else {
            // we want want to recur and visit all directories that aren't explicitly ignored
            to_visit.extend(std::fs::read_dir(next).unwrap().filter_map(|entry| {
                if let Ok(entry) = entry {
                    let path = entry.path();
                    if path.is_dir() && !args.ignore.iter().any(|ignored| path.ends_with(ignored)) {
                        return Some(path);
                    }
                }
                None
            }));
        }
    }

    println!("[!] total info is {:?}", aggregate_aggregates(&res));

    print!("\t [*] run took {:?}", run_start.elapsed());
}

/// Profile a crate by running a certain number of untimed warmup runs and then
/// a certain number of timed runs, returning aggregates of the timing results.
fn profile_on_crate(absolute_path: &std::path::PathBuf) -> AggrResult {
    let _warmup_results = (1..=WARMUP_RUNS)
        .map(|run| {
            print!("\t[*] running warmup {run}/{WARMUP_RUNS}");
            let _ = std::io::stdout().flush();
            let res = run_command_in(absolute_path);
            println!(" -- {res:?}");
            res
        })
        .collect::<Vec<_>>();

    let timed_results = (1..=TIMED_RUNS)
        .map(|run| {
            print!("\t[*] running timed run {run}/{TIMED_RUNS}");
            let _ = std::io::stdout().flush();
            let res = run_command_in(absolute_path);
            println!(" -- {res:?}");
            res
        })
        .collect::<Vec<_>>();

    let aggr = aggregate_results(absolute_path, &timed_results);
    println!("\t[!] results for {absolute_path:?} are in! {aggr:?}");

    aggr
}

type RunResult = Duration;

/// The Trust build tool: `$CARGO` when this runs under `targo`, else `targo`.
/// Never a bare `cargo`, which on an ALab host is not the Trust toolchain.
fn targo() -> OsString {
    std::env::var_os("CARGO").filter(|cargo| !cargo.is_empty()).unwrap_or_else(|| "targo".into())
}

/// Build the profiling command: `TIME_COMPILER=true targo trust-mc --only-codegen`
/// rooted at `absolute_path` (the `targo-trust-mc` front door, installed with
/// `targo --unverified install --path .`).
fn build_profile_command(absolute_path: &Path) -> Command {
    let mut cmd = Command::new(targo());
    cmd.current_dir(absolute_path)
        .arg("trust-mc")
        .arg("--only-codegen")
        .env("TIME_COMPILER", "true");
    cmd
}

/// Run `targo trust-mc` in a crate and parse out the compiler timing info outputted
/// by the `TIME_COMPILER` environment variable.
fn run_command_in(absolute_path: &Path) -> RunResult {
    // `targo clean` first to ensure the compiler is fully run again
    let _ = Command::new(targo())
        .current_dir(absolute_path)
        .arg("clean")
        .stdout(Stdio::null())
        .output()
        .expect("targo clean should succeed");

    // do the actual compiler run (using `--only-codegen` to save time)
    let trust_mc_output =
        build_profile_command(absolute_path).output().expect("targo trust-mc should succeed");

    // parse the output bytes into a string
    let out_str =
        String::from_utf8(trust_mc_output.stdout).expect("utf8 conversion should succeed");

    if !trust_mc_output.status.success() {
        println!(
            "the `TIME_COMPILER=true targo trust-mc --only-codegen` command failed in {absolute_path:?} with output -- {out_str:?}"
        );
        panic!("targo trust-mc command failed");
    }

    // parse that string for the compiler build information
    // and if it's built multiple times (which could happen in a workspace with multiple crates),
    // we just sum up the total time
    out_str.split("\n").filter(|line| line.starts_with("BUILT")).map(extract_duration).sum()
}

fn extract_duration(s: &str) -> Duration {
    // The digits after the first `IN` (the whole line when it has none).
    let s = s.split_once("IN").map_or(s, |(_, after)| after);
    let micros = s.chars().filter(|c| c.is_ascii_digit()).collect::<String>().parse().ok().unwrap();

    Duration::from_micros(micros)
}

fn aggregate_results(path: &Path, results: &[Duration]) -> AggrResult {
    assert!(results.len() == TIMED_RUNS);

    // sort and calculate the subset of times in the interquartile range
    let mut sorted = results.to_vec();
    sorted.sort();
    let iqr_bounds = (results.len() / 4, results.len() * 3 / 4);
    let iqr_durations = sorted
        .into_iter()
        .enumerate()
        .filter_map(|(i, v)| if i >= iqr_bounds.0 && i <= iqr_bounds.1 { Some(v) } else { None })
        .collect::<Vec<Duration>>();

    // TIMED_RUNS (10) runs keep six in the interquartile range, and compile
    // times are far below the overflow bound, so both summaries exist.
    let stats = |runs: &[Duration]| {
        result_stats(runs).expect("TIMED_RUNS compile timings always have statistics")
    };
    AggrResult::new(path.to_path_buf(), stats(&iqr_durations), stats(results))
}

/// Record the stats from a subset slice of timing runs: `None` when there are
/// no runs or a sum overflows, instead of dividing by zero or overflowing.
fn result_stats(results: &[Duration]) -> Option<Stats> {
    let range = (*results.iter().min()?, *results.iter().max()?);
    let runs = u32::try_from(results.len()).ok()?;
    let avg = results
        .iter()
        .try_fold(Duration::ZERO, |sum, run| sum.checked_add(*run))?
        .checked_div(runs)?;

    let deviations = results.iter().try_fold(0_u128, |sum, run| {
        sum.checked_add(run.abs_diff(avg).as_micros().checked_pow(2)?)
    })?;
    let variance = deviations.checked_div(u128::from(runs))?;
    let std_dev = Duration::from_micros(u64::try_from(variance.isqrt()).ok()?);

    Some(Stats { avg, std_dev, range })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsStr;

    #[test]
    fn test_build_profile_command_args_and_env() {
        let dir = Path::new("/tmp/test_crate");
        let cmd = build_profile_command(dir);

        // The Trust build tool: `$CARGO` under targo, else `targo`; never `cargo`.
        assert_eq!(cmd.get_program(), targo());
        assert_eq!(Path::new(cmd.get_program()).file_stem(), Some(OsStr::new("targo")));
        let args: Vec<&OsStr> = cmd.get_args().collect();
        assert_eq!(args, vec!["trust-mc", "--only-codegen"]);

        let has_time_compiler =
            cmd.get_envs().any(|(k, v)| k == "TIME_COMPILER" && v == Some(OsStr::new("true")));
        assert!(has_time_compiler, "TIME_COMPILER=true must be set");

        assert_eq!(cmd.get_current_dir(), Some(dir));
    }

    #[test]
    fn extract_duration_reads_the_digits_after_in() {
        assert_eq!(extract_duration("BUILT crate42 IN 1500us"), Duration::from_micros(1500));
        // Without an `IN` marker every digit of the line counts, as before.
        assert_eq!(extract_duration("BUILT 7 9"), Duration::from_micros(79));
    }

    #[test]
    fn result_stats_summarizes_runs() {
        let stats = result_stats(&[Duration::from_secs(1), Duration::from_secs(3)])
            .expect("two runs have statistics");
        assert_eq!(stats.avg, Duration::from_secs(2));
        assert_eq!(stats.std_dev, Duration::from_secs(1));
        assert_eq!(stats.range, (Duration::from_secs(1), Duration::from_secs(3)));
    }

    #[test]
    fn result_stats_refuses_empty_and_overflowing_runs() {
        assert!(result_stats(&[]).is_none(), "no runs: no average to divide out");
        assert!(
            result_stats(&[Duration::MAX, Duration::MAX]).is_none(),
            "a sum past Duration::MAX is refused, not wrapped or panicked"
        );
        assert!(
            result_stats(&[Duration::ZERO, Duration::MAX]).is_none(),
            "a squared deviation past u128::MAX is refused"
        );
    }
}

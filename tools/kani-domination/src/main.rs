// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! kani-domination — download, build and run Kani's upstream test/benchmark
//! corpus through trust-mc, and track the burndown to full Kani replacement.
//!
//! This is the trust-mc analogue of AY's `ay z3-audit` / `ay bench
//! --reference-solver z3` domination tooling: it measures whether trust-mc
//! reaches the same verdict Kani does, across Kani's own test suites.
#![allow(unreachable_pub, dead_code, clippy::struct_excessive_bools)]

mod clone;
mod discover;
mod env;
mod model;
mod quarantine;
mod rekey;
mod runner;
mod score;
mod suites;
mod triage;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use std::path::PathBuf;

use crate::discover::{Discovered, discover_suite};
use crate::env::Env;
use crate::model::{TestResult, Verdict};

#[derive(Parser)]
#[command(
    name = "kani-domination",
    about = "Track trust-mc's burndown to full Kani replacement by running Kani's own corpus.",
    version
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Shallow-clone Kani's source at a pinned revision into the cache.
    Clone {
        #[arg(long, default_value = clone::DEFAULT_KANI_REV)]
        rev: String,
        #[arg(long, default_value = "https://github.com/model-checking/kani")]
        repo: String,
        #[arg(long)]
        force: bool,
    },
    /// Build the trust-mc verifier (cargo build-dev).
    Build,
    /// Enumerate the Kani corpus and print the layered parity denominators
    /// (no verification run).
    Inventory {
        #[arg(long, value_delimiter = ',', default_value = "verification")]
        scope: Vec<String>,
    },
    /// Run trust-mc over the selected Kani suites and record per-test results.
    Run {
        /// Scope keywords: verification, benchmark, diagnostic, full.
        #[arg(long, value_delimiter = ',', default_value = "verification")]
        scope: Vec<String>,
        /// Explicit suite names (overrides --scope).
        #[arg(long, value_delimiter = ',')]
        suite: Vec<String>,
        #[arg(long, default_value = "chc")]
        backend: String,
        #[arg(long, default_value_t = 20)]
        timeout: u64,
        #[arg(long)]
        jobs: Option<usize>,
        /// Cap the number of *runnable* tests (0 = no cap); for smoke runs.
        #[arg(long, default_value_t = 0)]
        limit: usize,
        /// Only run tests whose suite-relative path contains one of these
        /// comma-separated substrings (slice re-runs).
        #[arg(long, value_delimiter = ',')]
        filter: Vec<String>,
        /// Harness spelling surface. `legacy` (default) runs the corpus
        /// verbatim — byte-identical behavior to before this flag existed.
        /// `native` mechanically re-keys each expressible `#[kani::proof]`
        /// unit to the native `#[kani::harness]` spelling before compilation
        /// (fail-closed: inexpressible units run legacy, with the per-unit
        /// provenance recorded either way).
        #[arg(long, value_enum, default_value_t = rekey::Surface::Legacy)]
        surface: rekey::Surface,
        /// Forward `--cbmc-args …` verbatim instead of stripping (default strips).
        #[arg(long)]
        keep_cbmc_args: bool,
        /// Results JSONL path (default: cache/reports/results-<scope>.jsonl).
        #[arg(long)]
        out: Option<PathBuf>,
        /// Delete any prior results file first (no resume).
        #[arg(long)]
        fresh: bool,
        /// Clone Kani automatically if the checkout is missing.
        #[arg(long, default_value_t = true)]
        auto_clone: bool,
    },
    /// Summarise a results JSONL into the layered burndown.
    Score {
        report: PathBuf,
        #[arg(long, default_value = "text")]
        format: String,
    },
    /// Group non-parity harnesses by normalized root cause (what to fix next).
    Triage {
        report: PathBuf,
        /// Restrict to one class (e.g. encoding_gap, false_positive, unsupported).
        #[arg(long)]
        only: Option<String>,
        #[arg(long, default_value_t = 25)]
        top: usize,
    },
    /// Apply the native-surface re-keyer across the corpus WITHOUT running
    /// any verification, and print the inventory: units rewritten cleanly to
    /// `#[kani::harness]` vs. left legacy, by reason. The read-only planning
    /// half of `run --surface native`.
    RekeyDryRun {
        /// Scope keywords: verification, benchmark, diagnostic, full.
        #[arg(long, value_delimiter = ',', default_value = "verification")]
        scope: Vec<String>,
        /// Explicit suite names (overrides --scope).
        #[arg(long, value_delimiter = ',')]
        suite: Vec<String>,
        /// Sample unit paths to print per legacy reason.
        #[arg(long, default_value_t = 3)]
        samples: usize,
    },
    /// Compute the burndown and append a row to the committed trend ledger.
    Burndown {
        report: PathBuf,
        #[arg(long, default_value = "md")]
        format: String,
        /// Ledger path (default: tools/kani-domination/burndown-ledger.jsonl).
        #[arg(long)]
        ledger: Option<PathBuf>,
        /// Do not append to the ledger (print only).
        #[arg(long)]
        no_append: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Clone { rev, repo, force } => {
            let env = Env::discover()?;
            clone::clone_kani(&env.kani_dir(), &rev, &repo, force)?;
        }
        Cmd::Build => {
            let env = Env::discover()?;
            eprintln!("[kani-domination] cargo build-dev …");
            let status = std::process::Command::new("cargo")
                .arg("build-dev")
                .current_dir(&env.repo)
                .status()
                .context("running cargo build-dev")?;
            if !status.success() {
                bail!("cargo build-dev failed");
            }
            eprintln!("[kani-domination] verifier: {}", env.verifier.display());
        }
        Cmd::Inventory { scope } => cmd_inventory(&scope)?,
        Cmd::Run {
            scope,
            suite,
            backend,
            timeout,
            jobs,
            limit,
            filter,
            surface,
            keep_cbmc_args,
            out,
            fresh,
            auto_clone,
        } => cmd_run(RunArgs {
            scope,
            suite,
            backend,
            timeout,
            jobs,
            limit,
            filter,
            surface,
            keep_cbmc_args,
            out,
            fresh,
            auto_clone,
        })?,
        Cmd::RekeyDryRun { scope, suite, samples } => cmd_rekey_dry_run(&scope, &suite, samples)?,
        Cmd::Score { report, format } => {
            let results = read_jsonl(&report)?;
            let summary = score::summarize(&results);
            let prov = load_provenance(&report);
            print_summary(&summary, &prov, &format);
        }
        Cmd::Triage { report, only, top } => {
            let results = read_jsonl(&report)?;
            print!("{}", triage::render_triage(&results, only.as_deref(), top));
        }
        Cmd::Burndown { report, format, ledger, no_append } => {
            let env = Env::discover().ok();
            let results = read_jsonl(&report)?;
            let summary = score::summarize(&results);
            let prov = load_provenance(&report);
            print_summary(&summary, &prov, &format);
            let row = score::ledger_row(&summary, &prov);
            if !no_append {
                let path = ledger.unwrap_or_else(|| {
                    env.as_ref()
                        .map(|e| e.repo.join("tools/kani-domination/burndown-ledger.jsonl"))
                        .unwrap_or_else(|| PathBuf::from("burndown-ledger.jsonl"))
                });
                score::append_ledger(&path, &row)?;
                eprintln!("[kani-domination] appended ledger row -> {}", path.display());
            }
        }
    }
    Ok(())
}

struct RunArgs {
    scope: Vec<String>,
    suite: Vec<String>,
    backend: String,
    timeout: u64,
    jobs: Option<usize>,
    limit: usize,
    filter: Vec<String>,
    surface: rekey::Surface,
    keep_cbmc_args: bool,
    out: Option<PathBuf>,
    fresh: bool,
    auto_clone: bool,
}

fn cmd_inventory(scope: &[String]) -> Result<()> {
    let env = Env::discover()?;
    let kani_tests = env.kani_dir().join("tests");
    if !kani_tests.is_dir() {
        bail!("Kani not cloned at {} — run `kani-domination clone`", env.kani_dir().display());
    }
    let selected = suites::suites_for_scopes(scope);
    println!("Kani-domination inventory (scope: {})", scope.join(","));
    println!("{:<18} {:<13} {:>7} {:>8} {:>8} {:>8}", "suite", "scope", "entries", "expect↑", "expect↓", "cargo");
    let (mut t_entries, mut t_succ, mut t_fail) = (0u64, 0u64, 0u64);
    for s in &selected {
        let found = discover_suite(&kani_tests, s);
        let succ = found.iter().filter(|d| d.oracle == Verdict::Success).count() as u64;
        let fail = found.iter().filter(|d| d.oracle == Verdict::Fail).count() as u64;
        t_entries += found.len() as u64;
        t_succ += succ;
        t_fail += fail;
        println!(
            "{:<18} {:<13} {:>7} {:>8} {:>8} {:>8}",
            s.name, s.scope.as_str(), found.len(), succ, fail,
            if s.cargo_project { "yes" } else { "no" }
        );
    }
    println!("{:-<64}", "");
    println!("{:<18} {:<13} {:>7} {:>8} {:>8}", "TOTAL", "", t_entries, t_succ, t_fail);
    Ok(())
}

fn cmd_run(a: RunArgs) -> Result<()> {
    let env = Env::discover()?;
    if !env.kani_dir().join("tests").is_dir() {
        if a.auto_clone {
            clone::clone_kani(&env.kani_dir(), clone::DEFAULT_KANI_REV, "https://github.com/model-checking/kani", false)?;
        } else {
            bail!("Kani not cloned — run `kani-domination clone` (or drop --no-auto-clone)");
        }
    }
    let kani_tests = env.kani_dir().join("tests");

    let selected: Vec<&suites::Suite> = if a.suite.is_empty() {
        suites::suites_for_scopes(&a.scope)
    } else {
        a.suite.iter().filter_map(|n| suites::lookup(n)).collect()
    };
    if selected.is_empty() {
        bail!("no suites selected");
    }

    // Discover: single-file entries plus cargo units (both are runnable — the
    // cargo lane drives the driver in its `cargo trust-mc` identity).
    let mut runnable: Vec<Discovered> = Vec::new();
    for s in &selected {
        runnable.extend(discover_suite(&kani_tests, s));
    }
    if !a.filter.is_empty() {
        runnable.retain(|d| a.filter.iter().any(|f| d.rel.contains(f)));
    }
    if a.limit > 0 && runnable.len() > a.limit {
        runnable.truncate(a.limit);
    }

    // Native runs get their own default results file so a resume never mixes
    // rows from the two surfaces in one artifact.
    let scope_tag = if a.suite.is_empty() { a.scope.join("-") } else { a.suite.join("-") };
    let surface_tag =
        if a.surface == rekey::Surface::Native { "-native" } else { "" };
    let jsonl = a
        .out
        .unwrap_or_else(|| env.reports_dir().join(format!("results-{scope_tag}{surface_tag}.jsonl")));
    if a.fresh && jsonl.exists() {
        std::fs::remove_file(&jsonl).ok();
    }
    std::fs::create_dir_all(jsonl.parent().unwrap()).ok();

    let cfg = runner::RunConfig {
        harness_timeout_s: a.timeout,
        outer_multiplier: 5,
        grace_s: 30,
        jobs: a.jobs.unwrap_or_else(runner::default_jobs),
        backend: a.backend.clone(),
        strip_cbmc: !a.keep_cbmc_args,
        surface: a.surface,
    };

    // Persist the authority tuple as a sidecar so `score`/`burndown` (and the
    // committed ledger) report the run's true timeout/jobs/backend.
    let mut prov = env.provenance(&a.backend, a.timeout, cfg.jobs, &a.scope);
    if a.surface == rekey::Surface::Native {
        prov.surface = Some(rekey::Surface::Native.as_str().to_string());
        eprintln!("[kani-domination] surface=native: re-keying expressible units to #[kani::harness]");
    }
    let sidecar = provenance_sidecar(&jsonl);
    if let Ok(txt) = serde_json::to_string_pretty(&prov) {
        std::fs::write(&sidecar, txt).ok();
    }

    let cargo_units =
        runnable.iter().filter(|d| !matches!(d.kind, discover::EntryKind::SingleFile { .. })).count();
    eprintln!(
        "[kani-domination] {} runnable ({} cargo unit(s)) across {} suite(s); results -> {}",
        runnable.len(), cargo_units, selected.len(), jsonl.display()
    );
    runner::run_all(&env, runnable, &cfg, &jsonl)?;

    // Score from the complete on-disk artifact.
    let all = read_jsonl(&jsonl)?;
    let summary = score::summarize(&all);
    print_summary(&summary, &prov, "text");
    eprintln!("\n[kani-domination] full results: {}", jsonl.display());
    eprintln!("[kani-domination] burndown:  kani-domination burndown {}", jsonl.display());
    Ok(())
}

fn print_summary(summary: &score::Summary, prov: &model::Provenance, format: &str) {
    match format {
        "md" | "markdown" => println!("{}", score::format_markdown(summary, prov)),
        "json" => {
            let row = score::ledger_row(summary, prov);
            println!("{}", serde_json::to_string_pretty(&row).unwrap_or_default());
        }
        _ => println!("{}", score::format_text(summary, prov)),
    }
}

fn provenance_sidecar(report: &std::path::Path) -> PathBuf {
    let mut s = report.as_os_str().to_os_string();
    s.push(".provenance.json");
    PathBuf::from(s)
}

/// Load the provenance sidecar written at run time; reconstruct a best-effort
/// tuple (timeout/jobs unknown) for results produced elsewhere.
fn load_provenance(report: &std::path::Path) -> model::Provenance {
    if let Ok(txt) = std::fs::read_to_string(provenance_sidecar(report)) {
        if let Ok(p) = serde_json::from_str::<model::Provenance>(&txt) {
            return p;
        }
    }
    let scopes = vec!["from-report".to_string()];
    Env::discover()
        .ok()
        .map(|e| e.provenance("chc", 0, 0, &scopes))
        .unwrap_or_else(|| model::Provenance {
            generated_unix: 0,
            generated_iso: "unknown".into(),
            trust_mc_head: "<unknown>".into(),
            trust_mc_dirty: false,
            ay_pin: "<unknown>".into(),
            ay_binary_version: "<unknown>".into(),
            ay_rev_matches_pin: false,
            kani_rev: "<unknown>".into(),
            kani_repo: "https://github.com/model-checking/kani".into(),
            backend: "chc".into(),
            harness_timeout_s: 0,
            jobs: 0,
            scopes,
            surface: None,
        })
}

/// Apply the native re-keyer across the corpus without running anything and
/// print the inventory (needs only the Kani checkout, not a built verifier).
fn cmd_rekey_dry_run(scope: &[String], suite: &[String], samples: usize) -> Result<()> {
    let repo = env::repo_root_lax()?;
    let kani_dir = repo.join("target/kani-domination/kani");
    if !kani_dir.join("tests").is_dir() {
        clone::clone_kani(
            &kani_dir,
            clone::DEFAULT_KANI_REV,
            "https://github.com/model-checking/kani",
            false,
        )?;
    }
    let kani_tests = kani_dir.join("tests");
    let selected: Vec<&suites::Suite> = if suite.is_empty() {
        suites::suites_for_scopes(scope)
    } else {
        suite.iter().filter_map(|n| suites::lookup(n)).collect()
    };
    if selected.is_empty() {
        bail!("no suites selected");
    }

    struct ReasonBucket {
        count: u64,
        samples: Vec<String>,
    }
    let mut reasons: std::collections::BTreeMap<String, ReasonBucket> = Default::default();
    let (mut t_units, mut t_native, mut t_rewritten, mut t_hoisted) = (0u64, 0u64, 0u64, 0u64);

    println!("Kani-domination native re-key dry run (scope: {})", scope.join(","));
    println!("{:<18} {:>6} {:>7} {:>7} {:>8} {:>10} {:>8}",
        "suite", "units", "native", "legacy", "native%", "harnesses", "params");
    for s in &selected {
        let found = discover_suite(&kani_tests, s);
        let (mut units, mut native, mut rewritten, mut hoisted) = (0u64, 0u64, 0u64, 0u64);
        for d in &found {
            units += 1;
            let outcome = match &d.kind {
                discover::EntryKind::CargoPackage { .. } => {
                    rekey::Rekey::Legacy { reason: "cargo_unit".to_string() }
                }
                discover::EntryKind::SingleFile { .. } => match std::fs::read_to_string(&d.abs) {
                    Ok(src) => rekey::rekey_source(&src),
                    Err(_) => rekey::Rekey::Legacy { reason: "read_error".to_string() },
                },
            };
            match outcome {
                rekey::Rekey::Native { rewritten: r, hoisted_params: h, .. } => {
                    native += 1;
                    rewritten += r as u64;
                    hoisted += h as u64;
                }
                rekey::Rekey::Legacy { reason } => {
                    let b = reasons
                        .entry(reason)
                        .or_insert(ReasonBucket { count: 0, samples: Vec::new() });
                    b.count += 1;
                    if b.samples.len() < samples {
                        b.samples.push(format!("{}/{}", d.suite, d.rel));
                    }
                }
            }
        }
        let pct = if units == 0 { 0.0 } else { 100.0 * native as f64 / units as f64 };
        println!("{:<18} {:>6} {:>7} {:>7} {:>7.1}% {:>10} {:>8}",
            s.name, units, native, units - native, pct, rewritten, hoisted);
        t_units += units;
        t_native += native;
        t_rewritten += rewritten;
        t_hoisted += hoisted;
    }
    let pct = if t_units == 0 { 0.0 } else { 100.0 * t_native as f64 / t_units as f64 };
    println!("{:-<70}", "");
    println!("{:<18} {:>6} {:>7} {:>7} {:>7.1}% {:>10} {:>8}",
        "TOTAL", t_units, t_native, t_units - t_native, pct, t_rewritten, t_hoisted);

    if !reasons.is_empty() {
        let mut ranked: Vec<(&String, &ReasonBucket)> = reasons.iter().collect();
        ranked.sort_by(|a, b| b.1.count.cmp(&a.1.count).then(a.0.cmp(b.0)));
        println!("\nLeft legacy by reason:");
        for (reason, b) in ranked {
            println!("  {:>6}  {}", b.count, reason);
            if !b.samples.is_empty() {
                println!("          e.g. {}", b.samples.join(" · "));
            }
        }
    }
    Ok(())
}

fn read_jsonl(path: &PathBuf) -> Result<Vec<TestResult>> {
    let txt = std::fs::read_to_string(path)
        .with_context(|| format!("reading results {}", path.display()))?;
    let mut out = Vec::new();
    for line in txt.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str::<TestResult>(line) {
            Ok(r) => out.push(r),
            Err(e) => eprintln!("[kani-domination] skipping malformed result line: {e}"),
        }
    }
    Ok(out)
}


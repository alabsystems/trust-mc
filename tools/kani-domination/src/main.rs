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
mod compare;
mod discover;
mod env;
mod flips;
mod model;
mod quarantine;
mod rekey;
mod rescore;
mod route;
mod runner;
mod score;
mod spec;
mod suites;
mod triage;
mod unitlog;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use std::path::PathBuf;

use crate::discover::{Discovered, UpstreamIgnoredReport, discover_suite, discover_suite_with};
use crate::env::Env;
use crate::model::{Engine, SCORER_VERSION, TestResult, Verdict};

#[derive(Parser)]
#[command(
    name = "kani-domination",
    about = "Track trust-mc's burndown to full Kani replacement by running Kani's own corpus.",
    version
)]
struct Cli {
    /// Kani corpus checkout (default: `<user cache>/trust-mc/kani-domination/<rev>`,
    /// e.g. `~/Library/Caches/...` on macOS; also `KANI_DOMINATION_CORPUS_DIR`).
    /// Keep it outside every cargo workspace: cargo units inherit the
    /// `.cargo/config.toml` of every ancestor directory, and `run` refuses a
    /// location that would.
    #[arg(long, global = true)]
    kani_dir: Option<PathBuf>,
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Shallow-clone Kani's source at a pinned revision into the corpus cache.
    Clone {
        #[arg(long, default_value = clone::DEFAULT_KANI_REV)]
        rev: String,
        #[arg(long, default_value = "https://github.com/model-checking/kani")]
        repo: String,
        #[arg(long)]
        force: bool,
    },
    /// Build the trust-mc verifier (`targo --unverified build-dev`).
    Build,
    /// Enumerate the Kani corpus and print the layered parity denominators
    /// (no verification run).
    Inventory {
        #[arg(long, value_delimiter = ',', default_value = "verification")]
        scope: Vec<String>,
        /// Also print every entry: `<suite>/<file>  oracle  harnesses  kind  expected-file`.
        #[arg(long)]
        list: bool,
    },
    /// Run trust-mc (or upstream Kani) over the selected Kani suites and
    /// record per-test results, with each unit's wall time and peak memory.
    Run {
        /// Scope keywords: verification, benchmark, diagnostic, full.
        #[arg(long, value_delimiter = ',', default_value = "verification")]
        scope: Vec<String>,
        /// Explicit suite names (overrides --scope).
        #[arg(long, value_delimiter = ',')]
        suite: Vec<String>,
        /// Which verifier runs every unit. `trust-mc` (default) is
        /// byte-identical to runs before this flag existed. `kani` drives the
        /// upstream Kani install (`$KANI_BIN`, else `~/.cargo/bin/kani`) on
        /// the same units, oracles, cwd, target dirs and watchdog, so the two
        /// results files `compare` row for row; results default to
        /// `results-<scope>-kani.jsonl`, `--backend` is ignored (Kani's is
        /// CBMC), `--cbmc-args` is always forwarded, and `--surface native`
        /// is refused (upstream Kani has no `#[kani::harness]`).
        #[arg(long, value_enum, default_value_t = Engine::TrustMc)]
        engine: Engine,
        #[arg(long, default_value = "chc")]
        backend: String,
        #[arg(long, default_value_t = 20)]
        timeout: u64,
        #[arg(long)]
        jobs: Option<usize>,
        /// Cap the number of *runnable* tests (0 = no cap); for smoke runs.
        #[arg(long, default_value_t = 0)]
        limit: usize,
        /// Only run tests whose suite-relative path, or `<suite>/<path>`,
        /// contains one of these comma-separated substrings (slice re-runs).
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
        /// Append a flag verbatim to EVERY driver invocation (repeatable).
        ///
        /// For A/B-ing a backend knob across the whole corpus without editing
        /// the runner — e.g. deciding whether bounded-loop unrolling should be
        /// a default:
        ///   --extra-driver-flag=--ay-chc-bounded-unroll
        ///   --extra-driver-flag=--default-unwind --extra-driver-flag=20
        /// Any run using this prints a NON-STOCK banner so its number is never
        /// mistaken for a stock measurement.
        #[arg(long = "extra-driver-flag")]
        extra_driver_flag: Vec<String>,
        /// Results JSONL path (default: cache/reports/results-<scope>.jsonl).
        #[arg(long)]
        out: Option<PathBuf>,
        /// Delete any prior results file first (no resume).
        #[arg(long)]
        fresh: bool,
        /// Clone Kani automatically if the checkout is missing.
        #[arg(long, default_value_t = true)]
        auto_clone: bool,
        /// Compiler route (T1-D1). `dev-cli` (default) is the driver child this
        /// runner always spawned. `trustc` runs every unit through
        /// `trust-mc-driver --compiler-route trustc --trustc <p> --backend-dylib <p>`
        /// with `TRUST_MC_SYSROOT=<KEY>`, after attesting those artifacts; a route
        /// refusal, a preflight failure or a missing route marker is an `error` row.
        #[arg(long, value_enum, default_value_t = route::Route::DevCli)]
        route: route::Route,
        /// KEY directory for `--route trustc` (default: TRUST_MC_SYSROOT).
        #[arg(long, value_name = "DIR")]
        key: Option<PathBuf>,
        /// Canonical trustc for `--route trustc` (default: TRUST_MC_TRUSTC, then
        /// the compiler KEY.json records).
        #[arg(long, value_name = "PATH")]
        trustc: Option<PathBuf>,
        /// Backend dylib for `--route trustc` (default: TRUST_MC_BACKEND_DYLIB,
        /// then <KEY>/codegen-backends/librustc_codegen_trust_mc.dylib).
        #[arg(long, value_name = "PATH")]
        backend_dylib: Option<PathBuf>,
        /// Allow `--route trustc` on a smoke KEY (prebuilt dist std). The run is
        /// marked non-counting and its row never reaches the ledger (T1-D5).
        #[arg(long)]
        allow_smoke_key: bool,
        /// Allow `--route trustc` on a seal that fails (or cannot run)
        /// `tools/tuple-check`, e.g. the store's `current` while tools/tuple.toml
        /// names an older build. The run is marked non-counting and its row never
        /// reaches the ledger: a row from other inputs is not a row of the tuple.
        #[arg(long)]
        allow_off_tuple: bool,
    },
    /// Summarise a results JSONL into the layered burndown.
    Score {
        report: PathBuf,
        #[arg(long, default_value = "text")]
        format: String,
    },
    /// Re-classify every row of a results file from its saved unit log under
    /// the current scorer (no corpus run), write `<stem>-rescored.jsonl`
    /// beside it, and print the classifications that moved.
    Rescore {
        report: PathBuf,
        /// Where to write the rescored file (and its sidecar beside it);
        /// default `<stem>-rescored.jsonl` beside the input, which is never
        /// overwritten.
        #[arg(long)]
        out: Option<PathBuf>,
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
    /// A results file produced by `--engine kani` is refused unless the run
    /// only prints (`--no-append` or `--ledger none`): the ledger is
    /// trust-mc's trend line.
    Burndown {
        report: PathBuf,
        #[arg(long, default_value = "md")]
        format: String,
        /// Ledger path (default: tools/kani-domination/burndown-ledger.jsonl);
        /// `none` prints without appending.
        #[arg(long)]
        ledger: Option<PathBuf>,
        /// Do not append to the ledger (print only).
        #[arg(long)]
        no_append: bool,
    },
    /// Report the flip set across N results files of one measurement tuple:
    /// the units whose classification differs between runs, the per-class and
    /// parity spread, and the noise floor a claimed delta must exceed (plan
    /// G9). Refuses files whose sidecars name different tuples.
    Flips {
        /// Two or more results JSONL files (each with its provenance sidecar).
        #[arg(required = true, num_args = 2..)]
        reports: Vec<PathBuf>,
        #[arg(long, default_value = "text")]
        format: String,
        /// Report even when the files' tuples differ (marked NOT IDENTICAL).
        #[arg(long)]
        allow_tuple_mismatch: bool,
    },
    /// Join a trust-mc results file with a Kani results file on the same
    /// units and report verdict agreement plus wall-time and peak-memory
    /// ratios (trust-mc / Kani) over the units both engines solve.
    Compare {
        /// Results JSONL from `run --engine trust-mc`.
        trust_mc: PathBuf,
        /// Results JSONL from `run --engine kani`.
        kani: PathBuf,
        #[arg(long, default_value = "text")]
        format: String,
        /// How many units to list per axis, worst ratio first.
        #[arg(long, default_value_t = 25)]
        worst: usize,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let kani_flag = cli.kani_dir;
    match cli.cmd {
        Cmd::Clone { rev, repo, force } => {
            let dir = crate::env::corpus_dir(kani_flag.as_deref(), &rev)?;
            clone::clone_kani(&dir, &rev, &repo, force)?;
            if rev != clone::DEFAULT_KANI_REV {
                // `run`, `inventory` and `rekey-dry-run` default to the pinned
                // rev's directory; without this hint they would auto-clone the
                // pin and silently ignore the checkout just made.
                eprintln!(
                    "[kani-domination] cloned non-default rev {rev} into {}; pass `--kani-dir {}` to use it",
                    dir.display(),
                    dir.display()
                );
            }
            for cfg in crate::env::inherited_cargo_configs(&dir, crate::env::cargo_home().as_deref()) {
                eprintln!(
                    "[kani-domination] WARNING: cargo units in {} would inherit {} (`run` refuses this location for cargo units)",
                    dir.display(),
                    cfg.display()
                );
            }
        }
        Cmd::Build => {
            // The Targo of the pinned Trust toolchain, resolved like every tool a
            // run attests; `build-dev` is the unverified lane (no proof claim).
            let repo =
                crate::env::find_repo_root().context("could not locate the trust-mc repo root")?;
            let targo = crate::env::resolve_targo(&repo)?;
            eprintln!("[kani-domination] {} --unverified build-dev …", targo.display());
            let status = std::process::Command::new(&targo)
                .args(["--unverified", "build-dev"])
                .current_dir(&repo)
                .status()
                .with_context(|| format!("running {} --unverified build-dev", targo.display()))?;
            if !status.success() {
                bail!("targo --unverified build-dev failed");
            }
            let env = Env::discover(
                crate::env::corpus_dir(kani_flag.as_deref(), clone::DEFAULT_KANI_REV)?,
                Engine::TrustMc,
            )?;
            let verifier = &env.trust_mc().expect("discovered for trust-mc").verifier;
            eprintln!("[kani-domination] verifier: {}", verifier.display());
        }
        Cmd::Inventory { scope, list } => cmd_inventory(&scope, list, kani_flag.as_deref())?,
        Cmd::Run {
            scope,
            suite,
            engine,
            backend,
            timeout,
            jobs,
            limit,
            filter,
            surface,
            keep_cbmc_args,
            extra_driver_flag,
            out,
            fresh,
            auto_clone,
            route,
            key,
            trustc,
            backend_dylib,
            allow_smoke_key,
            allow_off_tuple,
        } => cmd_run(RunArgs {
            scope,
            suite,
            engine,
            backend,
            timeout,
            jobs,
            limit,
            filter,
            surface,
            keep_cbmc_args,
            extra_driver_flag,
            out,
            fresh,
            auto_clone,
            kani_dir: kani_flag,
            route,
            key,
            trustc,
            backend_dylib,
            allow_smoke_key,
            allow_off_tuple,
        })?,
        Cmd::RekeyDryRun { scope, suite, samples } => {
            cmd_rekey_dry_run(&scope, &suite, samples, kani_flag.as_deref())?
        }
        Cmd::Score { report, format } => {
            let results = read_jsonl(&report)?;
            let prov = load_provenance(&report);
            score::report_route(&results, &prov).with_context(|| format!("scoring {}", report.display()))?;
            let summary = score::summarize(&results);
            print_summary(&summary, &prov, &format);
        }
        Cmd::Rescore { report, out } => rescore::cmd_rescore(&report, out.as_deref())?,
        Cmd::Flips { reports, format, allow_tuple_mismatch } => flips::cmd_flips(&reports, &format, allow_tuple_mismatch)?,
        Cmd::Triage { report, only, top } => {
            let results = read_jsonl(&report)?;
            print!("{}", triage::render_triage(&results, only.as_deref(), top));
        }
        Cmd::Burndown { report, format, ledger, no_append } => {
            let repo = crate::env::repo_root_lax().ok();
            let results = read_jsonl(&report)?;
            let prov = load_provenance(&report);
            score::report_route(&results, &prov).with_context(|| format!("scoring {}", report.display()))?;
            let summary = score::summarize(&results);
            // `--ledger none` is the print-only spelling.
            let ledger_none = ledger.as_deref().is_some_and(|l| l.as_os_str() == "none");
            let print_only = no_append || ledger_none;
            let ledger = ledger.filter(|_| !ledger_none);
            print_summary(&summary, &prov, &format);
            let row = score::ledger_row(&summary, &prov);
            if !print_only {
                // Fail closed, after the summary is printed: a Kani file, an
                // uncounted Trustc run (preflight, tuple-check, smoke KEY) and a
                // mixed-scorer file are each scored, never appended.
                if let Some(why) = score::ledger_refusal(&prov).or_else(|| score::mixed_scorer_versions(&summary)) {
                    bail!(
                        "refusing to append {} to the ledger: {why}. Print only with --no-append or --ledger none.",
                        report.display()
                    );
                }
                let path = ledger.unwrap_or_else(|| {
                    repo.as_ref()
                        .map(|r| r.join("tools/kani-domination/burndown-ledger.jsonl"))
                        .unwrap_or_else(|| PathBuf::from("burndown-ledger.jsonl"))
                });
                score::append_ledger(&path, &row)?;
                eprintln!("[kani-domination] appended ledger row -> {}", path.display());
            }
        }
        Cmd::Compare { trust_mc, kani, format, worst } => {
            let a = read_jsonl(&trust_mc)?;
            let b = read_jsonl(&kani)?;
            // The positional order is the contract; a sidecar that says
            // otherwise is a swapped invocation, not a different report.
            for (path, want) in [(&trust_mc, Engine::TrustMc), (&kani, Engine::Kani)] {
                if let Some(p) = read_sidecar(path) {
                    if p.engine() != want {
                        bail!(
                            "{} was produced by engine `{}`, but is given in the `{}` position",
                            path.display(),
                            p.engine().as_str(),
                            want.as_str()
                        );
                    }
                } else {
                    eprintln!(
                        "[kani-domination] WARNING: {} has no provenance sidecar; taking it as the `{}` file by position",
                        path.display(),
                        want.as_str()
                    );
                }
            }
            let c = compare::compare(&a, &b, worst);
            match format.as_str() {
                "json" => println!("{}", serde_json::to_string_pretty(&c)?),
                _ => print!("{}", compare::format_text(&c)),
            }
        }
    }
    Ok(())
}

struct RunArgs {
    scope: Vec<String>,
    suite: Vec<String>,
    engine: Engine,
    backend: String,
    timeout: u64,
    jobs: Option<usize>,
    limit: usize,
    filter: Vec<String>,
    surface: rekey::Surface,
    keep_cbmc_args: bool,
    extra_driver_flag: Vec<String>,
    out: Option<PathBuf>,
    fresh: bool,
    auto_clone: bool,
    kani_dir: Option<PathBuf>,
    route: route::Route,
    key: Option<PathBuf>,
    trustc: Option<PathBuf>,
    backend_dylib: Option<PathBuf>,
    allow_smoke_key: bool,
    allow_off_tuple: bool,
}

fn cmd_inventory(scope: &[String], list: bool, kani_flag: Option<&std::path::Path>) -> Result<()> {
    let kani_dir = crate::env::corpus_dir(kani_flag, clone::DEFAULT_KANI_REV)?;
    let kani_tests = kani_dir.join("tests");
    if !kani_tests.is_dir() {
        bail!("Kani not cloned at {} — run `kani-domination clone`", kani_dir.display());
    }
    let selected = suites::suites_for_scopes(scope);
    let spec = crate::spec::load_for_corpus(&kani_dir)?;
    let mut all_found: Vec<Discovered> = Vec::new();
    println!("Kani-domination inventory (scope: {})", scope.join(","));
    println!("{:<18} {:<13} {:>7} {:>8} {:>8} {:>8}", "suite", "scope", "entries", "expect↑", "expect↓", "cargo");
    let (mut t_entries, mut t_succ, mut t_fail) = (0u64, 0u64, 0u64);
    for s in &selected {
        let found = discover_suite_with(&kani_tests, s, spec.as_ref());
        let succ = found.iter().filter(|d| d.oracle == Verdict::Success).count() as u64;
        let fail = found.iter().filter(|d| d.oracle == Verdict::Fail).count() as u64;
        t_entries += found.len() as u64;
        t_succ += succ;
        t_fail += fail;
        if list {
            for d in &found {
                let (kind, harnesses) = match &d.kind {
                    discover::EntryKind::SingleFile { harness_count } => ("single-file", *harness_count),
                    discover::EntryKind::CargoPackage { harness_count, .. } => ("cargo", *harness_count),
                };
                println!(
                    "  {}/{}\toracle={}\tharnesses={}\tkind={}\texpected={}{}",
                    d.suite,
                    d.rel,
                    format!("{:?}", d.oracle).to_lowercase(),
                    harnesses,
                    kind,
                    d.expected_path.as_deref().map(|p| p.display().to_string()).unwrap_or_else(|| "-".into()),
                    if d.upstream_ignored { "\tupstream_ignored" } else { "" },
                );
            }
        }
        println!(
            "{:<18} {:<13} {:>7} {:>8} {:>8} {:>8}",
            s.name, s.scope.as_str(), found.len(), succ, fail,
            if s.cargo_project { "yes" } else { "no" }
        );
        all_found.extend(found);
    }
    println!("{:-<64}", "");
    println!("{:<18} {:<13} {:>7} {:>8} {:>8}", "TOTAL", "", t_entries, t_succ, t_fail);
    let ignored = UpstreamIgnoredReport::of(&all_found, spec.as_ref());
    println!("{}", ignored.banner());
    if list {
        for unit in &ignored.units {
            println!("  upstream_ignored {unit}");
        }
    }
    Ok(())
}

fn cmd_run(a: RunArgs) -> Result<()> {
    if a.engine == Engine::Kani && a.surface == rekey::Surface::Native {
        bail!("--surface native re-keys units to `#[kani::harness]`, which upstream Kani does not have; use --surface legacy with --engine kani");
    }
    let route_inputs_given = a.key.is_some()
        || a.trustc.is_some()
        || a.backend_dylib.is_some()
        || a.allow_smoke_key
        || a.allow_off_tuple;
    if a.engine == Engine::Kani {
        // The route is how the trust-mc driver compiles; upstream Kani compiles
        // with its own toolchain, so `--engine kani` has no route at all.
        if a.route != route::Route::DevCli || route_inputs_given {
            eprintln!(
                "[kani-domination] --engine kani ignores --route and its inputs (--key, --trustc, --backend-dylib, \
                 --allow-smoke-key, --allow-off-tuple): upstream Kani compiles with its own toolchain"
            );
        }
    } else if a.route == route::Route::DevCli && route_inputs_given {
        bail!(
            "--key, --trustc, --backend-dylib, --allow-smoke-key and --allow-off-tuple only apply \
             with --route trustc"
        );
    }
    let env = Env::discover(
        crate::env::corpus_dir(a.kani_dir.as_deref(), clone::DEFAULT_KANI_REV)?,
        a.engine,
    )?;
    if !env.kani_dir().join("tests").is_dir() {
        if a.auto_clone {
            clone::clone_kani(&env.kani_dir(), clone::DEFAULT_KANI_REV, "https://github.com/model-checking/kani", false)?;
        } else {
            bail!("Kani not cloned — run `kani-domination clone` (or drop --no-auto-clone)");
        }
    }
    let kani_tests = env.kani_dir().join("tests");

    // The route's artifacts are read and cross-checked once, before any unit.
    // `--engine kani` runs no trust-mc driver, so it has no route to attest.
    let route_engine = match a.route {
        _ if a.engine == Engine::Kani => route::RouteEngine::DevCli(route::DevCliEngine),
        route::Route::DevCli => route::RouteEngine::DevCli(route::DevCliEngine),
        route::Route::Trustc => {
            let request = route::TrustcRequest {
                trustc: a.trustc.clone(),
                backend_dylib: a.backend_dylib.clone(),
                key: a.key.clone(),
            };
            let inputs = request.resolve(|name| std::env::var_os(name))?;
            let attestation = route::attest_trustc(&inputs, &route::SystemHost { repo: env.repo.clone() });
            if attestation.preflight_errors.is_empty()
                && attestation.library_mode.as_deref() != Some(route::PARITY_LIBRARY_MODE)
                && !a.allow_smoke_key
            {
                bail!(
                    "refusing a counted --route trustc run: KEY {} has library_mode {:?}, not parity, and rows \
                     on a smoke library never count (T1-D5). Build a parity KEY (build-keyed --std build-std), \
                     or pass --allow-smoke-key for a non-counting run.",
                    inputs.key_dir.display(),
                    attestation.library_mode
                );
            }
            if attestation.preflight_errors.is_empty()
                && attestation.tuple_check.as_deref() != Some(route::TUPLE_CHECK_PASS)
                && !a.allow_off_tuple
            {
                bail!(
                    "refusing a counted --route trustc run: tools/tuple-check with seal {} held says {}, \
                     and a row from other inputs is not a row of tools/tuple.toml. Use the tuple's seal \
                     (TRUST_MC_TRUST_TOOLCHAIN), move the tuple in the same commit as the pin, or pass \
                     --allow-off-tuple for a non-counting run.",
                    attestation.trust_seal_build.as_deref().unwrap_or("<none>"),
                    attestation.tuple_check.as_deref().unwrap_or("<none>")
                );
            }
            route::RouteEngine::Trustc(Box::new(route::TrustcEngine { inputs, attestation }))
        }
    };

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
    // Upstream-ignored units (plan D1) are tagged by compiletest's path rule
    // and, when the generated spec for this corpus rev exists, its `fixme`
    // class; a spec that exists but does not parse refuses the run.
    let spec = crate::spec::load_for_corpus(&env.kani_dir())?;
    let mut runnable: Vec<Discovered> = Vec::new();
    for s in &selected {
        runnable.extend(discover_suite_with(&kani_tests, s, spec.as_ref()));
    }
    if !a.filter.is_empty() {
        runnable.retain(|d| {
            let qualified = format!("{}/{}", d.suite, d.rel);
            a.filter.iter().any(|f| d.rel.contains(f) || qualified.contains(f))
        });
    }
    if a.limit > 0 && runnable.len() > a.limit {
        runnable.truncate(a.limit);
    }
    eprintln!("[kani-domination] {}", UpstreamIgnoredReport::of(&runnable, spec.as_ref()).banner());

    // Cargo discovers configuration from every ancestor of the package
    // directory. A corpus under another workspace (historically
    // `<trust-mc>/target`) makes each cargo unit build with that workspace's
    // rustc-wrapper and rustflags, so its row measures the host, not the
    // verifier. Refuse rather than record such rows.
    let cargo_units =
        runnable.iter().filter(|d| !matches!(d.kind, discover::EntryKind::SingleFile { .. })).count();
    if cargo_units > 0 {
        let inherited =
            crate::env::inherited_cargo_configs(&env.kani_dir(), crate::env::cargo_home().as_deref());
        if !inherited.is_empty() {
            let list: Vec<String> = inherited.iter().map(|p| p.display().to_string()).collect();
            bail!(
                "refusing to run {cargo_units} cargo unit(s): the Kani corpus at {} inherits cargo \
                 configuration or workspace membership from {}. Those rows would measure that configuration, not the \
                 verifier. Use a checkout outside every cargo workspace (default: {}) via \
                 --kani-dir or {}.",
                env.kani_dir().display(),
                list.join(", "),
                crate::env::default_corpus_dir(clone::DEFAULT_KANI_REV)
                    .map(|p| p.display().to_string())
                    .unwrap_or_else(|| "<user cache>/trust-mc/kani-domination/<rev>".into()),
                crate::env::CORPUS_DIR_ENV,
            );
        }
    }

    // Native runs and Kani runs get their own default results file so a
    // resume never mixes rows from two surfaces or two engines in one artifact.
    let scope_tag = if a.suite.is_empty() { a.scope.join("-") } else { a.suite.join("-") };
    let surface_tag =
        if a.surface == rekey::Surface::Native { "-native" } else { "" };
    let engine_tag = if a.engine == Engine::Kani { "-kani" } else { "" };
    // Likewise per route: a default-path resume never mixes routes.
    let route_tag = if route_engine.route() == route::Route::Trustc { "-trustc" } else { "" };
    let jsonl = a.out.clone().unwrap_or_else(|| {
        env.reports_dir().join(format!("results-{scope_tag}{surface_tag}{engine_tag}{route_tag}.jsonl"))
    });
    if a.fresh && jsonl.exists() {
        std::fs::remove_file(&jsonl).ok();
    }
    std::fs::create_dir_all(jsonl.parent().unwrap()).ok();

    // Kani's backend is CBMC whatever `--backend` says; the trust-mc flag has
    // no Kani counterpart, and the sidecar records `cbmc` for the same reason.
    let backend = if a.engine == Engine::Kani { "cbmc".to_string() } else { a.backend.clone() };
    // Every unit's driver log goes under `<reports_dir>/logs/<results stem>/`,
    // and the row records the path relative to the reports directory.
    let results_stem = jsonl
        .file_stem()
        .and_then(|s| s.to_str())
        .map(str::to_string)
        .unwrap_or_else(|| "results".into());
    let log_rel_prefix = format!("logs/{results_stem}");
    let cfg = runner::RunConfig {
        engine: a.engine,
        harness_timeout_s: a.timeout,
        outer_multiplier: 5,
        grace_s: 30,
        jobs: a.jobs.unwrap_or_else(runner::default_jobs),
        backend: backend.clone(),
        // Kani consumes `--cbmc-args` itself; only the AY backend strips it.
        strip_cbmc: !a.keep_cbmc_args && a.engine == Engine::TrustMc,
        surface: a.surface,
        extra_driver_flags: a.extra_driver_flag.clone(),
        log_dir: env.reports_dir().join(&log_rel_prefix),
        log_rel_prefix,
        route_engine,
    };
    if std::env::var_os("KANI_DOMINATION_KEEP_OUTPUT").is_some_and(|d| !d.is_empty()) {
        eprintln!(
            "[kani-domination] KANI_DOMINATION_KEEP_OUTPUT is superseded and ignored: every unit's full output \
             (stdout, stderr, argv, cwd, environment, exit code) is always kept in its unit log under {} \
             (each row's `log_path`)",
            cfg.log_dir.display()
        );
    }
    if cfg.extra_driver_flags.iter().any(|f| f == runner::UNPINNED_AY_FLAG) {
        bail!(
            "refusing to forward `{}` to the driver: a ledger row must come from the pinned `ay` \
             (point AY_BIN or TRUST_MC_AY_BIN at a build of the Cargo.toml pin instead)",
            runner::UNPINNED_AY_FLAG
        );
    }
    if !cfg.extra_driver_flags.is_empty() {
        println!(
            "[kani-domination] EXTRA DRIVER FLAGS ACTIVE (non-stock run): {:?}",
            cfg.extra_driver_flags
        );
    }

    // Persist the authority tuple as a sidecar so `score`/`burndown` (and the
    // committed ledger) report the run's true timeout/jobs/backend.
    let mut prov = env.provenance(&backend, a.timeout, cfg.jobs, &a.scope);
    prov.log_root = Some(env.reports_dir().display().to_string());
    if a.surface == rekey::Surface::Native {
        prov.surface = Some(rekey::Surface::Native.as_str().to_string());
        eprintln!("[kani-domination] surface=native: re-keying expressible units to #[kani::harness]");
    }
    // Only the trust-mc engine has a compiler route; a Kani sidecar names none.
    prov.route = (a.engine == Engine::TrustMc).then(|| cfg.route_engine.route().as_str().to_string());
    if let route::RouteEngine::Trustc(trustc) = &cfg.route_engine {
        prov.route_attestation = Some(trustc.attestation.clone());
        if let Some(att) = prov.attestation.as_mut() {
            // No trust-mc-compiler runs on this route, and the sysroot the driver
            // receives is the KEY.
            att.compiler_path = None;
            att.compiler_sha256 = None;
            att.sysroot = trustc.inputs.key_dir.display().to_string();
        }
    }
    let sidecar = provenance_sidecar(&jsonl);
    // A resume keeps the rows already in `jsonl`, and the sidecar written below
    // attests EVERY row. Refuse to resume across a different engine, verifier,
    // solver, backend or timeout; when the earlier rows carry no attestation to
    // compare against, record none rather than vouch for binaries that did not
    // run them. A Kani run has no such fallback: without a sidecar the file's
    // engine is unknowable, and a Kani row must never join a trust-mc file.
    let has_prior_rows =
        std::fs::read_to_string(&jsonl).is_ok_and(|t| t.lines().any(|l| !l.trim().is_empty()));
    if has_prior_rows {
        let prior_rows = read_jsonl(&jsonl)?;
        // The rows themselves carry their scorer version; a file never mixes
        // two, whatever the sidecar says (or whether there is one).
        let prior_versions: std::collections::BTreeSet<u32> = prior_rows.iter().map(|r| r.scorer_version).collect();
        if prior_versions.iter().any(|v| *v != SCORER_VERSION) {
            let list: Vec<String> = prior_versions.iter().map(|v| format!("v{v}")).collect();
            bail!(
                "refusing to resume {}: its rows were scored under scorer {} and this runner scores under v{SCORER_VERSION}. \
                 Pass --fresh, --out a new results file, or `rescore` the file first.",
                jsonl.display(),
                list.join("/")
            );
        }
        // Nor two compiler routes: the rows name theirs too.
        score::report_route(&prior_rows, &prov).with_context(|| {
            format!(
                "refusing to resume {} on route {}",
                jsonl.display(),
                route::route_or_legacy(prov.route.as_deref())
            )
        })?;
        let prior = read_sidecar(&jsonl);
        let attested = |p: &model::Provenance| p.attestation.is_some() || p.kani_attestation.is_some();
        match prior {
            Some(prior) if attested(&prior) || !attested(&prov) => {
                let diff = model::resume_mismatch(&prior, &prov);
                if !diff.is_empty() {
                    bail!(
                        "refusing to resume {}: its recorded rows came from a different verifier configuration ({}). \
                         Pass --fresh, or --out a new results file.",
                        jsonl.display(),
                        diff.join("; ")
                    );
                }
            }
            prior if a.engine == Engine::Kani => {
                bail!(
                    "refusing to resume {}: its rows carry no {} (--engine kani needs one to know which engine wrote them). \
                     Pass --fresh, or --out a new results file.",
                    jsonl.display(),
                    if prior.is_some() { "Kani attestation" } else { "provenance sidecar" }
                );
            }
            _ if prov.route_attestation.is_some() => bail!(
                "refusing to resume {} on --route trustc: its earlier rows carry no runner attestation to \
                 compare the route against. Pass --fresh, or --out a new results file.",
                jsonl.display()
            ),
            _ => {
                eprintln!(
                    "[kani-domination] WARNING: resuming {} whose earlier rows carry no runner attestation; \
                     this run records none (use --fresh for an attested run)",
                    jsonl.display()
                );
                prov.attestation = None;
            }
        }
    }
    if let Ok(txt) = serde_json::to_string_pretty(&prov) {
        std::fs::write(&sidecar, txt).ok();
    }
    if let Some(att) = &prov.kani_attestation {
        eprintln!(
            "[kani-domination] engine kani: {} (sha256 {}, {}, via {}) · cargo-kani {} · home {} · toolchain {} · corpus {} · load {:?}",
            att.kani_path,
            &att.kani_sha256[..att.kani_sha256.len().min(16)],
            att.kani_version,
            att.kani_source,
            att.cargo_kani_path,
            att.kani_home.as_deref().unwrap_or("<unknown>"),
            att.kani_toolchain.as_deref().unwrap_or("<unknown>"),
            att.kani_dir,
            att.load_average_start,
        );
        if !att.child_env_scrubbed.is_empty() {
            eprintln!("[kani-domination] removed from Kani children: {}", att.child_env_scrubbed.join(" "));
        }
    }
    if let Some(att) = &prov.attestation {
        eprintln!(
            "[kani-domination] driver {} (sha256 {}, {}) · ay {} [{}] · corpus {} · load {:?}",
            att.driver_path,
            &att.driver_sha256[..att.driver_sha256.len().min(16)],
            att.driver_version,
            att.ay_binary_path,
            att.ay_binary_source,
            att.kani_dir,
            att.load_average_start,
        );
        if !att.child_env_scrubbed.is_empty() {
            eprintln!(
                "[kani-domination] removed from verifier children: {}",
                att.child_env_scrubbed.join(" ")
            );
        }
    }

    if let Some(ra) = &prov.route_attestation {
        let short = |v: &Option<String>| v.as_deref().map_or("<none>".to_string(), |v| v[..v.len().min(16)].to_string());
        eprintln!(
            "[kani-domination] route trustc: {} (commit {}, seal {}) · driver {} · KEY {} (library_mode {}) · backend {} (sha256 {}) · tuple-check {}",
            ra.trustc_path,
            short(&ra.trustc_commit),
            ra.trust_seal_build.as_deref().unwrap_or("<none>"),
            ra.rustc_driver_name.as_deref().unwrap_or("<none>"),
            ra.key_dir,
            ra.library_mode.as_deref().unwrap_or("<none>"),
            ra.backend_dylib_path,
            short(&ra.backend_dylib_sha256),
            ra.tuple_check.as_deref().unwrap_or("<none>"),
        );
        for error in &ra.preflight_errors {
            eprintln!("[kani-domination] ROUTE PREFLIGHT FAILED: {error}");
        }
        if !ra.preflight_errors.is_empty() {
            eprintln!("[kani-domination] every unit is recorded as `error` without running the driver");
        } else if !ra.counted {
            let why = if ra.tuple_check.as_deref() != Some(route::TUPLE_CHECK_PASS) {
                format!("tools/tuple-check says {}, not pass", ra.tuple_check.as_deref().unwrap_or("<none>"))
            } else {
                "the KEY is not a parity library".to_string()
            };
            eprintln!("[kani-domination] NON-COUNTING run: {why}; burndown appends no row");
        }
    }
    eprintln!(
        "[kani-domination] {} runnable ({} cargo unit(s)) across {} suite(s); results -> {}",
        runnable.len(), cargo_units, selected.len(), jsonl.display()
    );
    runner::run_all(&env, runnable, &cfg, &jsonl)?;

    // Close the attestation: the host load when the run finished.
    // Sampled after `run_all` has reaped every child, so `own_excluded` is
    // normally 0 here and `competing` is the rest of the host.
    if let Some(att) = prov.attestation.as_mut() {
        att.load_average_end = crate::env::load_average();
        att.load_end = Some(crate::env::host_load());
    }
    if let Some(att) = prov.kani_attestation.as_mut() {
        att.load_average_end = crate::env::load_average();
        att.load_end = Some(crate::env::host_load());
    }
    if let Ok(txt) = serde_json::to_string_pretty(&prov) {
        std::fs::write(&sidecar, txt).ok();
    }

    // Score from the complete on-disk artifact.
    let all = read_jsonl(&jsonl)?;
    score::report_route(&all, &prov)?;
    let summary = score::summarize(&all);
    print_summary(&summary, &prov, "text");
    eprintln!("\n[kani-domination] full results: {}", jsonl.display());
    if a.engine == Engine::Kani {
        eprintln!(
            "[kani-domination] compare:   kani-domination compare <trust-mc results.jsonl> {}",
            jsonl.display()
        );
    } else {
        eprintln!("[kani-domination] burndown:  kani-domination burndown {}", jsonl.display());
    }
    if let Some(ra) = prov.route_attestation.as_ref().filter(|ra| !ra.preflight_errors.is_empty()) {
        bail!(
            "route preflight failed, so every row in {} is `error`: {}",
            jsonl.display(),
            ra.preflight_errors.join("; ")
        );
    }
    Ok(())
}

/// The provenance sidecar beside a results file, if it exists and parses.
fn read_sidecar(report: &std::path::Path) -> Option<model::Provenance> {
    std::fs::read_to_string(provenance_sidecar(report))
        .ok()
        .and_then(|t| serde_json::from_str::<model::Provenance>(&t).ok())
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
    // A report without its sidecar gets today's tuple but NO attestation and
    // no engine identity: today's binaries did not produce it.
    crate::env::corpus_dir(None, clone::DEFAULT_KANI_REV)
        .ok()
        .and_then(|kani| Env::discover(kani, Engine::TrustMc).ok())
        .map(|e| {
            let mut p = e.provenance("chc", 0, 0, &scopes);
            p.attestation = None;
            p.engine = None;
            p.engine_version = None;
            p.engine_path = None;
            p.engine_sha256 = None;
            p
        })
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
            attestation: None,
            engine: None,
            engine_version: None,
            engine_path: None,
            engine_sha256: None,
            kani_attestation: None,
            scorer_version: 1,
            log_root: None,
            rescored_from: None,
            route: None,
            route_attestation: None,
        })
}

/// Apply the native re-keyer across the corpus without running anything and
/// print the inventory (needs only the Kani checkout, not a built verifier).
fn cmd_rekey_dry_run(
    scope: &[String],
    suite: &[String],
    samples: usize,
    kani_flag: Option<&std::path::Path>,
) -> Result<()> {
    let kani_dir = crate::env::corpus_dir(kani_flag, clone::DEFAULT_KANI_REV)?;
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


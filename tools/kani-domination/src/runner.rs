// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The execution engine: run trust-mc (or upstream Kani, `--engine kani`) on
//! each discovered Kani test, parse its verdict + AY soundness markers,
//! classify against the oracle, account its wall time and peak memory, and
//! write results incrementally (resumable across a multi-hour run).

use std::collections::{BTreeSet, HashSet};
use std::ffi::OsString;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::discover::{Discovered, EntryKind};
use crate::env::{Env, EngineEnv};
use crate::model::{Classification, Engine, RouteAttestation, SCORER_VERSION, TestResult, Verdict};
use crate::rekey::{Rekey, Surface, rekey_source};
use crate::suites::{self, PassCriterion};
use crate::unitlog::{self, UnitLog};
use crate::route::{
    DriverInvocation, Route, RouteEngine, UnitArg, check_route_output, single_file_crate_name,
    strip_crate_qualified_harness_names,
};

/// Tunables for a run.
#[derive(Debug, Clone)]
pub struct RunConfig {
    /// Which verifier runs every unit. Decides the command line, the flag
    /// sanitizer, the child environment and the engine-specific parts of the
    /// classifier; everything else (discovery, oracle, cwd, target dir,
    /// watchdog, retry, accounting) is identical between engines.
    pub engine: Engine,
    pub harness_timeout_s: u64,
    /// Outer watchdog = `harness_timeout_s * outer_multiplier + grace_s`.
    pub outer_multiplier: u64,
    pub grace_s: u64,
    pub jobs: usize,
    /// `chc` (in-process portfolio) or `bmc`.
    pub backend: String,
    /// Drop `--cbmc-args` and everything after it (CBMC-only solver tuning the
    /// AY backend does not accept).
    pub strip_cbmc: bool,
    /// Harness spelling surface: `Legacy` runs the corpus verbatim
    /// (byte-identical to pre-`--surface` behavior); `Native` re-keys each
    /// expressible single-file unit to `#[kani::harness]` before compilation.
    pub surface: Surface,
    /// Extra flags appended verbatim to every driver invocation.
    ///
    /// Exists so a backend knob can be A/B'd across the whole corpus WITHOUT
    /// editing the runner (e.g. deciding whether bounded-loop unrolling should
    /// become a default). Recorded in the run header so a flagged run can never
    /// be mistaken for a stock one.
    pub extra_driver_flags: Vec<String>,
    /// Where every unit's driver log is written:
    /// `<reports_dir>/logs/<results-file-stem>`. The row records the path
    /// relative to the reports directory (`log_rel_prefix` + suite + file).
    pub log_dir: PathBuf,
    /// `logs/<results-file-stem>`.
    pub log_rel_prefix: String,
    /// The compiler route every trust-mc unit runs on (`--route`): the driver
    /// child it spawns and the attestation each unit's output is checked
    /// against. Orthogonal to [`Self::engine`]; the Kani engine ignores it.
    pub route_engine: RouteEngine,
}

impl RunConfig {
    /// Base watchdog for a one-harness unit.
    fn base_outer_timeout(&self) -> Duration {
        Duration::from_secs(self.harness_timeout_s * self.outer_multiplier + self.grace_s)
    }

    /// Single-file watchdog: the driver budgets `--harness-timeout` *per
    /// harness*, so a multi-harness file gets the base watchdog plus one
    /// harness-timeout per additional harness (== base for 1 harness; never
    /// smaller than the old fixed cap).
    fn outer_timeout(&self, harness_count: usize) -> Duration {
        self.base_outer_timeout()
            + Duration::from_secs(self.harness_timeout_s * harness_count.saturating_sub(1) as u64)
    }

    /// Cargo units verify a whole package (possibly many harnesses) and must
    /// first `cargo build` the dependency graph: base watchdog + a per-harness
    /// budget + a flat compile allowance.
    fn cargo_outer_timeout(&self, harness_count: usize) -> Duration {
        self.base_outer_timeout()
            + Duration::from_secs(self.harness_timeout_s * harness_count.max(1) as u64 + 300)
    }
}

/// Run all `tests`, appending each result to `jsonl_path` as it completes.
/// Returns the full result vector (including any pre-existing resumed rows).
pub fn run_all(
    env: &Env,
    tests: Vec<Discovered>,
    cfg: &RunConfig,
    jsonl_path: &PathBuf,
) -> anyhow::Result<Vec<TestResult>> {
    // Resume: skip (suite,file) already recorded in the JSONL.
    let mut prior: Vec<TestResult> = Vec::new();
    let mut done: HashSet<(String, String)> = HashSet::new();
    if let Ok(txt) = std::fs::read_to_string(jsonl_path) {
        for line in txt.lines().filter(|l| !l.trim().is_empty()) {
            if let Ok(r) = serde_json::from_str::<TestResult>(line) {
                done.insert((r.suite.clone(), r.file.clone()));
                prior.push(r);
            }
        }
    }
    let pending: Vec<Discovered> =
        tests.into_iter().filter(|t| !done.contains(&(t.suite.clone(), t.rel.clone()))).collect();

    let total = pending.len();
    if total == 0 {
        eprintln!("[kani-domination] nothing to run ({} already recorded)", prior.len());
        return Ok(prior);
    }
    eprintln!(
        "[kani-domination] running {total} test(s) on {} job(s), engine={}, route={}, backend={}, harness-timeout={}s (outer {:?} + per-extra-harness)  [{} resumed]",
        cfg.jobs,
        cfg.engine.as_str(),
        if cfg.engine == Engine::TrustMc { cfg.route_engine.route().as_str() } else { "n/a" },
        cfg.backend, cfg.harness_timeout_s, cfg.base_outer_timeout(), prior.len()
    );

    if let Some(parent) = jsonl_path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    let sink = Arc::new(Mutex::new(
        std::fs::OpenOptions::new().create(true).append(true).open(jsonl_path)?,
    ));
    let queue = Arc::new(Mutex::new(pending));
    let collected: Arc<Mutex<Vec<TestResult>>> = Arc::new(Mutex::new(Vec::new()));
    let counter = Arc::new(AtomicUsize::new(0));

    std::thread::scope(|scope| {
        for _ in 0..cfg.jobs.max(1) {
            let queue = Arc::clone(&queue);
            let sink = Arc::clone(&sink);
            let collected = Arc::clone(&collected);
            let counter = Arc::clone(&counter);
            scope.spawn(move || {
                loop {
                    let job = { queue.lock().unwrap().pop() };
                    let Some(test) = job else { break };
                    let result = run_one(env, &test, cfg);
                    let n = counter.fetch_add(1, Ordering::SeqCst) + 1;
                    eprintln!(
                        "[{n}/{total}] {:<11} {:<52} oracle={:<7} -> {:<8} {}ms {}MB",
                        test.suite,
                        truncate(&test.rel, 52),
                        format!("{:?}", test.oracle).to_lowercase(),
                        result.classification.map(|c| c.as_str()).unwrap_or("?"),
                        result.duration_ms,
                        result.tree_peak_rss_kb.unwrap_or(result.max_rss_kb) / 1024,
                    );
                    if let Ok(line) = serde_json::to_string(&result) {
                        let mut f = sink.lock().unwrap();
                        let _ = writeln!(f, "{line}");
                        let _ = f.flush();
                    }
                    collected.lock().unwrap().push(result);
                }
            });
        }
    });

    let mut all = prior;
    all.extend(Arc::try_unwrap(collected).unwrap().into_inner().unwrap());
    Ok(all)
}

/// Everything the scorer needs about a unit that its output does not carry.
pub struct UnitCtx<'a> {
    pub engine: Engine,
    pub suite: &'a str,
    pub rel: &'a str,
    pub oracle: Verdict,
    pub is_cargo: bool,
    pub check_fail: bool,
    /// Content of the governing Kani expected file, if any.
    pub expected: Option<&'a str>,
    /// The compiler route the unit ran on (`--route`; the row's `route`).
    /// Read only on the trust-mc engine.
    pub route: Route,
    /// What a Trustc run attested before its first unit (the sidecar's
    /// `route_attestation`); `None` on DevCli and on the Kani engine.
    pub route_attestation: Option<&'a RouteAttestation>,
    /// Upstream Kani's compiletest never runs this unit (`fixme` / `ignore`
    /// path, or the spec's `fixme` class; `discover::upstream_ignored`).
    /// Stamped on the row; it moves the row to the burndown's `fixme`
    /// column, never its classification.
    pub upstream_ignored: bool,
}

/// One attempt's captured output, as classified.
pub struct Attempt<'a> {
    pub stdout: &'a str,
    pub stderr: &'a str,
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    pub retried_after_outer_timeout: bool,
    /// The child could not be spawned at all; nothing else is meaningful.
    pub spawn_error: Option<&'a str>,
}

/// Score one attempt of `unit` into `result`: the parsed markers, the
/// observed verdict, the classification, the note, the tiebreak bit and the
/// scorer version. A pure function of its inputs — `run_one` calls it on the
/// live output and `rescore` on the saved log, and the two must agree.
pub fn score_unit(unit: &UnitCtx<'_>, attempt: &Attempt<'_>, result: &mut TestResult) {
    result.scorer_version = SCORER_VERSION;
    result.upstream_ignored = unit.upstream_ignored;
    result.exit_code = attempt.exit_code;
    result.tiebreak_applied = false;
    // The route applies to the trust-mc driver only (`--engine kani` has none).
    let routed = unit.engine == Engine::TrustMc;
    if let Some(att) = unit.route_attestation.filter(|a| routed && !a.preflight_errors.is_empty()) {
        result.observed = Some(Verdict::Unknown);
        result.classification = Some(Classification::Error);
        result.note = format!("route-preflight-failed (driver not run): {}", att.preflight_errors.join("; "));
        return;
    }
    if let Some(err) = attempt.spawn_error {
        result.observed = None;
        result.classification = Some(Classification::Error);
        result.note = format!("spawn-failed: {err}");
        return;
    }
    let combined = format!("{}\n{}", attempt.stdout, attempt.stderr);
    // TEMPORARY (`route::strip_crate_qualified_harness_names`): the Trustc route
    // prints crate-qualified harness names until the driver fix lands. The
    // crate name is the unit file's stem, which the suite-relative path keeps.
    let combined = match single_file_crate_name(Path::new(unit.rel)) {
        Some(krate) if routed && unit.route == Route::Trustc && !unit.is_cargo => {
            strip_crate_qualified_harness_names(&combined, &krate)
        }
        _ => combined,
    };
    parse_markers(&combined, result);
    // P1 MECH D: in a coherent multi-harness run, surface the FIRST FAILING
    // harness's category/reason instead of the stream-first marker (which may
    // belong to a should-panic success and misattribute the note).
    reattribute_multi_harness_markers(&combined, result, unit.engine);
    let observed = parse_verdict(&combined);
    result.observed = Some(observed);
    if unit.engine == Engine::Kani && combined.contains(KANI_NO_HARNESSES) {
        result.no_harnesses = true;
    }
    let ctx = ClassifyCtx {
        engine: unit.engine,
        criterion: suites::lookup(unit.suite).map(|s| s.criterion).unwrap_or(PassCriterion::Other),
        oracle: unit.oracle,
        observed,
        timed_out: attempt.timed_out,
        exit: attempt.exit_code,
        is_cargo: unit.is_cargo,
        expected: unit.expected,
        check_fail: unit.check_fail,
        ice_oracle: unit.expected.is_some_and(|exp| {
            crate::discover::expected_is_kani_ice(exp)
                || crate::quarantine::compile_fail_oracle(unit.suite, unit.rel)
                    .is_some_and(|e| e.upstream_ice && exp.contains(e.expected_quote))
        }),
    };
    let scored = match unit.engine {
        Engine::TrustMc => classify(&ctx, result, &combined),
        Engine::Kani => classify_kani(&ctx, result, &combined),
    };
    result.tiebreak_applied = scored.tiebreak_applied;
    // Explicit corpus quarantine: a manifest-listed un-compilable source that
    // (as expected) produced an `Error` row is the corpus's failure, not
    // trust-mc's — reclassify to the visible `corpus_invalid` column with the
    // manifest's evidence. Verdict-bearing runs are never touched.
    let (class, evidence) =
        crate::quarantine::apply_corpus_quarantine(scored.class, unit.suite, unit.rel);
    // The route decides last, after the corpus quarantine: output that did not
    // come from the attested route (a driver refusal, no route marker, a marker
    // naming another trustc, backend or KEY) is the measurement's failure. It is
    // never parity, never an unknown, and never a quarantined corpus file.
    if routed {
        if let Err(why) = check_route_output(unit.route, unit.route_attestation, &combined) {
            result.classification = Some(Classification::Error);
            result.tiebreak_applied = false;
            result.note = format!("route-error: {why}");
            if attempt.retried_after_outer_timeout {
                result.note = format!("{} [retried-after-outer-timeout]", result.note);
            }
            return;
        }
    }
    result.classification = Some(class);
    result.note = match evidence {
        Some(evidence) => format!("corpus-invalid (not a trust-mc failure): {evidence}"),
        None => {
            let note = note_for(result, &ctx, &combined, scored);
            // A Kani row compiletest would never have produced: no upstream
            // verdict exists for a `fixme` / `ignore` path, so a miss there
            // is not a miss against Kani's own regression suite.
            if unit.engine == Engine::Kani && class != Classification::Parity && unit.upstream_ignored {
                format!("{note} [Kani's compiletest skips this path (`fixme`/`ignore` in it)]")
                    .trim_start()
                    .to_string()
            } else {
                note
            }
        }
    };
    if attempt.retried_after_outer_timeout {
        result.note = format!("{} [retried-after-outer-timeout]", result.note);
    }
}

/// The exact invocation a `Command` describes: argv, cwd, the variables it
/// sets and the ones it removes — what the unit log records.
fn describe_command(cmd: &Command) -> (Vec<String>, Option<String>, Vec<(String, String)>, Vec<String>) {
    let lossy = |o: &std::ffi::OsStr| o.to_string_lossy().into_owned();
    let mut argv = vec![lossy(cmd.get_program())];
    argv.extend(cmd.get_args().map(lossy));
    let cwd = cmd.get_current_dir().map(|p| p.display().to_string());
    let mut set = Vec::new();
    let mut removed = Vec::new();
    for (k, v) in cmd.get_envs() {
        match v {
            Some(v) => set.push((lossy(k), lossy(v))),
            None => removed.push(lossy(k)),
        }
    }
    (argv, cwd, set, removed)
}

/// Run a single test and classify it.
fn run_one(env: &Env, test: &Discovered, cfg: &RunConfig) -> TestResult {
    let mut result = TestResult::blank(&test.suite, &test.rel, test.oracle);
    // The compiler route is the trust-mc driver's (`--route`). Upstream Kani
    // compiles with its own toolchain, so its rows carry no route and nothing
    // is checked against one.
    let (unit_route, route_attestation) = match cfg.engine {
        Engine::TrustMc => (Some(cfg.route_engine.route()), cfg.route_engine.engine().attest()),
        Engine::Kani => (None, None),
    };
    result.route = unit_route.map(|r| r.as_str().to_string());

    let flags = match &env.engine {
        EngineEnv::TrustMc(_) => sanitize_flags(&test.flags, cfg),
        EngineEnv::Kani(_) => kani_flags(&test.flags, &test.cbmc_flags, cfg),
    };
    result.flags = flags.clone();

    // Per-test isolated target dir (avoids rmeta/smt2 write collisions).
    let iso = env
        .build_base_for(unit_route.unwrap_or_default(), &cfg.backend)
        .join(&test.suite)
        .join(test.rel.replace('/', "_").trim_end_matches(".rs"))
        .join("target");
    std::fs::create_dir_all(&iso).ok();

    // Native surface: mechanically re-key the unit to `#[kani::harness]`
    // where expressible (single-file units only); record the provenance
    // either way. Legacy surface leaves everything byte-identical.
    let mut run_abs = test.abs.clone();
    if cfg.surface == Surface::Native {
        let outcome = match &test.kind {
            EntryKind::CargoPackage { .. } => {
                // Cargo units span whole packages; re-keying them would mean
                // rewriting package sources in place. Out of the certain
                // fragment — run legacy with a recorded reason.
                Rekey::Legacy { reason: "cargo_unit".to_string() }
            }
            EntryKind::SingleFile { .. } => match std::fs::read_to_string(&test.abs) {
                Ok(src) => rekey_source(&src),
                Err(_) => Rekey::Legacy { reason: "read_error".to_string() },
            },
        };
        result.rekey = Some(outcome.provenance());
        if let Rekey::Native { source, rewritten, .. } = outcome {
            if rewritten > 0 {
                // Compile the rewritten copy from the per-test isolated dir
                // (cleaned up with it); the original corpus stays untouched.
                let dir = iso.parent().unwrap_or(&iso).join("native");
                let file = dir.join(test.abs.file_name().unwrap_or_default());
                if std::fs::create_dir_all(&dir).is_ok() && std::fs::write(&file, &source).is_ok()
                {
                    run_abs = file;
                } else {
                    result.rekey = Some("rekey:legacy(rewrite_io_error)".to_string());
                }
            }
        }
    }

    // PATH with the engine's own directory prepended — the ay binary's for
    // trust-mc (SMT path resolves `ay`), the `kani` launcher's for Kani (that
    // is `~/.cargo/bin`, which also holds the rustup proxies Kani's driver
    // calls `cargo`/`rustc` through) — and, for cargo units, the cargo
    // binary's directory (both drivers shell out to `cargo`).
    let mut path = std::env::var_os("PATH").unwrap_or_default();
    {
        let mut parts: Vec<PathBuf> = Vec::new();
        let engine_dir = match &env.engine {
            EngineEnv::TrustMc(tm) => tm.ay.parent(),
            EngineEnv::Kani(k) => k.kani.parent(),
        };
        if let Some(dir) = engine_dir {
            parts.push(dir.to_path_buf());
        }
        if let Some(cargo_dir) = env.cargo.as_deref().and_then(|c| c.parent()) {
            parts.push(cargo_dir.to_path_buf());
        }
        parts.extend(std::env::split_paths(&path));
        if let Ok(joined) = std::env::join_paths(parts) {
            path = joined;
        }
    }

    let scrubbed = crate::env::scrubbed_child_env_present();

    // Built as a closure so an outer-watchdog kill can be RETRIED once; see the
    // retry below for why that is a measurement fix, not budget laundering.
    let build_cmd = || {
        match &env.engine {
            EngineEnv::TrustMc(tm) => {
                let kani_dir = env.kani_dir();
                let (unit, cwd, outer_timeout) = match &test.kind {
                    // Run from the Kani checkout root, mirroring Kani's own harness.
                    // Test headers declare paths RELATIVE to that root, e.g.
                    // `// kani-flags: -Z c-ffi --c-lib tests/kani/ForeignItems/lib.c`.
                    // Without this the child inherits the runner's cwd
                    // (tools/kani-domination), the path resolves to nothing, and the
                    // driver silently ingests an EMPTY C library — so the row cannot
                    // distinguish "the C-body lane is inert" from "the C-body lane is
                    // never reached". A corpus that cannot fail is not evidence.
                    EntryKind::SingleFile { harness_count } => {
                        (UnitArg::File(&run_abs), kani_dir.as_path(), cfg.outer_timeout(*harness_count))
                    }
                    // Invoke the driver in its `cargo trust-mc` identity (argv[1] =
                    // `trust-mc`) inside the package dir, mirroring Kani's
                    // `run_cargo_kani_test`: `--harness <stem>` unless the expected
                    // file is the package-wide `expected`.
                    EntryKind::CargoPackage { manifest_dir, harness, harness_count } => (
                        UnitArg::Cargo { harness: harness.as_deref() },
                        manifest_dir.as_path(),
                        cfg.cargo_outer_timeout(*harness_count),
                    ),
                };
                // Measure the verifier, not the shell that launched the runner: the
                // toolchain and cargo-build selectors it may carry are removed (see
                // `env::SCRUBBED_CHILD_ENV`) before the child's own environment is
                // set. `RUSTUP_TOOLCHAIN` is among them and is never set again: the
                // driver resolves the toolchain its compiler links. The route
                // (`--route`) adds its arguments and decides `TRUST_MC_SYSROOT`.
                let invocation = DriverInvocation {
                    driver: &tm.verifier,
                    unit,
                    flags: &flags,
                    cwd,
                    target_dir: &iso,
                    devcli_sysroot: &tm.sysroot,
                    path_env: &path,
                    ay: &tm.ay,
                    rustflags: &test.rustflags,
                    scrubbed: &scrubbed,
                    jobs: cfg.jobs,
                };
                (cfg.route_engine.engine().command(&invocation), outer_timeout)
            }
            EngineEnv::Kani(k) => {
                let (mut cmd, outer_timeout) = match &test.kind {
                    EntryKind::SingleFile { harness_count } => {
                        // `kani <file> --target-dir <iso> <kani-flags…>`, Kani's
                        // compiletest `run_kani` spelling plus the isolated target
                        // dir (see `kani_single_file_args` for why it goes BEFORE
                        // the flags), from the checkout root: compiletest sets no
                        // cwd and its regression script runs from the repo root,
                        // and it is the cwd the trust-mc lane uses, so header paths
                        // resolve identically under both engines. Kani consumes
                        // `--cbmc-args` itself; nothing is stripped (see
                        // `kani_flags`).
                        let mut cmd = Command::new(&k.kani);
                        cmd.args(kani_single_file_args(&run_abs, &iso, &flags)).current_dir(env.kani_dir());
                        (cmd, cfg.outer_timeout(*harness_count))
                    }
                    EntryKind::CargoPackage { manifest_dir, harness, harness_count } => {
                        // `cargo kani --target-dir <iso> [--harness <stem>]` in the
                        // package dir, as compiletest's `run_cargo_kani_test` does,
                        // invoked through the `cargo-kani` binary itself (argv[1] =
                        // `kani`, the spelling cargo hands it) so no cargo subcommand
                        // lookup can pick a different Kani than the one attested.
                        let mut cmd = Command::new(&k.cargo_kani);
                        cmd.arg("kani").arg("--target-dir").arg(&iso).current_dir(manifest_dir);
                        if let Some(h) = harness {
                            cmd.args(["--harness", h]);
                        }
                        cmd.args(&flags);
                        (cmd, cfg.cargo_outer_timeout(*harness_count))
                    }
                };
                // As above: the selectors are removed first, and the `kani`
                // launcher selects the nightly its install was built for.
                for key in &scrubbed {
                    cmd.env_remove(key);
                }
                crate::env::kani_child_env(&mut cmd, k.launcher_home.as_deref());
                // Uniform with the trust-mc child; upstream Kani ignores it.
                cmd.env("PATH", &path)
                    .env(crate::route::JOBS_ENV, cfg.jobs.to_string())
                    .stdin(Stdio::null())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped());
                if !test.rustflags.is_empty() {
                    cmd.env("RUSTFLAGS", test.rustflags.join(" "));
                }
                (cmd, outer_timeout)
            }
        }
    };

    // The unit's identity for the scorer and its log. The expected file is
    // read once and embedded in the log, so a rescore reads the same bytes.
    let expected_content =
        test.expected_path.as_deref().and_then(|p| std::fs::read_to_string(p).ok());
    let is_cargo = matches!(test.kind, EntryKind::CargoPackage { .. });
    let unit = UnitCtx {
        engine: cfg.engine,
        suite: &test.suite,
        rel: &test.rel,
        oracle: test.oracle,
        is_cargo,
        check_fail: test.check_fail,
        expected: expected_content.as_deref(),
        route: unit_route.unwrap_or_default(),
        route_attestation,
        upstream_ignored: test.upstream_ignored,
    };
    let log_name = unitlog::log_file_name(&test.rel);
    let log_abs = cfg.log_dir.join(&test.suite).join(&log_name);
    let log_rel = format!("{}/{}/{}", cfg.log_rel_prefix, test.suite, log_name);
    let record = |result: &mut TestResult, log: UnitLog| match unitlog::write(&log_abs, &log) {
        Ok(()) => result.log_path = Some(log_rel.clone()),
        Err(e) => {
            // A row without its log is visible as such, never silently bare.
            result.log_path = None;
            result.note = format!("{} [log-write-failed: {e}]", result.note);
        }
    };

    let start = Instant::now();
    let (cmd, outer_timeout) = build_cmd();
    let (argv, cwd, env_set, env_removed) = describe_command(&cmd);
    let mut log = UnitLog {
        scorer_version: SCORER_VERSION,
        engine: cfg.engine,
        route: result.route.clone(),
        suite: test.suite.clone(),
        file: test.rel.clone(),
        oracle: test.oracle,
        is_cargo,
        check_fail: test.check_fail,
        upstream_ignored: test.upstream_ignored,
        argv,
        cwd,
        env_set,
        env_removed,
        spawn_error: None,
        exit_code: None,
        timed_out: false,
        retried_after_outer_timeout: false,
        wall_ms: 0,
        max_rss_kb: 0,
        tree_peak_rss_kb: None,
        expected_path: test.expected_path.as_deref().map(|p| p.display().to_string()),
        expected: expected_content.clone(),
        stdout: String::new(),
        stderr: String::new(),
        first_attempt: None,
    };
    // A route whose artifacts failed the runner's preflight measures nothing:
    // every unit is an `error` row and the driver is never spawned. The row
    // still gets its log (naming the command that did not run), so `rescore`
    // reads every row of the file and reaches the same verdict.
    if let Some(att) = route_attestation.filter(|a| !a.preflight_errors.is_empty()) {
        let attempt = Attempt {
            stdout: "",
            stderr: "",
            exit_code: None,
            timed_out: false,
            retried_after_outer_timeout: false,
            spawn_error: None,
        };
        score_unit(&unit, &attempt, &mut result);
        log.spawn_error =
            Some(format!("route preflight failed, driver not run: {}", att.preflight_errors.join("; ")));
        drop(cmd);
        record(&mut result, log);
        let _ = std::fs::remove_dir_all(iso.parent().unwrap_or(&iso));
        return result;
    }
    let mut run = match spawn_with_timeout(cmd, outer_timeout) {
        Ok(v) => v,
        Err(e) => {
            let err = e.to_string();
            let attempt = Attempt {
                stdout: "",
                stderr: "",
                exit_code: None,
                timed_out: false,
                retried_after_outer_timeout: false,
                spawn_error: Some(&err),
            };
            score_unit(&unit, &attempt, &mut result);
            result.duration_ms = start.elapsed().as_millis() as u64;
            log.spawn_error = Some(err);
            record(&mut result, log);
            let _ = std::fs::remove_dir_all(iso.parent().unwrap_or(&iso));
            return result;
        }
    };
    // RETRY ONCE ON AN OUTER-WATCHDOG KILL.
    //
    // The outer watchdog is a harness-level backstop, not a verdict. With
    // `--jobs N` the corpus runs N tests concurrently, and a large fraction of
    // this corpus sits at 40-80s against a 105s ceiling, so a load spike from
    // co-scheduled peers pushes an otherwise-passing row over the edge and it
    // is recorded as `unknown`. MEASURED: `arbitrary/enums/main.rs` (52s),
    // `function-contract/history/block.rs` (52s) and
    // `bounded-arbitrary/reverse_vec/vec.rs` (79s) each answered CORRECTLY when
    // re-run alone, having been killed at 102s/55s/110s inside a 3-job run.
    // Attributing those flips to a code change is simply wrong, and it has
    // burned real debugging time.
    //
    // This is NOT extra budget: the retry gets the SAME `outer_timeout`, so a
    // row that genuinely needs longer still fails. It only removes the
    // dependence on what happened to be running alongside it. Retries are
    // recorded in the note so the number stays auditable, and the killed
    // attempt's output is kept in the log after the classified one.
    let mut retried_after_outer_timeout = false;
    if run.timed_out {
        retried_after_outer_timeout = true;
        let (cmd2, outer_timeout2) = build_cmd();
        if let Ok(second) = spawn_with_timeout(cmd2, outer_timeout2) {
            let killed = std::mem::replace(&mut run, second);
            log.first_attempt = Some((killed.stdout, killed.stderr));
        }
    }
    // `duration_ms` is the whole unit (both attempts on a retry); the resource
    // fields describe the attempt whose output is classified below.
    result.duration_ms = start.elapsed().as_millis() as u64;
    result.wall_ms = run.wall_ms;
    result.max_rss_kb = run.max_rss_kb;
    result.tree_peak_rss_kb = run.tree_peak_rss_kb;

    let attempt = Attempt {
        stdout: &run.stdout,
        stderr: &run.stderr,
        exit_code: run.exit_code,
        timed_out: run.timed_out,
        retried_after_outer_timeout,
        spawn_error: None,
    };
    score_unit(&unit, &attempt, &mut result);

    log.exit_code = run.exit_code;
    log.timed_out = run.timed_out;
    log.retried_after_outer_timeout = retried_after_outer_timeout;
    log.wall_ms = run.wall_ms;
    log.max_rss_kb = run.max_rss_kb;
    log.tree_peak_rss_kb = run.tree_peak_rss_kb;
    log.stdout = run.stdout;
    log.stderr = run.stderr;
    record(&mut result, log);
    // Reclaim the per-test artifact dir (rmeta/rlib/smt2) — the verdict is
    // captured, so ~20MB/test * thousands of tests need not accumulate.
    let _ = std::fs::remove_dir_all(iso.parent().unwrap_or(&iso));
    result
}

/// The driver flag that runs an off-pin `ay` (demoting every success).
pub const UNPINNED_AY_FLAG: &str = "--allow-unpinned-ay";

/// Printed by the driver for every harness that ran on an off-pin `ay`.
const SOLVER_PIN_MISMATCH_MARKER: &str = "[AY:SOLVER_PIN_MISMATCH:";

/// Build the final verifier flag list from the raw kani-flags + config.
fn sanitize_flags(raw: &[String], cfg: &RunConfig) -> Vec<String> {
    let mut kept = Vec::new();
    let mut has_unstable = false;
    let mut has_htimeout = false;
    let mut has_chc = false;
    let mut i = 0;
    while i < raw.len() {
        let f = &raw[i];
        if f == UNPINNED_AY_FLAG {
            // A row must come from the pinned solver: never let a test header
            // opt a verifier child into an off-pin `ay` (the environment
            // spelling is scrubbed in `env::SCRUBBED_CHILD_ENV`).
            i += 1;
            continue;
        }
        if cfg.strip_cbmc && f == "--cbmc-args" {
            break; // CBMC consumes the remainder; the AY backend ignores it.
        }
        if f == "-Z" && raw.get(i + 1).map(String::as_str) == Some("unstable-options") {
            has_unstable = true;
            kept.push(f.clone());
            kept.push(raw[i + 1].clone());
            i += 2;
            continue;
        }
        if f.starts_with("--harness-timeout") {
            has_htimeout = true;
        }
        if f == "--ay-chc" || f.starts_with("--ay-chc=") {
            has_chc = true;
        }
        kept.push(f.clone());
        i += 1;
    }

    let mut out = Vec::new();
    if !has_unstable {
        out.push("-Z".to_string());
        out.push("unstable-options".to_string());
    }
    out.extend(kept);
    if cfg.backend == "chc" && !has_chc {
        out.push("--ay-chc".to_string());
    }
    if !has_htimeout {
        out.push(format!("--harness-timeout={}s", cfg.harness_timeout_s));
    }
    // Appended last so an operator-supplied knob wins over the corpus's own
    // kani-flags, and so an A/B of a backend default needs no runner edit.
    // Never the off-pin solver switch (`cmd_run` refuses it up front; this is
    // the backstop for any other caller).
    out.extend(cfg.extra_driver_flags.iter().filter(|f| f.as_str() != UNPINNED_AY_FLAG).cloned());
    out
}

/// The Kani single-file argv: `<file> --target-dir <iso> <flags…>`.
///
/// The isolated target dir goes BEFORE the header flags. `--cbmc-args`
/// swallows every argument after it (Kani hands that tail to CBMC verbatim),
/// so a `--target-dir` appended after the flags reached CBMC on every unit
/// with a `cbmc-flags` header or a `--cbmc-args` tail — 14 of the 1126
/// verification-scope units — and CBMC refused it: `Usage error! Unknown
/// option: --target-dir`, `CBMC failed with status 64`, `VERIFICATION:-
/// FAILED`. Measured 2026-09-13 on `kani/Vectors/vector_extend_in_new.rs`
/// (`cbmc-flags: --unwinding-assertions`): FAILED with the flag after the
/// tail, SUCCESSFUL with it before. compiletest's `run_kani` passes no
/// `--target-dir` at all, so its argv ends with the CBMC tail.
fn kani_single_file_args(file: &Path, iso: &Path, flags: &[String]) -> Vec<OsString> {
    let mut argv: Vec<OsString> = vec![file.into(), "--target-dir".into(), iso.into()];
    argv.extend(flags.iter().map(OsString::from));
    argv
}

/// The Kani engine's flag list for a unit: the header's `kani-flags`
/// verbatim — Kani consumes `--cbmc-args` itself, so nothing is stripped and
/// no `-Z unstable-options` / `--ay-chc` / `--harness-timeout` is injected —
/// with the operator's extra flags inserted BEFORE any `--cbmc-args`
/// (everything after it belongs to CBMC), and the `cbmc-flags` header
/// appended the way compiletest's `run_kani` does
/// (`-Zunstable-options --cbmc-args …`).
///
/// No per-harness timeout on purpose: Kani runs its own corpus the way its
/// compiletest runs it, under the outer watchdog only, so its verdicts are the
/// reference and not a budget-shaped variant of it.
fn kani_flags(raw: &[String], cbmc_flags: &[String], cfg: &RunConfig) -> Vec<String> {
    let split = raw.iter().position(|f| f == "--cbmc-args").unwrap_or(raw.len());
    let mut out: Vec<String> = raw[..split].to_vec();
    out.extend(cfg.extra_driver_flags.iter().cloned());
    out.extend(raw[split..].iter().cloned());
    if !cbmc_flags.is_empty() {
        if split == raw.len() {
            out.push("-Zunstable-options".to_string());
            out.push("--cbmc-args".to_string());
        }
        out.extend(cbmc_flags.iter().cloned());
    }
    out
}

/// What one spawned attempt produced, with its resource accounting.
pub struct ChildRun {
    pub stdout: String,
    pub stderr: String,
    /// Exit code; `None` when the child died on a signal (a watchdog kill
    /// included).
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    /// Spawn to reap, milliseconds.
    pub wall_ms: u64,
    /// `ru_maxrss` from `wait4`, KB (see `TestResult::max_rss_kb`).
    pub max_rss_kb: u64,
    /// Sampled tree peak, KB; `None` off Linux (see `TestResult::tree_peak_rss_kb`).
    pub tree_peak_rss_kb: Option<u64>,
}

/// Spawn a child in its own process group, drain stdout/stderr concurrently,
/// poll it every 50 ms (sampling the resident memory of its whole process
/// tree at each poll), reap it with `wait4` for its exact `ru_maxrss`, and
/// kill the WHOLE group (plus every descendant the `/proc` walk can still
/// see) if it runs past `timeout`.
///
/// Killing only the direct child, as this did before, left the driver's
/// compiler and solver subtree running after an outer-watchdog kill — the
/// orphan population documented in
/// `docs/findings/2026-08-24-external-cancellation-orphans-the-solver-tree.md`,
/// whose background load skewed the very timings this tool records. A child
/// in its own group is also outside the terminal's foreground group, so the
/// runner forwards SIGINT/SIGTERM/SIGHUP to every live group itself
/// (`live_children`), otherwise Ctrl-C would orphan the same trees.
fn spawn_with_timeout(mut cmd: Command, timeout: Duration) -> anyhow::Result<ChildRun> {
    use std::os::unix::process::CommandExt;
    // The child becomes its group's leader: pgid == pid, so `kill(-pid)`
    // reaches everything it spawns that does not leave the group.
    cmd.process_group(0);
    let start = Instant::now();
    let mut child = cmd.spawn()?;
    let pid = child.id() as libc::pid_t;
    let _registered = live_children::register(pid);
    let mut so = child.stdout.take().expect("piped stdout");
    let mut se = child.stderr.take().expect("piped stderr");
    let t_out = std::thread::spawn(move || {
        let mut b = Vec::new();
        let _ = so.read_to_end(&mut b);
        b
    });
    let t_err = std::thread::spawn(move || {
        let mut b = Vec::new();
        let _ = se.read_to_end(&mut b);
        b
    });

    let deadline = start + timeout;
    let mut timed_out = false;
    // Sampled before every poll, the first one right after the spawn; a unit
    // that exits inside the first interval may still never be sampled, which
    // the floor below covers.
    let mut tree_peak: u64 = 0;
    let (exit, rusage) = loop {
        if let Some(sum) = process_tree::sample_peak_kb(pid as u32) {
            tree_peak = tree_peak.max(sum);
        }
        if let Some(reaped) = reap(pid, libc::WNOHANG)? {
            break reaped;
        }
        if Instant::now() >= deadline {
            kill_process_tree(pid);
            timed_out = true;
            // The group is dead; the leader is at most a zombie now, so this
            // blocking reap returns at once.
            break reap(pid, 0)?.expect("a blocking wait4 on a live child returns it");
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let wall_ms = start.elapsed().as_millis() as u64;
    let max_rss_kb = maxrss_kb(&rusage);
    let stdout = String::from_utf8_lossy(&t_out.join().unwrap_or_default()).into_owned();
    let stderr = String::from_utf8_lossy(&t_err.join().unwrap_or_default()).into_owned();
    Ok(ChildRun {
        stdout,
        stderr,
        exit_code: exit,
        timed_out,
        wall_ms,
        max_rss_kb,
        // Linux only. Floored at the exact `ru_maxrss`: a sampled sum never
        // reports less than the peak of a process it certainly contained,
        // and a unit too short to be sampled at all still gets that.
        tree_peak_rss_kb: cfg!(target_os = "linux").then(|| tree_peak.max(max_rss_kb)),
    })
}

/// `wait4(pid)`: `Ok(None)` while the child runs (with `WNOHANG`),
/// `Ok(Some((exit code or None on a signal, rusage)))` once reaped.
fn reap(pid: libc::pid_t, flags: libc::c_int) -> anyhow::Result<Option<(Option<i32>, libc::rusage)>> {
    let mut status: libc::c_int = 0;
    // SAFETY: `rusage` is plain data that `wait4` fills in; a zeroed value is
    // a valid one.
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    loop {
        // SAFETY: `status` and `ru` outlive the call and are exclusively
        // borrowed; `pid` is a child of this process that nothing else waits on.
        let r = unsafe { libc::wait4(pid, &mut status, flags, &mut ru) };
        if r == pid {
            break;
        }
        if r == 0 {
            return Ok(None);
        }
        let err = std::io::Error::last_os_error();
        if err.raw_os_error() == Some(libc::EINTR) {
            continue;
        }
        return Err(anyhow::Error::from(err).context(format!("wait4({pid})")));
    }
    let code = if libc::WIFEXITED(status) { Some(libc::WEXITSTATUS(status)) } else { None };
    Ok(Some((code, ru)))
}

/// `ru_maxrss` normalized to KB: Linux reports KB, macOS bytes.
fn maxrss_kb(ru: &libc::rusage) -> u64 {
    let raw = ru.ru_maxrss.max(0) as u64;
    if cfg!(target_os = "macos") { raw / 1024 } else { raw }
}

/// SIGKILL the leader's whole process group and every descendant the `/proc`
/// walk can still see (a solver the driver moved into its own group is a
/// descendant but not a group member). Enumerated BEFORE the group kill: once
/// the leader dies its children are reparented and the walk cannot find them.
fn kill_process_tree(leader: libc::pid_t) {
    let descendants = process_tree::descendants(leader as u32);
    // SAFETY: plain signal sends; a negative pid addresses the process group.
    unsafe {
        libc::kill(-leader, libc::SIGKILL);
    }
    for pid in descendants {
        if pid as libc::pid_t != leader {
            // SAFETY: as above.
            unsafe {
                libc::kill(pid as libc::pid_t, libc::SIGKILL);
            }
        }
    }
}

/// The process groups of every child currently being waited on, kept in a
/// fixed table of atomics so a signal handler can read it without taking a
/// lock (the failure mode the findings doc describes for `try_lock`). On
/// SIGINT/SIGTERM/SIGHUP the runner SIGKILLs every registered group, restores
/// the default disposition and re-raises, so it still dies with the
/// conventional signal status and leaves no verifier tree behind.
mod live_children {
    use std::sync::Once;
    use std::sync::atomic::{AtomicI32, Ordering};

    const SLOTS: usize = 256;
    static LIVE: [AtomicI32; SLOTS] = [const { AtomicI32::new(0) }; SLOTS];
    static INSTALL: Once = Once::new();

    /// Clears its slot when dropped (the child has been reaped by then).
    pub struct Registration(Option<usize>);

    impl Drop for Registration {
        fn drop(&mut self) {
            if let Some(i) = self.0 {
                LIVE[i].store(0, Ordering::SeqCst);
            }
        }
    }

    pub fn register(pid: libc::pid_t) -> Registration {
        INSTALL.call_once(|| {
            let handler = forward as extern "C" fn(libc::c_int) as libc::sighandler_t;
            for sig in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
                // SAFETY: installing an async-signal-safe handler (it only
                // reads atomics and calls kill/signal/raise).
                unsafe {
                    libc::signal(sig, handler);
                }
            }
        });
        for (i, slot) in LIVE.iter().enumerate() {
            if slot.compare_exchange(0, pid, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                return Registration(Some(i));
            }
        }
        // More live children than slots: this one is not forwarded to.
        Registration(None)
    }

    /// Whether `pid` holds a slot right now (tests).
    #[cfg(test)]
    pub fn is_registered(pid: libc::pid_t) -> bool {
        LIVE.iter().any(|s| s.load(Ordering::SeqCst) == pid)
    }

    extern "C" fn forward(sig: libc::c_int) {
        for slot in LIVE.iter() {
            let pid = slot.load(Ordering::SeqCst);
            if pid > 0 {
                // SAFETY: async-signal-safe; addresses the child's group.
                unsafe {
                    libc::kill(-pid, libc::SIGKILL);
                }
            }
        }
        // SAFETY: async-signal-safe; re-raise with the default disposition.
        unsafe {
            libc::signal(sig, libc::SIG_DFL);
            libc::raise(sig);
        }
    }
}

/// The process tree under a child, read from Linux `/proc`: descendants by
/// parent links (`/proc/<pid>/task/<tid>/children`, or a full `/proc` scan
/// where the kernel lacks `CONFIG_PROC_CHILDREN`) and each one's `VmHWM`, the
/// high-water resident set of that process so far.
mod process_tree {
    #[cfg(target_os = "linux")]
    use std::path::Path;

    /// `root` and every process below it that is alive right now. Only
    /// `root` itself off Linux.
    #[cfg(target_os = "linux")]
    pub fn descendants(root: u32) -> Vec<u32> {
        if !children_files_supported() {
            return descendants_by_scan(root);
        }
        let mut seen = vec![root];
        let mut queue = vec![root];
        while let Some(p) = queue.pop() {
            for k in children_of(p) {
                if !seen.contains(&k) {
                    seen.push(k);
                    queue.push(k);
                }
            }
        }
        seen
    }

    #[cfg(not(target_os = "linux"))]
    pub fn descendants(root: u32) -> Vec<u32> {
        vec![root]
    }

    /// The sum of `VmHWM` over the live tree under `root`, KB. `None` off
    /// Linux, or once nothing in the tree can be read (it has exited).
    #[cfg(target_os = "linux")]
    pub fn sample_peak_kb(root: u32) -> Option<u64> {
        let mut any = false;
        let mut sum = 0;
        for pid in descendants(root) {
            if let Some(kb) = vm_hwm_kb(pid) {
                any = true;
                sum += kb;
            }
        }
        any.then_some(sum)
    }

    #[cfg(not(target_os = "linux"))]
    pub fn sample_peak_kb(_root: u32) -> Option<u64> {
        None
    }

    #[cfg(target_os = "linux")]
    fn children_files_supported() -> bool {
        static SUPPORTED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *SUPPORTED.get_or_init(|| {
            let me = std::process::id();
            Path::new(&format!("/proc/{me}/task/{me}/children")).exists()
        })
    }

    /// Direct children of `pid`: the union over its threads' `children`
    /// files (a child is listed under the thread that forked it). Empty once
    /// the process is gone.
    #[cfg(target_os = "linux")]
    fn children_of(pid: u32) -> Vec<u32> {
        let mut out = Vec::new();
        let Ok(tasks) = std::fs::read_dir(format!("/proc/{pid}/task")) else { return out };
        for task in tasks.flatten() {
            if let Ok(text) = std::fs::read_to_string(task.path().join("children")) {
                out.extend(text.split_whitespace().filter_map(|t| t.parse::<u32>().ok()));
            }
        }
        out
    }

    /// Fallback without `children` files: one pass over `/proc/*/stat`, then
    /// a parent-link walk from `root`, plus any member of `root`'s process
    /// group the walk cannot reach (already reparented).
    #[cfg(target_os = "linux")]
    fn descendants_by_scan(root: u32) -> Vec<u32> {
        let mut entries: Vec<(u32, u32, u32)> = Vec::new();
        let Ok(procs) = std::fs::read_dir("/proc") else { return vec![root] };
        for entry in procs.flatten() {
            let Some(pid) = entry.file_name().to_str().and_then(|n| n.parse::<u32>().ok()) else { continue };
            if let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) {
                if let Some((ppid, pgrp)) = parse_stat_ppid_pgrp(&stat) {
                    entries.push((pid, ppid, pgrp));
                }
            }
        }
        let mut seen = vec![root];
        let mut queue = vec![root];
        while let Some(p) = queue.pop() {
            for (pid, ppid, _) in &entries {
                if *ppid == p && !seen.contains(pid) {
                    seen.push(*pid);
                    queue.push(*pid);
                }
            }
        }
        for (pid, _, pgrp) in &entries {
            if *pgrp == root && !seen.contains(pid) {
                seen.push(*pid);
            }
        }
        seen
    }

    /// `(ppid, pgrp)` from a `/proc/<pid>/stat` line. The command name is
    /// parenthesized and may itself contain spaces or parentheses, so the
    /// fields are taken after the LAST `)`: state, ppid, pgrp, ...
    pub fn parse_stat_ppid_pgrp(stat: &str) -> Option<(u32, u32)> {
        let tail = &stat[stat.rfind(')')? + 1..];
        let mut fields = tail.split_whitespace();
        let _state = fields.next()?;
        let ppid = fields.next()?.parse().ok()?;
        let pgrp = fields.next()?.parse().ok()?;
        Some((ppid, pgrp))
    }

    /// The state character of a `/proc/<pid>/stat` line (`Z` = zombie).
    #[cfg(test)]
    pub fn parse_stat_state(stat: &str) -> Option<char> {
        let tail = &stat[stat.rfind(')')? + 1..];
        tail.split_whitespace().next()?.chars().next()
    }

    #[cfg(target_os = "linux")]
    fn vm_hwm_kb(pid: u32) -> Option<u64> {
        parse_vm_hwm_kb(&std::fs::read_to_string(format!("/proc/{pid}/status")).ok()?)
    }

    /// The `VmHWM:` line of `/proc/<pid>/status`, KB. Absent for a kernel
    /// thread or a zombie, whose resident set is gone.
    pub fn parse_vm_hwm_kb(status: &str) -> Option<u64> {
        status
            .lines()
            .find_map(|l| l.strip_prefix("VmHWM:"))
            .and_then(|v| v.split_whitespace().next())
            .and_then(|n| n.parse().ok())
    }
}

/// File-level observed verdict: any FAILED => Fail; else any bare UNVALIDATED (a
/// demoted per-harness verdict the driver could not independently validate,
/// e.g. `VERIFICATION:- UNVALIDATED (DT+BV)`, which is not a success at all) =>
/// Unknown — an unvalidated harness must never let the file score as an
/// observed Success; else any SUCCESSFUL => Success; else Unknown.
///
/// `VERIFICATION:- SUCCESSFUL (UNVALIDATED)` (a non-linear logic tier, or an
/// off-pin `ay` accepted under --allow-unpinned-ay) is different: it IS a
/// success claim, and the driver exits 0 on it by default. It stays Success
/// here so a Fail oracle still scores it `missed_bug`; [`clean_success`]
/// refuses it, so it can never earn `parity` or `exceeds_oracle` credit, and
/// [`classify`] refuses every row that ran on an off-pin solver outright.
///
/// Regression context (2026-07-19): kani/SIMD/portable_simd.rs classified
/// `unsound_pass` because check_mask emitted the bare UNVALIDATED verdict
/// (unknown to this parser), the two sibling harnesses were SUCCESSFUL, and
/// the file therefore aggregated to observed=Success while `clean_success`
/// correctly saw the fallback taint. The verdict-string set here must track
/// the driver's `verification_result` output strings.
///
/// A file-level SUCCESS needs EVERY harness to report SUCCESSFUL
/// ([`harness_without_success`]): until 2026-09-14 one SUCCESSFUL line was
/// enough, so a file whose other harnesses were `INCONCLUSIVE` read as a
/// success — parity when nothing else in the output tainted it, and
/// `unsound_pass` when a self-report printed in the INCONCLUSIVE harness's
/// section happened to (the BMC lane's `kani/Intrinsics/Atomic/Stable/AtomicPtr/main.rs`
/// shape). Such a file is now `Unknown`.
fn parse_verdict(s: &str) -> Verdict {
    if s.contains("VERIFICATION:- FAILED") {
        Verdict::Fail
    } else if s.contains("VERIFICATION:- UNVALIDATED") {
        Verdict::Unknown
    } else if s.contains("VERIFICATION:- SUCCESSFUL") {
        if harness_without_success(s) { Verdict::Unknown } else { Verdict::Success }
    } else {
        Verdict::Unknown
    }
}

/// Some harness of the run did not report SUCCESSFUL: any
/// `VERIFICATION:- INCONCLUSIVE` line, or a `Checking harness` section with no
/// SUCCESSFUL verdict of its own (cut short, or a verdict this parser does not
/// know). Fail-closed: a run that cannot show every harness succeeding is not
/// a file-level success.
fn harness_without_success(s: &str) -> bool {
    s.contains("VERIFICATION:- INCONCLUSIVE")
        || split_harness_sections(s).iter().any(|(_, text)| !text.contains("VERIFICATION:- SUCCESSFUL"))
}

/// Tally the AY soundness/quality markers.
fn parse_markers(s: &str, r: &mut TestResult) {
    r.effective_success = s.contains("[AY:EFFECTIVE_SUCCESS:");
    r.proof_marker = s.contains("[AY:PROOF]");
    r.native_proof_accepted = s.contains("[AY:NATIVE_PROOF_GRADE:accepted");
    r.sound_fallback = sum_marker(s, "[AY:SOUND_FALLBACK:");
    r.ctrex_category = marker_value(s, "[AY:CTREX_CAT:");
    r.ctrex_categories_raw = marker_all_values(s, "[AY:CTREX_CAT:");
    r.translation_drops = marker_all_values(s, "[AY:TRANSLATION_DROP_REASON:");
    r.no_harnesses = s.contains("[AY:NO_HARNESSES]");
    r.vacuous = s.contains("[AY:VACUOUS");
    r.aggregate_gap_reasons = marker_all_values(s, "[AY:AGGREGATE_GAP_REASON:");
    r.unknown_reason = marker_value(s, "[AY:UNKNOWN_REASON:");
    let (category, detail) = parse_unknown_category(s);
    r.unknown_category = category;
    r.unknown_category_detail = detail;
    r.demotion_reasons = marker_csv_values(s, "[AY:DEMOTION_REASONS:");
    r.route_limitations = marker_all_values(s, "[AY:ROUTE_LIMITATION:");
    r.self_reported_unsound = self_reported_unsound(s);
    r.certified_no_checks = certified_no_checks(s);
    r.proof_qualifiers = proof_qualifier_list(s);
}

/// The driver's D16 qualifier for a harness settled as compiler-certified
/// obligation-free (`scripts/soundness-dual-gate.py`,
/// `CERTIFIED_NO_CHECKS_QUALIFIER`).
const CERTIFIED_NO_CHECKS_QUALIFIER: &str = "no_checks=compiler_certified_obligation_free";

/// The verdict line the driver prints for such a harness.
const CERTIFIED_NO_CHECKS_VERDICT: &str = "VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)";

/// How many harnesses the run settled as compiler-certified obligation-free:
/// the larger of the `[AY:PROOF_QUALIFIERS:…]` markers carrying the qualifier
/// and the verdict lines naming it, so a driver that prints only one of the
/// two is still counted.
fn certified_no_checks(s: &str) -> u32 {
    let mut markers = 0u32;
    let mut rest = s;
    while let Some(idx) = rest.find("[AY:PROOF_QUALIFIERS:") {
        let after = &rest[idx + "[AY:PROOF_QUALIFIERS:".len()..];
        let end = after.find(']').unwrap_or(after.len());
        markers += u32::from(after[..end].contains(CERTIFIED_NO_CHECKS_QUALIFIER));
        rest = &after[end..];
    }
    let lines = s.matches(CERTIFIED_NO_CHECKS_VERDICT).count() as u32;
    markers.max(lines)
}

// ---- proof qualifiers (scorer version 5) ------------------------------------
//
// The driver prints `[AY:PROOF_QUALIFIERS:<q>,<q>…]` once per harness whose
// result is a success (`trust-mc-driver/src/harness_runner.rs`,
// `proof_qualifiers_marker`): `clean` when the backend reported no qualifier,
// else the list. A qualifier is the driver saying the success is NOT a clean
// proof, so the scorer reads every one, attributes it to the `Checking harness`
// section that printed it, and fails closed on anything it does not know.

/// The marker's prefix.
const PROOF_QUALIFIERS_MARKER: &str = "[AY:PROOF_QUALIFIERS:";

/// `TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER` (`trust-mc-driver/src/call_ay/chc.rs`),
/// set by `interpret_chc_trivial_safe` (`call_ay/chc/native_result.rs`): the CHC
/// problem queries `error` and no rule derives it, so the driver short-circuits
/// to SUCCESSFUL without a solver and reports every registered property SUCCESS.
/// The compiler's straight-line discharge names that shape "registered
/// properties but no error rules (lost checks, not proved checks)"
/// (`trust-mc-compiler/src/codegen_ay/chc/straightline_proof.rs`).
const TRIVIAL_SAFE_QUALIFIER: &str = "trivial_safe=no_error_rule";

/// `UNATTRIBUTED_CHC_CHECK_QUALIFIER` (`trust-mc-driver/src/harness_runner.rs`):
/// every non-cover check of the success is the anonymous `chc.0` fallback, which
/// names no property, so the proof cannot show which assertions it covered.
const UNATTRIBUTED_CHECK_QUALIFIER: &str = "unattributed_check=chc.0";

/// The section name under which a qualifier printed outside every harness
/// section is reported (it cannot be attributed, so it counts for the file).
const OUTSIDE_EVERY_HARNESS: &str = "<outside every harness section>";

/// Why a SUCCESSFUL is not a clean proof, least severe first: a file whose
/// successful harnesses carry several scores under the most severe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SuccessTaint {
    /// `unattributed_check=chc.0`.
    Unattributed,
    /// `trivial_safe=no_error_rule`.
    TrivialSafe,
    /// A sound fallback (`[AY:SOUND_FALLBACK:…]` or the `sound_fallback=N`
    /// qualifier), an `(UNVALIDATED)` success, a self-reported unsoundness, an
    /// effective success other than a validated should_panic pass, or a proof
    /// qualifier this scorer does not recognise.
    Unsound,
}

impl SuccessTaint {
    fn class(self) -> Classification {
        match self {
            SuccessTaint::Unattributed => Classification::UnattributedPass,
            SuccessTaint::TrivialSafe => Classification::TrivialSafePass,
            SuccessTaint::Unsound => Classification::UnsoundPass,
        }
    }

    fn meaning(self) -> &'static str {
        match self {
            SuccessTaint::Unattributed => "the success rests only on the anonymous chc.0 check, which names no property",
            SuccessTaint::TrivialSafe => "no CHC rule derives error, so the driver reported SUCCESSFUL without solving; the compiler calls that shape lost checks, not proved checks",
            SuccessTaint::Unsound => "a sound fallback, or a proof qualifier this scorer does not recognise",
        }
    }
}

/// The value of every `[AY:PROOF_QUALIFIERS:…]` marker in `text`, in order.
fn proof_qualifier_markers(text: &str) -> Vec<&str> {
    let mut values = Vec::new();
    let mut rest = text;
    while let Some(idx) = rest.find(PROOF_QUALIFIERS_MARKER) {
        let after = &rest[idx + PROOF_QUALIFIERS_MARKER.len()..];
        let end = after.find(']').unwrap_or(after.len());
        values.push(&after[..end]);
        rest = &after[end..];
    }
    values
}

/// The qualifiers one marker value carries. The driver prints `clean` only
/// alone, meaning "no qualifier"; `clean` beside another qualifier, or an empty
/// marker, is not a shape it prints and comes back as an (unrecognised) item.
fn marker_qualifiers(value: &str) -> Vec<&str> {
    if value == "clean" {
        return Vec::new();
    }
    value.split(',').map(str::trim).collect()
}

/// A qualifier this scorer knows the meaning of.
fn qualifier_recognised(qualifier: &str) -> bool {
    matches!(qualifier, CERTIFIED_NO_CHECKS_QUALIFIER | UNATTRIBUTED_CHECK_QUALIFIER | TRIVIAL_SAFE_QUALIFIER)
        || qualifier
            .strip_prefix("sound_fallback=")
            .and_then(|n| n.parse::<u64>().ok())
            .is_some_and(|n| n > 0)
}

/// What one qualifier does to the success it marks: `None` keeps it clean
/// (only the D16 certified no-checks qualifier, whose own rule is
/// `certified_no_checks`); everything unrecognised is `Unsound` (fail-closed).
fn qualifier_taint_of(qualifier: &str) -> Option<SuccessTaint> {
    match qualifier {
        CERTIFIED_NO_CHECKS_QUALIFIER => None,
        UNATTRIBUTED_CHECK_QUALIFIER => Some(SuccessTaint::Unattributed),
        TRIVIAL_SAFE_QUALIFIER => Some(SuccessTaint::TrivialSafe),
        _ => Some(SuccessTaint::Unsound),
    }
}

/// The most severe taint the qualifiers printed in `text` carry.
fn text_qualifier_taint(text: &str) -> Option<SuccessTaint> {
    proof_qualifier_markers(text)
        .into_iter()
        .flat_map(marker_qualifiers)
        .filter_map(qualifier_taint_of)
        .max()
}

/// Every proof qualifier of the run other than a lone `clean`, distinct, in
/// first-seen order (the row's `proof_qualifiers`).
fn proof_qualifier_list(s: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for q in proof_qualifier_markers(s).into_iter().flat_map(marker_qualifiers) {
        if !out.iter().any(|seen| seen == q) {
            out.push(q.to_string());
        }
    }
    out
}

/// Every tainting qualifier that bears on the file's success, as
/// `(harness, qualifier)`: those printed in a section that reports SUCCESSFUL
/// (a qualifier in a FAILED section qualifies no success the file credits), and,
/// fail-closed, those printed outside every section (preamble, summary, stderr),
/// which cannot be attributed.
fn tainting_qualifiers(combined: &str) -> Vec<(String, String)> {
    let (sections, rest, _) = split_harness_sections_with_rest(combined);
    let mut found = Vec::new();
    let texts = sections
        .iter()
        .filter(|(_, text)| text.contains("VERIFICATION:- SUCCESSFUL"))
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .chain(std::iter::once((OUTSIDE_EVERY_HARNESS, rest.as_str())));
    for (who, text) in texts {
        for q in proof_qualifier_markers(text).into_iter().flat_map(marker_qualifiers) {
            if qualifier_taint_of(q).is_some() {
                found.push((who.to_string(), q.to_string()));
            }
        }
    }
    found
}

/// The run-level qualifier taint: the most severe over [`tainting_qualifiers`].
fn qualifier_taint(combined: &str) -> Option<SuccessTaint> {
    tainting_qualifiers(combined).iter().filter_map(|(_, q)| qualifier_taint_of(q)).max()
}

/// The row note for a qualified success: what the most severe qualifier means,
/// then each tainting qualifier with the harnesses that carry it.
fn qualifier_note(combined: &str) -> Option<String> {
    let found = tainting_qualifiers(combined);
    let worst = found.iter().filter_map(|(_, q)| qualifier_taint_of(q)).max()?;
    let mut grouped: Vec<(String, Vec<String>)> = Vec::new();
    for (who, q) in found {
        match grouped.iter_mut().find(|(seen, _)| *seen == q) {
            Some((_, harnesses)) => {
                if !harnesses.contains(&who) {
                    harnesses.push(who);
                }
            }
            None => grouped.push((q, vec![who])),
        }
    }
    let parts: Vec<String> = grouped
        .iter()
        .map(|(q, harnesses)| {
            let tag = if qualifier_recognised(q) { "" } else { " (unrecognised)" };
            format!("{q}{tag} on {}", harnesses.join(", "))
        })
        .collect();
    Some(format!("not a clean proof ({}): {}", worst.meaning(), parts.join("; ")))
}

/// Does a self-reported unsoundness confession taint the run's SUCCESS claim?
///
/// Attributed per harness when it can be: the confession belongs to the
/// `Checking harness` section that printed it, and only a section that reports
/// SUCCESSFUL can make the file's success unclean. A confession printed in an
/// INCONCLUSIVE or FAILED harness's section says nothing about a sibling's
/// proof. Fail-closed whenever attribution is not possible: a single-harness
/// run (the run is the harness), a multi-harness run with no `Manual Harness
/// Summary:` line (the sections may run into the appended stderr), or a
/// confession printed outside every section (the preamble, the summary, the
/// stderr).
fn self_report_taints_success(s: &str) -> bool {
    if !self_reported_unsound(s) {
        return false;
    }
    let (sections, rest, summary_seen) = split_harness_sections_with_rest(s);
    if sections.len() < 2 || !summary_seen || self_reported_unsound(&rest) {
        return true;
    }
    sections
        .iter()
        .any(|(_, text)| text.contains("VERIFICATION:- SUCCESSFUL") && self_reported_unsound(text))
}

/// trust-mc printed a self-reported-unsoundness confession.
fn self_reported_unsound(s: &str) -> bool {
    s.contains("created fresh unconstrained")
        || s.contains("pointee_synthesis_fallback")
        || s.contains("unconstrained_assignment")
        || s.contains("UNSOUND verification")
}

/// Extract the `<value>` from the first `prefix<value>]` marker.
/// Parse the driver's `[AY:UNKNOWN-CATEGORY] <free text>` line into a
/// (normalized key, raw detail) pair.
///
/// Unlike the other markers this one closes its bracket BEFORE the payload, so
/// the value is the remainder of the LINE rather than a bracketed token — the
/// `marker_value` helpers cannot read it.
///
/// The keys mirror the driver's `UnknownCategory` variants
/// (`call_ay/chc/native.rs`). Matching is on stable ASCII substrings, never on
/// the leading `≥`/`—` punctuation, so an encoding change cannot silently
/// reclassify a bucket. An unrecognized line yields `Other` and keeps its raw
/// text, so a NEW driver category shows up as visibly unmapped instead of being
/// dropped.
fn parse_unknown_category(s: &str) -> (Option<String>, Option<String>) {
    const TAG: &str = "[AY:UNKNOWN-CATEGORY]";
    let idx = match s.find(TAG) {
        Some(i) => i,
        None => return (None, None),
    };
    let rest = &s[idx + TAG.len()..];
    let line = rest.lines().next().unwrap_or("").trim();
    if line.is_empty() {
        return (None, None);
    }
    let key = if line.contains("Array-sorted state parameters") {
        "ArrayParamLimit"
    } else if line.contains("PDR invariant synthesis timeout") {
        "PdrTimeout"
    } else if line.contains("solver error (engine=") {
        "SolverError"
    } else if line.contains("no error rule encoded") {
        "NoErrorRule"
    } else if line.contains("uncategorized") {
        "Uncategorized"
    } else {
        "Other"
    };
    (Some(key.to_string()), Some(line.to_string()))
}

fn marker_value(s: &str, prefix: &str) -> Option<String> {
    let idx = s.find(prefix)?;
    let rest = &s[idx + prefix.len()..];
    let end = rest.find(']').unwrap_or(rest.len());
    // The value may itself be `Cat:detail`; keep only the leading token.
    let v = &rest[..end];
    Some(v.split([':', ' ']).next().unwrap_or(v).to_string())
}

/// Every `prefix<value>]` occurrence, WHOLE value, de-duplicated, first-seen
/// order.
///
/// [`marker_value`]'s truncation at `:` is right for the classification key and
/// wrong for diagnosis: it turns `OverApproximation:chc_translation_drop=4`
/// into `OverApproximation`, keeping the symptom and dropping the cause.
///
/// Unlike [`marker_csv_values`] the value is taken whole rather than split on
/// commas, because these markers embed `:` and `=` rather than listing items.
/// A multi-harness file prints one per harness, so a single scan is not enough.
fn marker_all_values(s: &str, prefix: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut rest = s;
    while let Some(idx) = rest.find(prefix) {
        let after = &rest[idx + prefix.len()..];
        let end = after.find(']').unwrap_or(after.len());
        let v = after[..end].trim();
        if !v.is_empty() && !out.iter().any(|e| e == v) {
            out.push(v.to_string());
        }
        rest = &after[end..];
    }
    out
}

/// Collect the comma-separated values of EVERY `prefix<a,b,c>]` occurrence,
/// de-duplicated, preserving first-seen order. A multi-harness file prints one
/// marker per demoted harness, so a single scan is not enough.
fn marker_csv_values(s: &str, prefix: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut rest = s;
    while let Some(idx) = rest.find(prefix) {
        rest = &rest[idx + prefix.len()..];
        let end = rest.find(']').unwrap_or(rest.len());
        for tok in rest[..end].split(',') {
            let tok = tok.trim();
            if !tok.is_empty() && !out.iter().any(|seen| seen == tok) {
                out.push(tok.to_string());
            }
        }
        rest = &rest[end..];
    }
    out
}

fn sum_marker(s: &str, needle: &str) -> u32 {
    let mut total = 0u32;
    let mut rest = s;
    while let Some(idx) = rest.find(needle) {
        rest = &rest[idx + needle.len()..];
        let num: String = rest.chars().take_while(char::is_ascii_digit).collect();
        if let Ok(n) = num.parse::<u32>() {
            total += n;
        }
    }
    total
}

/// Does the FAILED verdict rest on a *genuine* counterexample, or on an
/// encoding gap / inconclusive UNKNOWN that trust-mc mapped to FAILED?
/// Returns (is_encoding_gap, is_inconclusive).
fn failure_quality(s: &str, r: &TestResult) -> (bool, bool) {
    let encoding_gap = s.contains("Failed to parse CHC problem")
        || s.contains("expected argument sort")
        || r.ctrex_category.as_deref() == Some("EncodingGap")
        || breakdown_count(s, "EncodingGap") > 0;
    let cat = r.ctrex_category.as_deref();
    let inconclusive = cat == Some("Unknown")
        || cat == Some("OverApproximation")
        || s.contains("ay-chc inconclusive")
        || r.unknown_reason.is_some()
        // A DEMOTED PROOF is not a counterexample. The driver classifies CTREX
        // only for non-demoted failures (harness_runner.rs:573), so a demoted
        // proof emits `[AY:DEMOTION_REASONS:…]` and NO `[AY:CTREX_CAT:…]` at
        // all. Without this disjunct such a row was read as a genuine cex:
        // oracle=fail credited PARITY for a result with no counterexample, and
        // oracle=success was blamed as a FalsePositive it never earned. The
        // multi-harness lane already fail-closes on precisely this state
        // (`cats.is_empty()`, see classify_multi_harness_fail), so the two lanes
        // disagreed on identical driver output; this aligns them.
        //
        // Deliberately gated on `!demotion_reasons.is_empty()` rather than
        // `cat.is_none()` alone: a bare cat-less FAILED can also come from a
        // driver predating the marker, and tainting those would over-reject.
        // Demotion reasons are positive evidence that the FAILED was originally
        // a PROOF.
        || (cat.is_none() && !r.demotion_reasons.is_empty())
        || (breakdown_count(s, "Genuine") == 0
            && (breakdown_count(s, "Unknown") > 0 || breakdown_count(s, "OverApproximation") > 0));
    (encoding_gap, inconclusive)
}

/// Parse "CTREX breakdown: N EncodingGap, M OverApproximation, K Genuine, J Unknown".
fn breakdown_count(s: &str, label: &str) -> u32 {
    let Some(line) = s.lines().find(|l| l.contains("CTREX breakdown:")) else { return 0 };
    for part in line.split(',') {
        let part = part.trim();
        if let Some(num) = part.strip_suffix(label).map(str::trim) {
            return num.rsplit(char::is_whitespace).next().unwrap_or("0").parse().unwrap_or(0);
        }
    }
    0
}

/// Collect every `prefix<value>]` marker value in the output (leading token
/// only, mirroring `marker_value`).
fn marker_values<'a>(s: &'a str, prefix: &str) -> Vec<&'a str> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(idx) = rest.find(prefix) {
        rest = &rest[idx + prefix.len()..];
        let end = rest.find(']').unwrap_or(rest.len());
        out.push(rest[..end].split([':', ' ']).next().unwrap_or(""));
        rest = &rest[end.min(rest.len())..];
    }
    out
}

// ---- P1 MECH D: per-harness aggregation for multi-harness runs -------------
//
// `marker_value` surfaces only the FIRST `[AY:CTREX_CAT:]` of a run and
// `failure_quality` trips on run-level strings, so in a multi-harness file one
// harness's markers adjudicate ANOTHER harness's verdict (live example:
// kani/Stubbing/StubPrimitives/stub_bool_methods.rs — the should-panic
// harness's Genuine marker is surfaced while the OverApproximation-failing
// harness drives the FAILED verdict; the reverse ordering silently credits
// parity). The driver runs harnesses sequentially by default (no `-j`), each
// section opening with `Checking harness <name>...`, so the output splits
// cleanly. Classification is per harness: a file is parity only when EVERY
// harness's verdict matches its oracle expectation, and failure-quality taint
// applies to the harness that produced it, not the whole file.
//
// Fail-closed: the per-harness path engages only when the split is COHERENT
// (>= 2 sections, every section carries an explicit final verdict, and the
// set of FAILED sections equals the summary's `Verification failed for -`
// list). Anything else — interleaved parallel output, watchdog kills,
// crashes — falls back to the unchanged run-level path.

/// One harness's slice of a sequential multi-harness driver run.
struct HarnessOutcome {
    name: String,
    verdict: Verdict,
    /// All `[AY:CTREX_CAT:]` leading tokens emitted in this harness's section.
    cats: Vec<String>,
    /// First `[AY:UNKNOWN_REASON:]` value in this harness's section.
    unknown_reason: Option<String>,
    /// Ill-sorted/unparseable CHC evidence in this harness's section.
    encoding_gap: bool,
    /// The FAILED verdict (if any) rests on a non-genuine category, an
    /// UNKNOWN reason, an inconclusive-solver line, or no category at all
    /// (demoted result) — fail-closed.
    inconclusive: bool,
    /// Why the SUCCESSFUL verdict (if any) is not a clean proof: a
    /// sound-fallback marker, an `(UNVALIDATED)` verdict, a self-reported
    /// unsoundness line, an effective success other than a Genuine-validated
    /// `#[kani::should_panic]` pass, or a non-clean proof qualifier printed in
    /// this section (the per-section form of [`success_taint`]). A file-level
    /// parity must not rest on one.
    success_taint: Option<SuccessTaint>,
}

/// A section's FAILED verdict is backed by a genuine counterexample: at
/// least one `[AY:CTREX_CAT:…]`, every one `Genuine`, and no encoding-gap or
/// inconclusive evidence (for Kani, every FAILED section — see
/// [`harness_outcome`]).
fn genuine_failure(o: &HarnessOutcome) -> bool {
    o.verdict == Verdict::Fail && !o.encoding_gap && !o.inconclusive
}

/// The per-section form of [`success_taint`] (which reads the whole run):
/// why a SUCCESSFUL section is not a clean proof, from its own text.
fn section_success_taint(text: &str) -> Option<SuccessTaint> {
    if section_success_caveat(text) {
        return Some(SuccessTaint::Unsound);
    }
    text_qualifier_taint(text)
}

/// A SUCCESSFUL section that carries a soundness caveat of its own (anything
/// but a proof qualifier).
fn section_success_caveat(text: &str) -> bool {
    if text.contains("[AY:SOUND_FALLBACK:")
        || text.contains("SUCCESSFUL (UNVALIDATED)")
        || self_reported_unsound(text)
    {
        return true;
    }
    let reasons = marker_values(text, "[AY:EFFECTIVE_SUCCESS:");
    if reasons.is_empty() {
        return false;
    }
    if reasons.iter().any(|v| *v != "should_panic_panics_only")
        || !text.contains("(encountered one or more panics as expected)")
    {
        return true;
    }
    let cats = marker_values(text, "[AY:CTREX_CAT:");
    cats.is_empty() || cats.iter().any(|c| *c != "Genuine")
}

/// Strip the `Thread N: ` prefix multi-threaded driver runs tag lines with.
fn strip_thread_prefix(line: &str) -> &str {
    let Some(rest) = line.strip_prefix("Thread ") else { return line };
    let digit_count = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
    if digit_count == 0 {
        return line;
    }
    rest[digit_count..].strip_prefix(": ").unwrap_or(line)
}

/// Split the sequential per-harness phase of a run into (name, section text)
/// pairs. Sections open at `Checking harness <name>...` lines and the phase
/// ends at the final summary — everything after it (summary + appended
/// stderr) is run-level, never attributed to the last harness.
fn split_harness_sections(combined: &str) -> Vec<(String, String)> {
    split_harness_sections_with_rest(combined).0
}

/// [`split_harness_sections`], plus every line outside all sections (the
/// preamble before the first `Checking harness`, the `Manual Harness Summary:`
/// and everything after it, the appended stderr included) and whether that
/// summary line was seen.
fn split_harness_sections_with_rest(combined: &str) -> (Vec<(String, String)>, String, bool) {
    let mut sections: Vec<(String, String)> = Vec::new();
    let mut current: Option<(String, String)> = None;
    let mut rest = String::new();
    let mut summary_seen = false;
    for line in combined.lines() {
        let content = strip_thread_prefix(line);
        if summary_seen || content.starts_with("Manual Harness Summary:") {
            summary_seen = true;
            rest.push_str(line);
            rest.push('\n');
            continue;
        }
        if let Some(name) = content.strip_prefix("Checking harness ") {
            if let Some(section) = current.take() {
                sections.push(section);
            }
            let name = name.trim_end().trim_end_matches("...").to_string();
            current = Some((name, String::new()));
        } else if let Some((_, text)) = current.as_mut() {
            text.push_str(line);
            text.push('\n');
        } else {
            rest.push_str(line);
            rest.push('\n');
        }
    }
    if let Some(section) = current.take() {
        sections.push(section);
    }
    (sections, rest, summary_seen)
}

fn harness_outcome(name: &str, text: &str, engine: Engine) -> HarnessOutcome {
    // FAILED wins over SUCCESSFUL if both somehow appear (conservative).
    // `SUCCESSFUL (UNVALIDATED)` lands in the non-failing arm on purpose: only
    // FAILED sections are adjudicated here, so it earns no credit, and reading
    // it as Unknown would let one harness's caveat void a sibling's genuine
    // counterexample, the cross-harness coupling this split exists to remove.
    // File-level credit is refused by `clean_success`.
    let verdict = if text.contains("VERIFICATION:- FAILED") {
        Verdict::Fail
    } else if text.contains("VERIFICATION:- SUCCESSFUL") {
        Verdict::Success
    } else {
        Verdict::Unknown
    };
    let cats: Vec<String> =
        marker_values(text, "[AY:CTREX_CAT:").into_iter().map(str::to_string).collect();
    let unknown_reason = marker_value(text, "[AY:UNKNOWN_REASON:");
    let encoding_gap = text.contains("Failed to parse CHC problem")
        || text.contains("expected argument sort")
        || cats.iter().any(|c| c == "EncodingGap");
    let inconclusive = match engine {
        // Fail-closed: only an unambiguous all-Genuine section is conclusive —
        // no category at all (demoted result), any non-Genuine category
        // (Unknown, OverApproximation, or a future label this parser does not
        // know), an UNKNOWN reason, or an inconclusive-solver line all taint.
        Engine::TrustMc => {
            cats.is_empty()
                || cats.iter().any(|c| c != "Genuine")
                || unknown_reason.is_some()
                || text.contains("ay-chc inconclusive")
        }
        // Kani prints no quality markers: a FAILED section IS CBMC's
        // bit-precise counterexample (or its unwinding-assertion verdict,
        // which the oracle records the same way). Reading the absence of
        // AY markers as taint would score every multi-harness Kani failure
        // `unknown`, i.e. the reference engine could never reach parity.
        Engine::Kani => false,
    };
    let success_taint = if verdict == Verdict::Success { section_success_taint(text) } else { None };
    HarnessOutcome {
        name: name.to_string(),
        verdict,
        cats,
        unknown_reason,
        encoding_gap,
        inconclusive,
        success_taint,
    }
}

/// Harness names the final summary reports as failed.
fn summary_failed_names(combined: &str) -> std::collections::BTreeSet<String> {
    combined
        .lines()
        .filter_map(|l| strip_thread_prefix(l).strip_prefix("Verification failed for - "))
        .map(|n| n.trim().to_string())
        .collect()
}

/// Per-harness outcomes, or `None` unless the split is fully coherent (the
/// fail-closed gate documented above).
fn coherent_multi_harness_outcomes(combined: &str, engine: Engine) -> Option<Vec<HarnessOutcome>> {
    let sections = split_harness_sections(combined);
    if sections.len() < 2 {
        return None;
    }
    let outcomes: Vec<HarnessOutcome> =
        sections.iter().map(|(name, text)| harness_outcome(name, text, engine)).collect();
    // Every section needs an explicit final verdict; a section without one
    // means the run was cut short or the output interleaved.
    if outcomes.iter().any(|o| o.verdict == Verdict::Unknown) {
        return None;
    }
    // The FAILED sections must be exactly the harnesses the summary reports
    // as failed (should-panic effective successes appear in neither).
    let section_failed: std::collections::BTreeSet<String> = outcomes
        .iter()
        .filter(|o| o.verdict == Verdict::Fail)
        .map(|o| o.name.clone())
        .collect();
    if section_failed != summary_failed_names(combined) {
        return None;
    }
    Some(outcomes)
}

/// Does trust-mc's output satisfy KANI'S OWN pass/fail rule for this test?
///
/// Kani's `expected` suite is decided by `contains_lines` over the output —
/// `run_expected_test` (kani compiletest `runtest.rs`) never inspects the exit
/// status. So when every line of the expected file is present in trust-mc's
/// output, this is a test Kani's compiletest considers PASSING.
///
/// Consulted ONLY on the false-positive arm, and under scorer version 2 it is
/// necessary but not sufficient for the tiebreak: it must be paired with
/// [`expected_names_exactly`]. Measured on 98 real runs, replacing the verdict
/// rule with `contains_lines` wholesale demotes 53 of 94 scorable rows —
/// trust-mc does not emit CBMC's per-check report text — and forgives verdict
/// errors on 111 of 470 rows, 17 of them missed-bug slots.
///
/// `TRUST_MC_NO_KANI_TIEBREAK=1` disables it (an A/B lever); every row the
/// tiebreak changes records `tiebreak_applied`, so the set is auditable.
fn kani_criterion_satisfied(ctx: &ClassifyCtx<'_>, combined: &str) -> bool {
    if std::env::var("TRUST_MC_NO_KANI_TIEBREAK").map(|v| v == "1").unwrap_or(false) {
        return false;
    }
    matches!(ctx.expected, Some(exp) if matches_expected(combined, exp))
}

/// The harnesses an expected file names as failed (`Verification failed for -
/// <name>` lines, with a trailing `\` block-join stripped).
fn expected_failed_names(expected: &str) -> BTreeSet<String> {
    expected
        .lines()
        .filter_map(|l| l.trim().strip_prefix("Verification failed for - "))
        .map(|n| n.trim().trim_end_matches('\\').trim().to_string())
        .filter(|n| !n.is_empty())
        .collect()
}

/// The failure count of the expected file's `Complete - … N failures, …`
/// summary line, when it has one. With it, a `Verification failed for -` list
/// of exactly N names is known to be complete.
fn expected_failure_count(expected: &str) -> Option<u64> {
    expected.lines().find_map(|l| {
        let rest = l.trim().strip_prefix("Complete -")?;
        rest.split(',').find_map(|seg| {
            let seg = seg.trim();
            seg.strip_suffix("failures")
                .or_else(|| seg.strip_suffix("failure"))
                .and_then(|n| n.trim().parse::<u64>().ok())
        })
    })
}

/// Does the expected file itself name exactly `failing` as the harnesses Kani
/// fails?
///
/// This is the only evidence an expected file can give about a FAILED harness
/// on a success-oracle file. The file-level oracle is derived with
/// `VERIFICATION:- SUCCESSFUL` taking precedence (a `should_panic` harness
/// quotes failure lines under a SUCCESSFUL verdict), so a multi-harness
/// expected file that quotes a sibling's SUCCESSFUL line and the summary's
/// `Verification failed for - X` derives `success` while Kani itself fails X;
/// trust-mc failing exactly X with a genuine counterexample is then the same
/// verdict, not a divergence. An expected file that is SILENT about the
/// failing harness (the `function-contract/modifies/field_replace_pass`
/// shape: `VERIFICATION:- SUCCESSFUL` and nothing about the contract harness)
/// proves nothing about it — Kani's compiletest passes such a file whatever
/// that harness does — and under scorer version 1 that silence scored parity.
/// Measured 2026-09-12 over the verification suites: no expected file has the
/// naming shape without also carrying `VERIFICATION:- FAILED` (a fail
/// oracle), so in this corpus the tiebreak never fires under version 2.
fn expected_names_exactly(expected: &str, failing: &BTreeSet<String>) -> bool {
    let named = expected_failed_names(expected);
    !named.is_empty() && &named == failing
}

/// A classification plus the two audit bits the tiebreak leaves behind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Scored {
    class: Classification,
    /// The Kani tiebreak fired and turned a false positive into parity.
    tiebreak_applied: bool,
    /// Kani's `contains_lines` criterion held on a false positive but the
    /// expected file does not name the failing harnesses, so scorer version 2
    /// refused the upgrade (version 1 would have credited parity).
    kani_criterion_refused: bool,
    /// Why, for the arms whose reason the markers alone do not show.
    reason: Option<&'static str>,
}

impl Scored {
    fn plain(class: Classification) -> Self {
        Scored { class, tiebreak_applied: false, kani_criterion_refused: false, reason: None }
    }
    fn because(class: Classification, reason: &'static str) -> Self {
        Scored { reason: Some(reason), ..Scored::plain(class) }
    }
}

/// Adjudicate a multi-harness FAILED run per harness. `None` = fall back to
/// the run-level path unchanged.
///
/// Every failing harness's own markers decide its quality, and the expected
/// file's own `Verification failed for -` list (when it has one) decides
/// WHICH harnesses may fail:
///
/// * oracle `success`: any genuine failing harness is a false positive,
///   whatever a sibling did — surfaced, never hidden under a sibling's
///   encoding gap or inconclusive verdict. The tiebreak upgrades it to parity
///   only when every failing harness is genuine, Kani's `contains_lines`
///   criterion holds AND the expected file names exactly those harnesses.
/// * oracle `fail`: an encoding gap or an inconclusive failing harness is
///   never parity; with every failing harness genuine, a harness the expected
///   file names as failed that trust-mc PASSED is a missed bug, an extra
///   failing harness is a false positive when the expected list is known
///   complete (its `Complete - … N failures` count matches) and `unknown`
///   when it may be partial, and a sibling success that is not a clean proof
///   makes the file an unsound pass rather than parity.
fn classify_multi_harness_fail(ctx: &ClassifyCtx<'_>, combined: &str) -> Option<Scored> {
    let outcomes = coherent_multi_harness_outcomes(combined, ctx.engine)?;
    let failing: Vec<&HarnessOutcome> =
        outcomes.iter().filter(|o| o.verdict == Verdict::Fail).collect();
    if failing.is_empty() {
        return None; // observed said Fail but no section failed — incoherent
    }
    let failing_names: BTreeSet<String> = failing.iter().map(|o| o.name.clone()).collect();
    let all_genuine = failing.iter().all(|o| genuine_failure(o));
    let sibling_taint = outcomes.iter().filter_map(|o| o.success_taint).max();
    if ctx.oracle != Verdict::Fail {
        if !failing.iter().any(|o| genuine_failure(o)) {
            // Fall through to the encoding-gap / inconclusive arms below.
        } else {
            let criterion = kani_criterion_satisfied(ctx, combined);
            let named = all_genuine
                && criterion
                && ctx.expected.is_some_and(|e| expected_names_exactly(e, &failing_names));
            if named {
                let (class, reason) = if let Some(taint) = sibling_taint {
                    (taint.class(), "expected file names exactly the harnesses that failed (Kani tiebreak), but a sibling harness success is not a clean proof")
                } else {
                    (Classification::Parity, "parity via Kani tiebreak: expected file names exactly the harnesses that failed")
                };
                return Some(Scored {
                    class,
                    tiebreak_applied: true,
                    kani_criterion_refused: false,
                    reason: Some(reason),
                });
            }
            return Some(Scored {
                class: Classification::FalsePositive,
                tiebreak_applied: false,
                kani_criterion_refused: criterion,
                reason: criterion.then_some(
                    "false positive; Kani contains_lines criterion holds but the expected file does not name the failing harness(es), so it is not credited (scorer v2)",
                ),
            });
        }
    }
    if failing.iter().any(|o| o.encoding_gap) {
        return Some(Scored::plain(Classification::EncodingGap));
    }
    // The taint applies per harness: ANY failing harness that is not a
    // genuine counterexample makes the file inconclusive — a co-harness's
    // Genuine can no longer mask it (and a should-panic success's Genuine
    // marker no longer vouches for a different harness's failure).
    if failing.iter().any(|o| o.inconclusive) {
        return Some(Scored::plain(Classification::Unknown));
    }
    // oracle == Fail, every failing harness genuine. The expected file may
    // name WHICH harnesses Kani fails; trust-mc's failing set must agree.
    let named = ctx.expected.map(expected_failed_names).unwrap_or_default();
    if !named.is_empty() {
        let passed_named: Vec<&HarnessOutcome> = outcomes
            .iter()
            .filter(|o| named.contains(&o.name) && o.verdict != Verdict::Fail)
            .collect();
        if !passed_named.is_empty() {
            return Some(Scored::because(
                Classification::MissedBug,
                "expected file names a failed harness that trust-mc verified SUCCESSFUL",
            ));
        }
        if !named.iter().all(|n| failing_names.contains(n)) {
            // A named harness that trust-mc never ran: a discovery gap, not a
            // proof of safety and not a counterexample.
            return Some(Scored::because(
                Classification::Unknown,
                "expected file names a failed harness that trust-mc did not run",
            ));
        }
        if failing_names != named {
            let list_complete = ctx
                .expected
                .and_then(expected_failure_count)
                .is_some_and(|n| n == named.len() as u64);
            return Some(if list_complete {
                Scored::because(
                    Classification::FalsePositive,
                    "trust-mc fails a harness the expected file's complete failure list does not name",
                )
            } else {
                Scored::because(
                    Classification::Unknown,
                    "trust-mc fails a harness the expected file does not name, and its failure list may be partial",
                )
            });
        }
    }
    Some(if let Some(taint) = sibling_taint {
        Scored::because(
            taint.class(),
            "every failing harness is genuine, but a sibling harness success is not a clean proof",
        )
    } else {
        Scored::plain(Classification::Parity)
    })
}

/// Re-key `ctrex_category` / `unknown_reason` to the FIRST FAILING harness of
/// a coherent multi-harness run: `parse_markers` records the first marker in
/// the stream, which may belong to a harness that succeeded (misattributed
/// notes/reports). Only touches attribution fields — classification reads the
/// per-harness outcomes directly.
fn reattribute_multi_harness_markers(combined: &str, r: &mut TestResult, engine: Engine) {
    let Some(outcomes) = coherent_multi_harness_outcomes(combined, engine) else {
        return;
    };
    let Some(first_failing) = outcomes.iter().find(|o| o.verdict == Verdict::Fail) else {
        return;
    };
    r.ctrex_category = first_failing.cats.first().cloned();
    r.unknown_reason = first_failing.unknown_reason.clone();
}

/// A SUCCESS whose only "effective" component is Kani's own
/// `#[kani::should_panic]` semantics: the harness *expects* a panic, trust-mc
/// found the panic and AY validated the counterexample as **Genuine**. That is
/// the correct verdict for the test — Kani itself prints `VERIFICATION:-
/// SUCCESSFUL (encountered one or more panics as expected)` for it — so it
/// must not be branded an unsound pass.
///
/// Fail-closed: every `[AY:EFFECTIVE_SUCCESS:…]` marker must carry the
/// `should_panic_panics_only` reason, the driver must have printed the
/// panics-as-expected verdict, every `[AY:CTREX_CAT:…]` in the run must be
/// `Genuine` (at least one — the panic evidence itself), no `(UNVALIDATED)`
/// verdict, no sound-fallback, no self-reported unsoundness.
fn validated_should_panic_success(s: &str, r: &TestResult) -> bool {
    if !r.effective_success || r.sound_fallback != 0 || self_report_taints_success(s) {
        return false;
    }
    let reasons = marker_values(s, "[AY:EFFECTIVE_SUCCESS:");
    if reasons.is_empty() || reasons.iter().any(|v| *v != "should_panic_panics_only") {
        return false;
    }
    if !s.contains("(encountered one or more panics as expected)")
        || s.contains("SUCCESSFUL (UNVALIDATED)")
    {
        return false;
    }
    let cats = marker_values(s, "[AY:CTREX_CAT:");
    !cats.is_empty() && cats.iter().all(|c| *c == "Genuine")
}

/// A SUCCESS with zero soundness caveats: no fallback, no self-reported
/// unsoundness in a harness that reports SUCCESSFUL (or anywhere it cannot be
/// attributed, [`self_report_taints_success`]), no success the driver itself
/// left unvalidated, and no effective-success marker — except the fully
/// validated `#[kani::should_panic]` pass, which is the *correct* verdict, not
/// a caveat.
///
/// Scorer version 5 adds the driver's proof qualifiers ([`success_taint`]): a
/// success carrying any qualifier but `clean` and the certified no-checks one
/// is not clean.
fn clean_success(s: &str, r: &TestResult) -> bool {
    success_taint(s, r).is_none()
}

/// Why the run's success is not a clean proof, most severe reason first: a
/// run-level caveat ([`clean_success`]'s list) is [`SuccessTaint::Unsound`];
/// otherwise the most severe proof qualifier a SUCCESSFUL harness carries
/// ([`qualifier_taint`]).
fn success_taint(s: &str, r: &TestResult) -> Option<SuccessTaint> {
    let caveat = r.sound_fallback != 0
        || self_report_taints_success(s)
        || unvalidated_success(s)
        || (r.effective_success && !validated_should_panic_success(s, r));
    if caveat { Some(SuccessTaint::Unsound) } else { qualifier_taint(s) }
}

/// The driver reported a success it did not validate: `SUCCESSFUL
/// (UNVALIDATED)`, with or without a should_panic suffix. The substring
/// `VERIFICATION:- SUCCESSFUL` matches it too, so without this check a
/// non-linear-tier success, or one from an off-pin `ay`, scored as parity.
fn unvalidated_success(s: &str) -> bool {
    s.contains("VERIFICATION:- SUCCESSFUL (UNVALIDATED)")
}

/// The run used an `ay` that is not the pinned revision. Its verdicts belong
/// to no measurement tuple, whatever they say.
fn ran_on_off_pin_solver(s: &str) -> bool {
    s.contains(SOLVER_PIN_MISMATCH_MARKER)
}

/// Kani's canonical unsupported-construct failure text. When an expected file
/// records the run's failure *via this artifact* (and not via a whole-run
/// `VERIFICATION:- FAILED` verdict), the oracle's `fail` means "Kani cannot
/// handle the construct", not "the program has a bug".
fn oracle_is_unsupported_artifact(expected: &str) -> bool {
    expected.contains("not currently supported by Kani")
        && !expected.contains("VERIFICATION:- FAILED")
}

/// The output ends in a genuine *rustc compile error* (coded diagnostic or
/// rustc's abort line), not a driver/compiler panic.
fn rustc_compile_error(s: &str) -> bool {
    (s.contains("error[E") || s.contains("error: aborting due to"))
        && !s.contains("panicked at")
}

/// A compile-fail oracle is met: the run failed to compile the way the oracle
/// says. Fail-closed on every axis — a nonzero exit, NO `VERIFICATION:-` line
/// at all (a verdict of either polarity, or an unvalidated one, is the wrong
/// kind of answer), and:
///
/// * with an expected file, every expected line(-block) in the output — the
///   diagnostic itself is the evidence — and no panic unless the oracle's
///   diagnostic is one (`ice_oracle`: the file quotes an ICE banner, or its
///   manifest entry records that upstream panics with the quoted message; a
///   crash is not the diagnostic any other file names);
/// * without one (a bare `kani-check-fail` directive), a genuine rustc
///   compile error and no panic ([`rustc_compile_error`]).
fn compile_failed_as_expected(combined: &str, exit: Option<i32>, expected: Option<&str>, ice_oracle: bool) -> bool {
    if !exit.is_some_and(|c| c != 0) || combined.contains("VERIFICATION:-") {
        return false;
    }
    match expected {
        None => rustc_compile_error(combined),
        Some(exp) => matches_expected(combined, exp) && (ice_oracle || !combined.contains("panicked at")),
    }
}

/// Everything the classifier needs beyond the parsed markers.
struct ClassifyCtx<'a> {
    /// Which engine produced the output. The trust-mc rules are exactly the
    /// pre-`--engine` rules; Kani differs only where trust-mc's AY-marker
    /// discipline has no counterpart (see `harness_outcome`) and in its own
    /// unsupported-construct text.
    engine: Engine,
    /// How Kani's own compiletest scores the unit's suite. Read by the Kani
    /// engine only (`classify_kani`); the trust-mc rules never consult it.
    criterion: PassCriterion,
    oracle: Verdict,
    observed: Verdict,
    timed_out: bool,
    exit: Option<i32>,
    /// Test is a cargo unit (whole-package `cargo trust-mc` run).
    is_cargo: bool,
    /// Content of the governing Kani expected file, if any.
    expected: Option<&'a str>,
    /// The test header says `// kani-check-fail`: the oracle is a *compile*
    /// failure (Kani itself fails to build the file).
    check_fail: bool,
    /// The compile-fail oracle's diagnostic is a compiler panic: the expected
    /// file quotes an ICE banner, or its `quarantine::COMPILE_FAIL_ORACLES`
    /// entry records that upstream Kani panics with the quoted message.
    ice_oracle: bool,
}

/// Kani compiletest `contains_lines` semantics: every line of the expected
/// file must appear (as a substring, whitespace-trimmed) in the output; a
/// trailing `\` joins expected lines into a block that must match
/// *consecutive* output lines.
pub fn matches_expected(output: &str, expected: &str) -> bool {
    missing_expected_block(output, expected).is_none()
}

/// The first expected line(-block) the output lacks, or `None` when every
/// one is present — the return value of compiletest's `contains_lines`, so a
/// note can say which line failed a test.
pub fn missing_expected_block<'a>(output: &str, expected: &'a str) -> Option<Vec<&'a str>> {
    let out_lines: Vec<&str> = output.lines().collect();
    let mut block: Vec<&'a str> = Vec::new();
    for line in expected.lines() {
        if let Some(prefix) = line.strip_suffix('\\') {
            block.push(prefix);
        } else {
            block.push(line);
            if !contains_block(&out_lines, &block) {
                return Some(block);
            }
            block.clear();
        }
    }
    // A `\` on the last line would otherwise leave the block untested.
    if !block.is_empty() && !contains_block(&out_lines, &block) {
        return Some(block);
    }
    None
}

/// Does any window of consecutive output lines contain the block's lines
/// (each expected line a whitespace-trimmed substring of its output line)?
fn contains_block(out_lines: &[&str], block: &[&str]) -> bool {
    debug_assert!(!block.is_empty());
    out_lines
        .windows(block.len())
        .any(|w| w.iter().zip(block).all(|(out, exp)| out.contains(exp.trim())))
}

/// The verifier (or its compiler subprocess) died on a signal.
fn crashed(combined: &str, exit: Option<i32>, timed_out: bool) -> bool {
    if timed_out {
        return false;
    }
    // The driver reports subprocess signal deaths; a None exit code (not
    // watchdog-killed) means the driver itself died on a signal.
    combined.contains("exited with status signal:") || exit.is_none()
}

/// Cargo could not even assemble the dependency graph in this environment
/// (network-restricted registry / unresolvable deps) — not a verifier defect.
fn build_unavailable(combined: &str) -> bool {
    ["failed to load source for dependency",
     "Unable to update registry",
     "failed to fetch ",
     "network failure seems to have happened",
     "failed to download",
     "error: no matching package named"]
        .iter()
        .any(|n| combined.contains(n))
}

/// A diagnostic-only output (no `VERIFICATION:-` verdict) that may earn
/// parity through Kani's `contains_lines` rule: nothing in it is a demoted,
/// unvalidated, vacuous or fallback-tainted verdict wearing a diagnostic's
/// clothes.
fn diagnostic_output_is_clean(combined: &str, r: &TestResult) -> bool {
    !combined.contains("VERIFICATION:- UNVALIDATED")
        && !r.vacuous
        && r.sound_fallback == 0
        && !r.self_reported_unsound
        && r.demotion_reasons.is_empty()
}

/// A genuine counterexample backs the FAILED verdict somewhere in the output:
/// on a coherent multi-harness split, some failing section is genuine; else
/// any `Genuine` category or a non-zero `Genuine` breakdown count.
fn genuine_counterexample_present(combined: &str, engine: Engine) -> bool {
    match coherent_multi_harness_outcomes(combined, engine) {
        Some(outcomes) => outcomes.iter().any(genuine_failure),
        None => {
            marker_values(combined, "[AY:CTREX_CAT:").iter().any(|c| *c == "Genuine")
                || breakdown_count(combined, "Genuine") > 0
        }
    }
}

/// The text of Kani's unsupported-construct check
/// (`codegen_cprover_gotoc/utils/utils.rs`: `"{item} is not currently supported by Kani"`).
const KANI_UNSUPPORTED_CHECK_TEXT: &str = "is not currently supported by Kani";

/// The approximation reason the engine records for a reproduced Kani
/// unsupported-construct check (`emit_kani_unsupported_check`); unidentified on
/// purpose, so the driver never certifies that failure Genuine and prints
/// `[AY:CTREX_CAT:OverApproximation:kani_unsupported_construct_check=N]`.
const KANI_UNSUPPORTED_CHECK_REASON: &str = "kani_unsupported_construct_check";

const UNSUPPORTED_CHECK_PARITY: &str = "parity: the harness(es) the expected file names fail on exactly Kani's unsupported-construct check, which the engine never certifies Genuine, and every expected line is present";

/// The unsupported-construct check descriptions an expected file names:
/// `Failed Checks: <d>` and `Description: "<d>"` lines carrying Kani's text.
fn expected_unsupported_checks(expected: &str) -> Vec<String> {
    expected
        .lines()
        .filter_map(|l| {
            let t = l.trim().trim_end_matches('\\').trim_end();
            let d = t
                .strip_prefix("Failed Checks: ")
                .or_else(|| t.strip_prefix("- Description: "))
                .or_else(|| t.strip_prefix("Description: "))?;
            let d = d.trim().trim_matches('"');
            d.contains(KANI_UNSUPPORTED_CHECK_TEXT).then(|| d.to_string())
        })
        .collect()
}

/// The descriptions of every FAILURE check in one harness section: a
/// `- Status: FAILURE` line's following `- Description:`, and every
/// `Failed Checks:` line.
fn failed_check_descriptions(section: &str) -> Vec<String> {
    let lines: Vec<&str> = section.lines().map(str::trim).collect();
    let mut out = Vec::new();
    for (i, l) in lines.iter().enumerate() {
        if *l == "- Status: FAILURE" {
            if let Some(d) = lines.get(i + 1).and_then(|n| n.strip_prefix("- Description: ")) {
                out.push(d.trim().trim_matches('"').to_string());
            }
        } else if let Some(d) = l.strip_prefix("Failed Checks: ") {
            out.push(d.trim().to_string());
        }
    }
    out
}

/// A fail-oracle unit whose expected file names Kani's own unsupported-construct
/// check, on which trust-mc fails exactly that check: parity by Kani's
/// compiletest criterion (the expected lines, a FAILED verdict), although the
/// counterexample is deliberately not certified Genuine. Every condition is
/// required, so it rescues nothing else:
///
/// * the trust-mc engine, a fail oracle that is not compile-fail, an expected
///   file naming at least one `… is not currently supported by Kani` check, and
///   every expected line(-block) in the output;
/// * the failing harnesses are the ones the expected file names (`Verification
///   failed for -`), or — when it names none — every FAILED section, at least
///   one; each is FAILED, no other section is, and every other section is a
///   clean SUCCESSFUL;
/// * in each failing section every FAILURE check is an unsupported-construct
///   check the expected file names (another failing property is not rescued),
///   every `[AY:CTREX_CAT:…]` is `Genuine` or `OverApproximation` whose every
///   entry is `kani_unsupported_construct_check=N` (an approximation of any
///   other kind, `EncodingGap`, `Unknown` or no category at all is not
///   rescued), and there is no UNKNOWN reason, inconclusive solver, demotion or
///   encoding-gap evidence.
///
/// A SUCCESSFUL never reaches this arm: against a fail oracle it stays
/// `missed_bug`.
fn unsupported_check_parity(ctx: &ClassifyCtx<'_>, combined: &str) -> Option<Scored> {
    if ctx.engine != Engine::TrustMc || ctx.oracle != Verdict::Fail || ctx.check_fail {
        return None;
    }
    let expected = ctx.expected?;
    let named_checks = expected_unsupported_checks(expected);
    if named_checks.is_empty() || !matches_expected(combined, expected) {
        return None;
    }
    let sections = split_harness_sections(combined);
    let named_harnesses = expected_failed_names(expected);
    let failed_sections: BTreeSet<&str> = sections
        .iter()
        .filter(|(_, t)| t.contains("VERIFICATION:- FAILED"))
        .map(|(n, _)| n.as_str())
        .collect();
    let failing: BTreeSet<&str> = if named_harnesses.is_empty() {
        failed_sections.clone()
    } else {
        named_harnesses.iter().map(String::as_str).collect()
    };
    if failing.is_empty() || failing != failed_sections {
        return None;
    }
    for (name, text) in &sections {
        if !failing.contains(name.as_str()) {
            if !text.contains("VERIFICATION:- SUCCESSFUL") || harness_without_success(text) || section_success_taint(text).is_some() {
                return None;
            }
            continue;
        }
        let checks = failed_check_descriptions(text);
        let named = |c: &String| named_checks.iter().any(|n| c.contains(n.as_str()) || n.contains(c.as_str()));
        if checks.is_empty() || !checks.iter().all(|c| c.contains(KANI_UNSUPPORTED_CHECK_TEXT) && named(c)) {
            return None;
        }
        let cats = marker_all_values(text, "[AY:CTREX_CAT:");
        if cats.is_empty() {
            return None;
        }
        for cat in &cats {
            let (label, detail) = cat.split_once(':').unwrap_or((cat.as_str(), ""));
            let ok = match label {
                "Genuine" => true,
                "OverApproximation" => {
                    !detail.is_empty()
                        && detail.split(',').all(|e| {
                            e.trim()
                                .strip_prefix(KANI_UNSUPPORTED_CHECK_REASON)
                                .and_then(|n| n.strip_prefix('='))
                                .is_some_and(|n| n.parse::<u64>().is_ok())
                        })
                }
                _ => false,
            };
            if !ok {
                return None;
            }
        }
        if text.contains("[AY:UNKNOWN_REASON:")
            || text.contains("ay-chc inconclusive")
            || text.contains("[AY:DEMOTION_REASONS:")
            || text.contains("Failed to parse CHC problem")
            || text.contains("expected argument sort")
        {
            return None;
        }
    }
    Some(Scored::because(Classification::Parity, UNSUPPORTED_CHECK_PARITY))
}

/// Score a FAILED verdict: its provenance is examined before it is trusted
/// as a counterexample, on every path that could credit it.
fn classify_failed(ctx: &ClassifyCtx<'_>, r: &TestResult, combined: &str) -> Scored {
    let ClassifyCtx { engine, oracle, .. } = *ctx;
    // 1. Unsupported construct / codegen panic -> feature gap. Never taken
    //    over a genuine counterexample: a validated counterexample is the
    //    verdict, whatever else the run printed, and against a success
    //    oracle it is a false positive. A trust-mc class: the Kani engine
    //    scores in `classify_kani`, where Kani's own unsupported-construct
    //    lines are part of its normal transcript and decide nothing.
    let unsupported = combined.contains("unsupported constructs")
        || combined.contains("Found the following unsupported")
        || combined.contains("codegen panic")
        || combined.contains("CHC codegen panic");
    if unsupported && !genuine_counterexample_present(combined, engine) {
        return Scored::plain(Classification::Unsupported);
    }
    // 1b. Kani's own unsupported-construct check, reproduced: see
    //     `unsupported_check_parity`. Before the per-harness and failure-quality
    //     arms, which would read its deliberately uncertified category as
    //     inconclusive.
    if let Some(scored) = unsupported_check_parity(ctx, combined) {
        return scored;
    }
    // 2a. P1 MECH D: multi-harness runs are adjudicated PER HARNESS — each
    //     failing harness's own markers decide its quality, so one harness's
    //     Genuine cannot vouch for (nor its taint poison) a sibling. Engages
    //     only on a coherent per-harness split; otherwise the run-level path
    //     below is unchanged.
    if let Some(scored) = classify_multi_harness_fail(ctx, combined) {
        return scored;
    }
    // 2b. Ill-sorted / unparseable CHC, or non-genuine CTREX that trust-mc
    //     mapped to FAILED -> trust-mc CHC encoding gap / inconclusive.
    let (encoding_gap, inconclusive) = failure_quality(combined, r);
    if encoding_gap {
        return Scored::plain(Classification::EncodingGap);
    }
    if inconclusive {
        return Scored::plain(Classification::Unknown);
    }
    // 3. Otherwise this is a genuine counterexample.
    if oracle == Verdict::Fail {
        return Scored::plain(Classification::Parity);
    }
    // oracle == Success but trust-mc found a (claimed-genuine) CEX: a false
    // positive. Without a coherent per-harness split there is no failing
    // harness set to check the expected file against, so Kani's
    // `contains_lines` criterion is recorded (for the audit) but cannot
    // upgrade the row — scorer version 1 let it, which is how a single
    // harness's wrong FAILED could score parity off a partial expected file.
    let criterion = kani_criterion_satisfied(ctx, combined);
    Scored {
        class: Classification::FalsePositive,
        tiebreak_applied: false,
        kani_criterion_refused: criterion,
        reason: criterion.then_some(
            "false positive; Kani contains_lines criterion holds but no per-harness split names the failing harness, so it is not credited (scorer v2)",
        ),
    }
}

/// The reason on a file whose SUCCESSFUL harness(es) sit beside a harness that
/// did not report SUCCESSFUL (INCONCLUSIVE, or no verdict).
const SUCCESS_BESIDE_UNFINISHED_HARNESS: &str =
    "a harness did not report SUCCESSFUL beside SUCCESSFUL sibling(s); a file-level success needs every harness SUCCESSFUL";

/// Kani's `Manual Harness Summary` line when a file declares no harness it
/// can see: nothing ran, and the launcher exits 0. In the pinned corpus
/// `kani/Closure/boxed_closure.rs` has its `#[kani::proof]` commented out
/// and Kani's compiletest passes it on that exit status.
const KANI_NO_HARNESSES: &str =
    "No proof harnesses (functions with #[kani::proof]) were found to verify.";

/// The reason on a Kani row whose verdict agrees with the oracle while the
/// expected file's lines do not all appear in its output: compiletest fails
/// that test (`verify_output`), so it is not parity.
const KANI_EXPECTED_LINES_MISSING: &str =
    "Kani's verdict agrees with the oracle but its output lacks expected-file line(s), so its compiletest fails the test";

/// The reason on a Kani `parity` row that compiletest passes by
/// `contains_lines` although the run also printed `VERIFICATION:- FAILED`
/// for a harness the expected file (whose own verdict is SUCCESSFUL) never
/// names — the `function-contract/gcd_rec_replacement_pass` shape under
/// Kani 0.67.0, where `gcd_harness` fails and the expected file lists only
/// the two harnesses that pass. Kani's own criterion credits it; the note
/// names the harness so the credit is auditable.
const KANI_PARITY_WITH_UNNAMED_FAILURE: &str =
    "parity by compiletest's contains_lines rule; the run also printed VERIFICATION:- FAILED for harness(es) the expected file does not name";

/// kani-driver itself panicked: whatever it printed before is not a verdict.
/// Measured 2026-09-13: Kani 0.67.0 panics on CBMC's `ERROR` status
/// (`kani-driver/src/cbmc_output_parser.rs:470`, upstream #4519, fixed after
/// 0.67.0) whenever a `--solver z3|bitwuzla` names a solver this host lacks —
/// after it has already printed the expected file's diagnostic lines, which
/// `contains_lines` alone would pass.
fn kani_driver_panicked(combined: &str) -> bool {
    combined.contains("panicked at kani-driver/")
}

/// Score a Kani-engine attempt the way Kani's own compiletest scores the
/// unit's suite (`PassCriterion`, from the `--mode` its regression scripts
/// use), then explain a non-pass in this tool's classes.
///
/// * `ExpectedLines` — compiletest's `expected` / `cargo-kani` modes
///   (`verify_output`): the test passes iff stdout+stderr contain every
///   line(-block) of the expected file (`contains_lines`); the exit status
///   is not consulted. A match is `parity`. Otherwise the verdict rules
///   below explain the miss, and a verdict that agrees with the oracle while
///   an expected line is missing is `unknown`, not parity, because
///   compiletest fails that test (the note names the first missing block).
/// * `ExitStatus` — compiletest's `kani` mode (`verify`): the test passes
///   iff `kani` exits successfully, inverted by `kani-verify-fail`. Kani
///   exits 0 exactly when every harness prints `VERIFICATION:- SUCCESSFUL`,
///   so the verdict against the oracle is the same criterion.
///
/// Kani prints no quality markers: a `SUCCESSFUL` is its proof and a
/// `FAILED` is CBMC's counterexample (or its unwinding-assertion verdict,
/// which the oracle records the same way). Its `unsupported_construct`
/// check lines and its `Found the following unsupported constructs`
/// warning are part of every normal transcript — any unit that touches
/// `Location::caller` or a foreign function prints them, with either
/// verdict — and compiletest scores by the verdict and the expected file
/// alone, so they never decide a class here; `unsupported` is a trust-mc
/// class. Before 2026-09-13 they scored 108 of 1122 verification rows
/// `unsupported`, 90 of them fail-oracle units Kani fails exactly as its
/// compiletest expects.
///
/// Fail-closed departures from compiletest, each spelled out in the note:
/// a run with no verdict (a compile error, a rejected flag, a kani-driver
/// panic) is `error` even where its nonzero exit would satisfy a
/// `kani-verify-fail` test, because a failure to run is not a
/// counterexample; a file Kani finds no harness in is `vacuous` even though
/// compiletest passes it on exit 0; and a kani-driver panic is `error` even
/// when the expected file's diagnostic lines were printed before it.
fn classify_kani(ctx: &ClassifyCtx<'_>, r: &TestResult, combined: &str) -> Scored {
    if ctx.timed_out {
        return Scored::plain(Classification::Timeout);
    }
    if crashed(combined, ctx.exit, ctx.timed_out) {
        return Scored::plain(Classification::Crash);
    }
    if kani_driver_panicked(combined) {
        return Scored::because(
            Classification::Error,
            "kani-driver panicked, so its output is not a Kani verdict (compiletest's expected mode would still pass a diagnostic-only expected file printed before the panic)",
        );
    }
    if ctx.criterion == PassCriterion::ExpectedLines {
        if let Some(exp) = ctx.expected {
            if missing_expected_block(combined, exp).is_none() {
                let named = expected_failed_names(exp);
                let failed = summary_failed_names(combined);
                let unnamed_failure = exp.contains("VERIFICATION:- SUCCESSFUL")
                    && !exp.contains("VERIFICATION:- FAILED")
                    && combined.contains("VERIFICATION:- FAILED")
                    && (failed.is_empty() || failed.iter().any(|n| !named.contains(n)));
                return if unnamed_failure {
                    Scored::because(Classification::Parity, KANI_PARITY_WITH_UNNAMED_FAILURE)
                } else {
                    Scored::plain(Classification::Parity)
                };
            }
            let scored = classify_kani_verdict(ctx, r, combined);
            if scored.class == Classification::Parity {
                return Scored::because(Classification::Unknown, KANI_EXPECTED_LINES_MISSING);
            }
            return scored;
        }
    }
    classify_kani_verdict(ctx, r, combined)
}

/// The Kani engine's verdict rules: what compiletest's `kani` mode decides
/// on the exit status, read off the `VERIFICATION:-` verdict, and the
/// explanation of a non-pass under either criterion.
fn classify_kani_verdict(ctx: &ClassifyCtx<'_>, r: &TestResult, combined: &str) -> Scored {
    let ClassifyCtx { oracle, observed, exit, is_cargo, expected, check_fail, .. } = *ctx;
    if observed == Verdict::Unknown {
        if r.no_harnesses {
            return Scored::because(
                Classification::Vacuous,
                "Kani found no harness to verify, so nothing ran; its compiletest passes the file on exit status 0 alone",
            );
        }
        if is_cargo && build_unavailable(combined) {
            return Scored::plain(Classification::BuildUnavailable);
        }
        // `// kani-check-fail`: compiletest runs `kani-compiler` and expects
        // it to fail; `kani` refusing the file with a rustc diagnostic is
        // that verdict (and a matching expected file, when there is one).
        if check_fail && oracle == Verdict::Fail && compile_failed_as_expected(combined, exit, expected, ctx.ice_oracle) {
            return Scored::plain(Classification::Parity);
        }
        let looks_like_error = combined.contains("error[")
            || combined.contains("error: ")
            || combined.contains("panicked at")
            || exit.map(|c| c != 0).unwrap_or(true);
        return Scored::plain(if looks_like_error { Classification::Error } else { Classification::Unknown });
    }
    if check_fail {
        // A compile-fail oracle can only be met by a compile error.
        return Scored::plain(Classification::Error);
    }
    if observed == Verdict::Fail {
        if oracle != Verdict::Fail {
            return Scored::plain(Classification::FalsePositive);
        }
        // An expected file that names the failed harnesses must agree with
        // WHICH harnesses failed: a named one Kani verified is a missed bug.
        if let (Some(exp), Some(outcomes)) =
            (expected, coherent_multi_harness_outcomes(combined, Engine::Kani))
        {
            let named = expected_failed_names(exp);
            if outcomes.iter().any(|o| named.contains(&o.name) && o.verdict == Verdict::Success) {
                return Scored::because(
                    Classification::MissedBug,
                    "expected file names a failed harness that Kani verified SUCCESSFUL",
                );
            }
        }
        return Scored::plain(Classification::Parity);
    }
    // observed == Success: Kani's proof.
    Scored::plain(if oracle == Verdict::Success {
        Classification::Parity
    } else {
        Classification::MissedBug
    })
}

fn classify(ctx: &ClassifyCtx<'_>, r: &TestResult, combined: &str) -> Scored {
    let ClassifyCtx { oracle, observed, timed_out, exit, is_cargo, expected, check_fail, .. } = *ctx;
    // Before anything else, timeouts included: a row from an off-pin solver
    // measures nothing this ledger names. The runner scrubs the switch that
    // allows one, so this only fires if a driver accepted one anyway.
    if ran_on_off_pin_solver(combined) {
        return Scored::plain(Classification::Error);
    }
    if timed_out {
        return Scored::plain(Classification::Timeout);
    }
    if crashed(combined, exit, timed_out) {
        return Scored::plain(Classification::Crash);
    }
    // Kani's own pass criterion for expected-output tests: the output contains
    // every expected line(-block). Applied when trust-mc produced NO verdict
    // (the expected file demands a *diagnostic*, e.g. a stubbing resolution
    // error) and the output is clean of demoted / vacuous / fallback verdicts.
    // Scorer version 1 also took this arm for every cargo unit, BEFORE the
    // failure-quality gate, so an encoding-gap or demoted FAILED whose output
    // happened to contain the expected summary lines scored parity; a
    // verdict-bearing cargo unit now goes through the verdict rules below like
    // any other unit (`contains_lines` can confirm a diagnostic, never launder
    // a verdict).
    // A compile-fail oracle is decided by its own arm below (a nonzero exit and
    // no verdict at all), never by this one.
    if let Some(exp) = expected.filter(|_| !check_fail) {
        if observed == Verdict::Unknown
            && diagnostic_output_is_clean(combined, r)
            && matches_expected(combined, exp)
        {
            return Scored::plain(Classification::Parity);
        }
    }
    if is_cargo && observed == Verdict::Unknown && build_unavailable(combined) {
        return Scored::plain(Classification::BuildUnavailable);
    }
    if observed == Verdict::Unknown {
        // A trust-mc *compiler/tool* timeout (codegen too slow to even reach the
        // solver) is a completeness/perf gap, not a tool error — bucket it as a
        // timeout so it reads as "not yet", not "broken".
        if combined.contains("timed out after") || combined.contains("--tool-timeout") {
            return Scored::plain(Classification::Timeout);
        }
        // `// kani-check-fail`: the oracle is "compilation fails" (Kani itself
        // errors out building this file). trust-mc refusing the same file with
        // a genuine rustc compile error IS the Kani verdict — parity. Strict:
        // requires the fail-oracle, a nonzero exit, a real rustc diagnostic
        // (never a driver panic), and — when an expected file exists — its
        // diagnostic text in the output (handled above; a non-matching
        // expected file blocks this path).
        if check_fail && oracle == Verdict::Fail && compile_failed_as_expected(combined, exit, expected, ctx.ice_oracle) {
            return Scored::plain(Classification::Parity);
        }
        // Distinguish a clean solver `unknown` from a hard tool error.
        let looks_like_error = combined.contains("error[")
            || combined.contains("error: ")
            || combined.contains("panicked at")
            || combined.contains("not found in PATH")
            || exit.map(|c| c != 0).unwrap_or(true);
        let has_unknown_verdict = combined.contains("[AY:UNKNOWN_QUALITY:")
            || combined.contains("VERIFICATION:- UNDETERMINED")
            || combined.contains("VERIFICATION:- INCONCLUSIVE")
            || combined.contains("UNREACHABLE");
        // An honest vacuity refusal is not breakage. The driver emits
        // `[AY:VACUOUS:no-checks]` + `VERIFICATION:- INCONCLUSIVE (no checks)`
        // and exits 1, which `looks_like_error` reads as a failure to run.
        // Before this arm those rows landed in `Error` alongside genuine
        // compile failures: a 2026-08-22 run reported `error=46`, of which 33
        // were vacuity and 3 were real compile breakage. Same non-parity
        // outcome, but the headline said "crash wave" when it meant "we
        // generated no checks".
        if r.vacuous {
            return Scored::plain(Classification::Vacuous);
        }
        // SUCCESSFUL harness(es) beside one that did not succeed: the verdict
        // rules make the file indeterminate (`parse_verdict`), whatever a
        // sibling section printed.
        if combined.contains("VERIFICATION:- SUCCESSFUL") && !combined.contains("VERIFICATION:- UNVALIDATED") {
            return Scored::because(Classification::Unknown, SUCCESS_BESIDE_UNFINISHED_HARNESS);
        }
        return Scored::plain(if looks_like_error && !has_unknown_verdict {
            Classification::Error
        } else {
            Classification::Unknown
        });
    }
    // A compile-fail oracle (`kani-check-fail` directive or a compile-error
    // expected file) can only be satisfied by a matching compile error — the
    // program is not supposed to build, so a verification verdict of EITHER
    // polarity is the wrong kind of answer. Without this gate the
    // `expected/intrinsics/simd-*` E0511 family scores dishonestly: trust-mc
    // "verifying" a program rustc rejects at monomorphization would count as
    // parity (observed success) or the coarse fail==fail match would. Both
    // are tool gaps (the required rustc diagnostic was never surfaced), so
    // fail closed into `error`; `note_for` explains the shape.
    if check_fail {
        return Scored::plain(Classification::Error);
    }
    // A FAILED verdict needs its provenance examined before we trust it as a
    // genuine counterexample.
    if observed == Verdict::Fail {
        return classify_failed(ctx, r, combined);
    }

    // observed == Success
    if oracle == Verdict::Success {
        return Scored::plain(match success_taint(combined, r) {
            None => Classification::Parity,
            Some(taint) => taint.class(),
        });
    }
    // oracle == Fail, observed == Success. Before branding it a missed
    // bug, check for the corpus-oracle artifact: the expected file records
    // Kani's failure only as "construct not currently supported by Kani"
    // (no whole-run FAILED verdict) — there is no bug in the program, Kani
    // simply cannot encode it. A clean, `[AY:PROOF]`-backed trust-mc proof
    // then *exceeds* the oracle. Own class; never silently parity.
    // A compiler-certified no-checks success proved nothing, so it can never
    // exceed an oracle: against a fail oracle it stays a missed bug.
    if r.proof_marker
        && r.certified_no_checks == 0
        && clean_success(combined, r)
        && expected.is_some_and(oracle_is_unsupported_artifact)
    {
        return Scored::plain(Classification::ExceedsOracle);
    }
    // Soundness-critical missed bug.
    Scored::plain(Classification::MissedBug)
}

fn note_for(r: &TestResult, ctx: &ClassifyCtx<'_>, combined: &str, scored: Scored) -> String {
    let ClassifyCtx { timed_out, check_fail, .. } = *ctx;
    if r.classification == Some(Classification::Error) && ran_on_off_pin_solver(combined) {
        let marker = combined
            .lines()
            .find(|l| l.contains(SOLVER_PIN_MISMATCH_MARKER))
            .map(str::trim)
            .unwrap_or(SOLVER_PIN_MISMATCH_MARKER);
        return format!("ran on an off-pin ay solver, not scored: {marker}");
    }
    if timed_out {
        return "outer watchdog timeout".into();
    }
    if ctx.engine == Engine::Kani {
        // Kani rows carry no AY markers, so the reason is the whole note; a
        // missing expected line is named, and an error row quotes the rustc
        // diagnostic rather than the launcher's exit-status echo.
        if let Some(reason) = scored.reason {
            if reason == KANI_EXPECTED_LINES_MISSING {
                if let Some(block) = ctx.expected.and_then(|e| missing_expected_block(combined, e)) {
                    return format!("{reason}; first missing: {}", block.join(" \\ "));
                }
            }
            if reason == KANI_PARITY_WITH_UNNAMED_FAILURE {
                let named = ctx.expected.map(expected_failed_names).unwrap_or_default();
                let unnamed: Vec<String> =
                    summary_failed_names(combined).into_iter().filter(|n| !named.contains(n)).collect();
                if !unnamed.is_empty() {
                    return format!("{reason}: {}", unnamed.join(", "));
                }
            }
            return reason.to_string();
        }
        if r.classification == Some(Classification::Error) {
            return head_rustc_error(combined);
        }
    }
    if let Some(reason) = scored.reason {
        return match r.classification {
            Some(Classification::Unknown) => {
                format!("{reason} (ctrex={:?} reason={:?})", r.ctrex_category, r.unknown_reason)
            }
            _ => with_qualifier_note(reason.to_string(), r, combined),
        };
    }
    match r.classification {
        Some(Classification::Error)
            if check_fail && r.observed.is_some_and(|o| o != Verdict::Unknown) =>
        {
            format!(
                "expected a compile error (check-fail oracle) but trust-mc produced a {:?} verdict",
                r.observed.unwrap()
            )
        }
        Some(Classification::Error) => head_error(combined),
        Some(Classification::CorpusInvalid) => {
            "corpus-invalid source (see quarantine manifest)".into()
        }
        Some(Classification::Crash) => head_crash(combined),
        Some(Classification::BuildUnavailable) => {
            format!("cargo build unavailable in this environment: {}", head_error(combined))
        }
        Some(Classification::Unsupported) => head_unsupported(combined),
        Some(Classification::EncodingGap) => head_encoding_gap(combined),
        Some(Classification::Unknown) => {
            format!("ctrex={:?} reason={:?}", r.ctrex_category, r.unknown_reason)
        }
        Some(Classification::UnsoundPass) => with_qualifier_note(
            format!("sound_fallback={} effective_success={}", r.sound_fallback, r.effective_success),
            r,
            combined,
        ),
        Some(Classification::TrivialSafePass | Classification::UnattributedPass | Classification::MissedBug) => {
            with_qualifier_note(String::new(), r, combined)
        }
        Some(Classification::ExceedsOracle) => {
            "oracle fail is a Kani unsupported-construct artifact (no genuine bug); \
             trust-mc cleanly proves the assertions"
                .into()
        }
        Some(Classification::Parity) if r.observed == Some(Verdict::Unknown) && check_fail => {
            format!("compile fails as the compile-fail oracle expects: {}", head_rustc_error(combined))
        }
        Some(Classification::Parity) if r.observed == Some(Verdict::Unknown) => {
            "output matches Kani expected file (diagnostic parity)".into()
        }
        _ => String::new(),
    }
}

/// Append the [`qualifier_note`] to a success-shaped row's note (the three
/// qualified-pass classes and `missed_bug`), so the qualifier is named on the
/// row whichever rule decided the class.
fn with_qualifier_note(note: String, r: &TestResult, combined: &str) -> String {
    let success_shaped = matches!(
        r.classification,
        Some(
            Classification::UnsoundPass
                | Classification::TrivialSafePass
                | Classification::UnattributedPass
                | Classification::MissedBug
        )
    );
    match qualifier_note(combined).filter(|_| success_shaped) {
        Some(q) if note.is_empty() => q,
        Some(q) => format!("{note}; {q}"),
        None => note,
    }
}

fn head_crash(s: &str) -> String {
    for line in s.lines() {
        let l = line.trim();
        if l.contains("exited with status signal:") {
            return format!("verifier crash: {}", truncate(l.trim_start_matches("error: "), 140));
        }
    }
    "verifier killed by signal (no exit code)".into()
}

fn head_unsupported(s: &str) -> String {
    for line in s.lines() {
        let l = line.trim();
        if l.contains("codegen panic") || l.contains("Unsupported") || l.contains("unsupported") {
            return truncate(l, 180);
        }
    }
    "unsupported construct".into()
}

fn head_encoding_gap(s: &str) -> String {
    for line in s.lines() {
        let l = line.trim();
        if l.contains("Failed to parse CHC problem")
            || l.contains("expected argument sort")
            || l.contains("ay-chc inconclusive")
        {
            return truncate(l.trim_start_matches("[AY] "), 200);
        }
    }
    "non-genuine CTREX mapped to FAILED".into()
}

/// The first *rustc diagnostic* line (`error[E…]`), falling back to the
/// generic error head — for check-fail parity notes, the coded diagnostic is
/// the informative line, not the driver's exit-status echo.
fn head_rustc_error(s: &str) -> String {
    for line in s.lines() {
        let l = line.trim();
        if l.starts_with("error[") {
            return truncate(l, 160);
        }
    }
    head_error(s)
}

fn head_error(s: &str) -> String {
    for line in s.lines() {
        let l = line.trim();
        if l.starts_with("error[") || l.starts_with("error:") || l.contains("not found in PATH") {
            return truncate(l, 160);
        }
    }
    "no VERIFICATION verdict emitted".into()
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        let mut t: String = s.chars().take(n.saturating_sub(1)).collect();
        t.push('…');
        t
    }
}

/// Conservative default job count: half the cores, capped, since each verifier
/// is itself multi-threaded and memory-heavy.
pub fn default_jobs() -> usize {
    let par = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    (par / 2).clamp(1, 6)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Classification as C, Verdict as V};

    /// The `function-contract/modifies/field_replace_pass` shape: a user
    /// harness verifies, a sibling `proof_for_contract` harness fails with a
    /// genuine counterexample, and the expected file says `VERIFICATION:-
    /// SUCCESSFUL` and nothing about the contract harness. Kani's
    /// `contains_lines` rule passes such a file whatever that harness does,
    /// so the expected file cannot vouch for the failing harness: scorer
    /// version 1 credited parity here; version 2 keeps the false positive,
    /// records that the criterion held, and leaves `tiebreak_applied` false.
    #[test]
    fn silent_expected_file_cannot_upgrade_a_false_positive() {
        let combined = "\
Checking harness good...
VERIFICATION:- SUCCESSFUL
Checking harness contract_harness...
[AY:CTREX_CAT:Genuine]
Failed Checks: |result| bogus
VERIFICATION:- FAILED
Manual Harness Summary:
Verification failed for - contract_harness
Complete - 1 successfully verified harnesses, 1 failures, 2 total.
";
        let expected = "VERIFICATION:- SUCCESSFUL\n";
        let scored = scored_engine(Engine::TrustMc, V::Success, combined, false, Some(1), false, Some(expected), false);
        assert_eq!(scored.class, C::FalsePositive);
        assert!(!scored.tiebreak_applied);
        assert!(scored.kani_criterion_refused, "the criterion held; the refusal is recorded");
        let row = scored_unit(V::Success, combined, Some(1), Some(expected));
        assert_eq!(row.classification, Some(C::FalsePositive));
        assert!(!row.tiebreak_applied);
        assert!(row.note.contains("does not name the failing harness"), "{}", row.note);
        assert_eq!(row.scorer_version, SCORER_VERSION);
    }

    /// The one shape where the expected file DOES vouch for the failing
    /// harness: it quotes a sibling's SUCCESSFUL line (so the derived oracle
    /// is `success`) AND the summary's `Verification failed for - X` for
    /// exactly the harness trust-mc fails. Same verdict as Kani — parity,
    /// with `tiebreak_applied` set. An expected file naming a DIFFERENT
    /// harness, or a second failing harness it does not name, is not that
    /// shape and stays a false positive.
    #[test]
    fn tiebreak_needs_the_expected_file_to_name_exactly_the_failing_harnesses() {
        let combined = "\
Checking harness good...
VERIFICATION:- SUCCESSFUL
Checking harness contract_harness...
[AY:CTREX_CAT:Genuine]
VERIFICATION:- FAILED
Manual Harness Summary:
Verification failed for - contract_harness
Complete - 1 successfully verified harnesses, 1 failures, 2 total.
";
        let names_it = "VERIFICATION:- SUCCESSFUL\nVerification failed for - contract_harness\\\n";
        let scored = scored_engine(Engine::TrustMc, V::Success, combined, false, Some(1), false, Some(names_it), false);
        assert_eq!(scored, Scored {
            class: C::Parity,
            tiebreak_applied: true,
            kani_criterion_refused: false,
            reason: Some("parity via Kani tiebreak: expected file names exactly the harnesses that failed"),
        });
        let row = scored_unit(V::Success, combined, Some(1), Some(names_it));
        assert!(row.tiebreak_applied);
        assert!(row.note.starts_with("parity via Kani tiebreak"), "{}", row.note);

        let names_other = "VERIFICATION:- SUCCESSFUL\nVerification failed for - good\n";
        assert_eq!(
            classify_full(V::Success, combined, false, Some(1), false, Some(names_other)),
            C::FalsePositive
        );
        // Kani's criterion itself must still hold: a line the output lacks
        // blocks the tiebreak even when the names agree.
        let names_but_misses = "VERIFICATION:- SUCCESSFUL\nVerification failed for - contract_harness\nsome line trust-mc never prints\n";
        assert_eq!(
            classify_full(V::Success, combined, false, Some(1), false, Some(names_but_misses)),
            C::FalsePositive
        );
        // A tainted sibling success blocks parity even through the tiebreak.
        let tainted = combined.replace("VERIFICATION:- SUCCESSFUL\n", "[AY:SOUND_FALLBACK:1]\nVERIFICATION:- SUCCESSFUL\n");
        let scored = scored_engine(Engine::TrustMc, V::Success, &tainted, false, Some(1), false, Some(names_it), false);
        assert_eq!((scored.class, scored.tiebreak_applied), (C::UnsoundPass, true));
        // No expected file, or the run-level path (a single harness), never
        // fires it.
        let single = "Checking harness only...\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n";
        let scored = scored_engine(Engine::TrustMc, V::Success, single, false, Some(1), false, Some("VERIFICATION:- FAILED\n"), false);
        assert_eq!((scored.class, scored.tiebreak_applied, scored.kani_criterion_refused), (C::FalsePositive, false, true));
    }

    /// ...but the tiebreaker must NOT launder a real false positive. This is
    /// the `loop-contract/decreases_binary_search` shape: a single harness that
    /// fails, whose output never contains the expected success line at all.
    #[test]
    fn fp_survives_when_output_misses_the_expected_verdict() {
        let combined = "\
Checking harness only...
[AY:CTREX_CAT:Genuine]
Failed Checks: assertion failed: result == Some(2)
VERIFICATION:- FAILED
";
        let expected = "VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(
            classify_full(V::Success, combined, false, Some(1), false, Some(expected)),
            C::FalsePositive,
            "the expected success line is absent, so Kani fails this file too"
        );
    }

    /// With no expected file there is no Kani criterion to consult, so the
    /// verdict rule stands unchanged.
    #[test]
    fn fp_survives_without_an_expected_file() {
        let combined = "\
Checking harness only...
[AY:CTREX_CAT:Genuine]
VERIFICATION:- FAILED
";
        assert_eq!(
            classify_full(V::Success, combined, false, Some(1), false, None),
            C::FalsePositive
        );
    }

    /// End-to-end: parse a raw verifier transcript and classify it against an
    /// oracle, exactly as `run_one` does.
    fn classify_full(
        oracle: V,
        combined: &str,
        timed_out: bool,
        exit: Option<i32>,
        is_cargo: bool,
        expected: Option<&str>,
    ) -> C {
        classify_ctx(oracle, combined, timed_out, exit, is_cargo, expected, false)
    }

    #[allow(clippy::too_many_arguments)]
    fn classify_ctx(
        oracle: V,
        combined: &str,
        timed_out: bool,
        exit: Option<i32>,
        is_cargo: bool,
        expected: Option<&str>,
        check_fail: bool,
    ) -> C {
        classify_engine(Engine::TrustMc, oracle, combined, timed_out, exit, is_cargo, expected, check_fail)
    }

    /// The Kani engine's classification of a raw `kani` transcript for a
    /// `kani`-suite unit (compiletest `kani` mode: the exit-status
    /// criterion, no expected file consulted).
    fn classify_kani(oracle: V, combined: &str, exit: Option<i32>, expected: Option<&str>) -> C {
        classify_kani_in("kani", oracle, combined, exit, expected)
    }

    #[allow(clippy::too_many_arguments)]
    fn classify_engine(
        engine: Engine,
        oracle: V,
        combined: &str,
        timed_out: bool,
        exit: Option<i32>,
        is_cargo: bool,
        expected: Option<&str>,
        check_fail: bool,
    ) -> C {
        scored_engine(engine, oracle, combined, timed_out, exit, is_cargo, expected, check_fail).class
    }

    /// The full `Scored` (classification plus the tiebreak audit bits).
    #[allow(clippy::too_many_arguments)]
    fn scored_engine(
        engine: Engine,
        oracle: V,
        combined: &str,
        timed_out: bool,
        exit: Option<i32>,
        is_cargo: bool,
        expected: Option<&str>,
        check_fail: bool,
    ) -> Scored {
        let mut r = TestResult { exit_code: exit, ..TestResult::blank("t", "f.rs", oracle) };
        parse_markers(combined, &mut r);
        reattribute_multi_harness_markers(combined, &mut r, engine);
        let observed = parse_verdict(combined);
        r.observed = Some(observed);
        let ctx = ClassifyCtx {
            engine,
            criterion: PassCriterion::ExitStatus,
            oracle,
            observed,
            timed_out,
            exit,
            is_cargo,
            expected,
            check_fail,
            ice_oracle: expected.is_some_and(crate::discover::expected_is_kani_ice),
        };
        match engine {
            Engine::TrustMc => classify(&ctx, &r, combined),
            Engine::Kani => super::classify_kani(&ctx, &r, combined),
        }
    }

    /// The Kani engine's classification of a raw `kani` transcript for a
    /// unit of `suite`, under that suite's compiletest pass criterion.
    fn scored_kani(suite: &str, oracle: V, combined: &str, exit: Option<i32>, expected: Option<&str>) -> Scored {
        let mut r = TestResult { exit_code: exit, ..TestResult::blank(suite, "f.rs", oracle) };
        parse_markers(combined, &mut r);
        reattribute_multi_harness_markers(combined, &mut r, Engine::Kani);
        r.no_harnesses |= combined.contains(KANI_NO_HARNESSES);
        let observed = parse_verdict(combined);
        r.observed = Some(observed);
        let ctx = ClassifyCtx {
            engine: Engine::Kani,
            criterion: suites::lookup(suite).expect("a registered suite").criterion,
            oracle,
            observed,
            timed_out: false,
            exit,
            is_cargo: false,
            expected,
            check_fail: false,
            ice_oracle: false,
        };
        super::classify_kani(&ctx, &r, combined)
    }

    fn classify_kani_in(suite: &str, oracle: V, combined: &str, exit: Option<i32>, expected: Option<&str>) -> C {
        scored_kani(suite, oracle, combined, exit, expected).class
    }

    /// `score_unit` end to end, as `run_one` and `rescore` call it.
    fn scored_unit(oracle: V, combined: &str, exit: Option<i32>, expected: Option<&str>) -> TestResult {
        let mut r = TestResult::blank("t", "f.rs", oracle);
        let unit = UnitCtx {
            engine: Engine::TrustMc,
            suite: "t",
            rel: "f.rs",
            oracle,
            is_cargo: false,
            check_fail: false,
            expected,
            route: Route::DevCli,
            route_attestation: None,
            upstream_ignored: false,
        };
        let attempt = Attempt {
            stdout: combined,
            stderr: "",
            exit_code: exit,
            timed_out: false,
            retried_after_outer_timeout: false,
            spawn_error: None,
        };
        score_unit(&unit, &attempt, &mut r);
        r
    }

    fn classify_output(oracle: V, combined: &str, timed_out: bool, exit: Option<i32>) -> C {
        classify_full(oracle, combined, timed_out, exit, false, None)
    }

    #[test]
    fn verdict_parsing() {
        assert_eq!(parse_verdict("…\nVERIFICATION:- SUCCESSFUL\n"), V::Success);
        assert_eq!(parse_verdict("…\nVERIFICATION:- FAILED\n"), V::Fail);
        assert_eq!(parse_verdict("nothing here"), V::Unknown);
        // Any FAILED wins (a file with a failing harness among successes).
        assert_eq!(
            parse_verdict("VERIFICATION:- SUCCESSFUL\nVERIFICATION:- FAILED\n"),
            V::Fail
        );
    }

    #[test]
    fn marker_parsing() {
        let mut r = TestResult::blank("", "", V::Success);
        parse_markers(
            "[AY:SOUND_FALLBACK:2] x [AY:SOUND_FALLBACK:3]\n[AY:CTREX_CAT:Unknown]\n[AY:UNKNOWN_REASON:SolverError]\npointee_synthesis_fallback",
            &mut r,
        );
        assert_eq!(r.sound_fallback, 5);
        assert_eq!(r.ctrex_category.as_deref(), Some("Unknown"));
        assert_eq!(r.unknown_reason.as_deref(), Some("SolverError"));
        assert!(r.self_reported_unsound);
        assert!(r.demotion_reasons.is_empty(), "no marker => empty, not a phantom entry");
    }

    /// The `[AY:UNKNOWN-CATEGORY]` line closes its bracket BEFORE the payload,
    /// so the value is the rest of the line. Normalizing is what makes the
    /// rollup usable: the raw text carries `predicate=…, array_sorts=…`, which
    /// would otherwise make every row its own bucket.
    ///
    /// This exact line is copied from a real run (prusti/Heapsort.rs), which is
    /// the whole point of the field — it names the specific ceiling (#4259)
    /// instead of the useless catch-all `SolverError`.
    #[test]
    fn unknown_category_normalizes_and_keeps_detail() {
        let (key, detail) = parse_unknown_category(
            "[AY:UNKNOWN-CATEGORY] ≥2 Array-sorted state parameters \
             (predicate=main__bb0, array_sorts=6) — see #4259\nVERIFICATION:- FAILED\n",
        );
        assert_eq!(key.as_deref(), Some("ArrayParamLimit"));
        assert!(detail.unwrap().contains("array_sorts=6"), "raw detail must survive");
    }

    /// Each driver-side `UnknownCategory` variant maps to its own key, and an
    /// UNRECOGNIZED line becomes `Other` rather than being silently dropped —
    /// so a newly added driver category shows up as visibly unmapped.
    #[test]
    fn unknown_category_covers_every_variant_and_flags_new_ones() {
        for (line, want) in [
            ("[AY:UNKNOWN-CATEGORY] PDR invariant synthesis timeout (900ms, 2 engine(s) timed out)", "PdrTimeout"),
            ("[AY:UNKNOWN-CATEGORY] solver error (engine=pdr, stop_reason=NotApplicable)", "SolverError"),
            ("[AY:UNKNOWN-CATEGORY] no error rule encoded (see #4284)", "NoErrorRule"),
            ("[AY:UNKNOWN-CATEGORY] uncategorized — see verbose output", "Uncategorized"),
            ("[AY:UNKNOWN-CATEGORY] something the driver learned to say later", "Other"),
        ] {
            let (key, _) = parse_unknown_category(line);
            assert_eq!(key.as_deref(), Some(want), "line: {line}");
        }
    }

    /// Absent tag => both fields stay None (no phantom bucket on the ~88% of
    /// rows that never print the line).
    #[test]
    fn unknown_category_absent_yields_none() {
        let (key, detail) = parse_unknown_category("VERIFICATION:- SUCCESSFUL\n[AY:PROOF]\n");
        assert!(key.is_none() && detail.is_none());
    }

    /// A multi-harness file prints one `[AY:DEMOTION_REASONS:…]` per demoted
    /// harness. All occurrences are collected, comma-split, de-duplicated,
    /// first-seen order preserved.
    #[test]
    fn demotion_reasons_collected_across_occurrences_and_deduped() {
        let mut r = TestResult::blank("", "", V::Fail);
        parse_markers(
            "[AY:DEMOTION_REASONS:chc_fallback,constant_zero_fallback=1]\n\
             VERIFICATION:- FAILED\n\
             [AY:DEMOTION_REASONS:chc_fallback,drop_fallback]\n",
            &mut r,
        );
        assert_eq!(
            r.demotion_reasons,
            vec![
                "chc_fallback".to_string(),
                "constant_zero_fallback=1".to_string(),
                "drop_fallback".to_string()
            ]
        );
    }

    /// PARITY INTEGRITY: a demoted proof is not a counterexample, so it may
    /// never be credited as parity.
    ///
    /// A demoted proof carries `[AY:DEMOTION_REASONS:…]` and NO
    /// `[AY:CTREX_CAT:…]` (the driver classifies CTREX only for non-demoted
    /// failures, harness_runner.rs:573). Before the fix this row was read as a
    /// genuine cex: oracle=fail scored `Parity` — a parity credit for a result
    /// with no counterexample at all — and oracle=success scored
    /// `FalsePositive`. Both are now `Unknown`, matching what the multi-harness
    /// lane already did via `cats.is_empty()`.
    #[test]
    fn demoted_proof_is_never_credited_as_parity() {
        let demoted = "[AY:DEMOTION_REASONS:chc_fallback]\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Fail, demoted, false, Some(1)), C::Unknown);
        assert_eq!(classify_output(V::Success, demoted, false, Some(1)), C::Unknown);
    }

    /// The taint is gated on demotion EVIDENCE, not merely on a missing
    /// category: a bare cat-less FAILED (e.g. from a driver predating the
    /// marker) must keep its previous classification, so the fix cannot
    /// silently over-reject historical or third-party output.
    #[test]
    fn bare_cat_less_failure_is_unaffected_by_the_demotion_taint() {
        let bare = "VERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Fail, bare, false, Some(1)), C::Parity);
        assert_eq!(classify_output(V::Success, bare, false, Some(1)), C::FalsePositive);
    }

    #[test]
    fn parity_clean_proof() {
        let out = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::Parity);
    }

    #[test]
    fn parity_expected_fail_genuine_ctrex() {
        // oracle=Fail, trust-mc finds a genuine counterexample -> parity.
        let out = "[AY:CTREX_CAT:Genuine]\nCTREX breakdown: 0 EncodingGap, 0 OverApproximation, 1 Genuine, 0 Unknown\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Parity);
    }

    #[test]
    fn encoding_gap_ill_sorted_chc() {
        // The Fibonacci/ControlFlow class: ill-sorted CHC mapped to FAILED.
        let out = "Failed to parse CHC problem: parse error: Predicate 'main__bb44' expected argument sort (_ BitVec 64)\n[AY:CTREX_CAT:Unknown]\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::EncodingGap);
    }

    #[test]
    fn unknown_not_false_positive() {
        // Inconclusive UNKNOWN mapped to FAILED must NOT be a false positive.
        let out = "[AY:CTREX_CAT:Unknown]\n[AY:UNKNOWN_REASON:SolverError]\nCHC verification: ay-chc inconclusive\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Unknown);
    }

    #[test]
    fn genuine_false_positive() {
        // oracle=Success but trust-mc reports a genuine counterexample.
        let out = "[AY:CTREX_CAT:Genuine]\nCTREX breakdown: 0 EncodingGap, 0 OverApproximation, 1 Genuine, 0 Unknown\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::FalsePositive);
    }

    #[test]
    fn missed_bug_is_critical() {
        // oracle=Fail but trust-mc says SUCCESSFUL -> soundness-critical.
        let out = "VERIFICATION:- SUCCESSFUL\n";
        let c = classify_output(V::Fail, out, false, Some(0));
        assert_eq!(c, C::MissedBug);
        assert!(c.is_critical());
    }

    #[test]
    fn unsound_pass_via_fallback() {
        let out = "[AY:SOUND_FALLBACK:1]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::UnsoundPass);
    }

    #[test]
    fn unsound_pass_via_self_report() {
        let out = "UNSOUND verification - iterator constraints were lost.\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::UnsoundPass);
    }

    #[test]
    fn unsupported_construct() {
        let out = "CHC codegen panic in check_any_char\nunsupported constructs\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Unsupported);
    }

    #[test]
    fn compiler_timeout_is_timeout_not_error() {
        let out = "error: /…/trust-mc-compiler timed out after 80.0s. Use --tool-timeout to increase";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Timeout);
    }

    #[test]
    fn watchdog_timeout() {
        assert_eq!(classify_output(V::Success, "", true, None), C::Timeout);
    }

    #[test]
    fn hard_error_no_verdict() {
        let out = "error[E0425]: cannot find value\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Error);
    }

    // ---- crash / build-unavailable buckets ---------------------------------

    #[test]
    fn sigabrt_is_crash_not_error() {
        let out = "some output\nerror: Process exited with status signal: 6 (SIGABRT)\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Crash);
    }

    #[test]
    fn signal_death_without_exit_code_is_crash() {
        assert_eq!(classify_output(V::Success, "partial output", false, None), C::Crash);
    }

    #[test]
    fn unbuildable_cargo_package_is_build_unavailable() {
        let out = "error: failed to load source for dependency `tokio`\n\
                   Unable to update registry `crates-io`\n";
        assert_eq!(classify_full(V::Success, out, false, Some(101), true, None), C::BuildUnavailable);
    }

    // ---- Kani expected-output matching -------------------------------------

    #[test]
    fn matches_expected_plain_lines() {
        let out = "a\nerror: no harnesses matched the harness filter: `foo`\nb\n";
        assert!(matches_expected(out, "error: no harnesses matched the harness filter: `foo`\n"));
        assert!(!matches_expected(out, "error: something else\n"));
    }

    #[test]
    fn matches_expected_consecutive_blocks() {
        let exp = "error: failed to resolve `foo`: Found:\n       mod2::foo\\\n       mod1::foo\n";
        let hit = "error: failed to resolve `foo`: Found:\n       mod2::foo\n       mod1::foo\n";
        let miss = "error: failed to resolve `foo`: Found:\n       mod2::foo\nunrelated\n       mod1::foo\n";
        assert!(matches_expected(hit, exp));
        assert!(!matches_expected(miss, exp));
    }

    #[test]
    fn diagnostic_parity_when_output_matches_expected_and_no_verdict() {
        // The oracle EXPECTS this error diagnostic; trust-mc emitted exactly
        // it (and no verdict). That is parity, not an error.
        let exp = "error: no harnesses matched the harness filter: `foo`\n";
        let out = "Manual Harness Summary:\nerror: no harnesses matched the harness filter: `foo`\n";
        assert_eq!(classify_full(V::Success, out, false, Some(1), false, Some(exp)), C::Parity);
    }

    #[test]
    fn expected_match_does_not_override_verdict_discipline_for_single_files() {
        // Single-file test WITH a verdict: the CTREX-genuineness machinery
        // stays authoritative; a lucky line match must not upgrade an
        // encoding-gap FAILED to parity.
        let exp = "VERIFICATION:- FAILED\n";
        let out = "Failed to parse CHC problem: parse error: Predicate 'x' expected argument sort\n\
                   [AY:CTREX_CAT:Unknown]\nVERIFICATION:- FAILED\n";
        assert_eq!(
            classify_full(V::Fail, out, false, Some(1), false, Some(exp)),
            C::EncodingGap
        );
    }

    #[test]
    fn cargo_unit_parity_via_expected_file() {
        let exp = "Verification failed for - ptr::verify::check_as_ref_dangling\n\
                   Complete - 5 successfully verified harnesses, 1 failures, 6 total.\n";
        let out = "[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n\
                   Verification failed for - ptr::verify::check_as_ref_dangling\n\
                   Complete - 5 successfully verified harnesses, 1 failures, 6 total.\n";
        assert_eq!(classify_full(V::Fail, out, false, Some(1), true, Some(exp)), C::Parity);
    }

    // ---- validated #[kani::should_panic] passes (cluster: expected-panic) ---

    /// The exact single-file shape trust-mc emits for a `#[kani::should_panic]`
    /// harness whose expected panic was found and validated Genuine (e.g.
    /// `kani/Invariant/percentage.rs`, `expected/derive-invariant/…`,
    /// `expected/derive-arbitrary/…`): that IS Kani's pass verdict — parity,
    /// not an unsound pass.
    #[test]
    fn validated_should_panic_pass_is_parity() {
        let out = "[AY:CTREX] CHC verification: counterexample reachable (exact CHC derivation)\n\
                   [AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                   [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n\
                   [AY:PROOF] CHC verification: property proven (false error obligation)\n\
                   VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::Parity);
    }

    /// A should_panic "pass" whose panic evidence was NOT validated Genuine
    /// (OverApproximation / Unknown CTREX) stays an unsound pass — the panic
    /// may be spurious.
    #[test]
    fn should_panic_pass_without_genuine_ctrex_stays_unsound() {
        let out = "[AY:CTREX_CAT:OverApproximation]\n\
                   VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                   [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n";
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::UnsoundPass);
        // No CTREX category at all: fail closed.
        let out2 = "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                    [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n";
        assert_eq!(classify_output(V::Success, out2, false, Some(0)), C::UnsoundPass);
    }

    /// A bare per-harness `VERIFICATION:- UNVALIDATED (...)` (a driver
    /// demotion the harness could not validate, e.g. DT+BV) must aggregate the
    /// FILE verdict to Unknown, never let sibling SUCCESSFUL harnesses score
    /// the file as an observed Success. Regression: kani/SIMD/portable_simd.rs
    /// classified unsound_pass when check_mask emitted this verdict alongside
    /// two genuine successes (2026-07-19 wall).
    #[test]
    fn bare_unvalidated_harness_never_aggregates_to_file_success() {
        let out = "Checking harness check_resize...\n\
                   VERIFICATION:- SUCCESSFUL\n\
                   Checking harness check_mask...\n\
                   [AY:SOUND_FALLBACK:1]\n\
                   [AY:UNKNOWN_REASON:SolverError]\n\
                   VERIFICATION:- UNVALIDATED (DT+BV)\n\
                   Checking harness check_sum_any...\n\
                   VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(super::parse_verdict(out), Verdict::Unknown);
        // The inline `SUCCESSFUL (UNVALIDATED)` form is a success claim and
        // stays a Success at the parser level; clean_success keeps it from
        // earning credit (`an_unvalidated_success_never_earns_credit`).
        let legacy = "VERIFICATION:- SUCCESSFUL (UNVALIDATED) (encountered one or more panics as expected)\n";
        assert_eq!(super::parse_verdict(legacy), Verdict::Success);
    }

    /// `VERIFICATION:- SUCCESSFUL (UNVALIDATED)` without any effective-success
    /// marker (a non-linear tier, or an off-pin solver) used to satisfy
    /// `clean_success` and score parity. It never earns credit, and against a
    /// Fail oracle it is still a missed bug.
    #[test]
    fn an_unvalidated_success_never_earns_credit() {
        let out = "VERIFICATION:- SUCCESSFUL (UNVALIDATED)\n";
        assert_eq!(super::parse_verdict(out), Verdict::Success);
        assert_eq!(classify_output(V::Success, out, false, Some(0)), C::UnsoundPass);
        assert_eq!(classify_output(V::Fail, out, false, Some(0)), C::MissedBug);

        // The cargo-unit expected-file arm does not launder it either.
        let summary = "Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        let cargo_out = format!("{out}{summary}");
        assert_eq!(
            classify_full(V::Success, &cargo_out, false, Some(0), true, Some(summary)),
            C::UnsoundPass
        );
        let clean_cargo = format!("VERIFICATION:- SUCCESSFUL\n{summary}");
        assert_eq!(
            classify_full(V::Success, &clean_cargo, false, Some(0), true, Some(summary)),
            C::Parity
        );

        // Nor does a proof marker make it exceed an unsupported-construct oracle.
        let unsupported = "Failed Checks: foo is not currently supported by Kani\n";
        let proved = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL (UNVALIDATED)\n";
        assert_eq!(
            classify_full(V::Fail, proved, false, Some(0), false, Some(unsupported)),
            C::MissedBug
        );
        let clean_proof = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(
            classify_full(V::Fail, clean_proof, false, Some(0), false, Some(unsupported)),
            C::ExceedsOracle
        );
    }

    /// A row whose driver accepted an off-pin `ay` is never scored, whatever
    /// its verdict, and says why.
    #[test]
    fn a_run_on_an_off_pin_solver_is_an_error_row() {
        let marker = "[AY:SOLVER_PIN_MISMATCH:found=dd4de9e94e0bb94a458641c7e5aa814c8aeadf59:pin=94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322]";
        let success = format!("{marker}\nVERIFICATION:- SUCCESSFUL (UNVALIDATED)\n");
        let genuine_fail = format!("{marker}\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n");
        for out in [&success, &genuine_fail] {
            for oracle in [V::Success, V::Fail] {
                assert_eq!(classify_output(oracle, out, false, Some(0)), C::Error, "{out}");
            }
            assert_eq!(classify_output(V::Success, out, true, None), C::Error, "{out}");
        }
        let r = TestResult {
            observed: Some(V::Fail),
            classification: Some(C::Error),
            ..TestResult::blank("t", "f.rs", V::Fail)
        };
        let ctx = ClassifyCtx {
            engine: Engine::TrustMc,
            criterion: PassCriterion::ExitStatus,
            oracle: V::Fail,
            observed: V::Fail,
            timed_out: true,
            exit: None,
            is_cargo: false,
            expected: None,
            check_fail: false,
            ice_oracle: false,
        };
        let note = note_for(&r, &ctx, &genuine_fail, Scored::plain(C::Error));
        assert!(note.starts_with("ran on an off-pin ay solver"), "{note}");
        assert!(note.contains(marker), "{note}");
    }

    /// An effective success with any reason other than the should_panic one,
    /// or an UNVALIDATED verdict, or a fallback alongside, stays unsound.
    #[test]
    fn other_effective_success_shapes_stay_unsound() {
        let other_reason = "[AY:CTREX_CAT:Genuine]\n\
                            VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                            [AY:EFFECTIVE_SUCCESS:some_new_reason]\n";
        assert_eq!(classify_output(V::Success, other_reason, false, Some(0)), C::UnsoundPass);
        let unvalidated = "[AY:CTREX_CAT:Genuine]\n\
                           VERIFICATION:- SUCCESSFUL (UNVALIDATED) (encountered one or more panics as expected)\n\
                           [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n";
        assert_eq!(classify_output(V::Success, unvalidated, false, Some(0)), C::UnsoundPass);
        let with_fallback = "[AY:SOUND_FALLBACK:1]\n[AY:CTREX_CAT:Genuine]\n\
                             VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                             [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n";
        assert_eq!(classify_output(V::Success, with_fallback, false, Some(0)), C::UnsoundPass);
    }

    /// The dir-level expected file of a should_panic test matches trust-mc's
    /// output for a cargo unit: the validated pass is parity there too.
    #[test]
    fn cargo_should_panic_pass_via_expected_file_is_parity() {
        let exp = "Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        let out = "[AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                   [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n\
                   Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        assert_eq!(classify_full(V::Success, out, false, Some(0), true, Some(exp)), C::Parity);
    }

    // ---- kani-check-fail compile-error parity ------------------------------

    /// `// kani-check-fail`: Kani expects *compilation* to fail. trust-mc
    /// rejecting the file with the same genuine rustc error (E0382 & co) is
    /// the oracle verdict — parity, not a tool error (kani/Slice/drop_in_place,
    /// kani/Serde/main, kani/Panic/compile_panic, kani/Intrinsics/Forget/forget_fail).
    #[test]
    fn check_fail_compile_error_is_parity() {
        let out = "error[E0382]: borrow of moved value: `v`\n\
                   error: aborting due to 1 previous error; 1 warning emitted\n\
                   error: Process exited with status exit status: 101\n";
        assert_eq!(classify_ctx(V::Fail, out, false, Some(1), false, None, true), C::Parity);
    }

    /// Without the kani-check-fail directive the same compile error stays an
    /// error: Kani would have compiled the file (e.g. kani-verify-fail tests),
    /// so trust-mc failing to build it is a genuine gap.
    #[test]
    fn compile_error_without_check_fail_directive_stays_error() {
        let out = "error[E0382]: borrow of moved value: `v`\n\
                   error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, out, false, Some(1), false, None, false), C::Error);
    }

    /// A check-fail test where trust-mc dies of its own driver/compiler panic
    /// (not a rustc diagnostic) is NOT parity.
    #[test]
    fn check_fail_driver_panic_is_not_parity() {
        let out = "thread 'rustc' panicked at compiler/…: internal error\n\
                   error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, out, false, Some(1), false, None, true), C::Error);
        // A zero exit can't be a compile failure either.
        let out2 = "error[E0382]: borrow of moved value: `v`\nerror: aborting due to 1 previous error\n";
        assert_ne!(classify_ctx(V::Fail, out2, false, Some(0), false, None, true), C::Parity);
    }

    /// A compile-fail oracle is never satisfied by a *verification* verdict:
    /// the `expected/intrinsics/simd-*` E0511 family (expected file = rustc
    /// compile-error text) must not score parity when trust-mc verifies — or
    /// fail-verifies — a program rustc itself rejects at monomorphization.
    /// Both polarities are an `error` (missing rustc diagnostic), never
    /// parity / missed_bug / false_positive.
    #[test]
    fn check_fail_oracle_with_verification_verdict_is_error() {
        // trust-mc "proves" the uncompilable program (simd-extract-wrong-type
        // shape: was dishonest parity via the defaulted success oracle).
        let proved = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_ctx(V::Fail, proved, false, Some(0), false, None, true), C::Error);
        // trust-mc reports a genuine-looking counterexample instead of the
        // compile error (simd-result-type-is-float shape): coarse fail==fail
        // must not count as parity.
        let cex = "[AY:CTREX_CAT:Genuine]\n\
                   CTREX breakdown: 0 EncodingGap, 0 OverApproximation, 1 Genuine, 0 Unknown\n\
                   VERIFICATION:- FAILED\n";
        assert_eq!(classify_ctx(V::Fail, cex, false, Some(1), false, None, true), C::Error);
        // A matching expected diagnostic (observed Unknown) still classifies
        // parity through the existing check-fail path.
        let exp = "expected return type with integer elements\nerror: aborting due to 1 previous error\n";
        let diag = "error[E0511]: invalid monomorphization of `simd_eq` intrinsic: \
                    expected return type with integer elements, found `f32x2`\n\
                    error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, diag, false, Some(1), false, Some(exp), true), C::Parity);
    }

    /// When the check-fail test has an expected file, its diagnostic text must
    /// actually appear in trust-mc's output (e.g. expected/stub-set-* emit a
    /// *different* diagnostic today and must stay error).
    #[test]
    fn check_fail_with_non_matching_expected_stays_error() {
        let exp = "is not a stub set (missing `kani::stub_set!` definition)\n";
        let out = "error: failed to resolve `NOT_A_STUB_SET`: expected function / method, found constant\n\
                   error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, out, false, Some(1), false, Some(exp), true), C::Error);
        // …and matching expected text is parity.
        let out2 = "error: `NOT_A_STUB_SET` is not a stub set (missing `kani::stub_set!` definition)\n\
                    error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, out2, false, Some(1), false, Some(exp), true), C::Parity);
    }

    /// A compile-fail oracle from an expected file (plan item: diagnostic or
    /// ICE expected files are never oracle=Success) is parity only when
    /// trust-mc fails to compile with that diagnostic: nonzero exit, no
    /// verdict, the expected lines present, and no panic unless the expected
    /// file quotes an ICE. The diagnostic arm that credits verdict-less
    /// output never decides such a unit.
    #[test]
    fn compile_fail_oracle_needs_a_failed_compile_with_the_expected_diagnostic() {
        let exp = "error: Using the proof_for_contract attribute requires activating the unstable `function-contracts` feature\n";
        let out = "error: Using the proof_for_contract attribute requires activating the unstable `function-contracts` feature\n\
                   error: aborting due to 1 previous error\n";
        assert_eq!(classify_ctx(V::Fail, out, false, Some(1), false, Some(exp), true), C::Parity);
        // A zero exit is not a failed compile, even with the line printed and no verdict.
        assert_eq!(classify_ctx(V::Fail, out, false, Some(0), false, Some(exp), true), C::Error);
        // The unwind-flags-conflict shape: the diagnostic printed, then a verification anyway.
        let verified = format!("{out}[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]\nVERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)\n");
        assert_eq!(classify_ctx(V::Fail, &verified, false, Some(0), false, Some(exp), true), C::Error);
        assert_eq!(classify_ctx(V::Fail, &verified, false, Some(1), false, Some(exp), true), C::Error);
        // A different diagnostic is not the expected one.
        assert_eq!(classify_ctx(V::Fail, "error[E0425]: cannot find value `x`\n", false, Some(1), false, Some(exp), true), C::Error);
        // A panic is not the diagnostic a non-ICE expected file names …
        let panicked = format!("{out}thread 'rustc' panicked at compiler/x.rs:1:1\n");
        assert_eq!(classify_ctx(V::Fail, &panicked, false, Some(101), false, Some(exp), true), C::Error);
        // … but it is exactly what an ICE expected file names.
        let ice = "Kani unexpectedly panicked during compilation.\n";
        let ice_out = "thread 'rustc' panicked at compiler/rustc_mir_transform/src/validate.rs:81:25:\n\
                       Kani unexpectedly panicked during compilation.\n";
        assert_eq!(classify_ctx(V::Fail, ice_out, false, Some(1), false, Some(ice), true), C::Parity);
        assert_eq!(classify_ctx(V::Fail, "error: aborting due to 1 previous error\n", false, Some(1), false, Some(ice), true), C::Error);
        // A manifest entry whose upstream diagnostic is a panic carrying the
        // message (`offset-invalid-args`) accepts trust-mc's panic with it;
        // a non-ICE entry does not.
        let score = |rel: &str, exp: &str, out: &str| {
            let unit = UnitCtx {
                engine: Engine::TrustMc,
                suite: "expected",
                rel,
                oracle: V::Fail,
                is_cargo: false,
                check_fail: true,
                expected: Some(exp),
                route: Route::DevCli,
                route_attestation: None,
                upstream_ignored: false,
            };
            let attempt = Attempt { stdout: out, stderr: "", exit_code: Some(1), timed_out: false, retried_after_outer_timeout: false, spawn_error: None };
            let mut r = TestResult::blank("expected", rel, V::Fail);
            score_unit(&unit, &attempt, &mut r);
            r.classification
        };
        let offset = "                                Cannot offset non-pointer type &'{erased} [i32; 1_usize]\n\
                      thread 'rustc' (1) panicked at compiler/rustc_mir_transform/src/validate.rs:81:25:\n\
                      Kani unexpectedly panicked during compilation.\n";
        assert_eq!(score("offset-invalid-args/non_ptr_arg.rs", "Cannot offset non-pointer type\n", offset), Some(C::Parity));
        let stub = "error: `NOT_A_STUB_SET` is not a stub set (missing `kani::stub_set!` definition)\nthread 'rustc' panicked at x\n";
        let stub_exp = "is not a stub set (missing `kani::stub_set!` definition)\n";
        assert_eq!(score("stub-set-not-a-stub-set/main.rs", stub_exp, stub), Some(C::Error));
        // Without check_fail the diagnostic arm still credits verdict-less text (unchanged).
        let text = "Verification Time:\n";
        assert_eq!(classify_ctx(V::Success, "Verification Time: 1s\n", false, Some(0), false, Some(text), false), C::Parity);
    }

    /// BMC-lane transcripts in the shape of the `results-verification-bmc` unit
    /// logs (stdout plus stderr, corpus path as `/corpus`): clean SUCCESSFUL
    /// harnesses beside INCONCLUSIVE ones whose sections print a self-report
    /// (`unconstrained_assignment` inside `[AY:UNKNOWN_QUALITY:…]`, a demotion,
    /// a preamble warning). Scored `unsound_pass` before 2026-09-14. The log
    /// excerpts these were first cut from were never committed (the root
    /// `.gitignore` ignores `*.out`) and are lost; the files are
    /// reconstructions carrying the same markers, and each says so on its
    /// first line (`tests/fixtures_tracked.rs` keeps them trackable).
    const SELF_REPORT_FIXTURES: &[(&str, &str)] = &[
        ("kani/Intrinsics/Atomic/Stable/AtomicPtr/main.rs", include_str!("fixtures/self-report/kani__Intrinsics__Atomic__Stable__AtomicPtr__main.rs.out")),
        ("kani/Invariant/percentage.rs", include_str!("fixtures/self-report/kani__Invariant__percentage.rs.out")),
        ("kani/ProjectionElem/OpaqueCast/check_opaque_cast.rs", include_str!("fixtures/self-report/kani__ProjectionElem__OpaqueCast__check_opaque_cast.rs.out")),
        ("kani/Stubbing/StubPrimitives/stub_slice_methods.rs", include_str!("fixtures/self-report/kani__Stubbing__StubPrimitives__stub_slice_methods.rs.out")),
        ("kani/Coroutines/rustc-coroutine-tests/smoke.rs", include_str!("fixtures/self-report/kani__Coroutines__rustc-coroutine-tests__smoke.rs.out")),
    ];

    /// A clean SUCCESSFUL harness beside an INCONCLUSIVE one is scored by the
    /// verdict rules — `unknown` — never `unsound_pass` for a self-report the
    /// INCONCLUSIVE harness printed, and never `parity`.
    #[test]
    fn success_beside_an_inconclusive_harness_is_unknown_not_unsound_pass() {
        for (unit, out) in SELF_REPORT_FIXTURES {
            assert!(self_reported_unsound(out), "{unit}: the fixture carries a self-report");
            let r = scored_unit(V::Success, out, Some(1), None);
            assert_eq!(r.observed, Some(V::Unknown), "{unit}");
            assert_eq!(r.classification, Some(C::Unknown), "{unit}: {}", r.note);
            // Against a fail oracle it is not a missed bug either.
            assert_eq!(scored_unit(V::Fail, out, Some(1), None).classification, Some(C::Unknown), "{unit}");
        }
        // Same shape without any self-report: still unknown, not parity.
        let mixed = "Checking harness a...\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n\
                     Checking harness b...\n[AY:CTREX_CAT:Unknown]\nVERIFICATION:- INCONCLUSIVE (solver undecided)\n\
                     Manual Harness Summary:\nVerification failed for - b\nComplete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        let r = scored_unit(V::Success, mixed, Some(1), None);
        assert_eq!((r.observed, r.classification), (Some(V::Unknown), Some(C::Unknown)));
        assert!(r.note.starts_with(SUCCESS_BESIDE_UNFINISHED_HARNESS), "{}", r.note);
        // A harness section with no verdict at all is not a success either.
        let cut = "Checking harness a...\nVERIFICATION:- SUCCESSFUL\nChecking harness b...\n[AY:PROOF]\n";
        assert_eq!(parse_verdict(cut), V::Unknown);
    }

    /// The self-report is attributed to the section that printed it: only a
    /// SUCCESSFUL harness's own confession, or one that cannot be attributed
    /// (preamble, stderr after the summary, no summary, one harness), taints
    /// the file's success.
    #[test]
    fn a_self_report_taints_only_the_successful_harness_that_printed_it() {
        let summary = "Manual Harness Summary:\nComplete - 2 successfully verified harnesses, 0 failures, 2 total.\n";
        let clean = "Checking harness a...\nVERIFICATION:- SUCCESSFUL\n";
        let tainted = "Checking harness b...\nwarning: UNSOUND verification: unconstrained_assignment=1\nVERIFICATION:- SUCCESSFUL\n";
        let inconclusive = "Checking harness c...\n[AY:UNKNOWN_QUALITY:EncodingGap:unconstrained_assignment=1]\nVERIFICATION:- INCONCLUSIVE (solver undecided)\n";
        // In a SUCCESSFUL section: taints, and the all-SUCCESSFUL file is unsound_pass.
        let s = format!("{clean}{tainted}{summary}");
        assert!(self_report_taints_success(&s));
        assert_eq!(scored_unit(V::Success, &s, Some(0), None).classification, Some(C::UnsoundPass));
        // Only in an INCONCLUSIVE section: does not taint the successful sibling.
        assert!(!self_report_taints_success(&format!("{clean}{inconclusive}{summary}")));
        // Unattributable: preamble, after the summary (stderr), no summary, one harness.
        let preamble = "warning: UNSOUND: 5 pointer dereference(s) created fresh unconstrained symbolic variables\n";
        assert!(self_report_taints_success(&format!("{preamble}{clean}{clean}{summary}")));
        assert_eq!(scored_unit(V::Success, &format!("{preamble}{clean}{clean}{summary}"), Some(0), None).classification, Some(C::UnsoundPass));
        assert!(self_report_taints_success(&format!("{clean}{inconclusive}{summary}\npointee_synthesis_fallback\n")));
        assert!(self_report_taints_success(&format!("{clean}{inconclusive}")), "no summary line: sections may run into stderr");
        assert!(self_report_taints_success(tainted), "a single harness is the run");
        assert!(!self_report_taints_success(&format!("{clean}{clean}{summary}")));
    }

    /// A compiler-certified no-checks harness (D16) is counted per row from
    /// its qualifier marker or its verdict line; it scores parity against a
    /// success oracle, missed_bug against a fail oracle — never
    /// exceeds_oracle — and a Kani transcript counts none.
    #[test]
    fn certified_no_checks_is_counted_and_never_more_than_parity() {
        let certified = "Checking harness a...\n[AY:VACUOUS:no-checks] a: the harness produced no verification conditions\n\
                         [AY:PROOF] CHC verification: property proven (false error obligation)\n\
                         [AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]\n\
                         VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)\n";
        let clean = "Checking harness b...\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        let summary = "Manual Harness Summary:\nComplete - 2 successfully verified harnesses, 0 failures, 2 total.\n";
        let two = format!("{certified}{clean}{summary}");
        assert_eq!(certified_no_checks(certified), 1);
        assert_eq!(certified_no_checks(clean), 0);
        assert_eq!(certified_no_checks(&format!("{certified}{certified}")), 2);
        assert_eq!(certified_no_checks("VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)\n"), 1, "the verdict line alone counts");
        assert_eq!(certified_no_checks("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]\n"), 0);

        let r = scored_unit(V::Success, &two, Some(0), None);
        assert_eq!((r.classification, r.certified_no_checks), (Some(C::Parity), 1));
        let r = scored_unit(V::Fail, certified, Some(0), None);
        assert_eq!((r.classification, r.certified_no_checks), (Some(C::MissedBug), 1));
        // Even beside an unsupported-construct oracle artifact, never exceeds_oracle.
        let artifact = "Status: FAILURE\\\nDescription: \"foo is not currently supported by Kani\"\n";
        assert_eq!(scored_unit(V::Fail, certified, Some(0), Some(artifact)).classification, Some(C::MissedBug));
        let proof = "[AY:PROOF]\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(scored_unit(V::Fail, proof, Some(0), Some(artifact)).classification, Some(C::ExceedsOracle));
        assert_eq!(scored_kani("kani", V::Success, "Checking harness a...\nVERIFICATION:- SUCCESSFUL\n", Some(0), None).class, C::Parity);
    }

    // Proof-qualifier fixtures (`src/fixtures/proof-qualifiers/`): stdout plus
    // stderr in the driver's shape, corpus path as `/corpus`. They were first cut
    // from the chc-m1 unit logs (trust-mc `04d4e4e67`, `--ay-chc`) for
    // `trivial_safe=no_error_rule`, `clean` and the certified no-checks
    // qualifier, and from a Trust-lane driver log (`smack/structures/point.rs`,
    // CHC, external ay, 2026-09-14) for `unattributed_check=chc.0`; those
    // excerpts were never committed (the root `.gitignore` ignores `*.out`) and
    // are lost. The files are reconstructions with the same harnesses, markers
    // and verdicts, and each says so on its first line.
    const QUAL_IN_MATCH: &str = include_str!("fixtures/proof-qualifiers/kani__Assert__in_match.rs.out");
    const QUAL_FLOAT_SATURATING: &str = include_str!("fixtures/proof-qualifiers/kani__Cast__float_to_int_saturating.rs.out");
    const QUAL_OOB_UB: &str = include_str!("fixtures/proof-qualifiers/expected__offset-bounds-check__out_of_bounds_ub_check.rs.out");
    const QUAL_OOB_UB_EXPECTED: &str = include_str!("fixtures/proof-qualifiers/expected__offset-bounds-check__out_of_bounds_ub_check.rs.expected");
    const QUAL_OFFSET_FROM: &str = include_str!("fixtures/proof-qualifiers/expected__offset-bounds-check__offset_from.rs.out");
    const QUAL_OFFSET_FROM_EXPECTED: &str = include_str!("fixtures/proof-qualifiers/expected__offset-bounds-check__offset_from.rs.expected");
    const QUAL_CLEAN: &str = include_str!("fixtures/proof-qualifiers/kani__CodegenMisc__main.rs.out");
    const QUAL_NO_CHECKS: &str = include_str!("fixtures/proof-qualifiers/kani__DynTrait__upcast.rs.out");
    const QUAL_UNATTRIBUTED: &str = include_str!("fixtures/proof-qualifiers/smack__structures__point.rs.out");

    /// One SUCCESSFUL harness printing `marker`.
    fn one_harness(marker: &str) -> String {
        format!(
            "Checking harness h...\n[AY:PROOF]\n{marker}\nVERIFICATION:- SUCCESSFUL\n\
             Manual Harness Summary:\nComplete - 1 successfully verified harnesses, 0 failures, 1 total.\n"
        )
    }

    /// Every qualifier the driver can print, read per marker; `clean` only
    /// alone; anything else unrecognised and fail-closed. The combined strings
    /// are the driver's own (`harness_runner_tests.rs`): no measured log
    /// carries a `sound_fallback=N` qualifier.
    #[test]
    fn proof_qualifiers_are_read_per_marker_and_fail_closed() {
        let taint = |m: &str| section_success_taint(&format!("{m}\nVERIFICATION:- SUCCESSFUL\n"));
        assert_eq!(taint("[AY:PROOF_QUALIFIERS:clean]"), None);
        assert_eq!(taint("[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]"), None);
        assert_eq!(taint("[AY:PROOF_QUALIFIERS:unattributed_check=chc.0]"), Some(SuccessTaint::Unattributed));
        assert_eq!(taint("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]"), Some(SuccessTaint::TrivialSafe));
        assert_eq!(taint("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,sound_fallback=2]"), Some(SuccessTaint::Unsound));
        assert_eq!(
            taint("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,unattributed_check=chc.0,sound_fallback=1]"),
            Some(SuccessTaint::Unsound)
        );
        assert_eq!(
            taint("[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free,unattributed_check=chc.0]"),
            Some(SuccessTaint::Unattributed)
        );
        assert!(qualifier_recognised("sound_fallback=3"));
        for unrecognised in [
            "[AY:PROOF_QUALIFIERS:]",
            "[AY:PROOF_QUALIFIERS:clean,unattributed_check=chc.0]",
            "[AY:PROOF_QUALIFIERS:trivial_safe=something_else]",
            "[AY:PROOF_QUALIFIERS:unattributed_check=chc.1]",
            "[AY:PROOF_QUALIFIERS:sound_fallback=0]",
            "[AY:PROOF_QUALIFIERS:sound_fallback=many]",
            "[AY:PROOF_QUALIFIERS:a_future_qualifier=1]",
        ] {
            assert_eq!(taint(unrecognised), Some(SuccessTaint::Unsound), "{unrecognised}");
        }
        assert_eq!(
            proof_qualifier_list("[AY:PROOF_QUALIFIERS:clean]\n[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]\n[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,sound_fallback=1]\n"),
            vec!["trivial_safe=no_error_rule", "sound_fallback=1"]
        );

        // Scored end to end: the sound_fallback qualifier is unsound even
        // without the `[AY:SOUND_FALLBACK:N]` marker the driver prints beside it.
        let r = scored_unit(V::Success, &one_harness("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,sound_fallback=2]"), Some(0), None);
        assert_eq!(r.classification, Some(C::UnsoundPass), "{}", r.note);
        assert!(r.note.contains("sound_fallback=2 on h") && r.note.contains("trivial_safe=no_error_rule on h"), "{}", r.note);
        let r = scored_unit(V::Success, &one_harness("[AY:PROOF_QUALIFIERS:a_future_qualifier=1]"), Some(0), None);
        assert_eq!(r.classification, Some(C::UnsoundPass));
        assert!(r.note.contains("a_future_qualifier=1 (unrecognised) on h"), "{}", r.note);
        assert_eq!(r.proof_qualifiers, vec!["a_future_qualifier=1"]);
        // Against a fail oracle every qualified success is still a missed bug.
        for m in ["[AY:PROOF_QUALIFIERS:a_future_qualifier=1]", "[AY:PROOF_QUALIFIERS:sound_fallback=1]"] {
            assert_eq!(scored_unit(V::Fail, &one_harness(m), Some(0), None).classification, Some(C::MissedBug), "{m}");
        }
        // The Kani engine prints no qualifiers and its rules never read one.
        assert_eq!(scored_kani("kani", V::Success, &one_harness("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]"), Some(0), None).class, C::Parity);
    }

    /// `trivial_safe=no_error_rule` (chc-m1-shaped transcripts; the logs
    /// were all parity under scorer v4): its own class against a success oracle, the sibling class of
    /// a multi-harness fail-oracle file whose failures match, and still
    /// `missed_bug` where the oracle says the harness fails.
    #[test]
    fn a_trivial_safe_success_is_trivial_safe_pass_never_parity() {
        let r = scored_unit(V::Success, QUAL_IN_MATCH, Some(0), None);
        assert_eq!(r.classification, Some(C::TrivialSafePass), "{}", r.note);
        assert!(r.note.contains("trivial_safe=no_error_rule on check_assert_in_match"), "{}", r.note);
        assert!(r.note.contains("lost checks, not proved checks"), "{}", r.note);
        assert_eq!(r.proof_qualifiers, vec!["trivial_safe=no_error_rule"]);
        assert_eq!(scored_unit(V::Fail, QUAL_IN_MATCH, Some(0), None).classification, Some(C::MissedBug));
        let without = QUAL_IN_MATCH.replace("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]", "[AY:PROOF_QUALIFIERS:clean]");
        assert_eq!(scored_unit(V::Success, &without, Some(0), None).classification, Some(C::Parity), "the qualifier alone decides");

        // Nine harnesses, each on the shortcut.
        let r = scored_unit(V::Success, QUAL_FLOAT_SATURATING, Some(0), None);
        assert_eq!(r.classification, Some(C::TrivialSafePass), "{}", r.note);
        assert!(r.note.contains("check_f64_to_u128_saturation") && r.note.contains("check_issue_4536_f32_to_u8"), "{}", r.note);

        // Fail oracle, both named harnesses fail genuinely, the third
        // (`check_ptr_end`, SUCCESSFUL under Kani) rests on the shortcut.
        let r = scored_unit(V::Fail, QUAL_OOB_UB, Some(1), Some(QUAL_OOB_UB_EXPECTED));
        assert_eq!(r.classification, Some(C::TrivialSafePass), "{}", r.note);
        assert!(r.note.contains("sibling harness success is not a clean proof") && r.note.contains("on check_ptr_end"), "{}", r.note);
        let without = QUAL_OOB_UB.replace("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]", "[AY:PROOF_QUALIFIERS:clean]");
        assert_eq!(scored_unit(V::Fail, &without, Some(1), Some(QUAL_OOB_UB_EXPECTED)).classification, Some(C::Parity));

        // A named failing harness trust-mc verified stays a missed bug.
        let r = scored_unit(V::Fail, QUAL_OFFSET_FROM, Some(1), Some(QUAL_OFFSET_FROM_EXPECTED));
        assert_eq!(r.classification, Some(C::MissedBug), "{}", r.note);
    }

    /// `unattributed_check=chc.0` (a Trust-lane-shaped transcript): its own class
    /// against a success oracle, `missed_bug` against a fail oracle, and never
    /// `exceeds_oracle`, which the same transcript earns with `clean`.
    #[test]
    fn an_unattributed_chc_check_success_is_unattributed_pass_never_parity() {
        let r = scored_unit(V::Success, QUAL_UNATTRIBUTED, Some(0), None);
        assert_eq!(r.classification, Some(C::UnattributedPass), "{}", r.note);
        assert!(r.note.contains("unattributed_check=chc.0 on main") && r.note.contains("names no property"), "{}", r.note);
        assert_eq!(scored_unit(V::Fail, QUAL_UNATTRIBUTED, Some(0), None).classification, Some(C::MissedBug));
        let artifact = "Status: FAILURE\\\nDescription: \"foo is not currently supported by Kani\"\n";
        assert_eq!(scored_unit(V::Fail, QUAL_UNATTRIBUTED, Some(0), Some(artifact)).classification, Some(C::MissedBug));
        let clean = QUAL_UNATTRIBUTED.replace("[AY:PROOF_QUALIFIERS:unattributed_check=chc.0]", "[AY:PROOF_QUALIFIERS:clean]");
        assert_eq!(scored_unit(V::Fail, &clean, Some(0), Some(artifact)).classification, Some(C::ExceedsOracle));
        assert_eq!(scored_unit(V::Success, &clean, Some(0), None).classification, Some(C::Parity));
    }

    /// `clean` and `no_checks=compiler_certified_obligation_free` (chc-m1-shaped
    /// transcripts) keep the rules they had.
    #[test]
    fn clean_and_certified_no_checks_qualifiers_keep_their_rules() {
        let r = scored_unit(V::Success, QUAL_CLEAN, Some(0), None);
        assert_eq!((r.classification, r.proof_qualifiers.is_empty()), (Some(C::Parity), true), "{}", r.note);
        let r = scored_unit(V::Success, QUAL_NO_CHECKS, Some(0), None);
        assert_eq!((r.classification, r.certified_no_checks), (Some(C::Parity), 1), "{}", r.note);
        assert_eq!(r.proof_qualifiers, vec!["no_checks=compiler_certified_obligation_free"]);
        assert_eq!(scored_unit(V::Fail, QUAL_NO_CHECKS, Some(0), None).classification, Some(C::MissedBug));
    }

    /// A qualifier belongs to the `Checking harness` section that printed it;
    /// the most severe over the SUCCESSFUL sections decides; one printed
    /// outside every section counts (fail-closed); one in a FAILED section
    /// qualifies no success.
    #[test]
    fn a_proof_qualifier_belongs_to_the_harness_section_that_printed_it() {
        let ok2 = "Manual Harness Summary:\nComplete - 2 successfully verified harnesses, 0 failures, 2 total.\n";
        let clean_a = "Checking harness a...\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        let clean_c = "Checking harness c...\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        let unattributed_b = "Checking harness b...\n[AY:PROOF_QUALIFIERS:unattributed_check=chc.0]\nVERIFICATION:- SUCCESSFUL\n";
        let trivial_c = "Checking harness c...\n[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]\nVERIFICATION:- SUCCESSFUL\n";

        let r = scored_unit(V::Success, &format!("{clean_a}{unattributed_b}{ok2}"), Some(0), None);
        assert_eq!(r.classification, Some(C::UnattributedPass), "{}", r.note);
        assert!(r.note.ends_with("unattributed_check=chc.0 on b"), "{}", r.note);
        assert_eq!(scored_unit(V::Success, &format!("{clean_a}{clean_c}{ok2}"), Some(0), None).classification, Some(C::Parity));

        let r = scored_unit(V::Success, &format!("{unattributed_b}{trivial_c}{ok2}"), Some(0), None);
        assert_eq!(r.classification, Some(C::TrivialSafePass), "the most severe decides: {}", r.note);
        assert!(r.note.contains("unattributed_check=chc.0 on b") && r.note.contains("trivial_safe=no_error_rule on c"), "{}", r.note);

        let stray = format!("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]\n{clean_a}{clean_c}{ok2}");
        let r = scored_unit(V::Success, &stray, Some(0), None);
        assert_eq!(r.classification, Some(C::TrivialSafePass), "{}", r.note);
        assert!(r.note.contains(OUTSIDE_EVERY_HARNESS), "{}", r.note);

        let failed_f = "Checking harness f...\n[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n";
        let fail_summary = "Manual Harness Summary:\nVerification failed for - f\nComplete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        let r = scored_unit(V::Fail, &format!("{clean_a}{failed_f}{fail_summary}"), Some(1), None);
        assert_eq!(r.classification, Some(C::Parity), "{}", r.note);
        let r = scored_unit(V::Fail, &format!("{unattributed_b}{failed_f}{fail_summary}"), Some(1), None);
        assert_eq!(r.classification, Some(C::UnattributedPass), "the SUCCESSFUL sibling's qualifier decides: {}", r.note);
    }

    const FFI_PTR_EXPECTED: &str = include_str!("fixtures/unsupported-check/ffi_ptr.expected");
    const FFI_PTR_OUT: &str = include_str!("fixtures/unsupported-check/ffi_ptr.synthetic.out");
    const REACHABLE_EXPECTED: &str = include_str!("fixtures/unsupported-check/reachable.expected");
    const REACHABLE_OUT: &str = include_str!("fixtures/unsupported-check/reachable.synthetic.out");

    /// Kani's own unsupported-construct check, reproduced by trust-mc and
    /// deliberately left uncertified (`OverApproximation:kani_unsupported_construct_check=1`),
    /// is parity against the corpus expected files that name it
    /// (`expected/foreign-function/expected`, `expected/report/unsupported/reachable/expected`,
    /// copied verbatim; the transcripts are synthetic, and were reconstructed
    /// after the uncommitted originals were lost). Scorer v3 scored both
    /// `unknown`.
    #[test]
    fn kani_unsupported_check_failure_named_by_the_expected_file_is_parity() {
        for (name, out, exp) in [("ffi_ptr", FFI_PTR_OUT, FFI_PTR_EXPECTED), ("reachable", REACHABLE_OUT, REACHABLE_EXPECTED)] {
            let r = scored_unit(V::Fail, out, Some(1), Some(exp));
            assert_eq!(r.classification, Some(C::Parity), "{name}: {}", r.note);
            assert_eq!(r.note, UNSUPPORTED_CHECK_PARITY, "{name}");
        }
        assert_eq!(expected_unsupported_checks(FFI_PTR_EXPECTED), vec!["call to foreign \"C\" function `foreign` is not currently supported by Kani".to_string()]);
    }

    /// Fail-closed: every other shape stays what the verdict rules make it.
    #[test]
    fn kani_unsupported_check_rescue_refuses_every_other_shape() {
        let class = |out: &str, exp: &str| scored_unit(V::Fail, out, Some(1), Some(exp)).classification;
        let not_parity = |out: String, exp: &str, why: &str| {
            let c = class(&out, exp);
            assert_ne!(c, Some(C::Parity), "{why}: {c:?}");
        };
        // The failing check is a different property.
        not_parity(
            FFI_PTR_OUT
                .replace("\t - Status: FAILURE\n\t - Description: \"call to foreign \"C\" function `foreign` is not currently supported by Kani\"", "\t - Status: UNDETERMINED\n\t - Description: \"call to foreign \"C\" function `foreign` is not currently supported by Kani\"")
                .replace("\t - Status: UNDETERMINED\n\t - Description: \"assertion failed: call_on", "\t - Status: FAILURE\n\t - Description: \"assertion failed: call_on"),
            FFI_PTR_EXPECTED,
            "a different failing property",
        );
        // An extra failing property beside the unsupported check.
        not_parity(REACHABLE_OUT.replace("\t - Status: UNDETERMINED\n", "\t - Status: FAILURE\n"), REACHABLE_EXPECTED, "an extra failing check");
        // Another approximation on the harness.
        not_parity(FFI_PTR_OUT.replace("kani_unsupported_construct_check=1", "kani_unsupported_construct_check=1,chc_translation_drop=1,unhandled_calls=1"), FFI_PTR_EXPECTED, "another approximation");
        not_parity(FFI_PTR_OUT.replace("OverApproximation:kani_unsupported_construct_check=1", "OverApproximation:chc_translation_drop=1,unhandled_calls=1"), FFI_PTR_EXPECTED, "the old havoc shape");
        assert_eq!(class(&FFI_PTR_OUT.replace("OverApproximation:kani_unsupported_construct_check=1", "EncodingGap:offset_provenance_unresolved=1"), FFI_PTR_EXPECTED), Some(C::EncodingGap));
        not_parity(FFI_PTR_OUT.replace("OverApproximation:kani_unsupported_construct_check=1", "Unknown"), FFI_PTR_EXPECTED, "an Unknown category");
        not_parity(FFI_PTR_OUT.replace("[AY:CTREX_CAT:OverApproximation:kani_unsupported_construct_check=1]\n", ""), FFI_PTR_EXPECTED, "no category");
        not_parity(FFI_PTR_OUT.replace("VERIFICATION:- FAILED\n", "[AY:UNKNOWN_REASON:SolverError]\nVERIFICATION:- FAILED\n"), FFI_PTR_EXPECTED, "an unknown reason");
        // An expected line missing from the output (Kani's compiletest fails it too).
        not_parity(REACHABLE_OUT.replace("** WARNING", "** NOTE"), REACHABLE_EXPECTED, "a missing expected line");
        // A harness the expected file does not name fails too.
        not_parity(FFI_PTR_OUT.replace("Verification failed for - check_fn_ptr_called", "Verification failed for - check_fn_ptr_not_called\nVerification failed for - check_fn_ptr_called").replace("[AY:PROOF_QUALIFIERS:clean]\nCheck 1: check_fn_ptr_not_called.assertion.1\n\t - Status: SUCCESS", "[AY:CTREX_CAT:Genuine]\nCheck 1: check_fn_ptr_not_called.assertion.1\n\t - Status: FAILURE").replace("VERIFICATION:- SUCCESSFUL\n", "VERIFICATION:- FAILED\n"), FFI_PTR_EXPECTED, "an unnamed failing harness");
        // The sibling success is not clean.
        not_parity(FFI_PTR_OUT.replace("[AY:PROOF_QUALIFIERS:clean]", "[AY:SOUND_FALLBACK:1]"), FFI_PTR_EXPECTED, "a tainted sibling success");
        // A construct the expected file does not name.
        not_parity(FFI_PTR_OUT.replace("function `foreign` is not currently", "function `other` is not currently"), FFI_PTR_EXPECTED, "another unsupported construct");
        // A success oracle, or a SUCCESSFUL run against the fail oracle.
        assert_ne!(scored_unit(V::Success, FFI_PTR_OUT, Some(1), Some(FFI_PTR_EXPECTED)).classification, Some(C::Parity));
        let proved = "Checking harness main...\n[AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(class(proved, REACHABLE_EXPECTED), Some(C::MissedBug));
        // The Kani engine keeps its own criterion.
        assert_eq!(scored_kani("expected", V::Fail, REACHABLE_OUT, Some(1), Some(REACHABLE_EXPECTED)).class, C::Parity);
    }

    // ---- exceeds_oracle (corpus-oracle unsupported-construct artifact) -----

    /// `expected/slice-pattern-array/main.rs` shape: the oracle records FAILURE
    /// only because the construct "is not currently supported by Kani"
    /// (issue #707) — no genuine bug. A clean [AY:PROOF]-backed trust-mc
    /// SUCCESS exceeds the oracle; it is counted out of missed_bug but NOT
    /// into parity.
    #[test]
    fn kani_unsupported_artifact_with_clean_proof_is_exceeds_oracle() {
        let exp = "Status: FAILURE\\\n\
                   Description: \"Sub-array binding is not currently supported by Kani. Please post your example at https://github.com/model-checking/kani/issues/707\"\n";
        let out = "[AY:PROOF] CHC verification: property proven (false error obligation)\n\
                   [AY:PROOF_QUALIFIERS:clean]\nVERIFICATION:- SUCCESSFUL\n";
        let c = classify_full(V::Fail, out, false, Some(0), false, Some(exp));
        assert_eq!(c, C::ExceedsOracle);
        assert!(!c.is_parity());
        assert!(!c.is_critical());
    }

    /// The exceeds_oracle escape hatch must NOT fire for genuine fail oracles:
    /// no unsupported mention, an authoritative whole-run FAILED verdict in the
    /// expected file, a fallback-tainted success, or a success without the
    /// [AY:PROOF] marker all stay missed_bug.
    #[test]
    fn genuine_fail_oracles_stay_missed_bug() {
        let proof = "[AY:PROOF] CHC verification: property proven\nVERIFICATION:- SUCCESSFUL\n";
        // Genuine bug oracle (expected/uninit/vec-read-bad-len shape).
        let uninit = "Failed Checks: Undefined Behavior: Reading from an uninitialized pointer of type `*const [u8]`\n\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_full(V::Fail, proof, false, Some(0), false, Some(uninit)), C::MissedBug);
        // Unsupported mention BUT an authoritative FAILED verdict: stays missed_bug.
        let mixed = "x is not currently supported by Kani\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_full(V::Fail, proof, false, Some(0), false, Some(mixed)), C::MissedBug);
        // No expected file at all.
        assert_eq!(classify_full(V::Fail, proof, false, Some(0), false, None), C::MissedBug);
        // Unsupported artifact but the success is fallback-tainted.
        let unsup = "Description: \"asm! is not currently supported by Kani\"\n";
        let tainted = "[AY:SOUND_FALLBACK:1]\n[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_full(V::Fail, tainted, false, Some(0), false, Some(unsup)), C::MissedBug);
        // Unsupported artifact but no [AY:PROOF] marker backing the success.
        let bare = "VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_full(V::Fail, bare, false, Some(0), false, Some(unsup)), C::MissedBug);
    }

    // ---- outer watchdog scaling ---------------------------------------------

    /// The single-file outer cap must scale with the file's harness count (the
    /// driver budgets --harness-timeout per harness): 11-harness files like
    /// expected/valid-value-checks/custom_niche.rs need more than the fixed cap,
    /// while 1-harness files keep exactly the old budget.
    #[test]
    fn single_file_outer_timeout_scales_with_harness_count() {
        let cfg = RunConfig {
            engine: Engine::TrustMc,
            harness_timeout_s: 15,
            outer_multiplier: 5,
            grace_s: 30,
            jobs: 1,
            backend: "chc".into(),
            strip_cbmc: true,
            surface: Surface::Legacy,
            extra_driver_flags: Vec::new(),
            log_dir: PathBuf::from("/tmp/kd-logs"),
            log_rel_prefix: "logs/t".into(),
            route_engine: RouteEngine::DevCli(crate::route::DevCliEngine),
        };
        let base = Duration::from_secs(15 * 5 + 30);
        assert_eq!(cfg.outer_timeout(0), base);
        assert_eq!(cfg.outer_timeout(1), base);
        assert_eq!(cfg.outer_timeout(11), base + Duration::from_secs(15 * 10));
        // Cargo scaling unchanged: base + per-harness budget + compile allowance.
        assert_eq!(cfg.cargo_outer_timeout(2), base + Duration::from_secs(15 * 2 + 300));
    }

    /// Neither a test header nor an operator's extra driver flag can opt a
    /// verifier child into an off-pin solver.
    #[test]
    fn no_flag_can_opt_a_child_into_an_off_pin_solver() {
        let cfg = RunConfig {
            engine: Engine::TrustMc,
            harness_timeout_s: 15,
            outer_multiplier: 5,
            grace_s: 30,
            jobs: 1,
            backend: "bmc".into(),
            strip_cbmc: true,
            surface: Surface::Legacy,
            extra_driver_flags: vec![UNPINNED_AY_FLAG.into(), "--ay-solver=ay".into()],
            log_dir: PathBuf::from("/tmp/kd-logs"),
            log_rel_prefix: "logs/t".into(),
            route_engine: RouteEngine::DevCli(crate::route::DevCliEngine),
        };
        let raw: Vec<String> =
            [UNPINNED_AY_FLAG, "--default-unwind", "3"].iter().map(|f| f.to_string()).collect();
        let out = sanitize_flags(&raw, &cfg);
        assert!(!out.iter().any(|f| f == UNPINNED_AY_FLAG), "{out:?}");
        assert!(out.windows(2).any(|w| w[0] == "--default-unwind" && w[1] == "3"), "{out:?}");
        assert!(out.iter().any(|f| f == "--ay-solver=ay"), "{out:?}");
    }

    #[test]
    fn cargo_unit_expected_success_via_fallback_is_unsound_pass() {
        let exp = "Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        let out = "[AY:SOUND_FALLBACK:1]\nVERIFICATION:- SUCCESSFUL\n\
                   Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        assert_eq!(
            classify_full(V::Success, out, false, Some(0), true, Some(exp)),
            C::UnsoundPass
        );
    }

    // ---- P1 MECH D: per-harness aggregation for multi-harness runs ---------

    /// The live stub_bool_methods.rs shape: a Genuine should-panic SUCCESS
    /// followed by an OverApproximation-inconclusive FAILED harness. The
    /// failing harness's OWN quality (inconclusive) decides the file —
    /// honest `unknown`, and the surfaced category is the FAILING harness's
    /// OverApproximation, not the should-panic harness's stream-first Genuine.
    #[test]
    fn multi_harness_should_panic_genuine_plus_inconclusive_is_unknown() {
        let out = "Checking harness check_stub_then...\n\
                   [AY:CTREX] CHC verification: counterexample reachable (exact CHC derivation)\n\
                   [AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
                   Checking harness check_stub_then_some...\n\
                   [AY:CTREX_CAT:OverApproximation:chc_translation_drop=1]\n\
                   [AY:SOUND_FALLBACK:1]\n\
                   VERIFICATION:- FAILED\n\
                   Manual Harness Summary:\n\
                   Verification failed for - check_stub_then_some\n\
                   CTREX breakdown: 0 EncodingGap, 1 OverApproximation, 0 Genuine, 0 Unknown\n\
                   Complete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::Unknown);
        // Attribution: the recorded category re-keys to the failing harness.
        let mut r = TestResult { exit_code: Some(1), ..TestResult::blank("t", "f.rs", V::Success) };
        parse_markers(out, &mut r);
        assert_eq!(r.ctrex_category.as_deref(), Some("Genuine")); // stream-first (the bug)
        reattribute_multi_harness_markers(out, &mut r, Engine::TrustMc);
        assert_eq!(r.ctrex_category.as_deref(), Some("OverApproximation"));
    }

    /// A route LIMITATION is recorded by NAME, deduplicated across harnesses,
    /// and changes nothing else about the row: the run produced its verdict,
    /// it just could not take one optional step on this route.
    #[test]
    fn a_named_route_limitation_is_recorded_and_scores_nothing() {
        let out = "Checking harness a...\n\
                   [AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc]\n\
                   [AY:LOOP_TWO_LANE] not run on the trustc compiler route: the lanes need \
                   engine environment knob(s) TRUST_MC_COMPOUND_DECREASES, TRUST_MC_NO_LOOP_RULE\n\
                   Checking harness b...\n\
                   [AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc]\n\
                   VERIFICATION:- FAILED\n";
        let mut r = TestResult { exit_code: Some(1), ..TestResult::blank("t", "f.rs", V::Fail) };
        parse_markers(out, &mut r);
        assert_eq!(r.route_limitations, vec!["two-lane-loop-contract-retry route=trustc"]);
        assert!(!r.self_reported_unsound && !r.vacuous);
        // oracle fail, observed fail: still plain parity.
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Parity);
    }

    /// The failure-quality taint applies PER HARNESS in both orders: a
    /// genuine-failing harness cannot vouch for an inconclusive-failing
    /// sibling regardless of which one runs (and prints its marker) first.
    /// Pre-MECH-D this was order-dependent: Genuine-first scored parity.
    #[test]
    fn multi_harness_genuine_plus_inconclusive_fail_is_unknown_both_orders() {
        let genuine_first = "Checking harness check_a...\n\
                             [AY:CTREX_CAT:Genuine]\n\
                             VERIFICATION:- FAILED\n\
                             Checking harness check_b...\n\
                             [AY:CTREX_CAT:OverApproximation:pointee_synth=1]\n\
                             VERIFICATION:- FAILED\n\
                             Manual Harness Summary:\n\
                             Verification failed for - check_a\n\
                             Verification failed for - check_b\n\
                             CTREX breakdown: 0 EncodingGap, 1 OverApproximation, 1 Genuine, 0 Unknown\n\
                             Complete - 0 successfully verified harnesses, 2 failures, 2 total.\n";
        let inconclusive_first = "Checking harness check_b...\n\
                                  [AY:CTREX_CAT:OverApproximation:pointee_synth=1]\n\
                                  VERIFICATION:- FAILED\n\
                                  Checking harness check_a...\n\
                                  [AY:CTREX_CAT:Genuine]\n\
                                  VERIFICATION:- FAILED\n\
                                  Manual Harness Summary:\n\
                                  Verification failed for - check_a\n\
                                  Verification failed for - check_b\n\
                                  CTREX breakdown: 0 EncodingGap, 1 OverApproximation, 1 Genuine, 0 Unknown\n\
                                  Complete - 0 successfully verified harnesses, 2 failures, 2 total.\n";
        assert_eq!(classify_output(V::Fail, genuine_first, false, Some(1)), C::Unknown);
        assert_eq!(classify_output(V::Fail, inconclusive_first, false, Some(1)), C::Unknown);
    }

    /// Per-harness adjudication must NOT over-taint: a genuine-failing
    /// harness beside a validated should-panic SUCCESS keeps fail-oracle
    /// parity, and run-level noise from a harness that ultimately SUCCEEDED
    /// (a retry rung's "ay-chc inconclusive" line) no longer poisons the
    /// genuine failure.
    #[test]
    fn multi_harness_genuine_fail_keeps_parity_despite_sibling_noise() {
        let out = "Checking harness check_ok...\n\
                   CHC verification: ay-chc inconclusive (retry rung 1)\n\
                   [AY:PROOF] CHC verification: property proven\n\
                   VERIFICATION:- SUCCESSFUL\n\
                   Checking harness check_bug...\n\
                   [AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- FAILED\n\
                   Manual Harness Summary:\n\
                   Verification failed for - check_bug\n\
                   CTREX breakdown: 0 EncodingGap, 0 OverApproximation, 1 Genuine, 0 Unknown\n\
                   Complete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        // Run-level failure_quality would trip on the "ay-chc inconclusive"
        // string; the per-harness path scopes it to the succeeded harness.
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Parity);
        // The same genuine failure against a success oracle stays a
        // false positive (soundness-critical signal preserved).
        assert_eq!(classify_output(V::Success, out, false, Some(1)), C::FalsePositive);
    }

    /// Fail-closed gating: an incoherent split (FAILED section not listed by
    /// the summary — e.g. a watchdog kill cut the run) falls back to the
    /// unchanged run-level path.
    #[test]
    fn multi_harness_incoherent_split_falls_back_to_run_level() {
        let out = "Checking harness check_a...\n\
                   [AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- FAILED\n\
                   Checking harness check_b...\n\
                   [AY:UNKNOWN_REASON:DriverTimeout]\n\
                   [AY:UNKNOWN] driver wall-clock timeout after 80s\n\
                   VERIFICATION:- FAILED\n";
        assert!(coherent_multi_harness_outcomes(out, Engine::TrustMc).is_none());
        // Run-level path: unknown_reason present -> inconclusive -> Unknown.
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Unknown);
    }

    /// Section splitting: thread-prefixed boundaries parse, the summary tail
    /// is never attributed to the last harness, and a demoted FAILED harness
    /// (no CTREX category at all) is inconclusive fail-closed.
    #[test]
    fn multi_harness_section_parsing_details() {
        let out = "Thread 0: Checking harness check_a...\n\
                   [AY:CTREX_CAT:Genuine]\n\
                   VERIFICATION:- FAILED\n\
                   Thread 1: Checking harness check_b...\n\
                   [AY:DEMOTION_REASONS:chc_fallback]\n\
                   VERIFICATION:- FAILED\n\
                   Manual Harness Summary:\n\
                   Verification failed for - check_a\n\
                   Verification failed for - check_b\n\
                   [AY:CTREX_CAT:Unknown] stray-post-summary-marker\n";
        let sections = split_harness_sections(out);
        assert_eq!(sections.len(), 2);
        assert_eq!(sections[0].0, "check_a");
        assert_eq!(sections[1].0, "check_b");
        assert!(!sections[1].1.contains("stray-post-summary-marker"));
        let outcomes = coherent_multi_harness_outcomes(out, Engine::TrustMc).expect("coherent");
        assert!(!outcomes[0].inconclusive);
        assert!(outcomes[1].inconclusive, "category-less FAILED harness is inconclusive");
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Unknown);
    }

    // ---- scorer v2: fail-closed credit ----------------------------------------

    /// 1a. A cargo unit's FAILED verdict goes through the failure-quality gate
    /// BEFORE the expected file is consulted: an encoding gap, a demoted proof
    /// or an over-approximation whose output happens to contain the expected
    /// summary lines is that defect, never parity. Scorer version 1 returned
    /// parity from the `is_cargo && contains_lines` arm first.
    #[test]
    fn cargo_unit_failed_verdict_is_quality_gated_before_contains_lines() {
        let exp = "Verification failed for - ptr::check\n\
                   Complete - 0 successfully verified harnesses, 1 failures, 1 total.\n";
        let tail = "VERIFICATION:- FAILED\nVerification failed for - ptr::check\n\
                    Complete - 0 successfully verified harnesses, 1 failures, 1 total.\n";
        let encoding_gap = format!("Failed to parse CHC problem: expected argument sort\n[AY:CTREX_CAT:Unknown]\n{tail}");
        assert_eq!(classify_full(V::Fail, &encoding_gap, false, Some(1), true, Some(exp)), C::EncodingGap);
        let demoted = format!("[AY:DEMOTION_REASONS:chc_fallback]\n{tail}");
        assert_eq!(classify_full(V::Fail, &demoted, false, Some(1), true, Some(exp)), C::Unknown);
        let overapprox = format!("[AY:CTREX_CAT:OverApproximation:chc_translation_drop=4]\n{tail}");
        assert_eq!(classify_full(V::Fail, &overapprox, false, Some(1), true, Some(exp)), C::Unknown);
        // A genuine counterexample still earns the cargo unit its parity.
        let genuine = format!("[AY:CTREX_CAT:Genuine]\n{tail}");
        assert_eq!(classify_full(V::Fail, &genuine, false, Some(1), true, Some(exp)), C::Parity);
        // A cargo unit's verdict that CONTRADICTS the oracle is never laundered
        // by matching lines: a genuine FAILED on a success-oracle unit whose
        // partial expected file is present in the output is a false positive.
        let partial = "VERIFICATION:- SUCCESSFUL\n";
        let mixed = "Checking harness ok...\nVERIFICATION:- SUCCESSFUL\nChecking harness bad...\n\
                     [AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\nManual Harness Summary:\n\
                     Verification failed for - bad\nComplete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        assert_eq!(classify_full(V::Success, mixed, false, Some(1), true, Some(partial)), C::FalsePositive);
        // …and a SUCCESSFUL verdict on a fail-oracle unit is a missed bug even
        // when the expected lines happen to appear.
        let fail_exp = "Failed Checks: assertion failed: x\n";
        let proved = "Failed Checks: assertion failed: x\n[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_full(V::Fail, proved, false, Some(0), true, Some(fail_exp)), C::MissedBug);
    }

    /// 1a. The diagnostic-only `contains_lines` path (no verdict at all) only
    /// credits a CLEAN diagnostic: a bare `VERIFICATION:- UNVALIDATED`
    /// (observed Unknown), a vacuity refusal, a fallback marker or a demotion
    /// in the output means the lines matched by accident, not by parity.
    #[test]
    fn diagnostic_contains_lines_parity_needs_a_clean_output() {
        let exp = "error: no harnesses matched the harness filter: `foo`\n";
        let diag = "error: no harnesses matched the harness filter: `foo`\n";
        assert_eq!(classify_full(V::Success, diag, false, Some(1), false, Some(exp)), C::Parity);
        for taint in [
            "VERIFICATION:- UNVALIDATED (DT+BV)\n",
            "[AY:VACUOUS:no-checks]\nVERIFICATION:- INCONCLUSIVE (no checks)\n",
            "[AY:SOUND_FALLBACK:1]\n",
            "[AY:DEMOTION_REASONS:chc_fallback]\n",
            "pointee_synthesis_fallback\n",
        ] {
            let out = format!("{taint}{diag}");
            assert_ne!(classify_full(V::Success, &out, false, Some(1), false, Some(exp)), C::Parity, "{taint}");
        }
    }

    /// 1b. `unsupported` is taken only when no genuine counterexample backs
    /// the FAILED verdict. A validated counterexample beside an unsupported
    /// warning is the verdict: parity against a fail oracle, a false positive
    /// against a success oracle.
    #[test]
    fn unsupported_is_never_taken_over_a_genuine_counterexample() {
        let noise = "warning: Found the following unsupported constructs:\n - asm! (1)\n";
        let no_cex = format!("{noise}VERIFICATION:- FAILED\n");
        assert_eq!(classify_output(V::Success, &no_cex, false, Some(1)), C::Unsupported);
        assert_eq!(classify_output(V::Fail, &no_cex, false, Some(1)), C::Unsupported);
        let genuine = format!("{noise}[AY:CTREX_CAT:Genuine]\nCTREX breakdown: 0 EncodingGap, 0 OverApproximation, 1 Genuine, 0 Unknown\nVERIFICATION:- FAILED\n");
        assert_eq!(classify_output(V::Success, &genuine, false, Some(1)), C::FalsePositive);
        assert_eq!(classify_output(V::Fail, &genuine, false, Some(1)), C::Parity);
        // Multi-harness: the genuine failure must be a FAILING section's — a
        // should-panic SUCCESS harness's Genuine marker does not count.
        let sp_plus_unsupported = format!(
            "Checking harness sp...\n[AY:CTREX_CAT:Genuine]\n\
             VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\
             [AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n\
             Checking harness bad...\n{noise}VERIFICATION:- FAILED\n\
             Manual Harness Summary:\nVerification failed for - bad\n"
        );
        assert_eq!(classify_output(V::Success, &sp_plus_unsupported, false, Some(1)), C::Unsupported);
        let two_failing = format!(
            "Checking harness a...\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n\
             Checking harness b...\n{noise}VERIFICATION:- FAILED\n\
             Manual Harness Summary:\nVerification failed for - a\nVerification failed for - b\n"
        );
        // Success oracle: a's genuine counterexample is a false positive,
        // whatever b is; fail oracle: b (no category) is inconclusive.
        assert_eq!(classify_output(V::Success, &two_failing, false, Some(1)), C::FalsePositive);
        assert_eq!(classify_output(V::Fail, &two_failing, false, Some(1)), C::Unknown);
    }

    /// Multi-harness, fail oracle: the expected file's own failed-harness
    /// list decides WHICH harnesses may fail. A named harness that trust-mc
    /// verified is a missed bug; an extra failing harness is a false positive
    /// when the list is complete (`Complete - … N failures` agrees) and
    /// unknown when it may be partial; a named harness trust-mc never ran is
    /// unknown; and a tainted sibling success turns parity into an unsound
    /// pass. File-level fail==fail alone credited all of these before.
    #[test]
    fn multi_harness_fail_oracle_checks_which_harnesses_failed() {
        let run = |a: &str, b: &str| {
            format!(
                "Checking harness a...\n{a}\nChecking harness b...\n{b}\nManual Harness Summary:\n{}{}",
                if a.contains("FAILED") { "Verification failed for - a\n" } else { "" },
                if b.contains("FAILED") { "Verification failed for - b\n" } else { "" },
            )
        };
        let ok = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL";
        let bad = "[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED";
        let a_fails = run(bad, ok);
        let both_fail = run(bad, bad);
        let names_a = "Verification failed for - a\nVERIFICATION:- FAILED\n\
                       Complete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        assert_eq!(classify_full(V::Fail, &a_fails, false, Some(1), false, Some(names_a)), C::Parity);
        // trust-mc passed b, which the expected file names as failed.
        let names_b = "Verification failed for - b\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_full(V::Fail, &a_fails, false, Some(1), false, Some(names_b)), C::MissedBug);
        // trust-mc fails b as well; the expected list is complete (1 failure).
        assert_eq!(classify_full(V::Fail, &both_fail, false, Some(1), false, Some(names_a)), C::FalsePositive);
        // …and with no `Complete -` count the list may be partial: unknown.
        let names_a_partial = "Verification failed for - a\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_full(V::Fail, &both_fail, false, Some(1), false, Some(names_a_partial)), C::Unknown);
        // A named harness trust-mc never ran.
        let names_c = "Verification failed for - c\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_full(V::Fail, &a_fails, false, Some(1), false, Some(names_c)), C::Unknown);
        // No names at all: file-level parity as before.
        assert_eq!(classify_full(V::Fail, &a_fails, false, Some(1), false, Some("VERIFICATION:- FAILED\n")), C::Parity);
        assert_eq!(classify_full(V::Fail, &a_fails, false, Some(1), false, None), C::Parity);
        // A sibling success reached through a fallback is not a clean proof.
        let tainted = run(bad, "[AY:SOUND_FALLBACK:1]\nVERIFICATION:- SUCCESSFUL");
        assert_eq!(classify_full(V::Fail, &tainted, false, Some(1), false, Some(names_a)), C::UnsoundPass);
        let unvalidated = run(bad, "VERIFICATION:- SUCCESSFUL (UNVALIDATED)");
        assert_eq!(classify_full(V::Fail, &unvalidated, false, Some(1), false, None), C::UnsoundPass);
        // A Genuine-validated should-panic sibling IS a clean success.
        let sp = run(bad, "[AY:CTREX_CAT:Genuine]\nVERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n[AY:EFFECTIVE_SUCCESS:should_panic_panics_only]");
        assert_eq!(classify_full(V::Fail, &sp, false, Some(1), false, None), C::Parity);
    }

    /// 1d. `[AY:SOLVER_PIN_MISMATCH:` keeps a row `error` on every path:
    /// the cargo contains_lines arm, the check-fail arm, the diagnostic arm
    /// and the multi-harness tiebreak — and through `score_unit`, with the
    /// off-pin note.
    #[test]
    fn solver_pin_mismatch_is_error_on_every_path() {
        let marker = "[AY:SOLVER_PIN_MISMATCH:found=dd4de9e94e0bb94a458641c7e5aa814c8aeadf59:pin=94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322]";
        let cargo_exp = "Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n";
        let cargo = format!("{marker}\n[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n{cargo_exp}");
        assert_eq!(classify_full(V::Success, &cargo, false, Some(0), true, Some(cargo_exp)), C::Error);
        let compile = format!("{marker}\nerror[E0382]: borrow of moved value\nerror: aborting due to 1 previous error\n");
        assert_eq!(classify_ctx(V::Fail, &compile, false, Some(1), false, None, true), C::Error);
        let diag_exp = "error: no harnesses matched the harness filter: `foo`\n";
        let diag = format!("{marker}\n{diag_exp}");
        assert_eq!(classify_full(V::Success, &diag, false, Some(1), false, Some(diag_exp)), C::Error);
        let row = scored_unit(V::Fail, &format!("{marker}\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n"), Some(1), None);
        assert_eq!(row.classification, Some(C::Error));
        assert!(row.note.starts_with("ran on an off-pin ay solver"), "{}", row.note);
        assert_eq!(row.scorer_version, SCORER_VERSION);
    }

    /// 1e. Every row `score_unit` writes carries the current scorer version
    /// and the tiebreak bit, and both serialize; a spawn failure is an
    /// `error` row that still carries them.
    #[test]
    fn score_unit_stamps_the_scorer_version() {
        let row = scored_unit(V::Success, "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n", Some(0), None);
        assert_eq!(row.classification, Some(C::Parity));
        assert_eq!(row.observed, Some(V::Success));
        let json = serde_json::to_value(&row).unwrap();
        assert_eq!(json["scorer_version"], SCORER_VERSION);
        assert_eq!(json["tiebreak_applied"], false);
        assert!(json.get("log_path").is_none(), "no log was written for a scored-in-memory row");

        let mut failed = TestResult::blank("t", "f.rs", V::Success);
        let unit = UnitCtx { engine: Engine::TrustMc, suite: "t", rel: "f.rs", oracle: V::Success, is_cargo: false, check_fail: false, expected: None, route: Route::DevCli, route_attestation: None, upstream_ignored: false };
        let attempt = Attempt { stdout: "", stderr: "", exit_code: None, timed_out: false, retried_after_outer_timeout: false, spawn_error: Some("No such file") };
        score_unit(&unit, &attempt, &mut failed);
        assert_eq!(failed.classification, Some(C::Error));
        assert_eq!(failed.note, "spawn-failed: No such file");
        assert_eq!(failed.scorer_version, SCORER_VERSION);
        // A retry is recorded in the note.
        let mut retried = TestResult::blank("t", "f.rs", V::Success);
        let attempt = Attempt { stdout: "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n", stderr: "", exit_code: Some(0), timed_out: false, retried_after_outer_timeout: true, spawn_error: None };
        score_unit(&unit, &attempt, &mut retried);
        assert_eq!(retried.classification, Some(C::Parity));
        assert!(retried.note.ends_with("[retried-after-outer-timeout]"), "{}", retried.note);
    }

    /// The route is part of `score_unit`, so `run` and `rescore` apply it the
    /// same way: on the trust-mc engine a Trustc unit without its route marker
    /// is a `route-error`, a failed route preflight is an `error` row whatever
    /// the output, and DevCli output carrying Trustc route output is an error;
    /// the Kani engine is never checked against a route.
    #[test]
    fn score_unit_applies_the_route_on_the_trust_mc_engine_only() {
        let proof = "[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        let attempt = Attempt { stdout: proof, stderr: "", exit_code: Some(0), timed_out: false, retried_after_outer_timeout: false, spawn_error: None };
        let att = RouteAttestation { route: "trustc".into(), counted: true, ..Default::default() };
        let trustc = UnitCtx { engine: Engine::TrustMc, suite: "t", rel: "f.rs", oracle: V::Success, is_cargo: false, check_fail: false, expected: None, route: Route::Trustc, route_attestation: Some(&att), upstream_ignored: false };

        let mut row = TestResult::blank("t", "f.rs", V::Success);
        score_unit(&trustc, &attempt, &mut row);
        assert_eq!(row.classification, Some(C::Error));
        assert!(row.note.starts_with("route-error: no [AY:COMPILER_ROUTE] marker"), "{}", row.note);

        let failed = RouteAttestation { preflight_errors: vec!["KEY driver_sha256 differs".into()], ..att.clone() };
        let mut row = TestResult::blank("t", "f.rs", V::Success);
        score_unit(&UnitCtx { route_attestation: Some(&failed), ..trustc }, &attempt, &mut row);
        assert_eq!(row.classification, Some(C::Error));
        assert_eq!(row.note, "route-preflight-failed (driver not run): KEY driver_sha256 differs");

        let mut row = TestResult::blank("t", "f.rs", V::Success);
        score_unit(&UnitCtx { engine: Engine::Kani, route_attestation: Some(&failed), ..trustc }, &attempt, &mut row);
        assert!(!row.note.starts_with("route-"), "the Kani engine has no route: {}", row.note);

        let dev_cli = UnitCtx { route: Route::DevCli, route_attestation: None, ..trustc };
        let mut row = TestResult::blank("t", "f.rs", V::Success);
        score_unit(&dev_cli, &attempt, &mut row);
        assert_eq!(row.classification, Some(C::Parity));
        let leaked = Attempt { stdout: "[AY:COMPILER_ROUTE route=trustc]\n[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n", ..attempt };
        let mut row = TestResult::blank("t", "f.rs", V::Success);
        score_unit(&dev_cli, &leaked, &mut row);
        assert_eq!(row.classification, Some(C::Error));
        assert!(row.note.starts_with("route-error: a dev-cli run printed Trustc route output"), "{}", row.note);
    }

    /// The expected-file parsers behind the tiebreak and the name check.
    #[test]
    fn expected_file_failed_names_and_count() {
        let exp = "Summary:\\\nVerification failed for - a\\\nVerification failed for - b::c\n\
                   Complete - 3 successfully verified harnesses, 2 failures, 5 total.\n";
        let names: Vec<String> = expected_failed_names(exp).into_iter().collect();
        assert_eq!(names, vec!["a".to_string(), "b::c".to_string()]);
        assert_eq!(expected_failure_count(exp), Some(2));
        assert_eq!(expected_failure_count("Complete - 0 successfully verified harnesses, 1 failure, 1 total.\n"), Some(1));
        assert_eq!(expected_failure_count("VERIFICATION:- FAILED\n"), None);
        assert!(expected_failed_names("VERIFICATION:- FAILED\n").is_empty());
    }

    // ---- the Kani engine ---------------------------------------------------

    fn kani_cfg(extra: &[&str]) -> RunConfig {
        RunConfig {
            engine: Engine::Kani,
            harness_timeout_s: 15,
            outer_multiplier: 5,
            grace_s: 30,
            jobs: 1,
            backend: "cbmc".into(),
            strip_cbmc: false,
            surface: Surface::Legacy,
            extra_driver_flags: extra.iter().map(|f| f.to_string()).collect(),
            log_dir: PathBuf::from("/tmp/kd-logs"),
            log_rel_prefix: "logs/t".into(),
            route_engine: RouteEngine::DevCli(crate::route::DevCliEngine),
        }
    }

    /// Kani gets its header flags verbatim: no `-Z unstable-options`, no
    /// `--ay-chc`, no `--harness-timeout`; `--cbmc-args` and its tail stay
    /// (Kani consumes them); an operator flag lands before the CBMC tail; and
    /// a `cbmc-flags` header is spelled the way compiletest spells it.
    #[test]
    fn kani_flags_are_verbatim_plus_compiletests_cbmc_spelling() {
        let s = |v: &[&str]| v.iter().map(|f| f.to_string()).collect::<Vec<_>>();
        assert_eq!(kani_flags(&s(&["--default-unwind", "3"]), &[], &kani_cfg(&[])), s(&["--default-unwind", "3"]));
        assert_eq!(
            kani_flags(&s(&["-Z", "unstable-options", "--cbmc-args", "--object-bits", "10"]), &[], &kani_cfg(&["--no-slice-formula"])),
            s(&["-Z", "unstable-options", "--no-slice-formula", "--cbmc-args", "--object-bits", "10"])
        );
        assert_eq!(
            kani_flags(&s(&["--default-unwind", "3"]), &s(&["--unwinding-assertions"]), &kani_cfg(&[])),
            s(&["--default-unwind", "3", "-Zunstable-options", "--cbmc-args", "--unwinding-assertions"])
        );
        // Both channels feed CBMC: the header's tail first, then cbmc-flags.
        assert_eq!(
            kani_flags(&s(&["--cbmc-args", "--a"]), &s(&["--b"]), &kani_cfg(&[])),
            s(&["--cbmc-args", "--a", "--b"])
        );
        // The trust-mc sanitizer would have injected three things here.
        let tm = sanitize_flags(&s(&["--default-unwind", "3"]), &RunConfig { engine: Engine::TrustMc, strip_cbmc: true, backend: "chc".into(), ..kani_cfg(&[]) });
        assert!(tm.iter().any(|f| f == "--ay-chc") && tm.iter().any(|f| f.starts_with("--harness-timeout")), "{tm:?}");
    }

    /// `--target-dir` precedes the header flags, so a `--cbmc-args` tail can
    /// never swallow it (CBMC refuses `--target-dir` with a usage error that
    /// Kani reports as `VERIFICATION:- FAILED`).
    #[test]
    fn kani_target_dir_precedes_the_cbmc_tail() {
        let flags: Vec<String> =
            ["-Zunstable-options", "--cbmc-args", "--unwinding-assertions"].iter().map(|f| f.to_string()).collect();
        let argv: Vec<String> = kani_single_file_args(Path::new("/c/t.rs"), Path::new("/iso"), &flags)
            .iter()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            argv,
            ["/c/t.rs", "--target-dir", "/iso", "-Zunstable-options", "--cbmc-args", "--unwinding-assertions"]
        );
        let td = argv.iter().position(|a| a == "--target-dir").unwrap();
        let cb = argv.iter().position(|a| a == "--cbmc-args").unwrap();
        assert!(td < cb, "{argv:?}");
        // No flags at all: still the file and its target dir.
        let bare: Vec<String> = kani_single_file_args(Path::new("/c/t.rs"), Path::new("/iso"), &[])
            .iter()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(bare, ["/c/t.rs", "--target-dir", "/iso"]);
    }

    /// The transcript `kani two.rs` printed on this host (Kani 0.67.0): a
    /// FAILED harness and a SUCCESSFUL one. Kani prints no AY quality
    /// markers, so its FAILED sections must count as genuine counterexamples
    /// — parity against a fail oracle, a false positive against a success
    /// oracle — where the trust-mc rules (fail-closed on missing markers)
    /// would score the same text `unknown`.
    #[test]
    fn kani_multi_harness_failure_is_a_genuine_counterexample() {
        let out = "Kani Rust Verifier 0.67.0 (standalone)\n\
                   Checking harness bad...\n\
                   RESULTS:\n\
                   Check 1: bad.assertion.1\n\
                   \t - Status: FAILURE\n\
                   \t - Description: \"assertion failed: x < 3\"\n\
                   SUMMARY:\n\
                   \x20** 1 of 1 failed\n\
                   Failed Checks: assertion failed: x < 3\n\
                   VERIFICATION:- FAILED\n\
                   Verification Time: 0.04384401s\n\
                   Checking harness ok...\n\
                   SUMMARY:\n\
                   \x20** 0 of 1 failed\n\
                   VERIFICATION:- SUCCESSFUL\n\
                   Verification Time: 0.047549993s\n\
                   Manual Harness Summary:\n\
                   Verification failed for - bad\n\
                   Complete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        assert_eq!(classify_kani(V::Fail, out, Some(1), None), C::Parity);
        assert_eq!(classify_kani(V::Success, out, Some(1), None), C::FalsePositive);
        // A `kani`-suite unit is scored on the exit status alone, so an
        // expected file changes nothing there; in the `expected` suite the
        // same file IS the criterion: every line present is a compiletest
        // pass, whatever the verdict-derived oracle says.
        assert_eq!(classify_kani(V::Success, out, Some(1), Some("VERIFICATION:- SUCCESSFUL\n")), C::FalsePositive);
        assert_eq!(
            classify_kani(V::Success, out, Some(1), Some("VERIFICATION:- SUCCESSFUL\nVerification failed for - bad\n")),
            C::FalsePositive
        );
        assert_eq!(classify_kani_in("expected", V::Success, out, Some(1), Some("VERIFICATION:- SUCCESSFUL\n")), C::Parity);
        assert_eq!(
            classify_kani_in("expected", V::Success, out, Some(1), Some("VERIFICATION:- SUCCESSFUL\nVerification failed for - bad\n")),
            C::Parity
        );
        // A fail oracle whose expected file names a harness Kani verified.
        assert_eq!(
            classify_kani_in("expected", V::Fail, out, Some(1), Some("VERIFICATION:- FAILED\nVerification failed for - ok\n")),
            C::MissedBug
        );
        // Same text under the trust-mc rules: fail-closed, as before.
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Unknown);
        let outcomes = coherent_multi_harness_outcomes(out, Engine::Kani).expect("coherent");
        assert!(!outcomes[0].inconclusive && outcomes[0].verdict == V::Fail);
        assert!(coherent_multi_harness_outcomes(out, Engine::TrustMc).unwrap()[0].inconclusive);
        // Single-harness shapes go through the run-level path unchanged.
        let single_fail = "Checking harness only...\nFailed Checks: boom\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_kani(V::Fail, single_fail, Some(1), None), C::Parity);
        let single_ok = "Checking harness only...\n ** 0 of 1 failed\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_kani(V::Success, single_ok, Some(0), None), C::Parity);
        assert_eq!(classify_kani(V::Fail, single_ok, Some(0), None), C::MissedBug);
        let should_panic = "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n";
        assert_eq!(classify_kani(V::Success, should_panic, Some(0), None), C::Parity);
    }

    /// The `smack/vector/vec_resize_fail.rs` transcript shape (Kani 0.67.0):
    /// `unsupported_construct` check lines and the "Found the following
    /// unsupported constructs" warning appear in a normal run with either
    /// verdict, so for the Kani engine they decide nothing — the verdict
    /// against the oracle does, as compiletest's `kani` mode does on the
    /// exit status. The trust-mc rule set is byte-for-byte the old one, so a
    /// trust-mc row carrying the same warning keeps its old class.
    #[test]
    fn kani_unsupported_construct_lines_never_decide_a_class() {
        let warning = "warning: Found the following unsupported constructs:\n\
                       \x20            - caller_location (1)\n\
                       \x20            - foreign function (2)\n\
                       \x20        Verification will fail if one or more of these constructs is reachable.\n";
        let failed = format!(
            "Kani Rust Verifier 0.67.0 (standalone)\n\
             Checking harness main...\n\
             Check 8: std::panic::Location::<'_>::caller.unsupported_construct.1\n\
             \t - Status: UNREACHABLE\n\
             \t - Description: \"caller_location is not currently supported by Kani. Please post your example at https://github.com/model-checking/kani/issues/374\"\n\
             SUMMARY:\n\
             \x20** 1 of 55 failed (2 unreachable)\n\
             Failed Checks: assertion failed: v1[1] != 3\n\
             VERIFICATION:- FAILED\n\
             Manual Harness Summary:\n\
             Verification failed for - main\n\
             Complete - 0 successfully verified harnesses, 1 failures, 1 total.\n{warning}"
        );
        assert_eq!(classify_kani(V::Fail, &failed, Some(1), None), C::Parity);
        assert_eq!(classify_kani(V::Success, &failed, Some(1), None), C::FalsePositive);
        let succeeded = format!(
            "Checking harness main...\n\
             Check 32: std::panic::Location::<'_>::caller.unsupported_construct.1\n\
             \t - Status: UNREACHABLE\n\
             SUMMARY:\n\
             \x20** 0 of 81 failed (2 unreachable)\n\
             VERIFICATION:- SUCCESSFUL\n\
             Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n{warning}"
        );
        assert_eq!(classify_kani(V::Success, &succeeded, Some(0), None), C::Parity);
        assert_eq!(classify_kani(V::Fail, &succeeded, Some(0), None), C::MissedBug);
        // A reachable unsupported construct is a FAILED check like any other:
        // Kani's verdict, which its compiletest scores as such.
        let reachable = "Checking harness h...\n\
                         Failed Checks: sub-array binding is not currently supported by Kani. Please post your example at https://github.com/model-checking/kani/issues/707\n\
                         VERIFICATION:- FAILED\n";
        assert_eq!(classify_kani(V::Fail, reachable, Some(1), None), C::Parity);
        assert_eq!(classify_kani(V::Success, reachable, Some(1), None), C::FalsePositive);
        assert_eq!(classify_output(V::Success, reachable, false, Some(1)), C::FalsePositive);
        assert_eq!(classify_output(V::Fail, reachable, false, Some(1)), C::Parity);
        // The trust-mc engine still reads the warning as its own gap signal.
        let warned = "warning: Found the following unsupported constructs:\n - asm! (1)\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_output(V::Success, warned, false, Some(1)), C::Unsupported);
        assert_eq!(classify_kani(V::Success, warned, Some(1), None), C::FalsePositive);
        // A compile error against a check-fail oracle is parity for Kani too.
        let compile = "error[E0382]: borrow of moved value: `v`\nerror: aborting due to 1 previous error\n";
        assert_eq!(classify_engine(Engine::Kani, V::Fail, compile, false, Some(1), false, None, true), C::Parity);
        // Watchdog and crash buckets are engine-agnostic.
        assert_eq!(classify_engine(Engine::Kani, V::Success, "", true, None, false, None, false), C::Timeout);
        assert_eq!(classify_kani(V::Success, "partial", None, None), C::Crash);
    }

    /// An `expected`-suite unit passes Kani's compiletest iff its output
    /// contains every expected line(-block) — `verify_output`, exit status
    /// not consulted. A verdict that agrees with the oracle while a line is
    /// missing is `unknown` (compiletest fails the test), and the note names
    /// the first missing block.
    #[test]
    fn kani_expected_suite_scores_by_contains_lines() {
        let out = "Checking harness main...\n\
                   Check 3: main.assertion.1\n\
                   \t - Status: FAILURE\n\
                   \t - Description: \"assertion failed: x < 3\"\n\
                   Failed Checks: assertion failed: x < 3\n\
                   VERIFICATION:- FAILED\n";
        let exact = "main.assertion.1\\\n\t - Status: FAILURE\\\n\t - Description: \"assertion failed: x < 3\"\n\nVERIFICATION:- FAILED\n";
        assert_eq!(classify_kani_in("expected", V::Fail, out, Some(1), Some(exact)), C::Parity);
        let stale = "main.assertion.1\\\n\t - Status: FAILURE\\\n\t - Description: \"assertion failed: x < 4\"\n\nVERIFICATION:- FAILED\n";
        let scored = scored_kani("expected", V::Fail, out, Some(1), Some(stale));
        assert_eq!(scored.class, C::Unknown);
        assert_eq!(scored.reason, Some(KANI_EXPECTED_LINES_MISSING));
        assert_eq!(
            missing_expected_block(out, stale).unwrap(),
            vec!["main.assertion.1", "\t - Status: FAILURE", "\t - Description: \"assertion failed: x < 4\""]
        );
        // The verdict rules explain a miss whose verdicts disagree.
        assert_eq!(classify_kani_in("expected", V::Success, out, Some(1), Some("VERIFICATION:- SUCCESSFUL\n")), C::FalsePositive);
        let ok = "Checking harness main...\nVERIFICATION:- SUCCESSFUL\n";
        assert_eq!(classify_kani_in("expected", V::Fail, ok, Some(0), Some("VERIFICATION:- FAILED\n")), C::MissedBug);
        // A diagnostic-only expected file is satisfied by the diagnostic.
        let diag = "warning: `kani::forall` has an unbounded (~2^64) range; consider tighter bounds\n";
        assert_eq!(classify_kani_in("expected", V::Success, diag, Some(0), Some("`kani::forall` has an unbounded (~2^64) range\n")), C::Parity);
        // A `kani`-suite unit with the same text ignores the file.
        assert_eq!(classify_kani_in("kani", V::Fail, out, Some(1), Some(stale)), C::Parity);
        // `matches_expected` and the block finder agree on the boundary case.
        assert!(matches_expected(out, exact));
        assert!(!matches_expected(out, stale));
        // A `\` on the last expected line still tests that line.
        assert_eq!(missing_expected_block(out, "VERIFICATION:- FAILED\\\n"), None);
        assert_eq!(missing_expected_block(out, "VERIFICATION:- SUCCESSFUL\\\n").unwrap(), vec!["VERIFICATION:- SUCCESSFUL"]);
    }

    /// `expected/function-contract/gcd_rec_replacement_pass.rs` under Kani
    /// 0.67.0: two harnesses pass, `gcd_harness` FAILS, and the expected
    /// file quotes only the passing checks and `VERIFICATION:- SUCCESSFUL`.
    /// compiletest passes it (`contains_lines`), so it is parity — with the
    /// unnamed failed harness in the note.
    #[test]
    fn kani_contains_lines_parity_names_an_unnamed_failed_harness() {
        let out = "Checking harness Frac::check_equals...\n\
                   Check 1: Frac::check_equals.assertion.1\n\
                   \t - Status: SUCCESS\n\
                   \t - Description: \"assertion failed: gcd1 == gcd2\"\n\
                   VERIFICATION:- SUCCESSFUL\n\
                   Checking harness gcd_harness...\n\
                   Failed Checks: No recursive call to function gcd when checking contract gcd\n\
                   VERIFICATION:- FAILED\n\
                   Manual Harness Summary:\n\
                   Verification failed for - gcd_harness\n\
                   Complete - 1 successfully verified harnesses, 1 failures, 2 total.\n";
        let exp = "Frac::check_equals.assertion\\\n- Status: SUCCESS\\\n- Description: \"assertion failed: gcd1 == gcd2\"\n\nVERIFICATION:- SUCCESSFUL\n";
        let scored = scored_kani("expected", V::Success, out, Some(1), Some(exp));
        assert_eq!((scored.class, scored.reason), (C::Parity, Some(KANI_PARITY_WITH_UNNAMED_FAILURE)));
        let mut r = TestResult::blank("expected", "function-contract/gcd_rec_replacement_pass.rs", V::Success);
        let unit = UnitCtx {
            engine: Engine::Kani,
            suite: "expected",
            rel: "function-contract/gcd_rec_replacement_pass.rs",
            oracle: V::Success,
            is_cargo: false,
            check_fail: false,
            expected: Some(exp),
            route: Route::DevCli,
            route_attestation: None,
            upstream_ignored: false,
        };
        let attempt = Attempt {
            stdout: out,
            stderr: "",
            exit_code: Some(1),
            timed_out: false,
            retried_after_outer_timeout: false,
            spawn_error: None,
        };
        score_unit(&unit, &attempt, &mut r);
        assert_eq!(r.classification, Some(C::Parity));
        assert!(r.note.ends_with("does not name: gcd_harness"), "{}", r.note);
        // An expected file that itself records the FAILED verdict, or names
        // the failed harness, is ordinary parity with an empty note.
        let names_it = format!("{exp}Verification failed for - gcd_harness\n");
        assert_eq!(scored_kani("expected", V::Success, out, Some(1), Some(&names_it)).reason, None);
        let failed_exp = "VERIFICATION:- FAILED\n";
        assert_eq!(scored_kani("expected", V::Fail, out, Some(1), Some(failed_exp)).reason, None);
    }

    /// `kani/Closure/boxed_closure.rs` (its `#[kani::proof]` is commented
    /// out): Kani finds no harness, verifies nothing and exits 0. That is
    /// `vacuous`, not parity, although compiletest passes it.
    #[test]
    fn kani_no_harness_is_vacuous_not_parity() {
        let out = format!("Kani Rust Verifier 0.67.0 (standalone)\nManual Harness Summary:\n{KANI_NO_HARNESSES}\n");
        let scored = scored_kani("kani", V::Success, &out, Some(0), None);
        assert_eq!(scored.class, C::Vacuous);
        assert!(scored.reason.unwrap().contains("no harness"));
    }

    /// `expected/quantifiers/large_range_warning.rs` on a host without z3
    /// (Kani 0.67.0): the expected diagnostic lines are printed, then
    /// kani-driver panics on CBMC's `ERROR` status. `contains_lines` would
    /// pass it; a panicked driver measured nothing, so it is `error`.
    #[test]
    fn kani_driver_panic_is_error_even_after_expected_lines() {
        let out = "warning: `kani::forall` has an unbounded (~2^64) range\n\
                   Checking harness check_unbounded_forall_warns...\n\
                   Running SMT2 QF_AUFBV using Z3\n\
                   thread '<unnamed>' (1492387) panicked at kani-driver/src/cbmc_output_parser.rs:470:25:\n\
                   called `Result::unwrap()` on an `Err` value: Error(\"unknown variant `ERROR`, expected one of `FAILURE`, `COVERED`\")\n";
        let scored = scored_kani("expected", V::Success, out, Some(101), Some("`kani::forall` has an unbounded (~2^64) range\n"));
        assert_eq!(scored.class, C::Error);
        assert!(scored.reason.unwrap().contains("kani-driver panicked"));
        assert_eq!(classify_kani_in("kani", V::Success, out, Some(101), None), C::Error);
    }

    /// `kani/ArithOperators/unsafe_sub_fail.rs` under Kani 0.67.0 (a
    /// `kani-verify-fail` test whose harness takes arguments, which 0.67.0
    /// rejects): the compile error's nonzero exit satisfies compiletest's
    /// `kani` mode, but a run with no verdict is `error` here, and the note
    /// quotes the rustc diagnostic rather than the launcher's echo.
    #[test]
    fn kani_run_without_a_verdict_is_error_even_for_a_verify_fail_test() {
        let out = "Kani Rust Verifier 0.67.0 (standalone)\n\
                   error: /home/u/.kani/kani-0.67.0/bin/kani-compiler exited with status exit status: 101\n\
                   error: functions used as harnesses cannot have any arguments\n\
                   error: aborting due to 1 previous error; 2 warnings emitted\n";
        let mut r = TestResult::blank("kani", "ArithOperators/unsafe_sub_fail.rs", V::Fail);
        let unit = UnitCtx {
            engine: Engine::Kani,
            suite: "kani",
            rel: "ArithOperators/unsafe_sub_fail.rs",
            oracle: V::Fail,
            is_cargo: false,
            check_fail: false,
            expected: None,
            route: Route::DevCli,
            route_attestation: None,
            upstream_ignored: false,
        };
        let attempt = Attempt {
            stdout: out,
            stderr: "",
            exit_code: Some(1),
            timed_out: false,
            retried_after_outer_timeout: false,
            spawn_error: None,
        };
        score_unit(&unit, &attempt, &mut r);
        assert_eq!(r.classification, Some(C::Error));
        assert!(r.note.starts_with("error: /home/u/.kani"), "{}", r.note);
        let rustc = "error[E0433]: failed to resolve: could not find `stub_set` in `kani`\nerror: aborting due to 2 previous errors\n";
        let with_code = format!("error: kani-compiler exited with status exit status: 101\n{rustc}");
        let mut r2 = TestResult::blank("kani", "Stubbing/stub_set_basic.rs", V::Success);
        let unit2 = UnitCtx { rel: "Stubbing/stub_set_basic.rs", oracle: V::Success, ..unit };
        score_unit(&unit2, &Attempt { stdout: &with_code, ..attempt }, &mut r2);
        assert_eq!(r2.classification, Some(C::Error));
        assert!(r2.note.starts_with("error[E0433]"), "{}", r2.note);
    }

    /// A non-parity Kani row on an upstream-ignored unit says that
    /// compiletest skips it, since no upstream verdict exists for it; a
    /// parity row and a trust-mc row do not. Every row carries the unit's
    /// `upstream_ignored` bit whatever its engine or class.
    #[test]
    fn kani_fixme_paths_are_flagged_in_the_note() {
        let failed = "Checking harness main...\nFailed Checks: assertion failed: x\nVERIFICATION:- FAILED\n";
        let score = |engine: Engine, rel: &str, oracle: V| {
            let mut r = TestResult::blank("kani", rel, oracle);
            let upstream_ignored = crate::discover::compiletest_ignores("kani", rel);
            let unit = UnitCtx { engine, suite: "kani", rel, oracle, is_cargo: false, check_fail: false, expected: None, route: Route::DevCli, route_attestation: None, upstream_ignored };
            let attempt = Attempt {
                stdout: failed,
                stderr: "",
                exit_code: Some(1),
                timed_out: false,
                retried_after_outer_timeout: false,
                spawn_error: None,
            };
            score_unit(&unit, &attempt, &mut r);
            r
        };
        let fp = score(Engine::Kani, "PointerOffset/fixme_wrap_nonzero_offset.rs", V::Success);
        assert_eq!(fp.classification, Some(C::FalsePositive));
        assert_eq!(fp.note, "[Kani's compiletest skips this path (`fixme`/`ignore` in it)]");
        let parity = score(Engine::Kani, "PointerOffset/fixme_wrap_nonzero_offset.rs", V::Fail);
        assert_eq!((parity.classification, parity.note.as_str()), (Some(C::Parity), ""));
        let plain = score(Engine::Kani, "PointerOffset/wrap.rs", V::Success);
        assert_eq!((plain.classification, plain.note.as_str()), (Some(C::FalsePositive), ""));
        let tm = score(Engine::TrustMc, "PointerOffset/fixme_wrap_nonzero_offset.rs", V::Success);
        assert!(!tm.note.contains("compiletest skips"), "{}", tm.note);
        assert!(fp.upstream_ignored && parity.upstream_ignored && tm.upstream_ignored);
        assert!(!plain.upstream_ignored);
    }

    // ---- per-unit resource accounting ---------------------------------------

    fn sh(script: &str) -> Command {
        let mut c = Command::new("sh");
        c.arg("-c").arg(script).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
        c
    }

    fn python3() -> Option<PathBuf> {
        which::which("python3").ok()
    }

    /// A finished child reports its exit code, a positive wall time, its own
    /// exact `ru_maxrss`, and (on Linux) a tree peak no smaller than that.
    /// With a memory-hungry GRANDCHILD (python under sh) the tree peak sees
    /// the allocation, and so does `max_rss_kb`: Linux folds the peak of
    /// reaped descendants into `wait4`'s `ru_maxrss` (as a max, not a sum).
    #[test]
    fn spawn_accounts_wall_time_and_memory() {
        let run = spawn_with_timeout(sh("echo out; echo err >&2; exit 3"), Duration::from_secs(30)).unwrap();
        assert_eq!(run.exit_code, Some(3));
        assert!(!run.timed_out);
        assert_eq!((run.stdout.trim(), run.stderr.trim()), ("out", "err"));
        assert!(run.max_rss_kb > 0, "ru_maxrss of a shell is never zero");
        if cfg!(target_os = "linux") {
            let tree = run.tree_peak_rss_kb.expect("Linux samples the tree");
            assert!(tree >= run.max_rss_kb, "{tree} < {}", run.max_rss_kb);
        } else {
            assert_eq!(run.tree_peak_rss_kb, None);
        }

        let Some(py) = python3() else {
            eprintln!("python3 not found; skipping the grandchild-memory half");
            return;
        };
        // 96 MB touched by a grandchild that then lingers long enough to be
        // sampled at least a few times.
        let script = format!(
            "{} -c 'b = bytearray(96 << 20)\nfor i in range(0, len(b), 4096): b[i] = 1\nimport time; time.sleep(0.4)'",
            py.display()
        );
        let run = spawn_with_timeout(sh(&script), Duration::from_secs(60)).unwrap();
        assert_eq!(run.exit_code, Some(0), "{}", run.stderr);
        assert!(run.wall_ms >= 300, "wall {}ms", run.wall_ms);
        if cfg!(target_os = "linux") {
            let tree = run.tree_peak_rss_kb.unwrap();
            assert!(tree >= 90_000, "tree peak {tree} KB did not see the grandchild's 96 MB");
            assert!(run.max_rss_kb >= 90_000, "wait4 ru_maxrss {} KB should fold in the reaped grandchild", run.max_rss_kb);
        }
    }

    /// An outer-watchdog kill takes the WHOLE process group with it: the
    /// grandchild `sleep` that used to be orphaned is dead too, and the
    /// leader is reported as signaled (no exit code) and timed out.
    #[test]
    fn watchdog_kills_the_whole_process_group() {
        // The shell prints the grandchild's pid, then waits on it.
        let run = spawn_with_timeout(sh("sleep 300 & echo $!; wait"), Duration::from_millis(400)).unwrap();
        assert!(run.timed_out);
        assert_eq!(run.exit_code, None);
        assert!(run.wall_ms >= 400 && run.wall_ms < 5_000, "wall {}ms", run.wall_ms);
        let grandchild: u32 = run.stdout.trim().parse().expect("the shell printed a pid");
        // Killed processes may linger as zombies until their new parent reaps
        // them; alive-and-running is the only failure.
        let alive = |pid: u32| {
            std::fs::read_to_string(format!("/proc/{pid}/stat"))
                .ok()
                .and_then(|s| process_tree::parse_stat_state(&s))
                .is_some_and(|state| state != 'Z' && state != 'X')
        };
        let mut waited = 0;
        while cfg!(target_os = "linux") && alive(grandchild) && waited < 2_000 {
            std::thread::sleep(Duration::from_millis(50));
            waited += 50;
        }
        if cfg!(target_os = "linux") {
            assert!(!alive(grandchild), "grandchild sleep {grandchild} survived the group kill");
        } else {
            // SAFETY: signal 0 only probes for existence.
            let probe = unsafe { libc::kill(grandchild as libc::pid_t, 0) };
            assert!(probe != 0 || std::io::Error::last_os_error().raw_os_error() != Some(0));
        }
    }

    /// A registration holds its slot exactly as long as it lives, so the
    /// signal handler only ever kills groups that are still being waited on.
    /// (Checked on the specific pid: the table is process-global and other
    /// tests spawn concurrently.)
    #[test]
    fn live_child_registration_is_scoped() {
        let pid: libc::pid_t = 1_000_000_007;
        assert!(!live_children::is_registered(pid));
        let reg = live_children::register(pid);
        assert!(live_children::is_registered(pid));
        drop(reg);
        assert!(!live_children::is_registered(pid));
    }

    /// The `/proc` parsers: a command name with spaces and parentheses does
    /// not shift the ppid/pgrp fields, and `VmHWM` is read in KB.
    #[test]
    fn proc_parsers() {
        let stat = "1234 (my (odd) cmd) S 77 1234 1234 0 -1 4194560 ...";
        assert_eq!(process_tree::parse_stat_ppid_pgrp(stat), Some((77, 1234)));
        assert_eq!(process_tree::parse_stat_state(stat), Some('S'));
        assert_eq!(process_tree::parse_stat_ppid_pgrp("garbage"), None);
        let status = "Name:\tsh\nVmPeak:\t   5000 kB\nVmHWM:\t    1536 kB\nVmRSS:\t 1000 kB\n";
        assert_eq!(process_tree::parse_vm_hwm_kb(status), Some(1536));
        assert_eq!(process_tree::parse_vm_hwm_kb("Name:\tkthreadd\n"), None);
        // The live tree under this test process contains at least itself.
        let me = std::process::id();
        assert!(process_tree::descendants(me).contains(&me));
        if cfg!(target_os = "linux") {
            assert!(process_tree::sample_peak_kb(me).unwrap() > 0);
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The execution engine: run trust-mc on each discovered Kani test, parse its
//! verdict + AY soundness markers, classify against the oracle, and write
//! results incrementally (resumable across a multi-hour run).

use std::collections::HashSet;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::discover::{Discovered, EntryKind};
use crate::env::Env;
use crate::model::{Classification, TestResult, Verdict};
use crate::rekey::{Rekey, Surface, rekey_source};

/// Tunables for a run.
#[derive(Debug, Clone)]
pub struct RunConfig {
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
        "[kani-domination] running {total} test(s) on {} job(s), backend={}, harness-timeout={}s (outer {:?} + per-extra-harness)  [{} resumed]",
        cfg.jobs, cfg.backend, cfg.harness_timeout_s, cfg.base_outer_timeout(), prior.len()
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
                        "[{n}/{total}] {:<11} {:<52} oracle={:<7} -> {:<8} {}",
                        test.suite,
                        truncate(&test.rel, 52),
                        format!("{:?}", test.oracle).to_lowercase(),
                        result.classification.map(|c| c.as_str()).unwrap_or("?"),
                        format!("{}ms", result.duration_ms),
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

/// Run a single test and classify it.
fn run_one(env: &Env, test: &Discovered, cfg: &RunConfig) -> TestResult {
    let mut result = TestResult {
        suite: test.suite.clone(),
        file: test.rel.clone(),
        oracle: test.oracle,
        observed: None,
        classification: None,
        sound_fallback: 0,
        effective_success: false,
        proof_marker: false,
        native_proof_accepted: false,
        ctrex_category: None,
        ctrex_categories_raw: Vec::new(),
        translation_drops: Vec::new(),
        no_harnesses: false,
        vacuous: false,
        aggregate_gap_reasons: Vec::new(),
        unknown_reason: None,
        unknown_category: None,
        unknown_category_detail: None,
        demotion_reasons: Vec::new(),
        self_reported_unsound: false,
        duration_ms: 0,
        exit_code: None,
        flags: Vec::new(),
        note: String::new(),
        rekey: None,
    };

    let flags = sanitize_flags(&test.flags, cfg);
    result.flags = flags.clone();

    // Per-test isolated target dir (avoids rmeta/smt2 write collisions).
    let iso = env
        .build_base()
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

    // PATH with the ay binary's directory prepended (SMT path resolves `ay`)
    // and, for cargo units, the cargo binary's directory (the driver shells
    // out to `cargo`).
    let mut path = std::env::var_os("PATH").unwrap_or_default();
    {
        let mut parts: Vec<PathBuf> = Vec::new();
        if let Some(ay_dir) = env.ay.parent() {
            parts.push(ay_dir.to_path_buf());
        }
        if let Some(cargo_dir) = env.cargo.as_deref().and_then(|c| c.parent()) {
            parts.push(cargo_dir.to_path_buf());
        }
        parts.extend(std::env::split_paths(&path));
        if let Ok(joined) = std::env::join_paths(parts) {
            path = joined;
        }
    }

    // Built as a closure so an outer-watchdog kill can be RETRIED once; see the
    // retry below for why that is a measurement fix, not budget laundering.
    let build_cmd = || {
    let mut cmd = Command::new(&env.verifier);
    let outer_timeout = match &test.kind {
        EntryKind::SingleFile { harness_count } => {
            // Run from the Kani checkout root, mirroring Kani's own harness.
            // Test headers declare paths RELATIVE to that root, e.g.
            // `// kani-flags: -Z c-ffi --c-lib tests/kani/ForeignItems/lib.c`.
            // Without this the child inherits the runner's cwd
            // (tools/kani-domination), the path resolves to nothing, and the
            // driver silently ingests an EMPTY C library — so the row cannot
            // distinguish "the C-body lane is inert" from "the C-body lane is
            // never reached". A corpus that cannot fail is not evidence.
            // Only the CargoPackage arm set a cwd before; this arm did not.
            cmd.arg(&run_abs).args(&flags).current_dir(env.kani_dir());
            cfg.outer_timeout(*harness_count)
        }
        EntryKind::CargoPackage { manifest_dir, harness, harness_count } => {
            // Invoke the driver in its `cargo trust-mc` identity (argv[1] =
            // `trust-mc`) inside the package dir, mirroring Kani's
            // `run_cargo_kani_test`: `--harness <stem>` unless the expected
            // file is the package-wide `expected`.
            cmd.arg("trust-mc").args(&flags).current_dir(manifest_dir);
            if let Some(h) = harness {
                cmd.args(["--harness", h]);
            }
            cfg.cargo_outer_timeout(*harness_count)
        }
    };
    cmd.arg("--target-dir")
        .arg(&iso)
        .env("TRUST_MC_SYSROOT", &env.sysroot)
        .env("PATH", &path)
        .env("TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS", "1")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if !test.rustflags.is_empty() {
        cmd.env("RUSTFLAGS", test.rustflags.join(" "));
    }
        (cmd, outer_timeout)
    };

    let start = Instant::now();
    let (cmd, outer_timeout) = build_cmd();
    let (mut out, mut err, mut exit, mut timed_out) = match spawn_with_timeout(cmd, outer_timeout) {
        Ok(v) => v,
        Err(e) => {
            result.note = format!("spawn-failed: {e}");
            result.classification = Some(Classification::Error);
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
    // recorded in the note so the number stays auditable.
    let mut retried_after_outer_timeout = false;
    if timed_out {
        retried_after_outer_timeout = true;
        let (cmd2, outer_timeout2) = build_cmd();
        if let Ok((o2, e2, x2, t2)) = spawn_with_timeout(cmd2, outer_timeout2) {
            out = o2;
            err = e2;
            exit = x2;
            timed_out = t2;
        }
    }
    result.duration_ms = start.elapsed().as_millis() as u64;
    result.exit_code = exit;

    let combined = format!("{out}\n{err}");
    parse_markers(&combined, &mut result);
    // P1 MECH D: in a coherent multi-harness run, surface the FIRST FAILING
    // harness's category/reason instead of the stream-first marker (which may
    // belong to a should-panic success and misattribute the note).
    reattribute_multi_harness_markers(&combined, &mut result);
    let observed = parse_verdict(&combined);
    result.observed = Some(observed);
    let expected_content =
        test.expected_path.as_deref().and_then(|p| std::fs::read_to_string(p).ok());
    let ctx = ClassifyCtx {
        oracle: test.oracle,
        observed,
        timed_out,
        exit,
        is_cargo: matches!(test.kind, EntryKind::CargoPackage { .. }),
        expected: expected_content.as_deref(),
        check_fail: test.check_fail,
    };
    result.classification = Some(classify(&ctx, &result, &combined));
    // Explicit corpus quarantine: a manifest-listed un-compilable source that
    // (as expected) produced an `Error` row is the corpus's failure, not
    // trust-mc's — reclassify to the visible `corpus_invalid` column with the
    // manifest's evidence. Verdict-bearing runs are never touched.
    if let Some(class) = result.classification {
        let (class, evidence) =
            crate::quarantine::apply_corpus_quarantine(class, &test.suite, &test.rel);
        result.classification = Some(class);
        if let Some(evidence) = evidence {
            result.note = format!("corpus-invalid (not a trust-mc failure): {evidence}");
        }
    }
    if result.note.is_empty() {
        result.note = note_for(&result, timed_out, &combined, test.check_fail);
    }
    if retried_after_outer_timeout {
        result.note = format!("{} [retried-after-outer-timeout]", result.note);
    }
    // Reclaim the per-test artifact dir (rmeta/rlib/smt2) — the verdict is
    // captured, so ~20MB/test * thousands of tests need not accumulate.
    let _ = std::fs::remove_dir_all(iso.parent().unwrap_or(&iso));
    result
}

/// Build the final verifier flag list from the raw kani-flags + config.
fn sanitize_flags(raw: &[String], cfg: &RunConfig) -> Vec<String> {
    let mut kept = Vec::new();
    let mut has_unstable = false;
    let mut has_htimeout = false;
    let mut has_chc = false;
    let mut i = 0;
    while i < raw.len() {
        let f = &raw[i];
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
    out.extend(cfg.extra_driver_flags.iter().cloned());
    out
}

/// Spawn a child, draining stdout/stderr concurrently, killing it if it runs
/// past `timeout`. Returns (stdout, stderr, exit_code, timed_out).
fn spawn_with_timeout(
    mut cmd: Command,
    timeout: Duration,
) -> anyhow::Result<(String, String, Option<i32>, bool)> {
    let mut child = cmd.spawn()?;
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

    let deadline = Instant::now() + timeout;
    let mut timed_out = false;
    let exit = loop {
        match child.try_wait()? {
            Some(status) => break status.code(),
            None => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    timed_out = true;
                    break None;
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    };
    let out = String::from_utf8_lossy(&t_out.join().unwrap_or_default()).into_owned();
    let err = String::from_utf8_lossy(&t_err.join().unwrap_or_default()).into_owned();
    Ok((out, err, exit, timed_out))
}

/// File-level observed verdict: any FAILED => Fail; else any UNVALIDATED (a
/// demoted per-harness verdict the driver could not independently validate,
/// e.g. `VERIFICATION:- UNVALIDATED (DT+BV)`) => Unknown — an unvalidated
/// harness must never let the file score as an observed Success; else any
/// SUCCESSFUL => Success; else Unknown.
///
/// Regression context (2026-07-19): kani/SIMD/portable_simd.rs classified
/// `unsound_pass` because check_mask emitted the bare UNVALIDATED verdict
/// (unknown to this parser), the two sibling harnesses were SUCCESSFUL, and
/// the file therefore aggregated to observed=Success while `clean_success`
/// correctly saw the fallback taint. The verdict-string set here must track
/// the driver's `verification_result` output strings.
fn parse_verdict(s: &str) -> Verdict {
    if s.contains("VERIFICATION:- FAILED") {
        Verdict::Fail
    } else if s.contains("VERIFICATION:- UNVALIDATED") {
        Verdict::Unknown
    } else if s.contains("VERIFICATION:- SUCCESSFUL") {
        Verdict::Success
    } else {
        Verdict::Unknown
    }
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
    r.self_reported_unsound = s.contains("created fresh unconstrained")
        || s.contains("pointee_synthesis_fallback")
        || s.contains("unconstrained_assignment")
        || s.contains("UNSOUND verification");
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
    let mut sections: Vec<(String, String)> = Vec::new();
    let mut current: Option<(String, String)> = None;
    for line in combined.lines() {
        let content = strip_thread_prefix(line);
        if content.starts_with("Manual Harness Summary:") {
            break;
        }
        if let Some(rest) = content.strip_prefix("Checking harness ") {
            if let Some(section) = current.take() {
                sections.push(section);
            }
            let name = rest.trim_end().trim_end_matches("...").to_string();
            current = Some((name, String::new()));
        } else if let Some((_, text)) = current.as_mut() {
            text.push_str(line);
            text.push('\n');
        }
    }
    if let Some(section) = current.take() {
        sections.push(section);
    }
    sections
}

fn harness_outcome(name: &str, text: &str) -> HarnessOutcome {
    // FAILED wins over SUCCESSFUL if both somehow appear (conservative).
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
    // Fail-closed: only an unambiguous all-Genuine section is conclusive —
    // no category at all (demoted result), any non-Genuine category
    // (Unknown, OverApproximation, or a future label this parser does not
    // know), an UNKNOWN reason, or an inconclusive-solver line all taint.
    let inconclusive = cats.is_empty()
        || cats.iter().any(|c| c != "Genuine")
        || unknown_reason.is_some()
        || text.contains("ay-chc inconclusive");
    HarnessOutcome { name: name.to_string(), verdict, cats, unknown_reason, encoding_gap, inconclusive }
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
fn coherent_multi_harness_outcomes(combined: &str) -> Option<Vec<HarnessOutcome>> {
    let sections = split_harness_sections(combined);
    if sections.len() < 2 {
        return None;
    }
    let outcomes: Vec<HarnessOutcome> =
        sections.iter().map(|(name, text)| harness_outcome(name, text)).collect();
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

/// Adjudicate a multi-harness FAILED run per harness. `None` = fall back to
/// the run-level path unchanged.
/// Does trust-mc's output satisfy KANI'S OWN pass/fail rule for this test?
///
/// Kani's `expected` suite is decided by `contains_lines` over the output —
/// `run_expected_test` (kani compiletest `runtest.rs`) never inspects the exit
/// status. So when every line of the expected file is present in trust-mc's
/// output, this is a test Kani considers PASSING and trust-mc reproduced it;
/// calling that a divergence-from-Kani would be wrong.
///
/// Used ONLY as a tiebreaker on the false-positive arms (see the call sites),
/// never as the scoring rule. Measured on 98 real runs, replacing the verdict
/// rule with `contains_lines` wholesale demotes 53 of 94 scorable rows —
/// trust-mc does not emit CBMC's per-check report text — and forgives verdict
/// errors on 111 of 470 rows, 17 of them missed-bug slots. Confined to the
/// false-positive arm it can only ever correct a wrong FP; it cannot demote a
/// passing row, and it cannot launder a real FP whose output is missing the
/// expected verdict line outright.
fn kani_criterion_satisfied(ctx: &ClassifyCtx<'_>, combined: &str) -> bool {
    // Triage lever: A/B the tiebreaker across the corpus without editing code.
    // Every flip it causes must be auditable, so keep a way to measure the set.
    if std::env::var("TRUST_MC_NO_KANI_TIEBREAK").map(|v| v == "1").unwrap_or(false) {
        return false;
    }
    matches!(ctx.expected, Some(exp) if matches_expected(combined, exp))
}

fn classify_multi_harness_fail(oracle: Verdict, combined: &str) -> Option<Classification> {
    let outcomes = coherent_multi_harness_outcomes(combined)?;
    let failing: Vec<&HarnessOutcome> =
        outcomes.iter().filter(|o| o.verdict == Verdict::Fail).collect();
    if failing.is_empty() {
        return None; // observed said Fail but no section failed — incoherent
    }
    if failing.iter().any(|o| o.encoding_gap) {
        return Some(Classification::EncodingGap);
    }
    // The taint applies per harness: ANY failing harness that is not a
    // genuine counterexample makes the file inconclusive — a co-harness's
    // Genuine can no longer mask it (and a should-panic success's Genuine
    // marker no longer vouches for a different harness's failure).
    if failing.iter().any(|o| o.inconclusive) {
        return Some(Classification::Unknown);
    }
    // Every failing harness carries a genuine counterexample (the
    // inconclusive gate above is fail-closed: cats non-empty, all Genuine).
    Some(if oracle == Verdict::Fail {
        Classification::Parity
    } else {
        Classification::FalsePositive
    })
}

/// Re-key `ctrex_category` / `unknown_reason` to the FIRST FAILING harness of
/// a coherent multi-harness run: `parse_markers` records the first marker in
/// the stream, which may belong to a harness that succeeded (misattributed
/// notes/reports). Only touches attribution fields — classification reads the
/// per-harness outcomes directly.
fn reattribute_multi_harness_markers(combined: &str, r: &mut TestResult) {
    let Some(outcomes) = coherent_multi_harness_outcomes(combined) else {
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
    if !r.effective_success || r.sound_fallback != 0 || r.self_reported_unsound {
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
/// unsoundness, and no effective-success marker — except the fully validated
/// `#[kani::should_panic]` pass, which is the *correct* verdict, not a caveat.
fn clean_success(s: &str, r: &TestResult) -> bool {
    r.sound_fallback == 0
        && !r.self_reported_unsound
        && (!r.effective_success || validated_should_panic_success(s, r))
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

/// Everything the classifier needs beyond the parsed markers.
struct ClassifyCtx<'a> {
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
}

/// Kani compiletest `contains_lines` semantics: every line of the expected
/// file must appear (as a substring, whitespace-trimmed) in the output; a
/// trailing `\` joins expected lines into a block that must match
/// *consecutive* output lines.
pub fn matches_expected(output: &str, expected: &str) -> bool {
    let out_lines: Vec<&str> = output.lines().collect();
    let mut block: Vec<&str> = Vec::new();
    for line in expected.lines() {
        if let Some(prefix) = line.strip_suffix('\\') {
            block.push(prefix);
        } else {
            block.push(line);
            if !contains_block(&out_lines, &block) {
                return false;
            }
            block.clear();
        }
    }
    block.is_empty() || contains_block(&out_lines, &block)
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

fn classify(ctx: &ClassifyCtx<'_>, r: &TestResult, combined: &str) -> Classification {
    let ClassifyCtx { oracle, observed, timed_out, exit, is_cargo, expected, check_fail } = *ctx;
    if timed_out {
        return Classification::Timeout;
    }
    if crashed(combined, exit, timed_out) {
        return Classification::Crash;
    }
    // Kani's own pass criterion for expected-output tests: the output contains
    // every expected line(-block). Applied when trust-mc produced no verdict
    // (the expected file demands a *diagnostic*, e.g. a stubbing resolution
    // error) and, for cargo units, as the primary oracle — while keeping the
    // soundness discipline: a SUCCESS reached via fallback is never parity.
    if let Some(exp) = expected {
        if (observed == Verdict::Unknown || is_cargo) && matches_expected(combined, exp) {
            return if observed == Verdict::Success && !clean_success(combined, r) {
                Classification::UnsoundPass
            } else {
                Classification::Parity
            };
        }
    }
    if is_cargo && observed == Verdict::Unknown && build_unavailable(combined) {
        return Classification::BuildUnavailable;
    }
    if observed == Verdict::Unknown {
        // A trust-mc *compiler/tool* timeout (codegen too slow to even reach the
        // solver) is a completeness/perf gap, not a tool error — bucket it as a
        // timeout so it reads as "not yet", not "broken".
        if combined.contains("timed out after") || combined.contains("--tool-timeout") {
            return Classification::Timeout;
        }
        // `// kani-check-fail`: the oracle is "compilation fails" (Kani itself
        // errors out building this file). trust-mc refusing the same file with
        // a genuine rustc compile error IS the Kani verdict — parity. Strict:
        // requires the fail-oracle, a nonzero exit, a real rustc diagnostic
        // (never a driver panic), and — when an expected file exists — its
        // diagnostic text in the output (handled above; a non-matching
        // expected file blocks this path).
        if check_fail
            && oracle == Verdict::Fail
            && exit.is_some_and(|c| c != 0)
            && rustc_compile_error(combined)
            && expected.is_none_or(|e| matches_expected(combined, e))
        {
            return Classification::Parity;
        }
        // Distinguish a clean solver `unknown` from a hard tool error.
        let looks_like_error = combined.contains("error[")
            || combined.contains("error: ")
            || combined.contains("panicked at")
            || combined.contains("not found in PATH")
            || exit.map(|c| c != 0).unwrap_or(true);
        let has_unknown_verdict = combined.contains("[AY:UNKNOWN_QUALITY:")
            || combined.contains("VERIFICATION:- UNDETERMINED")
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
            return Classification::Vacuous;
        }
        return if looks_like_error && !has_unknown_verdict {
            Classification::Error
        } else {
            Classification::Unknown
        };
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
        return Classification::Error;
    }
    // A FAILED verdict needs its provenance examined before we trust it as a
    // genuine counterexample.
    if observed == Verdict::Fail {
        // 1. Unsupported construct / codegen panic -> feature gap.
        let unsupported = combined.contains("unsupported constructs")
            || combined.contains("Found the following unsupported")
            || combined.contains("codegen panic")
            || combined.contains("CHC codegen panic");
        if unsupported {
            return Classification::Unsupported;
        }
        // 2a. P1 MECH D: multi-harness runs are adjudicated PER HARNESS —
        //     each failing harness's own markers decide its quality, so one
        //     harness's Genuine cannot vouch for (nor its taint poison) a
        //     sibling. Engages only on a coherent per-harness split;
        //     otherwise the run-level path below is unchanged.
        if let Some(class) = classify_multi_harness_fail(oracle, combined) {
            // A multi-harness file whose expected content pins only SOME of its
            // harnesses can land here as a false positive while trust-mc is in
            // fact correct — e.g. `modifies/field_replace_pass` and
            // `modifies/check_only_verification` each pair a user harness with a
            // `proof_for_contract` harness whose contract is GENUINELY violated
            // (field_replace: `requires(*s.target < 100)` admits target=5 with
            // prior=7, so the body yields 6 while `ensures` claims prior+1 = 8;
            // check_only: `requires(*ptr < 100)` admits old=5, so the returned
            // `*ptr` is 6, not the 100 the `ensures` asserts). Kani's own rule
            // passes those files, so trust-mc has not diverged.
            if class == Classification::FalsePositive && kani_criterion_satisfied(ctx, combined) {
                return Classification::Parity;
            }
            return class;
        }
        // 2b. Ill-sorted / unparseable CHC, or non-genuine CTREX that trust-mc
        //    mapped to FAILED -> trust-mc CHC encoding gap / inconclusive.
        let (encoding_gap, inconclusive) = failure_quality(combined, r);
        if encoding_gap {
            return Classification::EncodingGap;
        }
        if inconclusive {
            return Classification::Unknown;
        }
        // 3. Otherwise this is a genuine counterexample.
        return if oracle == Verdict::Fail {
            Classification::Parity
        } else {
            // oracle == Success but trust-mc found a (claimed-genuine) CEX.
            //
            // Before calling that a false positive, ask the question the label
            // actually claims: does trust-mc DIVERGE FROM KANI here? Kani's own
            // pass/fail rule for the `expected` suite is `contains_lines` over
            // the output — `run_expected_test` (kani compiletest runtest.rs)
            // never inspects the exit status. So an expected file whose lines
            // are all present in trust-mc's output is a test KANI CONSIDERS
            // PASSING, and trust-mc reproduced it.
            //
            // This matters for multi-harness files whose expected content only
            // pins one harness. `function-contract/modifies/field_replace_pass`
            // and `.../check_only_verification` each pair a user harness with a
            // `proof_for_contract` harness whose contract is GENUINELY violated
            // (field_replace: `requires(*s.target < 100)` admits target=5 with
            // prior=7, so the body yields 6 while `ensures` claims prior+1=8;
            // check_only: `requires(*ptr < 100)` admits old=5, so the returned
            // `*ptr` is 6, not the 100 the `ensures` asserts). trust-mc is
            // RIGHT to fail those, and scoring it a false positive punishes a
            // correct answer.
            //
            // Deliberately NOT a wholesale oracle swap. Measured on 98 real
            // runs, replacing the verdict rule with contains_lines demotes 53
            // of 94 scorable rows (trust-mc does not emit CBMC's per-check
            // report text) and forgives verdict errors on 111 of 470 rows, 17
            // of them missed-bug slots. So contains_lines is used ONLY here, as
            // a tiebreaker on the false-positive arm, where it can reclassify a
            // wrong FP but can never demote a passing row. It also cannot
            // launder a real one: `loop-contract/decreases_binary_search` is a
            // single-harness file, its output lacks `VERIFICATION:- SUCCESSFUL`
            // entirely, contains_lines FAILS, and it stays a false positive.
            if kani_criterion_satisfied(ctx, combined) {
                Classification::Parity
            } else {
                Classification::FalsePositive
            }
        };
    }

    // observed == Success
    if oracle == Verdict::Success {
        if clean_success(combined, r) { Classification::Parity } else { Classification::UnsoundPass }
    } else {
        // oracle == Fail, observed == Success. Before branding it a missed
        // bug, check for the corpus-oracle artifact: the expected file records
        // Kani's failure only as "construct not currently supported by Kani"
        // (no whole-run FAILED verdict) — there is no bug in the program, Kani
        // simply cannot encode it. A clean, `[AY:PROOF]`-backed trust-mc proof
        // then *exceeds* the oracle. Own class; never silently parity.
        if r.proof_marker
            && clean_success(combined, r)
            && expected.is_some_and(oracle_is_unsupported_artifact)
        {
            return Classification::ExceedsOracle;
        }
        // Soundness-critical missed bug.
        Classification::MissedBug
    }
}

fn note_for(r: &TestResult, timed_out: bool, combined: &str, check_fail: bool) -> String {
    if timed_out {
        return "outer watchdog timeout".into();
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
        Some(Classification::UnsoundPass) => {
            format!("sound_fallback={} effective_success={}", r.sound_fallback, r.effective_success)
        }
        Some(Classification::ExceedsOracle) => {
            "oracle fail is a Kani unsupported-construct artifact (no genuine bug); \
             trust-mc cleanly proves the assertions"
                .into()
        }
        Some(Classification::Parity) if r.observed == Some(Verdict::Unknown) && check_fail => {
            format!("compile fails as kani-check-fail expects: {}", head_rustc_error(combined))
        }
        Some(Classification::Parity) if r.observed == Some(Verdict::Unknown) => {
            "output matches Kani expected file (diagnostic parity)".into()
        }
        _ => String::new(),
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

    /// A multi-harness file whose expected content pins only the harness that
    /// PASSES must not be branded a false positive when trust-mc is right.
    ///
    /// This is the `function-contract/modifies/field_replace_pass` /
    /// `check_only_verification` shape: a user harness verifies, a sibling
    /// `proof_for_contract` harness correctly REFUTES a contract that really is
    /// violated, and the expected file mentions only the former. Kani's own
    /// rule (`contains_lines`, exit status ignored) passes such a file, so
    /// trust-mc has not diverged.
    #[test]
    fn fp_is_downgraded_when_output_satisfies_kanis_own_criterion() {
        let combined = "\
Checking harness good...
VERIFICATION:- SUCCESSFUL
Checking harness contract_harness...
[AY:CTREX_CAT:Genuine]
Failed Checks: |result| bogus
VERIFICATION:- FAILED
";
        let expected = "VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(
            classify_full(V::Success, combined, false, Some(1), false, Some(expected)),
            C::Parity,
            "expected lines are all present, so Kani itself passes this file"
        );
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
        let mut r = TestResult {
            suite: "t".into(), file: "f.rs".into(), oracle, observed: None,
            classification: None, sound_fallback: 0, effective_success: false,
            proof_marker: false, native_proof_accepted: false, ctrex_category: None,
            ctrex_categories_raw: vec![], translation_drops: vec![], no_harnesses: false,
            vacuous: false, aggregate_gap_reasons: vec![],
            unknown_reason: None, unknown_category: None, unknown_category_detail: None,
            demotion_reasons: vec![], self_reported_unsound: false,
            duration_ms: 0,
            exit_code: exit, flags: vec![], note: String::new(), rekey: None,
        };
        parse_markers(combined, &mut r);
        let observed = parse_verdict(combined);
        r.observed = Some(observed);
        let ctx = ClassifyCtx { oracle, observed, timed_out, exit, is_cargo, expected, check_fail };
        classify(&ctx, &r, combined)
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
        let mut r = TestResult {
            suite: "".into(), file: "".into(), oracle: V::Success, observed: None,
            classification: None, sound_fallback: 0, effective_success: false,
            proof_marker: false, native_proof_accepted: false, ctrex_category: None,
            ctrex_categories_raw: vec![], translation_drops: vec![], no_harnesses: false,
            vacuous: false, aggregate_gap_reasons: vec![],
            unknown_reason: None, unknown_category: None, unknown_category_detail: None,
            demotion_reasons: vec![], self_reported_unsound: false,
            duration_ms: 0,
            exit_code: None, flags: vec![], note: String::new(), rekey: None,
        };
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
        let mut r = TestResult {
            suite: "".into(), file: "".into(), oracle: V::Fail, observed: None,
            classification: None, sound_fallback: 0, effective_success: false,
            proof_marker: false, native_proof_accepted: false, ctrex_category: None,
            ctrex_categories_raw: vec![], translation_drops: vec![], no_harnesses: false,
            vacuous: false, aggregate_gap_reasons: vec![],
            unknown_reason: None, unknown_category: None, unknown_category_detail: None,
            demotion_reasons: vec![], self_reported_unsound: false,
            duration_ms: 0,
            exit_code: None, flags: vec![], note: String::new(), rekey: None,
        };
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
        // The legacy inline form stays a Success at the parser level (its
        // soundness accounting is handled downstream by clean_success).
        let legacy = "VERIFICATION:- SUCCESSFUL (UNVALIDATED) (encountered one or more panics as expected)\n";
        assert_eq!(super::parse_verdict(legacy), Verdict::Success);
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
            harness_timeout_s: 15,
            outer_multiplier: 5,
            grace_s: 30,
            jobs: 1,
            backend: "chc".into(),
            strip_cbmc: true,
            surface: Surface::Legacy,
            extra_driver_flags: Vec::new(),
        };
        let base = Duration::from_secs(15 * 5 + 30);
        assert_eq!(cfg.outer_timeout(0), base);
        assert_eq!(cfg.outer_timeout(1), base);
        assert_eq!(cfg.outer_timeout(11), base + Duration::from_secs(15 * 10));
        // Cargo scaling unchanged: base + per-harness budget + compile allowance.
        assert_eq!(cfg.cargo_outer_timeout(2), base + Duration::from_secs(15 * 2 + 300));
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
        let mut r = TestResult {
            suite: "t".into(), file: "f.rs".into(), oracle: V::Success, observed: None,
            classification: None, sound_fallback: 0, effective_success: false,
            proof_marker: false, native_proof_accepted: false, ctrex_category: None,
            ctrex_categories_raw: vec![], translation_drops: vec![], no_harnesses: false,
            vacuous: false, aggregate_gap_reasons: vec![],
            unknown_reason: None, unknown_category: None, unknown_category_detail: None,
            demotion_reasons: vec![], self_reported_unsound: false,
            duration_ms: 0,
            exit_code: Some(1), flags: vec![], note: String::new(), rekey: None,
        };
        parse_markers(out, &mut r);
        assert_eq!(r.ctrex_category.as_deref(), Some("Genuine")); // stream-first (the bug)
        reattribute_multi_harness_markers(out, &mut r);
        assert_eq!(r.ctrex_category.as_deref(), Some("OverApproximation"));
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
        assert!(coherent_multi_harness_outcomes(out).is_none());
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
        let outcomes = coherent_multi_harness_outcomes(out).expect("coherent");
        assert!(!outcomes[0].inconclusive);
        assert!(outcomes[1].inconclusive, "category-less FAILED harness is inconclusive");
        assert_eq!(classify_output(V::Fail, out, false, Some(1)), C::Unknown);
    }
}

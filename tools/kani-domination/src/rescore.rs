// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `rescore`: re-classify every row of a results file from its saved unit
//! log (`unitlog`) under the CURRENT scorer, without re-running the corpus.
//! The output is a sibling `<stem>-rescored.jsonl` (plus its provenance
//! sidecar, re-stamped with the scorer version) and a per-row diff of the
//! classifications that moved. Fail-closed: a row without a log, a log that
//! does not parse, or a log whose identity disagrees with its row refuses the
//! whole file — a half-rescored file would be a mixed-scorer file.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

use crate::model::{Classification, RouteAttestation, SCORER_VERSION, TestResult};
use crate::route::{LEGACY_ROUTE, Route, route_or_legacy};
use crate::runner::{Attempt, UnitCtx, score_unit};
use crate::spec::SpecIndex;
use crate::unitlog;

/// What a rescore found, for the printed report.
#[derive(Debug, Default)]
pub struct Diff {
    pub rows: usize,
    /// `(unit, old class, new class, new note)` for every row that moved.
    pub changed: Vec<(String, String, String, String)>,
    pub old_counts: BTreeMap<String, u64>,
    pub new_counts: BTreeMap<String, u64>,
    /// Scorer versions the input rows carried.
    pub old_versions: BTreeMap<u32, u64>,
    /// `(unit, old oracle, new oracle)` for every row whose oracle the current
    /// discovery rules derive differently (`discover::rederive_oracle`).
    pub oracle_changed: Vec<(String, String, String)>,
}

fn class_str(c: Option<Classification>) -> String {
    c.map(|c| c.as_str().to_string()).unwrap_or_else(|| "?".into())
}

/// Re-score `rows` from their logs under `log_root`. Measurement fields
/// (timings, memory, flags, re-key provenance, the route, the log path) are
/// carried over; everything the scorer decides is recomputed from the log,
/// against `route_attestation` (the sidecar's) for a Trustc row. A unit is
/// upstream-ignored when its log says so (a log written before the field
/// reads as compiletest's path rule) or `spec` classifies it `fixme`.
pub fn rescore_rows(
    rows: &[TestResult],
    log_root: &Path,
    route_attestation: Option<&RouteAttestation>,
    spec: Option<&SpecIndex>,
) -> Result<(Vec<TestResult>, Diff)> {
    let mut out = Vec::with_capacity(rows.len());
    let mut diff = Diff { rows: rows.len(), ..Diff::default() };
    for row in rows {
        let unit_name = format!("{}/{}", row.suite, row.file);
        let Some(rel) = &row.log_path else {
            bail!(
                "{unit_name}: no `log_path` — its row was written before logs were captured \
                 (scorer version {}), so it cannot be re-scored; re-run the unit",
                row.scorer_version
            );
        };
        let log = unitlog::read(&log_root.join(rel))
            .with_context(|| format!("{unit_name}: cannot read its log {rel} under {}", log_root.display()))?;
        // The oracle is re-derived from the logged expected content under the
        // current rules, exactly as discovery derives it today. A row carries
        // either the oracle its log recorded or, once rescored, the re-derived
        // one; any other oracle is not this log's row. Before 2026-09-14 only
        // the logged oracle was accepted, so rescoring a rescored file whose
        // oracle had moved (a compile-fail unit) was refused.
        let (oracle, check_fail) = crate::discover::rederive_oracle(
            &log.suite,
            &log.file,
            log.oracle,
            log.check_fail,
            log.expected.as_deref(),
        );
        if log.suite != row.suite || log.file != row.file || (log.oracle != row.oracle && oracle != row.oracle) {
            bail!(
                "{unit_name}: its log describes {}/{} (oracle {:?}, re-derived {:?}), not this row (oracle {:?})",
                log.suite,
                log.file,
                log.oracle,
                oracle,
                row.oracle
            );
        }
        if route_or_legacy(log.route.as_deref()) != route_or_legacy(row.route.as_deref()) {
            bail!(
                "{unit_name}: its log ran on route {}, its row says {}",
                route_or_legacy(log.route.as_deref()),
                route_or_legacy(row.route.as_deref())
            );
        }
        let route = match route_or_legacy(row.route.as_deref()) {
            "trustc" => Route::Trustc,
            "dev-cli" => Route::DevCli,
            other => bail!("{unit_name}: unknown route `{other}`"),
        };
        if oracle != row.oracle {
            diff.oracle_changed.push((
                unit_name.clone(),
                format!("{:?}", row.oracle).to_lowercase(),
                format!("{oracle:?}").to_lowercase(),
            ));
        }
        let mut new = TestResult::blank(&row.suite, &row.file, oracle);
        new.route = row.route.clone();
        new.duration_ms = row.duration_ms;
        new.wall_ms = row.wall_ms;
        new.max_rss_kb = row.max_rss_kb;
        new.tree_peak_rss_kb = row.tree_peak_rss_kb;
        new.flags = row.flags.clone();
        new.rekey = row.rekey.clone();
        new.log_path = row.log_path.clone();
        let unit = UnitCtx {
            engine: log.engine,
            suite: &log.suite,
            rel: &log.file,
            oracle,
            is_cargo: log.is_cargo,
            check_fail,
            expected: log.expected.as_deref(),
            route,
            route_attestation,
            upstream_ignored: log.upstream_ignored || spec.is_some_and(|s| s.is_fixme(&log.suite, &log.file)),
        };
        let attempt = Attempt {
            stdout: &log.stdout,
            stderr: &log.stderr,
            exit_code: log.exit_code,
            timed_out: log.timed_out,
            retried_after_outer_timeout: log.retried_after_outer_timeout,
            spawn_error: log.spawn_error.as_deref(),
        };
        score_unit(&unit, &attempt, &mut new);

        *diff.old_versions.entry(row.scorer_version).or_default() += 1;
        *diff.old_counts.entry(class_str(row.classification)).or_default() += 1;
        *diff.new_counts.entry(class_str(new.classification)).or_default() += 1;
        if row.classification != new.classification {
            diff.changed.push((
                unit_name,
                class_str(row.classification),
                class_str(new.classification),
                new.note.clone(),
            ));
        }
        out.push(new);
    }
    Ok((out, diff))
}

/// The printed report: every moved row, then the totals.
pub fn format_diff(d: &Diff) -> String {
    let mut o = String::new();
    for (unit, old, new) in &d.oracle_changed {
        o.push_str(&format!("[rescore] {unit}: oracle {old} -> {new} (compile-fail oracle)\n"));
    }
    for (unit, old, new, note) in &d.changed {
        o.push_str(&format!("[rescore] {unit}: {old} -> {new}"));
        if !note.is_empty() {
            o.push_str(&format!("  ({note})"));
        }
        o.push('\n');
    }
    o.push_str("[rescore] totals (old -> new):\n");
    let classes: std::collections::BTreeSet<&String> =
        d.old_counts.keys().chain(d.new_counts.keys()).collect();
    for c in classes {
        let old = d.old_counts.get(c).copied().unwrap_or(0);
        let new = d.new_counts.get(c).copied().unwrap_or(0);
        o.push_str(&format!("  {c:<18} {old:>5} -> {new:<5}{}\n", if old != new { "  *" } else { "" }));
    }
    let versions: Vec<String> = d.old_versions.iter().map(|(v, n)| format!("{v}={n}")).collect();
    o.push_str(&format!(
        "[rescore] {} row(s): {} changed, {} unchanged; scorer_version {{{}}} -> {}\n",
        d.rows,
        d.changed.len(),
        d.rows - d.changed.len(),
        versions.join(","),
        SCORER_VERSION
    ));
    o
}

/// `<dir>/<stem>-rescored.jsonl` beside `report`.
pub fn output_path(report: &Path) -> PathBuf {
    let stem = report.file_stem().and_then(|s| s.to_str()).unwrap_or("results");
    report.with_file_name(format!("{stem}-rescored.jsonl"))
}

/// The `rescore <results.jsonl> [--out <path>]` command. `out` defaults to
/// [`output_path`]; the input is never overwritten.
pub fn cmd_rescore(report: &Path, out: Option<&Path>) -> Result<()> {
    let rows = crate::read_jsonl(&report.to_path_buf())?;
    if rows.is_empty() {
        bail!("{} has no rows", report.display());
    }
    let sidecar = crate::read_sidecar(report);
    let log_root = sidecar
        .as_ref()
        .and_then(|p| p.log_root.clone())
        .map(PathBuf::from)
        .or_else(|| {
            crate::env::repo_root_lax().ok().map(|r| r.join("target/kani-domination/reports"))
        })
        .context("cannot locate the unit logs: the sidecar names no `log_root` and no trust-mc repo root was found")?;
    // A rescored file is scored like any other: one route, and a Trustc file
    // only against the attestation its sidecar carries.
    match &sidecar {
        Some(p) => {
            crate::score::report_route(&rows, p).with_context(|| format!("rescoring {}", report.display()))?
        }
        None if rows.iter().any(|r| route_or_legacy(r.route.as_deref()) != LEGACY_ROUTE) => bail!(
            "{} has rows on a non-default route but no provenance sidecar to carry its route attestation",
            report.display()
        ),
        None => String::new(),
    };
    let route_attestation = sidecar.as_ref().and_then(|p| p.route_attestation.clone());
    // The spec is filed under the corpus rev the run read. Absent: the path
    // rule alone tags (and says so); present but unreadable: refused.
    let spec = match sidecar.as_ref().map(|p| p.kani_rev.as_str()).filter(|r| !r.starts_with('<')) {
        Some(rev) => crate::spec::load_for_rev(rev)?,
        None => {
            eprintln!("[rescore] no corpus rev in the sidecar: upstream-ignored units are tagged by compiletest's path rule alone");
            None
        }
    };
    let (new_rows, diff) = rescore_rows(&rows, &log_root, route_attestation.as_ref(), spec.as_ref())?;

    let out = out.map(Path::to_path_buf).unwrap_or_else(|| output_path(report));
    if out == report {
        bail!("refusing to rescore {} onto itself: --out must name another file", report.display());
    }
    if let Some(parent) = out.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    {
        let mut f = std::fs::File::create(&out).with_context(|| format!("creating {}", out.display()))?;
        for r in &new_rows {
            writeln!(f, "{}", serde_json::to_string(r)?)?;
        }
    }
    match sidecar {
        Some(mut p) => {
            p.scorer_version = SCORER_VERSION;
            p.rescored_from = Some(report.display().to_string());
            p.log_root = Some(log_root.display().to_string());
            std::fs::write(crate::provenance_sidecar(&out), serde_json::to_string_pretty(&p)?)?;
        }
        None => eprintln!(
            "[rescore] WARNING: {} has no provenance sidecar; {} gets none either",
            report.display(),
            out.display()
        ),
    }
    print!("{}", format_diff(&diff));
    eprintln!("[rescore] wrote {}", out.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Engine, Verdict};
    use crate::unitlog::UnitLog;

    fn log(suite: &str, file: &str, oracle: Verdict, stdout: &str, expected: Option<&str>) -> UnitLog {
        UnitLog {
            scorer_version: 1,
            engine: Engine::TrustMc,
            route: None,
            suite: suite.into(),
            file: file.into(),
            oracle,
            is_cargo: false,
            check_fail: false,
            upstream_ignored: false,
            argv: vec!["driver".into()],
            cwd: None,
            env_set: vec![],
            env_removed: vec![],
            spawn_error: None,
            exit_code: Some(1),
            timed_out: false,
            retried_after_outer_timeout: false,
            wall_ms: 7,
            max_rss_kb: 8,
            tree_peak_rss_kb: None,
            expected_path: None,
            expected: expected.map(str::to_string),
            stdout: stdout.into(),
            stderr: String::new(),
            first_attempt: None,
        }
    }

    /// A row scored from its log lands on the classification the live run
    /// would produce, keeps its measurements, and the diff names what moved.
    /// A row whose recorded class was wrong under the old rules is corrected
    /// and reported; a row without a log refuses the whole file.
    #[test]
    fn rescore_reclassifies_from_the_saved_log() {
        let root = std::env::temp_dir().join(format!("kd-rescore-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        // Row 1: a genuine counterexample against a fail oracle — parity.
        let l1 = log("kani", "a/b.rs", Verdict::Fail, "[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n", None);
        // Row 2: recorded as parity by an older scorer, but its log shows a
        // demoted proof (no counterexample): unknown under the current rules.
        let l2 = log("kani", "c.rs", Verdict::Fail, "[AY:DEMOTION_REASONS:chc_fallback]\nVERIFICATION:- FAILED\n", None);
        for (l, rel) in [(&l1, "logs/r/kani/a__b.rs.log"), (&l2, "logs/r/kani/c.rs.log")] {
            unitlog::write(&root.join(rel), l).unwrap();
        }
        let mut r1 = TestResult::blank("kani", "a/b.rs", Verdict::Fail);
        r1.classification = Some(Classification::Parity);
        r1.log_path = Some("logs/r/kani/a__b.rs.log".into());
        r1.wall_ms = 7;
        r1.scorer_version = 1;
        let mut r2 = TestResult::blank("kani", "c.rs", Verdict::Fail);
        r2.classification = Some(Classification::Parity);
        r2.log_path = Some("logs/r/kani/c.rs.log".into());
        r2.scorer_version = 1;

        let (rows, diff) = rescore_rows(&[r1.clone(), r2.clone()], &root, None, None).unwrap();
        assert_eq!(rows[0].classification, Some(Classification::Parity));
        assert_eq!(rows[0].wall_ms, 7, "measurements are carried over");
        assert_eq!(rows[0].scorer_version, SCORER_VERSION);
        assert_eq!(rows[0].observed, Some(Verdict::Fail));
        assert_eq!(rows[1].classification, Some(Classification::Unknown));
        assert_eq!(diff.changed.len(), 1);
        assert_eq!((diff.changed[0].0.as_str(), diff.changed[0].1.as_str(), diff.changed[0].2.as_str()), ("kani/c.rs", "parity", "unknown"));
        assert_eq!(diff.old_versions.get(&1), Some(&2));
        let text = format_diff(&diff);
        assert!(text.contains("kani/c.rs: parity -> unknown"), "{text}");
        assert!(text.contains("2 row(s): 1 changed, 1 unchanged"), "{text}");

        // Idempotent: rescoring the rescored rows changes nothing.
        let (_, again) = rescore_rows(&rows, &root, None, None).unwrap();
        assert!(again.changed.is_empty());

        // A row without a log refuses the file.
        let mut bare = r1.clone();
        bare.log_path = None;
        let err = rescore_rows(&[bare], &root, None, None).unwrap_err().to_string();
        assert!(err.contains("no `log_path`"), "{err}");
        // A log whose identity disagrees with its row refuses too.
        let mut swapped = r1.clone();
        swapped.log_path = Some("logs/r/kani/c.rs.log".into());
        assert!(rescore_rows(&[swapped], &root, None, None).is_err());
        let _ = std::fs::remove_dir_all(&root);
    }

    /// Rescoring tags a unit upstream-ignored from its log's own flag, from
    /// compiletest's path rule on a log written before the flag existed, or
    /// from the spec's `fixme` class — and its classification never moves
    /// because of it.
    #[test]
    fn rescore_tags_upstream_ignored_from_the_log_the_path_rule_or_the_spec() {
        let root = std::env::temp_dir().join(format!("kd-rescore-ign-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let out = "[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n";
        let mut rows = Vec::new();
        for (file, flag) in [("Tag/fixme_a.rs", false), ("Tag/plain.rs", false), ("Tag/spec_only.rs", false), ("Tag/logged.rs", true)] {
            let mut l = log("kani", file, Verdict::Fail, out, None);
            l.upstream_ignored = flag;
            let rel = format!("logs/r/kani/{}", unitlog::log_file_name(file));
            let mut bytes = String::from_utf8(unitlog::render(&l)).unwrap();
            if file == "Tag/fixme_a.rs" {
                // A log written before the header existed.
                bytes = bytes.replace("upstream_ignored: false\n", "");
            }
            std::fs::create_dir_all(root.join(&rel).parent().unwrap()).unwrap();
            std::fs::write(root.join(&rel), bytes).unwrap();
            let mut r = TestResult::blank("kani", file, Verdict::Fail);
            r.log_path = Some(rel);
            rows.push(r);
        }
        let spec = SpecIndex::parse(
            "{\"id\":\"kani/Tag/spec_only.rs\",\"suite\":\"kani\",\"classification\":\"fixme\",\"ignored\":null}\n",
            "r",
            PathBuf::from("/s/units.jsonl"),
        )
        .unwrap();
        let (new, _) = rescore_rows(&rows, &root, None, Some(&spec)).unwrap();
        let tags: Vec<(&str, bool)> = new.iter().map(|r| (r.file.as_str(), r.upstream_ignored)).collect();
        assert_eq!(tags, vec![("Tag/fixme_a.rs", true), ("Tag/plain.rs", false), ("Tag/spec_only.rs", true), ("Tag/logged.rs", true)]);
        assert!(new.iter().all(|r| r.classification == Some(Classification::Parity)));
        let (without_spec, _) = rescore_rows(&rows, &root, None, None).unwrap();
        assert!(!without_spec[2].upstream_ignored, "without the spec only the path rule and the log tag");
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A unit logged with a Success oracle whose expected file is a compile
    /// diagnostic is re-derived as a compile-fail oracle: parity when the log
    /// shows that compile failure, error when it shows a verification.
    #[test]
    fn rescore_rederives_a_compile_fail_oracle() {
        let root = std::env::temp_dir().join(format!("kd-rescore-cf-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let exp = "error: Nested calls to `old` are prohibited\n";
        let failed = "error: Nested calls to `old` are prohibited\nerror: aborting due to 1 previous error\n";
        let verified = "error: Nested calls to `old` are prohibited\n[AY:PROOF]\nVERIFICATION:- SUCCESSFUL\n";
        let mut rows = Vec::new();
        for (file, out, code) in [("a.rs", failed, Some(1)), ("b.rs", verified, Some(0))] {
            let mut l = log("expected", file, Verdict::Success, out, Some(exp));
            l.exit_code = code;
            let rel = format!("logs/r/expected/{file}.log");
            unitlog::write(&root.join(&rel), &l).unwrap();
            let mut r = TestResult::blank("expected", file, Verdict::Success);
            r.classification = Some(Classification::Parity);
            r.log_path = Some(rel);
            rows.push(r);
        }
        let (new, diff) = rescore_rows(&rows, &root, None, None).unwrap();
        assert_eq!(new[0].oracle, Verdict::Fail);
        assert_eq!(new[0].classification, Some(Classification::Parity));
        assert_eq!(new[1].classification, Some(Classification::Error));
        assert_eq!(diff.oracle_changed.len(), 2);
        assert!(format_diff(&diff).contains("expected/b.rs: oracle success -> fail"));
        // The rescored rows carry the re-derived oracle, their logs the old
        // one: rescoring them again is accepted and moves nothing.
        let (again, again_diff) = rescore_rows(&new, &root, None, None).unwrap();
        assert!(again_diff.changed.is_empty() && again_diff.oracle_changed.is_empty());
        assert_eq!(again[1].classification, Some(Classification::Error));
        // An oracle that is neither the logged nor the re-derived one is not this log's row.
        let mut stranger = new[0].clone();
        stranger.oracle = Verdict::Unknown;
        let err = rescore_rows(&[stranger], &root, None, None).unwrap_err().to_string();
        assert!(err.contains("not this row"), "{err}");
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn output_path_is_a_sibling_with_the_rescored_suffix() {
        assert_eq!(
            output_path(Path::new("/r/results-verification.jsonl")),
            PathBuf::from("/r/results-verification-rescored.jsonl")
        );
    }
}

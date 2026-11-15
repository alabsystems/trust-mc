// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `flips`: the noise floor of a measurement (plan G9). Given N results files
//! produced under one measurement tuple (same verifier binaries, solver,
//! backend, timeout, route, corpus rev, jobs and scorer), report the **flip
//! set** — the units whose classification differs between runs — so a claimed
//! delta between two configurations can be compared with the run-to-run
//! variation of one configuration. Fail-closed: files that do not name the same
//! tuple are refused (`--allow-tuple-mismatch` reports them anyway, marked).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Result, bail};
use serde::Serialize;

use crate::model::{Provenance, TestResult};

/// One unit whose classification is not the same in every run.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct FlipRow {
    pub unit: String,
    /// The classification in each run, in input order.
    pub classes: Vec<String>,
    pub upstream_ignored: bool,
}

/// What `flips` found.
#[derive(Debug, Clone, Serialize)]
pub struct Flips {
    pub runs: Vec<String>,
    /// Why the files are not one tuple (empty when they are).
    pub tuple_mismatches: Vec<String>,
    /// Units present in every run.
    pub joined: usize,
    /// Units missing from at least one run, with the runs (1-based) that have them.
    pub only_in_some: Vec<(String, Vec<usize>)>,
    pub flipped: Vec<FlipRow>,
    /// Per run: verification parity and its denominator (`score::summarize`).
    pub parity: Vec<(u64, u64)>,
    /// Class -> count in each run, over the joined units.
    pub per_class: BTreeMap<String, Vec<u64>>,
}

impl Flips {
    /// Flipped units over joined units, as a percentage.
    pub fn noise_floor_pct(&self) -> f64 {
        if self.joined == 0 { 0.0 } else { 100.0 * self.flipped.len() as f64 / self.joined as f64 }
    }
    /// Largest minus smallest parity count across runs.
    pub fn parity_spread(&self) -> u64 {
        let max = self.parity.iter().map(|p| p.0).max().unwrap_or(0);
        let min = self.parity.iter().map(|p| p.0).min().unwrap_or(0);
        max - min
    }
}

fn class_of(r: &TestResult) -> String {
    r.classification.map(|c| c.as_str().to_string()).unwrap_or_else(|| "?".into())
}

/// Why `provs` (one per run, `None` = no sidecar) are not one measurement
/// tuple: every difference from the first run, per run.
pub fn tuple_mismatches(runs: &[String], provs: &[Option<Provenance>], rows: &[Vec<TestResult>]) -> Vec<String> {
    let mut out = Vec::new();
    for (i, (name, p)) in runs.iter().zip(provs).enumerate() {
        if p.is_none() {
            out.push(format!("run {} ({name}): no provenance sidecar, so its tuple is unknown", i + 1));
        }
        let versions: BTreeSet<u32> = rows[i].iter().map(|r| r.scorer_version).collect();
        if versions.len() > 1 {
            out.push(format!("run {} ({name}): rows mix scorer versions {versions:?}", i + 1));
        }
    }
    let Some(first) = provs.first().and_then(Option::as_ref) else { return out };
    let first_versions: BTreeSet<u32> = rows[0].iter().map(|r| r.scorer_version).collect();
    for (i, p) in provs.iter().enumerate().skip(1) {
        let Some(p) = p else { continue };
        let mut diff = crate::model::resume_mismatch(first, p);
        let mut check = |name: &str, a: String, b: String| {
            if a != b {
                diff.push(format!("{name}: {a} -> {b}"));
            }
        };
        check("kani_rev", first.kani_rev.clone(), p.kani_rev.clone());
        check("jobs", first.jobs.to_string(), p.jobs.to_string());
        check("scopes", first.scopes.join(","), p.scopes.join(","));
        let versions: BTreeSet<u32> = rows[i].iter().map(|r| r.scorer_version).collect();
        check("row scorer_version", format!("{first_versions:?}"), format!("{versions:?}"));
        for d in diff {
            out.push(format!("run {} vs run 1: {d}", i + 1));
        }
    }
    out
}

/// The flip set of `runs` (`(name, rows)` in input order).
pub fn flips(runs: &[(String, Vec<TestResult>)], tuple_mismatches: Vec<String>) -> Flips {
    let maps: Vec<BTreeMap<String, &TestResult>> = runs
        .iter()
        .map(|(_, rows)| rows.iter().map(|r| (format!("{}/{}", r.suite, r.file), r)).collect())
        .collect();
    let all: BTreeSet<&String> = maps.iter().flat_map(|m| m.keys()).collect();
    let mut joined = 0usize;
    let mut only_in_some = Vec::new();
    let mut flipped = Vec::new();
    let mut per_class: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for unit in all {
        let present: Vec<usize> = maps.iter().enumerate().filter(|(_, m)| m.contains_key(unit)).map(|(i, _)| i + 1).collect();
        if present.len() != maps.len() {
            only_in_some.push((unit.clone(), present));
            continue;
        }
        joined += 1;
        let rows: Vec<&TestResult> = maps.iter().map(|m| m[unit]).collect();
        let classes: Vec<String> = rows.iter().map(|r| class_of(r)).collect();
        for (i, c) in classes.iter().enumerate() {
            per_class.entry(c.clone()).or_insert_with(|| vec![0; maps.len()])[i] += 1;
        }
        if classes.iter().any(|c| *c != classes[0]) {
            flipped.push(FlipRow {
                unit: unit.clone(),
                classes,
                upstream_ignored: rows.iter().any(|r| r.upstream_ignored),
            });
        }
    }
    let parity = runs
        .iter()
        .map(|(_, rows)| {
            let s = crate::score::summarize(rows);
            (s.verification.parity, s.verification.denominator())
        })
        .collect();
    Flips {
        runs: runs.iter().map(|(n, _)| n.clone()).collect(),
        tuple_mismatches,
        joined,
        only_in_some,
        flipped,
        parity,
        per_class,
    }
}

pub fn format_text(f: &Flips) -> String {
    let mut o = format!("flips across {} run(s)\n", f.runs.len());
    for (i, (run, (p, d))) in f.runs.iter().zip(&f.parity).enumerate() {
        o.push_str(&format!("  run {}: {run}  (verification parity {p}/{d})\n", i + 1));
    }
    if f.tuple_mismatches.is_empty() {
        o.push_str("  tuple: identical (verifier, solver, backend, timeout, surface, route, corpus rev, jobs, scopes, scorer)\n");
    } else {
        o.push_str("  tuple: NOT IDENTICAL — these runs do not measure one configuration's noise:\n");
        for m in &f.tuple_mismatches {
            o.push_str(&format!("    {m}\n"));
        }
    }
    o.push_str(&format!(
        "  units in every run: {} · in only some: {}\n  flip set: {} unit(s) = {:.2}% of joined units (the noise floor)\n  parity spread across runs: {} (min {} max {})\n",
        f.joined,
        f.only_in_some.len(),
        f.flipped.len(),
        f.noise_floor_pct(),
        f.parity_spread(),
        f.parity.iter().map(|p| p.0).min().unwrap_or(0),
        f.parity.iter().map(|p| p.0).max().unwrap_or(0),
    ));
    o.push_str("  per class (count in each run):\n");
    for (class, counts) in &f.per_class {
        let spread = counts.iter().max().unwrap_or(&0) - counts.iter().min().unwrap_or(&0);
        let list: Vec<String> = counts.iter().map(u64::to_string).collect();
        o.push_str(&format!("    {class:<18} {}{}\n", list.join(" / "), if spread > 0 { format!("  (spread {spread})") } else { String::new() }));
    }
    if !f.flipped.is_empty() {
        o.push_str("  ---- flipped units ----\n");
        for row in &f.flipped {
            o.push_str(&format!(
                "  {}  {}{}\n",
                row.unit,
                row.classes.join(" | "),
                if row.upstream_ignored { "  [upstream-ignored]" } else { "" }
            ));
        }
    }
    if !f.only_in_some.is_empty() {
        o.push_str("  ---- units missing from some run(s) ----\n");
        for (unit, present) in &f.only_in_some {
            o.push_str(&format!("  {unit}  (in run(s) {present:?})\n"));
        }
    }
    o
}

/// The `flips <results.jsonl>...` command.
pub fn cmd_flips(reports: &[PathBuf], format: &str, allow_tuple_mismatch: bool) -> Result<()> {
    if reports.len() < 2 {
        bail!("flips needs at least two results files of one measurement tuple");
    }
    let unique: BTreeSet<&Path> = reports.iter().map(PathBuf::as_path).collect();
    if unique.len() != reports.len() {
        bail!("flips was given the same results file more than once");
    }
    let mut runs = Vec::new();
    let mut provs = Vec::new();
    for path in reports {
        let rows = crate::read_jsonl(path)?;
        if rows.is_empty() {
            bail!("{} has no rows", path.display());
        }
        provs.push(crate::read_sidecar(path));
        runs.push((path.display().to_string(), rows));
    }
    let names: Vec<String> = runs.iter().map(|(n, _)| n.clone()).collect();
    let rows: Vec<Vec<TestResult>> = runs.iter().map(|(_, r)| r.clone()).collect();
    let mismatches = tuple_mismatches(&names, &provs, &rows);
    if !mismatches.is_empty() && !allow_tuple_mismatch {
        bail!(
            "refusing to report a noise floor across runs of different measurement tuples:\n  {}\n\
             Pass --allow-tuple-mismatch to report the flips anyway (marked NOT IDENTICAL).",
            mismatches.join("\n  ")
        );
    }
    let f = flips(&runs, mismatches);
    match format {
        "json" => println!("{}", serde_json::to_string_pretty(&f)?),
        _ => print!("{}", format_text(&f)),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Classification as C, Verdict};

    fn row(file: &str, class: C) -> TestResult {
        TestResult { classification: Some(class), ..TestResult::blank("kani", file, Verdict::Success) }
    }

    fn prov(driver_sha: &str, jobs: usize) -> Provenance {
        serde_json::from_value(serde_json::json!({
            "generated_unix": 1, "generated_iso": "x", "trust_mc_head": "h", "trust_mc_dirty": false,
            "ay_pin": "p", "ay_binary_version": "ay", "ay_rev_matches_pin": true,
            "kani_rev": "k", "kani_repo": "r", "backend": "chc", "harness_timeout_s": 15, "jobs": jobs,
            "scopes": ["verification"], "scorer_version": crate::model::SCORER_VERSION,
            "attestation": {
                "driver_path": "/d", "driver_sha256": driver_sha, "driver_version": "v", "sysroot": "/s",
                "ay_binary_path": "/ay", "ay_binary_source": "AY_BIN", "trust_toolchain": "trust",
                "trust_toolchain_commit": "t", "ay_tree": "/t", "ay_tree_head": "a", "ay_tree_dirty": false,
                "kani_dir": "/k", "load_average_start": null
            }
        }))
        .unwrap()
    }

    /// A unit that changes class in any run is in the flip set with its class
    /// per run; a unit missing from a run is listed apart and never joined;
    /// per-class counts and the parity spread cover the joined units.
    #[test]
    fn flip_set_names_every_unit_whose_class_differs() {
        let r1 = vec![row("a.rs", C::Parity), row("b.rs", C::Parity), row("c.rs", C::Unknown), row("d.rs", C::Error)];
        let r2 = vec![row("a.rs", C::Parity), row("b.rs", C::Unknown), row("c.rs", C::Unknown)];
        let mut ign = row("b.rs", C::Parity);
        ign.upstream_ignored = true;
        let r3 = vec![row("a.rs", C::Parity), ign, row("c.rs", C::Timeout), row("d.rs", C::Error)];
        let f = flips(&[("r1".into(), r1), ("r2".into(), r2), ("r3".into(), r3)], Vec::new());
        assert_eq!(f.joined, 3);
        assert_eq!(f.only_in_some, vec![("kani/d.rs".to_string(), vec![1, 3])]);
        assert_eq!(
            f.flipped,
            vec![
                FlipRow { unit: "kani/b.rs".into(), classes: vec!["parity".into(), "unknown".into(), "parity".into()], upstream_ignored: true },
                FlipRow { unit: "kani/c.rs".into(), classes: vec!["unknown".into(), "unknown".into(), "timeout".into()], upstream_ignored: false },
            ]
        );
        assert_eq!(f.per_class["parity"], vec![2, 1, 2]);
        assert!((f.noise_floor_pct() - 200.0 / 3.0).abs() < 1e-9);
        let text = format_text(&f);
        assert!(text.contains("flip set: 2 unit(s) = 66.67%"), "{text}");
        assert!(text.contains("kani/b.rs  parity | unknown | parity  [upstream-ignored]"), "{text}");
        assert!(text.contains("kani/d.rs  (in run(s) [1, 3])"), "{text}");
        assert!(text.contains("tuple: identical"));
        // Per-run parity comes from the burndown's own summary (r3's b.rs is fixme).
        assert_eq!(f.parity, vec![(2, 4), (1, 3), (1, 3)]);
        assert_eq!(f.parity_spread(), 1);
    }

    /// Runs of different tuples are named, difference by difference: another
    /// driver, another jobs count, a missing sidecar, mixed scorer versions.
    #[test]
    fn tuple_mismatches_name_every_difference() {
        let names = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let rows = vec![vec![row("a.rs", C::Parity)], vec![row("a.rs", C::Parity)], vec![row("a.rs", C::Parity)]];
        assert!(tuple_mismatches(&names, &[Some(prov("aa", 6)), Some(prov("aa", 6)), Some(prov("aa", 6))], &rows).is_empty());
        let m = tuple_mismatches(&names, &[Some(prov("aa", 6)), Some(prov("bb", 6)), Some(prov("aa", 3))], &rows);
        assert!(m.iter().any(|d| d.starts_with("run 2 vs run 1: driver_sha256")), "{m:?}");
        assert!(m.iter().any(|d| d.starts_with("run 3 vs run 1: jobs: 6 -> 3")), "{m:?}");
        let m = tuple_mismatches(&names, &[Some(prov("aa", 6)), None, Some(prov("aa", 6))], &rows);
        assert_eq!(m, vec!["run 2 (b): no provenance sidecar, so its tuple is unknown".to_string()]);
        let mut mixed = rows.clone();
        mixed[2].push(TestResult { scorer_version: 1, ..row("z.rs", C::Parity) });
        let m = tuple_mismatches(&names, &[Some(prov("aa", 6)), Some(prov("aa", 6)), Some(prov("aa", 6))], &mixed);
        assert!(m.iter().any(|d| d.contains("rows mix scorer versions")), "{m:?}");
    }
}

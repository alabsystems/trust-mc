// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `compare`: join a trust-mc results file with a Kani results file on the
//! same corpus units and report verdict agreement plus wall-time and
//! peak-memory ratios — the owner's criterion ("100% of Kani's tests through
//! AY with as good or better runtime and memory") measured on identical units
//! under identical oracles.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::model::{Classification, TestResult, Verdict};

/// A unit key: `<suite>/<file>` (the file is the expected-file path for a
/// cargo unit, so it already encodes the harness).
fn key(r: &TestResult) -> String {
    format!("{}/{}", r.suite, r.file)
}

fn class_str(c: Option<Classification>) -> &'static str {
    c.map(Classification::as_str).unwrap_or("?")
}

/// Peak memory for a row: the sampled tree peak when present, else the exact
/// direct-child `ru_maxrss`. 0 means no data (a row written before the
/// resource fields existed).
pub fn memory_kb(r: &TestResult) -> u64 {
    r.tree_peak_rss_kb.unwrap_or(r.max_rss_kb)
}

/// Wall time for a row: `wall_ms`, else — for a row written by a tool
/// before the field existed — its `duration_ms`, which is the whole unit
/// and includes a killed first attempt when the outer watchdog retried. 0
/// means no data.
pub fn wall_ms(r: &TestResult) -> u64 {
    if r.wall_ms > 0 { r.wall_ms } else { r.duration_ms }
}

/// The row's wall time comes from the `duration_ms` fallback.
fn wall_from_duration(r: &TestResult) -> bool {
    r.wall_ms == 0 && r.duration_ms > 0
}

fn oracle_str(v: Verdict) -> &'static str {
    match v {
        Verdict::Success => "success",
        Verdict::Fail => "fail",
        Verdict::Unknown => "unknown",
    }
}

/// One cell of the verdict agreement matrix.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct MatrixCell {
    /// `success` / `fail` (the oracle's serde spelling).
    pub oracle: String,
    pub trust_mc: String,
    pub kani: String,
    pub count: u64,
}

/// One unit that one engine solved (parity) and the other did not.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct Delta {
    pub unit: String,
    pub oracle: Verdict,
    pub trust_mc: String,
    pub kani: String,
    /// The non-solving engine's note.
    pub note: String,
}

/// One unit on a resource axis.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct AxisRow {
    pub unit: String,
    pub trust_mc: u64,
    pub kani: u64,
    /// trust-mc / kani: above 1 means trust-mc used more.
    pub ratio: f64,
}

/// Ratio statistics for one axis over the units both engines solved.
#[derive(Debug, Clone, Serialize, PartialEq, Default)]
pub struct AxisStats {
    /// Units with data on both sides.
    pub n: u64,
    /// Both-parity units with no data on at least one side (old rows, or a
    /// zero measurement); excluded from every number below.
    pub no_data: u64,
    /// trust-mc used strictly less / more / the same.
    pub trust_mc_lower: u64,
    pub trust_mc_higher: u64,
    pub equal: u64,
    pub median_ratio: f64,
    pub p90_ratio: f64,
    pub geomean_ratio: f64,
    pub total_trust_mc: u64,
    pub total_kani: u64,
    /// total_trust_mc / total_kani.
    pub total_ratio: f64,
    /// The units with the highest ratio (trust-mc worst relative to Kani).
    pub worst: Vec<AxisRow>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Comparison {
    pub units_trust_mc: u64,
    pub units_kani: u64,
    pub units_both: u64,
    pub only_trust_mc: Vec<String>,
    pub only_kani: Vec<String>,
    /// Over the joined units.
    pub same_classification: u64,
    pub both_parity: u64,
    pub trust_mc_parity_only: u64,
    pub kani_parity_only: u64,
    pub neither_parity: u64,
    /// (oracle, trust-mc class, kani class) -> count, largest first.
    pub matrix: Vec<MatrixCell>,
    pub kani_solves_trust_mc_does_not: Vec<Delta>,
    pub trust_mc_solves_kani_does_not: Vec<Delta>,
    /// Wall time (`wall_ms`, else `duration_ms`) over both-parity units.
    pub wall_ms: AxisStats,
    /// Peak memory (`tree_peak_rss_kb`, else `max_rss_kb`) over both-parity units.
    pub peak_rss_kb: AxisStats,
    /// Both-parity units whose wall time on that side came from
    /// `duration_ms` because the row has no `wall_ms` (an older tool).
    pub trust_mc_wall_from_duration: u64,
    pub kani_wall_from_duration: u64,
    /// Both-parity units with no memory data on that side.
    pub trust_mc_memory_missing: u64,
    pub kani_memory_missing: u64,
}

/// Join `trust_mc` with `kani` on unit key and compute the comparison. `worst`
/// bounds the per-axis worst lists.
pub fn compare(trust_mc: &[TestResult], kani: &[TestResult], worst: usize) -> Comparison {
    let tm: BTreeMap<String, &TestResult> = trust_mc.iter().map(|r| (key(r), r)).collect();
    let kn: BTreeMap<String, &TestResult> = kani.iter().map(|r| (key(r), r)).collect();
    let only_trust_mc: Vec<String> = tm.keys().filter(|k| !kn.contains_key(*k)).cloned().collect();
    let only_kani: Vec<String> = kn.keys().filter(|k| !tm.contains_key(*k)).cloned().collect();

    // Keyed on the oracle's name (`Verdict` is not `Ord`); `fail` sorts before
    // `success`, which the final count-descending sort overrides anyway.
    let mut matrix: BTreeMap<(String, String, String), u64> = BTreeMap::new();
    let mut same_classification = 0;
    let (mut both_parity, mut tm_only, mut kn_only, mut neither) = (0, 0, 0, 0);
    let mut kani_solves = Vec::new();
    let mut tm_solves = Vec::new();
    let mut wall_rows = Vec::new();
    let mut mem_rows = Vec::new();
    let (mut wall_no_data, mut mem_no_data) = (0, 0);
    let (mut wall_fallback, mut mem_missing) = ([0u64; 2], [0u64; 2]);

    for (k, a) in &tm {
        let Some(b) = kn.get(k) else { continue };
        let (ca, cb) = (a.classification, b.classification);
        *matrix
            .entry((oracle_str(a.oracle).into(), class_str(ca).into(), class_str(cb).into()))
            .or_default() += 1;
        if ca == cb {
            same_classification += 1;
        }
        let pa = ca.is_some_and(Classification::is_parity);
        let pb = cb.is_some_and(Classification::is_parity);
        match (pa, pb) {
            (true, true) => {
                both_parity += 1;
                for (i, r) in [a, *b].into_iter().enumerate() {
                    wall_fallback[i] += u64::from(wall_from_duration(r));
                    mem_missing[i] += u64::from(memory_kb(r) == 0);
                }
                match axis_row(k, wall_ms(a), wall_ms(b)) {
                    Some(row) => wall_rows.push(row),
                    None => wall_no_data += 1,
                }
                match axis_row(k, memory_kb(a), memory_kb(b)) {
                    Some(row) => mem_rows.push(row),
                    None => mem_no_data += 1,
                }
            }
            (true, false) => {
                tm_only += 1;
                tm_solves.push(delta(k, a, b, &b.note));
            }
            (false, true) => {
                kn_only += 1;
                kani_solves.push(delta(k, a, b, &a.note));
            }
            (false, false) => neither += 1,
        }
    }

    let mut matrix: Vec<MatrixCell> = matrix
        .into_iter()
        .map(|((oracle, trust_mc, kani), count)| MatrixCell { oracle, trust_mc, kani, count })
        .collect();
    matrix.sort_by(|x, y| {
        y.count
            .cmp(&x.count)
            .then_with(|| (&x.oracle, &x.trust_mc, &x.kani).cmp(&(&y.oracle, &y.trust_mc, &y.kani)))
    });

    Comparison {
        units_trust_mc: tm.len() as u64,
        units_kani: kn.len() as u64,
        units_both: tm.keys().filter(|k| kn.contains_key(*k)).count() as u64,
        only_trust_mc,
        only_kani,
        same_classification,
        both_parity,
        trust_mc_parity_only: tm_only,
        kani_parity_only: kn_only,
        neither_parity: neither,
        matrix,
        kani_solves_trust_mc_does_not: kani_solves,
        trust_mc_solves_kani_does_not: tm_solves,
        wall_ms: axis_stats(wall_rows, wall_no_data, worst),
        peak_rss_kb: axis_stats(mem_rows, mem_no_data, worst),
        trust_mc_wall_from_duration: wall_fallback[0],
        kani_wall_from_duration: wall_fallback[1],
        trust_mc_memory_missing: mem_missing[0],
        kani_memory_missing: mem_missing[1],
    }
}

fn delta(k: &str, a: &TestResult, b: &TestResult, note: &str) -> Delta {
    Delta {
        unit: k.to_string(),
        oracle: a.oracle,
        trust_mc: class_str(a.classification).to_string(),
        kani: class_str(b.classification).to_string(),
        note: note.to_string(),
    }
}

/// A row on one axis, or `None` when either side has no data (0).
fn axis_row(unit: &str, trust_mc: u64, kani: u64) -> Option<AxisRow> {
    if trust_mc == 0 || kani == 0 {
        return None;
    }
    Some(AxisRow { unit: unit.to_string(), trust_mc, kani, ratio: trust_mc as f64 / kani as f64 })
}

fn axis_stats(mut rows: Vec<AxisRow>, no_data: u64, worst: usize) -> AxisStats {
    let n = rows.len() as u64;
    if n == 0 {
        return AxisStats { no_data, ..AxisStats::default() };
    }
    let mut ratios: Vec<f64> = rows.iter().map(|r| r.ratio).collect();
    ratios.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let total_trust_mc: u64 = rows.iter().map(|r| r.trust_mc).sum();
    let total_kani: u64 = rows.iter().map(|r| r.kani).sum();
    // Highest ratio first; ties broken by the unit name so the list is stable.
    rows.sort_by(|a, b| {
        b.ratio.partial_cmp(&a.ratio).unwrap_or(std::cmp::Ordering::Equal).then_with(|| a.unit.cmp(&b.unit))
    });
    rows.truncate(worst);
    AxisStats {
        n,
        no_data,
        trust_mc_lower: ratios.iter().filter(|r| **r < 1.0).count() as u64,
        trust_mc_higher: ratios.iter().filter(|r| **r > 1.0).count() as u64,
        equal: ratios.iter().filter(|r| **r == 1.0).count() as u64,
        median_ratio: median(&ratios),
        p90_ratio: percentile(&ratios, 0.9),
        geomean_ratio: (ratios.iter().map(|r| r.ln()).sum::<f64>() / n as f64).exp(),
        total_trust_mc,
        total_kani,
        total_ratio: total_trust_mc as f64 / total_kani as f64,
        worst: rows,
    }
}

/// Median of a sorted, non-empty slice (mean of the two middle values when even).
fn median(sorted: &[f64]) -> f64 {
    let n = sorted.len();
    if n % 2 == 1 { sorted[n / 2] } else { (sorted[n / 2 - 1] + sorted[n / 2]) / 2.0 }
}

/// Nearest-rank percentile of a sorted, non-empty slice.
fn percentile(sorted: &[f64], p: f64) -> f64 {
    let n = sorted.len();
    let rank = ((p * n as f64).ceil() as usize).clamp(1, n);
    sorted[rank - 1]
}

pub fn format_text(c: &Comparison) -> String {
    let mut o = String::new();
    o.push_str(&format!(
        "Kani-domination compare: trust-mc vs Kani\n  units: trust-mc {} · kani {} · in both {} · only trust-mc {} · only kani {}\n",
        c.units_trust_mc, c.units_kani, c.units_both, c.only_trust_mc.len(), c.only_kani.len()
    ));
    o.push_str(&format!(
        "  agreement over joined units: same classification {} · both parity {} · trust-mc parity only {} · kani parity only {} · neither {}\n",
        c.same_classification, c.both_parity, c.trust_mc_parity_only, c.kani_parity_only, c.neither_parity
    ));
    o.push_str("  ---- verdict matrix (oracle, trust-mc class, kani class) ----\n");
    o.push_str(&format!("  {:<8} {:<18} {:<18} {:>6}\n", "oracle", "trust-mc", "kani", "units"));
    for cell in &c.matrix {
        o.push_str(&format!(
            "  {:<8} {:<18} {:<18} {:>6}\n",
            cell.oracle, cell.trust_mc, cell.kani, cell.count
        ));
    }
    let wall_note = if c.trust_mc_wall_from_duration + c.kani_wall_from_duration > 0 {
        format!(
            "  wall time taken from duration_ms on rows with no wall_ms (an older tool; includes a killed first attempt on a retried unit): trust-mc {} · kani {}\n",
            c.trust_mc_wall_from_duration, c.kani_wall_from_duration
        )
    } else {
        String::new()
    };
    let mem_note = if c.trust_mc_memory_missing + c.kani_memory_missing > 0 {
        format!(
            "  memory: no data on the trust-mc side for {} both-parity unit(s), on the kani side for {} (rows written before the resource fields existed)\n",
            c.trust_mc_memory_missing, c.kani_memory_missing
        )
    } else {
        String::new()
    };
    for (title, unit, axis, note) in [
        ("wall time (ms, both-parity units)", "ms", &c.wall_ms, &wall_note),
        ("peak memory (KB, tree peak else ru_maxrss, both-parity units)", "KB", &c.peak_rss_kb, &mem_note),
    ] {
        o.push_str(&format!("  ---- {title} ----\n"));
        o.push_str(note);
        if axis.n == 0 {
            o.push_str(&format!("  no units with data on both sides ({} without data)\n", axis.no_data));
            continue;
        }
        o.push_str(&format!(
            "  n={} (no-data {}) · trust-mc lower {} · higher {} · equal {}\n  ratio trust-mc/kani: median {:.3} · p90 {:.3} · geomean {:.3} · totals {} / {} {} = {:.3}\n",
            axis.n,
            axis.no_data,
            axis.trust_mc_lower,
            axis.trust_mc_higher,
            axis.equal,
            axis.median_ratio,
            axis.p90_ratio,
            axis.geomean_ratio,
            axis.total_trust_mc,
            axis.total_kani,
            unit,
            axis.total_ratio
        ));
        o.push_str(&format!("  worst {} by ratio:\n", axis.worst.len()));
        for row in &axis.worst {
            o.push_str(&format!(
                "    {:>9.3}x  {:>10} vs {:>10} {unit}  {}\n",
                row.ratio, row.trust_mc, row.kani, row.unit
            ));
        }
    }
    for (title, list) in [
        ("Kani solves, trust-mc does not", &c.kani_solves_trust_mc_does_not),
        ("trust-mc solves, Kani does not", &c.trust_mc_solves_kani_does_not),
    ] {
        o.push_str(&format!("  ---- {title} ({}) ----\n", list.len()));
        for d in list {
            o.push_str(&format!(
                "    {:<60} oracle={:<7} trust-mc={:<14} kani={:<14} {}\n",
                d.unit,
                format!("{:?}", d.oracle).to_lowercase(),
                d.trust_mc,
                d.kani,
                d.note
            ));
        }
    }
    if !c.only_trust_mc.is_empty() || !c.only_kani.is_empty() {
        o.push_str(&format!(
            "  ---- unjoined ----\n  only in trust-mc file: {}\n  only in kani file: {}\n",
            c.only_trust_mc.join(" "),
            c.only_kani.join(" ")
        ));
    }
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(suite: &str, file: &str, oracle: Verdict, class: Classification, wall: u64, rss: u64, tree: Option<u64>) -> TestResult {
        TestResult {
            classification: Some(class),
            duration_ms: wall,
            wall_ms: wall,
            max_rss_kb: rss,
            tree_peak_rss_kb: tree,
            exit_code: Some(0),
            note: format!("note-{file}"),
            ..TestResult::blank(suite, file, oracle)
        }
    }

    use Classification as C;
    use Verdict as V;

    /// The join is on (suite, file); the matrix, the parity split and the
    /// solved-by-one-engine lists come only from joined units.
    #[test]
    fn joins_on_unit_and_splits_parity() {
        let tm = vec![
            row("kani", "a.rs", V::Success, C::Parity, 100, 10, Some(50)),
            row("kani", "b.rs", V::Fail, C::Unknown, 100, 10, None),
            row("kani", "c.rs", V::Success, C::Parity, 100, 10, None),
            row("kani", "only-tm.rs", V::Success, C::Parity, 1, 1, None),
        ];
        let kn = vec![
            row("kani", "a.rs", V::Success, C::Parity, 200, 20, Some(25)),
            row("kani", "b.rs", V::Fail, C::Parity, 300, 20, None),
            row("kani", "c.rs", V::Success, C::Unsupported, 300, 20, None),
            row("kani", "only-kani.rs", V::Success, C::Parity, 1, 1, None),
        ];
        let c = compare(&tm, &kn, 25);
        assert_eq!((c.units_trust_mc, c.units_kani, c.units_both), (4, 4, 3));
        assert_eq!(c.only_trust_mc, vec!["kani/only-tm.rs"]);
        assert_eq!(c.only_kani, vec!["kani/only-kani.rs"]);
        assert_eq!((c.same_classification, c.both_parity), (1, 1));
        assert_eq!((c.trust_mc_parity_only, c.kani_parity_only, c.neither_parity), (1, 1, 0));
        assert_eq!(c.kani_solves_trust_mc_does_not.len(), 1);
        let d = &c.kani_solves_trust_mc_does_not[0];
        assert_eq!((d.unit.as_str(), d.trust_mc.as_str(), d.kani.as_str()), ("kani/b.rs", "unknown", "parity"));
        assert_eq!(d.note, "note-b.rs", "the non-solving engine's note is carried");
        assert_eq!(c.trust_mc_solves_kani_does_not[0].unit, "kani/c.rs");
        assert_eq!(c.trust_mc_solves_kani_does_not[0].note, "note-c.rs");
        // Matrix: three joined cells, one unit each, largest-first then by key.
        assert_eq!(c.matrix.len(), 3);
        assert!(c.matrix.iter().all(|m| m.count == 1));
        assert!(c.matrix.iter().any(|m| m.oracle == "fail" && m.trust_mc == "unknown" && m.kani == "parity"));
        // Ratios only over the both-parity unit: wall 100/200, memory 50/25
        // (tree peak wins over ru_maxrss on both sides).
        assert_eq!(c.wall_ms.n, 1);
        assert!((c.wall_ms.median_ratio - 0.5).abs() < 1e-12);
        assert_eq!((c.wall_ms.trust_mc_lower, c.wall_ms.trust_mc_higher), (1, 0));
        assert_eq!(c.peak_rss_kb.n, 1);
        assert!((c.peak_rss_kb.median_ratio - 2.0).abs() < 1e-12);
        assert_eq!((c.peak_rss_kb.trust_mc_lower, c.peak_rss_kb.trust_mc_higher), (0, 1));
        assert_eq!(c.peak_rss_kb.worst[0].trust_mc, 50);
        assert_eq!(c.peak_rss_kb.worst[0].kani, 25);
        let text = format_text(&c);
        assert!(text.contains("Kani solves, trust-mc does not (1)"), "{text}");
        assert!(text.contains("kani/b.rs"), "{text}");
        assert!(serde_json::to_value(&c).unwrap()["wall_ms"]["median_ratio"].is_number());
    }

    /// Median, p90, geometric mean, totals and the faster/slower split over a
    /// known ratio set, and the worst list is ratio-descending and bounded.
    #[test]
    fn axis_statistics_over_known_ratios() {
        // ratios: 0.5, 1.0, 2.0, 4.0, 8.0 (kani fixed at 100)
        let walls = [50u64, 100, 200, 400, 800];
        let tm: Vec<TestResult> = walls
            .iter()
            .enumerate()
            .map(|(i, w)| row("s", &format!("u{i}.rs"), V::Success, C::Parity, *w, 1, None))
            .collect();
        let kn: Vec<TestResult> = walls
            .iter()
            .enumerate()
            .map(|(i, _)| row("s", &format!("u{i}.rs"), V::Success, C::Parity, 100, 1, None))
            .collect();
        let c = compare(&tm, &kn, 2);
        let w = &c.wall_ms;
        assert_eq!(w.n, 5);
        assert!((w.median_ratio - 2.0).abs() < 1e-12);
        assert!((w.p90_ratio - 8.0).abs() < 1e-12, "nearest rank: ceil(0.9*5)=5 -> 8.0");
        // geomean of 0.5,1,2,4,8 = 2^((-1+0+1+2+3)/5) = 2^1 = 2
        assert!((w.geomean_ratio - 2.0).abs() < 1e-9);
        assert_eq!((w.total_trust_mc, w.total_kani), (1550, 500));
        assert!((w.total_ratio - 3.1).abs() < 1e-12);
        assert_eq!((w.trust_mc_lower, w.trust_mc_higher, w.equal), (1, 3, 1));
        assert_eq!(w.worst.len(), 2, "bounded by --worst");
        assert_eq!(w.worst[0].unit, "s/u4.rs");
        assert_eq!(w.worst[1].unit, "s/u3.rs");
        // Even count: median is the mean of the middle pair.
        assert!((median(&[1.0, 2.0, 3.0, 4.0]) - 2.5).abs() < 1e-12);
    }

    /// A trust-mc file from a tool before `wall_ms` and the memory fields
    /// existed (rows carry `duration_ms` only): wall time falls back to
    /// `duration_ms`, memory is no-data, and the text says which side lacks
    /// what.
    #[test]
    fn older_trust_mc_rows_use_duration_for_wall_and_report_memory_as_missing() {
        let mut old = row("s", "a.rs", V::Success, C::Parity, 0, 0, None);
        old.duration_ms = 400;
        let kn = vec![row("s", "a.rs", V::Success, C::Parity, 200, 5, Some(9))];
        let c = compare(&[old], &kn, 25);
        assert_eq!(c.both_parity, 1);
        assert_eq!((c.wall_ms.n, c.wall_ms.no_data), (1, 0));
        assert!((c.wall_ms.median_ratio - 2.0).abs() < 1e-12, "400 (duration_ms) / 200 (wall_ms)");
        assert_eq!((c.trust_mc_wall_from_duration, c.kani_wall_from_duration), (1, 0));
        assert_eq!((c.peak_rss_kb.n, c.peak_rss_kb.no_data), (0, 1));
        assert_eq!((c.trust_mc_memory_missing, c.kani_memory_missing), (1, 0));
        let text = format_text(&c);
        assert!(text.contains("wall time taken from duration_ms"), "{text}");
        assert!(text.contains("trust-mc 1 · kani 0"), "{text}");
        assert!(
            text.contains("no data on the trust-mc side for 1 both-parity unit(s), on the kani side for 0"),
            "{text}"
        );
        assert!(serde_json::to_value(&c).unwrap()["trust_mc_wall_from_duration"].as_u64() == Some(1));
        // A row with `wall_ms` never falls back, and one with neither field
        // is still no-data on the wall axis.
        let both = vec![row("s", "a.rs", V::Success, C::Parity, 100, 1, None)];
        let c = compare(&both, &kn, 25);
        assert_eq!((c.wall_ms.n, c.trust_mc_wall_from_duration), (1, 0));
        assert!((c.wall_ms.median_ratio - 0.5).abs() < 1e-12);
        let none = vec![row("s", "a.rs", V::Success, C::Parity, 0, 0, None)];
        let c = compare(&none, &kn, 25);
        assert_eq!((c.wall_ms.n, c.wall_ms.no_data, c.trust_mc_wall_from_duration), (0, 1, 0));
        assert!(!format_text(&c).contains("taken from duration_ms"));
    }

    /// A both-parity unit with no data on one side (an old row) is counted
    /// as no-data and never divides by zero.
    #[test]
    fn missing_resource_data_is_counted_not_divided() {
        let tm = vec![row("s", "a.rs", V::Success, C::Parity, 10, 0, None)];
        let kn = vec![row("s", "a.rs", V::Success, C::Parity, 0, 5, None)];
        let c = compare(&tm, &kn, 25);
        assert_eq!(c.both_parity, 1);
        assert_eq!((c.wall_ms.n, c.wall_ms.no_data), (0, 1));
        assert_eq!((c.peak_rss_kb.n, c.peak_rss_kb.no_data), (0, 1));
        assert!(format_text(&c).contains("no units with data on both sides (1 without data)"));
    }
}

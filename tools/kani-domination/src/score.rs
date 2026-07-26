// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Aggregate per-test results into the layered burndown (verification parity +
//! full-corpus coverage) and a committed trend ledger.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;

use crate::model::{Classification, Provenance, Scope, TestResult};
use crate::suites;

#[derive(Debug, Default, Clone, Copy)]
pub struct Roll {
    pub parity: u64,
    pub unsound_pass: u64,
    pub false_positive: u64,
    pub unsupported: u64,
    pub encoding_gap: u64,
    pub missed_bug: u64,
    pub exceeds_oracle: u64,
    pub unknown: u64,
    pub error: u64,
    pub crash: u64,
    pub build_unavailable: u64,
    /// Quarantined corpus sources (explicit evidence-quoted manifest,
    /// `quarantine::CORPUS_INVALID`): counted in `total` but excluded from
    /// the parity denominator — see [`Roll::denominator`].
    pub corpus_invalid: u64,
    pub timeout: u64,
    pub skipped: u64,
    pub total: u64,
}

impl Roll {
    fn add(&mut self, c: Classification) {
        self.total += 1;
        match c {
            Classification::Parity => self.parity += 1,
            Classification::UnsoundPass => self.unsound_pass += 1,
            Classification::FalsePositive => self.false_positive += 1,
            Classification::Unsupported => self.unsupported += 1,
            Classification::EncodingGap => self.encoding_gap += 1,
            Classification::MissedBug => self.missed_bug += 1,
            Classification::ExceedsOracle => self.exceeds_oracle += 1,
            Classification::Unknown => self.unknown += 1,
            Classification::Error => self.error += 1,
            Classification::Crash => self.crash += 1,
            Classification::BuildUnavailable => self.build_unavailable += 1,
            Classification::CorpusInvalid => self.corpus_invalid += 1,
            Classification::Timeout => self.timeout += 1,
            Classification::Skipped => self.skipped += 1,
        }
    }
    fn merge(&mut self, o: &Roll) {
        self.parity += o.parity;
        self.unsound_pass += o.unsound_pass;
        self.false_positive += o.false_positive;
        self.unsupported += o.unsupported;
        self.encoding_gap += o.encoding_gap;
        self.missed_bug += o.missed_bug;
        self.exceeds_oracle += o.exceeds_oracle;
        self.unknown += o.unknown;
        self.error += o.error;
        self.crash += o.crash;
        self.build_unavailable += o.build_unavailable;
        self.corpus_invalid += o.corpus_invalid;
        self.timeout += o.timeout;
        self.skipped += o.skipped;
        self.total += o.total;
    }
    /// The parity denominator: every row except the quarantined
    /// corpus-invalid sources (un-compilable on the pinned toolchain by any
    /// verifier, Kani's compiletest skips them — they measure the corpus,
    /// not trust-mc). `corpus_invalid` stays visible in `total` and its own
    /// column; only the percentage excludes it.
    pub fn denominator(&self) -> u64 {
        self.total - self.corpus_invalid
    }
    pub fn pct(&self) -> f64 {
        let denom = self.denominator();
        if denom == 0 { 0.0 } else { 100.0 * self.parity as f64 / denom as f64 }
    }
}

pub struct Summary {
    pub by_suite: Vec<(String, Scope, Roll)>,
    pub verification: Roll,
    pub benchmark: Roll,
    pub diagnostic: Roll,
    pub full: Roll,
    /// Native-surface re-key provenance rollup: `rekey:native` /
    /// `rekey:legacy(<reason>)` -> unit count. Empty for legacy-surface runs
    /// (their reports and ledger rows stay byte-identical).
    pub rekey: BTreeMap<String, u64>,
}

pub fn summarize(results: &[TestResult]) -> Summary {
    let mut per: BTreeMap<String, Roll> = BTreeMap::new();
    let mut rekey: BTreeMap<String, u64> = BTreeMap::new();
    for r in results {
        let c = r.classification.unwrap_or(Classification::Skipped);
        per.entry(r.suite.clone()).or_default().add(c);
        if let Some(prov) = &r.rekey {
            *rekey.entry(prov.clone()).or_default() += 1;
        }
    }
    let mut by_suite = Vec::new();
    let (mut verification, mut benchmark, mut diagnostic) =
        (Roll::default(), Roll::default(), Roll::default());
    for (name, roll) in &per {
        let scope = suites::lookup(name).map(|s| s.scope).unwrap_or(Scope::Diagnostic);
        match scope {
            Scope::Verification => verification.merge(roll),
            Scope::Benchmark => benchmark.merge(roll),
            Scope::Diagnostic => diagnostic.merge(roll),
            Scope::Excluded => {}
        }
        by_suite.push((name.clone(), scope, *roll));
    }
    by_suite.sort_by(|a, b| (a.1.as_str(), &a.0).cmp(&(b.1.as_str(), &b.0)));
    let mut full = Roll::default();
    full.merge(&verification);
    full.merge(&benchmark);
    full.merge(&diagnostic);
    Summary { by_suite, verification, benchmark, diagnostic, full, rekey }
}

fn bar(pct: f64) -> String {
    let filled = (pct / 5.0).round() as usize; // 20 cells
    let mut s = String::with_capacity(20);
    for i in 0..20 {
        s.push(if i < filled { '█' } else { '░' });
    }
    s
}

pub fn format_markdown(s: &Summary, p: &Provenance) -> String {
    let mut o = String::new();
    let push = |o: &mut String, line: &str| {
        o.push_str(line);
        o.push('\n');
    };
    push(&mut o, "# Kani-domination burndown\n");
    push(
        &mut o,
        &format!(
            "_Generated {} · trust-mc `{}`{} · ay pin `{}` · ay binary `{}`{} · Kani `{}` · backend `{}` · harness-timeout {}s · jobs {}_\n",
            p.generated_iso,
            short(&p.trust_mc_head),
            if p.trust_mc_dirty { " (dirty)" } else { "" },
            short(&p.ay_pin),
            p.ay_binary_version,
            if p.ay_rev_matches_pin { "" } else { " ⚠ ay-rev≠pin" },
            short(&p.kani_rev),
            p.backend,
            p.harness_timeout_s,
            p.jobs,
        ),
    );

    push(&mut o, "## Headline\n");
    push(
        &mut o,
        &format!(
            "| Metric | Parity | Denominator | % | |\n|---|---:|---:|---:|---|\n\
             | **Verification verdict parity** (primary) | {} | {} | {:.1}% | `{}` |\n\
             | **Full-corpus parity** (outer) | {} | {} | {:.1}% | `{}` |",
            s.verification.parity, s.verification.denominator(), s.verification.pct(), bar(s.verification.pct()),
            s.full.parity, s.full.denominator(), s.full.pct(), bar(s.full.pct()),
        ),
    );
    if s.full.corpus_invalid > 0 {
        push(
            &mut o,
            &format!(
                "\n_Denominators exclude {} corpus-invalid test(s) (un-compilable corpus sources; explicit evidence-quoted quarantine manifest — own column below, raw totals: verification {}, full {})._",
                s.full.corpus_invalid, s.verification.total, s.full.total,
            ),
        );
    }
    push(
        &mut o,
        &format!(
            "\n**Soundness flags:** missed-bugs (oracle=fail, trust-mc=success) **{}** {} · exceeds-oracle (Kani-unsupported artifact, trust-mc proves) {} · genuine false-positives {} · CHC-encoding gaps {} · unsupported-construct gaps {} · unsound-fallback passes {} · unknown/inconclusive {} · error {} · crash {} · build-unavailable {} · timeout {}",
            s.full.missed_bug,
            if s.full.missed_bug > 0 { "⛔ CRITICAL" } else { "✅" },
            s.full.exceeds_oracle,
            s.full.false_positive,
            s.full.encoding_gap,
            s.full.unsupported,
            s.full.unsound_pass,
            s.full.unknown,
            s.full.error,
            s.full.crash,
            s.full.build_unavailable,
            s.full.timeout,
        ),
    );
    if s.full.corpus_invalid > 0 {
        push(
            &mut o,
            &format!(" · corpus-invalid (quarantined, out of denominator) {}", s.full.corpus_invalid),
        );
    }
    if !s.rekey.is_empty() {
        push(&mut o, &format!("\n**Native re-key (surface=native):** {}", rekey_line(&s.rekey)));
    }

    for (title, roll) in [
        ("Verification", &s.verification),
        ("Benchmark", &s.benchmark),
        ("Diagnostic", &s.diagnostic),
    ] {
        if roll.total == 0 {
            continue;
        }
        push(&mut o, &format!("\n## {title} ({}/{} parity, {:.1}%)\n", roll.parity, roll.denominator(), roll.pct()));
        push(&mut o, "| Suite | parity | exceeds | enc-gap | unsupported | false-pos | missed-bug | unsound | unknown | error | crash | build-unavail | corpus-inv | timeout | total | % |");
        push(&mut o, "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
        for (name, scope, r) in &s.by_suite {
            if scope.as_str() != title.to_lowercase() {
                continue;
            }
            push(
                &mut o,
                &format!(
                    "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {:.1}% |",
                    name, r.parity, r.exceeds_oracle, r.encoding_gap, r.unsupported,
                    r.false_positive, r.missed_bug, r.unsound_pass, r.unknown, r.error, r.crash,
                    r.build_unavailable, r.corpus_invalid, r.timeout, r.total, r.pct(),
                ),
            );
        }
    }
    o
}

pub fn format_text(s: &Summary, p: &Provenance) -> String {
    let mut o = String::new();
    o.push_str(&format!(
        "Kani-domination burndown  ({}, trust-mc {}{}, Kani {}, {} backend, {}s timeout)\n",
        p.generated_iso, short(&p.trust_mc_head),
        if p.trust_mc_dirty { "+dirty" } else { "" },
        short(&p.kani_rev), p.backend, p.harness_timeout_s,
    ));
    o.push_str(&format!(
        "  VERIFICATION parity : {:>5}/{:<5} {:>5.1}%  {}\n",
        s.verification.parity, s.verification.denominator(), s.verification.pct(), bar(s.verification.pct())
    ));
    o.push_str(&format!(
        "  FULL-CORPUS parity  : {:>5}/{:<5} {:>5.1}%  {}\n",
        s.full.parity, s.full.denominator(), s.full.pct(), bar(s.full.pct())
    ));
    if s.full.corpus_invalid > 0 {
        o.push_str(&format!(
            "  (denominators exclude {} corpus-invalid quarantined test(s); raw totals: verification {}, full {})\n",
            s.full.corpus_invalid, s.verification.total, s.full.total
        ));
    }
    o.push_str(&format!(
        "  missed-bugs={} exceeds-oracle={} false-pos={} enc-gap={} unsupported={} unsound-pass={} unknown={} error={} crash={} build-unavail={} corpus-invalid={} timeout={} skipped={}\n",
        s.full.missed_bug, s.full.exceeds_oracle, s.full.false_positive, s.full.encoding_gap,
        s.full.unsupported, s.full.unsound_pass, s.full.unknown, s.full.error, s.full.crash,
        s.full.build_unavailable, s.full.corpus_invalid, s.full.timeout, s.full.skipped
    ));
    if !s.rekey.is_empty() {
        o.push_str(&format!("  surface=native re-key: {}\n", rekey_line(&s.rekey)));
    }
    o.push_str("  ---- by suite ----\n");
    for (name, _scope, r) in &s.by_suite {
        o.push_str(&format!(
            "  {:<16} {:>4}/{:<4} {:>5.1}%  (exc={} enc={} unsup={} fp={} miss={} uns={} unk={} err={} crash={} bu={} ci={} to={} skip={})\n",
            name, r.parity, r.denominator(), r.pct(), r.exceeds_oracle,
            r.encoding_gap, r.unsupported, r.false_positive, r.missed_bug, r.unsound_pass,
            r.unknown, r.error, r.crash, r.build_unavailable, r.corpus_invalid, r.timeout, r.skipped
        ));
    }
    o
}

/// One compact, machine-readable ledger row capturing the authority tuple +
/// headline numbers, for trend tracking across runs. The `surface` / `rekey`
/// keys are additive: they appear only on `--surface native` runs, so legacy
/// rows stay byte-identical to the pre-`--surface` schema. `total` stays the
/// raw row count; the `pct` values exclude the quarantined `corpus_invalid`
/// rows from their denominator (see [`Roll::denominator`]).
pub fn ledger_row(s: &Summary, p: &Provenance) -> serde_json::Value {
    let mut row = serde_json::json!({
        "generated_unix": p.generated_unix,
        "generated_iso": p.generated_iso,
        "trust_mc_head": p.trust_mc_head,
        "trust_mc_dirty": p.trust_mc_dirty,
        "ay_pin": p.ay_pin,
        "ay_binary_version": p.ay_binary_version,
        "ay_rev_matches_pin": p.ay_rev_matches_pin,
        "kani_rev": p.kani_rev,
        "backend": p.backend,
        "harness_timeout_s": p.harness_timeout_s,
        "scopes": p.scopes,
        "verification": { "parity": s.verification.parity, "total": s.verification.total, "pct": round1(s.verification.pct()) },
        "full": { "parity": s.full.parity, "total": s.full.total, "pct": round1(s.full.pct()) },
        "missed_bugs": s.full.missed_bug,
        "exceeds_oracle": s.full.exceeds_oracle,
        "false_positives": s.full.false_positive,
        "encoding_gap": s.full.encoding_gap,
        "unsupported": s.full.unsupported,
        "unsound_pass": s.full.unsound_pass,
        "unknown": s.full.unknown,
        "error": s.full.error,
        "crash": s.full.crash,
        "build_unavailable": s.full.build_unavailable,
        "corpus_invalid": s.full.corpus_invalid,
        "timeout": s.full.timeout,
    });
    if let Some(surface) = &p.surface {
        row["surface"] = serde_json::json!(surface);
    }
    if !s.rekey.is_empty() {
        row["rekey"] = serde_json::json!(s.rekey);
    }
    row
}

pub fn append_ledger(path: &Path, row: &serde_json::Value) -> anyhow::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path)?;
    writeln!(f, "{}", serde_json::to_string(row)?)?;
    Ok(())
}

fn round1(x: f64) -> f64 {
    (x * 10.0).round() / 10.0
}
fn short(s: &str) -> String {
    s.chars().take(12).collect()
}

/// `rekey:native=412 rekey:legacy(cargo_unit)=131 …`, native first.
fn rekey_line(rekey: &BTreeMap<String, u64>) -> String {
    let mut entries: Vec<(&String, &u64)> = rekey.iter().collect();
    entries.sort_by(|a, b| {
        (a.0.as_str() != "rekey:native", std::cmp::Reverse(a.1), a.0)
            .cmp(&(b.0.as_str() != "rekey:native", std::cmp::Reverse(b.1), b.0))
    });
    entries.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Verdict;

    fn result(rekey: Option<&str>) -> TestResult {
        TestResult {
            suite: "expected".into(),
            file: "x.rs".into(),
            oracle: Verdict::Success,
            observed: Some(Verdict::Success),
            classification: Some(Classification::Parity),
            sound_fallback: 0,
            effective_success: false,
            proof_marker: true,
            native_proof_accepted: false,
            ctrex_category: None,
            unknown_reason: None,
            self_reported_unsound: false,
            duration_ms: 1,
            exit_code: Some(0),
            flags: vec![],
            note: String::new(),
            rekey: rekey.map(str::to_string),
        }
    }

    fn prov(surface: Option<&str>) -> Provenance {
        Provenance {
            generated_unix: 0,
            generated_iso: "1970-01-01T00:00:00Z".into(),
            trust_mc_head: "h".into(),
            trust_mc_dirty: false,
            ay_pin: "p".into(),
            ay_binary_version: "v".into(),
            ay_rev_matches_pin: true,
            kani_rev: "k".into(),
            kani_repo: "r".into(),
            backend: "chc".into(),
            harness_timeout_s: 1,
            jobs: 1,
            scopes: vec!["verification".into()],
            surface: surface.map(str::to_string),
        }
    }

    /// Legacy runs must keep the exact pre-`--surface` ledger row: no
    /// `surface` / `rekey` keys at all.
    #[test]
    fn ledger_row_is_additive_only() {
        let legacy = summarize(&[result(None)]);
        let row = ledger_row(&legacy, &prov(None));
        assert!(row.get("surface").is_none());
        assert!(row.get("rekey").is_none());

        let native = summarize(&[
            result(Some("rekey:native")),
            result(Some("rekey:legacy(cargo_unit)")),
            result(Some("rekey:native")),
        ]);
        let row = ledger_row(&native, &prov(Some("native")));
        assert_eq!(row["surface"], "native");
        assert_eq!(row["rekey"]["rekey:native"], 2);
        assert_eq!(row["rekey"]["rekey:legacy(cargo_unit)"], 1);
    }

    #[test]
    fn text_report_mentions_rekey_only_when_present() {
        let legacy = summarize(&[result(None)]);
        assert!(!format_text(&legacy, &prov(None)).contains("re-key"));
        let native = summarize(&[result(Some("rekey:native"))]);
        assert!(format_text(&native, &prov(Some("native"))).contains("rekey:native=1"));
    }

    fn result_with(class: Classification) -> TestResult {
        TestResult { classification: Some(class), ..result(None) }
    }

    /// `corpus_invalid` is excluded from the parity denominator (it measures
    /// the corpus, not trust-mc) while staying visible: in `total`, in its own
    /// ledger key, and in both report formats. 1 parity + 1 corpus_invalid =
    /// 100% of a denominator of 1, never 50% of 2 — and the exclusion is
    /// printed, not silent.
    #[test]
    fn corpus_invalid_is_visible_but_out_of_denominator() {
        let s = summarize(&[result(None), result_with(Classification::CorpusInvalid)]);
        assert_eq!(s.verification.total, 2);
        assert_eq!(s.verification.corpus_invalid, 1);
        assert_eq!(s.verification.denominator(), 1);
        assert!((s.verification.pct() - 100.0).abs() < 1e-9);

        let row = ledger_row(&s, &prov(None));
        assert_eq!(row["corpus_invalid"], 1);
        // Raw total stays raw; pct reflects the exclusion.
        assert_eq!(row["verification"]["total"], 2);
        assert_eq!(row["verification"]["pct"], 100.0);

        let text = format_text(&s, &prov(None));
        assert!(text.contains("corpus-invalid=1"));
        assert!(text.contains("denominators exclude 1 corpus-invalid"));
        let md = format_markdown(&s, &prov(None));
        assert!(md.contains("corpus-inv"));
        assert!(md.contains("Denominators exclude 1 corpus-invalid"));

        // An error row is NOT excluded: 1 parity + 1 error = 50%.
        let s = summarize(&[result(None), result_with(Classification::Error)]);
        assert_eq!(s.verification.denominator(), 2);
        assert!((s.verification.pct() - 50.0).abs() < 1e-9);
    }
}

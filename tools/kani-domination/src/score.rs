// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Aggregate per-test results into the layered burndown (verification parity +
//! full-corpus coverage) and a committed trend ledger.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;

use crate::model::{Classification, Engine, Provenance, Scope, TestResult};
use crate::route::route_or_legacy;
use crate::suites;

/// `engine <version> (<path>)` for a non-default engine, else nothing, so
/// trust-mc reports read exactly as before.
fn engine_line(p: &Provenance) -> Option<String> {
    (p.engine() != Engine::TrustMc).then(|| {
        format!(
            "engine {} ({})",
            p.engine_version.as_deref().unwrap_or(p.engine().as_str()),
            p.engine_path.as_deref().unwrap_or("<unknown path>")
        )
    })
}

#[derive(Debug, Default, Clone, Copy)]
pub struct Roll {
    pub parity: u64,
    pub unsound_pass: u64,
    /// `Classification::TrivialSafePass`: a success on `trivial_safe=no_error_rule`.
    pub trivial_safe_pass: u64,
    /// `Classification::UnattributedPass`: a success on `unattributed_check=chc.0`.
    pub unattributed_pass: u64,
    pub false_positive: u64,
    pub unsupported: u64,
    pub encoding_gap: u64,
    pub missed_bug: u64,
    pub exceeds_oracle: u64,
    pub unknown: u64,
    pub error: u64,
    pub vacuous: u64,
    pub crash: u64,
    pub build_unavailable: u64,
    /// Quarantined corpus sources (explicit evidence-quoted manifest,
    /// `quarantine::CORPUS_INVALID`): counted in `total` but excluded from
    /// the parity denominator — see [`Roll::denominator`].
    pub corpus_invalid: u64,
    pub timeout: u64,
    pub skipped: u64,
    /// Units upstream Kani's compiletest never runs (`TestResult::upstream_ignored`:
    /// a `fixme` / `ignore` path or the spec's `fixme` class), whatever their
    /// class — except `missed_bug`, which stays in its own column and in the
    /// denominator (plan D1). Counted in `total`, excluded from the
    /// denominator, never in any class counter.
    pub fixme: u64,
    /// Of `parity`: rows whose run settled at least one harness as
    /// compiler-certified obligation-free (`TestResult::certified_no_checks`).
    /// A sub-column of parity, not a class — already counted in `parity`.
    pub parity_no_checks: u64,
    pub total: u64,
}

impl Roll {
    fn add(&mut self, c: Classification, upstream_ignored: bool, certified_no_checks: bool) {
        self.total += 1;
        // No upstream verdict exists for an upstream-ignored unit, so it can
        // neither earn nor lose parity. A missed bug is the exception: trust-mc
        // proved a harness the file expects to fail, and that is a soundness
        // finding whether or not Kani's regression suite runs the file.
        if upstream_ignored && c != Classification::MissedBug {
            self.fixme += 1;
            return;
        }
        if c == Classification::Parity && certified_no_checks {
            self.parity_no_checks += 1;
        }
        match c {
            Classification::Parity => self.parity += 1,
            Classification::UnsoundPass => self.unsound_pass += 1,
            Classification::TrivialSafePass => self.trivial_safe_pass += 1,
            Classification::UnattributedPass => self.unattributed_pass += 1,
            Classification::FalsePositive => self.false_positive += 1,
            Classification::Unsupported => self.unsupported += 1,
            Classification::EncodingGap => self.encoding_gap += 1,
            Classification::MissedBug => self.missed_bug += 1,
            Classification::ExceedsOracle => self.exceeds_oracle += 1,
            Classification::Unknown => self.unknown += 1,
            Classification::Error => self.error += 1,
            Classification::Vacuous => self.vacuous += 1,
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
        self.trivial_safe_pass += o.trivial_safe_pass;
        self.unattributed_pass += o.unattributed_pass;
        self.false_positive += o.false_positive;
        self.unsupported += o.unsupported;
        self.encoding_gap += o.encoding_gap;
        self.missed_bug += o.missed_bug;
        self.exceeds_oracle += o.exceeds_oracle;
        self.unknown += o.unknown;
        self.error += o.error;
        self.vacuous += o.vacuous;
        self.crash += o.crash;
        self.build_unavailable += o.build_unavailable;
        self.corpus_invalid += o.corpus_invalid;
        self.timeout += o.timeout;
        self.skipped += o.skipped;
        self.fixme += o.fixme;
        self.parity_no_checks += o.parity_no_checks;
        self.total += o.total;
    }
    /// The parity denominator: every row except the quarantined
    /// corpus-invalid sources (un-compilable on the pinned toolchain by any
    /// verifier, Kani's compiletest skips them — they measure the corpus,
    /// not trust-mc) and the upstream-ignored `fixme` units (no upstream
    /// verdict exists for them). Both stay visible in `total` and their own
    /// columns; only the percentage excludes them.
    pub fn denominator(&self) -> u64 {
        self.total - self.corpus_invalid - self.fixme
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
    /// Parity-integrity instrumentation: `<classification>` -> count of rows in
    /// it whose run emitted `[AY:DEMOTION_REASONS:…]`, i.e. whose FAILED
    /// verdict is a DEMOTED PROOF and not a counterexample. A nonzero
    /// `parity` entry here is the number of parity credits that rest on a
    /// result with no counterexample at all. Empty on runs whose driver
    /// predates the marker, keeping those rows byte-identical.
    pub demoted_by_class: BTreeMap<String, u64>,
    /// `<demotion reason>` -> count of rows that emitted it (any
    /// classification). Names which nets are actually load-bearing.
    pub demotion_reasons: BTreeMap<String, u64>,
    /// `<unknown_reason>` -> count, over rows that finished inconclusive.
    ///
    /// The point of this rollup is to keep the driver's own split visible:
    /// `PreSolveDeadline` is BUDGET-bound (the per-harness deadline expired before
    /// solving even began), `UndecidedModel` is solver-side inconclusiveness, and
    /// `SolverError` is a genuine ay-chc error. Those used to share one label,
    /// which made the gate's largest bucket impossible to act on.
    pub unknown_reasons: BTreeMap<String, u64>,
    /// Normalized `[AY:UNKNOWN-CATEGORY]` key -> count. Groups inconclusive
    /// rows by a driver-side label. Treat these as DESCRIPTIVE: `ArrayParamLimit`
    /// records that some predicate has >=2 Array-sorted params, which is a
    /// structural fact about the VC, not a demonstrated solver ceiling — ay
    /// proves 2-array VCs. See docs/ay-asks/2026-08-02-array-scale.
    pub unknown_categories: BTreeMap<String, u64>,
    /// Rows the Kani `contains_lines` tiebreak turned from false positive to
    /// parity (`TestResult::tiebreak_applied`). Printed in every report and
    /// written to the ledger row so the credit is never invisible.
    pub tiebreak_applied: u64,
    /// `scorer_version` -> row count. One entry for a coherent file; more
    /// than one is a mixed file, which `burndown` refuses to ledger.
    pub scorer_versions: BTreeMap<u32, u64>,
    /// The classes of the rows in the `fixme` column (counted scopes only):
    /// what trust-mc did on units upstream never runs.
    pub fixme_by_class: BTreeMap<String, u64>,
    /// `<suite>/<file> <class>` of every row in the `fixme` column, sorted.
    pub fixme_units: Vec<String>,
    /// `<suite>/<file>` of every upstream-ignored row scored `missed_bug`,
    /// which stays in the denominator and the soundness count.
    pub fixme_missed_bugs: Vec<String>,
    /// `<suite>/<file>` of every parity row in the `parity-no-checks`
    /// sub-column (any scope), sorted.
    pub parity_no_checks_units: Vec<String>,
}

/// Why a summary may not be written as one ledger row: its rows were scored
/// under more than one scorer version.
pub fn mixed_scorer_versions(s: &Summary) -> Option<String> {
    (s.scorer_versions.len() > 1).then(|| {
        let parts: Vec<String> = s.scorer_versions.iter().map(|(v, n)| format!("v{v}: {n} row(s)")).collect();
        format!("rows scored under different scorer versions ({}); `rescore` the file first", parts.join(", "))
    })
}

/// The single scorer version of a coherent summary, else the whole map.
fn scorer_version_json(s: &Summary) -> serde_json::Value {
    if s.scorer_versions.len() == 1 {
        serde_json::json!(s.scorer_versions.keys().next().copied().unwrap_or(1))
    } else {
        serde_json::json!(s.scorer_versions.iter().map(|(v, n)| (v.to_string(), *n)).collect::<BTreeMap<_, _>>())
    }
}

fn scorer_version_line(s: &Summary) -> String {
    if s.scorer_versions.len() == 1 {
        format!("scorer_version={}", s.scorer_versions.keys().next().copied().unwrap_or(1))
    } else {
        let parts: Vec<String> = s.scorer_versions.iter().map(|(v, n)| format!("v{v}={n}")).collect();
        format!("scorer_version=MIXED[{}]", parts.join(" "))
    }
}

pub fn summarize(results: &[TestResult]) -> Summary {
    let mut per: BTreeMap<String, Roll> = BTreeMap::new();
    let mut rekey: BTreeMap<String, u64> = BTreeMap::new();
    let mut demoted_by_class: BTreeMap<String, u64> = BTreeMap::new();
    let mut demotion_reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut unknown_reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut unknown_categories: BTreeMap<String, u64> = BTreeMap::new();
    let mut tiebreak_applied = 0u64;
    let mut scorer_versions: BTreeMap<u32, u64> = BTreeMap::new();
    let mut fixme_by_class: BTreeMap<String, u64> = BTreeMap::new();
    let mut fixme_units: Vec<String> = Vec::new();
    let mut fixme_missed_bugs: Vec<String> = Vec::new();
    let mut parity_no_checks_units: Vec<String> = Vec::new();
    for r in results {
        let c = r.classification.unwrap_or(Classification::Skipped);
        per.entry(r.suite.clone()).or_default().add(c, r.upstream_ignored, r.certified_no_checks > 0);
        if c == Classification::Parity && r.certified_no_checks > 0 && !r.upstream_ignored {
            parity_no_checks_units.push(format!("{}/{}", r.suite, r.file));
        }
        let counted = suites::lookup(&r.suite).map(|s| s.scope).unwrap_or(Scope::Diagnostic) != Scope::Excluded;
        if r.upstream_ignored && counted {
            if c == Classification::MissedBug {
                fixme_missed_bugs.push(format!("{}/{}", r.suite, r.file));
            } else {
                *fixme_by_class.entry(c.as_str().to_string()).or_default() += 1;
                fixme_units.push(format!("{}/{} {}", r.suite, r.file, c.as_str()));
            }
        }
        tiebreak_applied += u64::from(r.tiebreak_applied);
        *scorer_versions.entry(r.scorer_version).or_default() += 1;
        if let Some(prov) = &r.rekey {
            *rekey.entry(prov.clone()).or_default() += 1;
        }
        if !r.demotion_reasons.is_empty() {
            *demoted_by_class.entry(c.as_str().to_string()).or_default() += 1;
            for reason in &r.demotion_reasons {
                *demotion_reasons.entry(reason.clone()).or_default() += 1;
            }
        }
        if let Some(reason) = &r.unknown_reason {
            *unknown_reasons.entry(reason.clone()).or_default() += 1;
        }
        if let Some(category) = &r.unknown_category {
            *unknown_categories.entry(category.clone()).or_default() += 1;
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
    Summary {
        by_suite,
        verification,
        benchmark,
        diagnostic,
        full,
        rekey,
        demoted_by_class,
        demotion_reasons,
        unknown_reasons,
        unknown_categories,
        tiebreak_applied,
        scorer_versions,
        fixme_by_class,
        fixme_units: {
            fixme_units.sort();
            fixme_units
        },
        fixme_missed_bugs: {
            fixme_missed_bugs.sort();
            fixme_missed_bugs
        },
        parity_no_checks_units: {
            parity_no_checks_units.sort();
            parity_no_checks_units
        },
    }
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

    if let Some(engine) = engine_line(p) {
        push(&mut o, &format!("_{engine}_\n"));
    }
    push(
        &mut o,
        &format!("_{} · Kani tiebreak applied on {} row(s)_\n", scorer_version_line(s), s.tiebreak_applied),
    );
    if let Some(att) = &p.attestation {
        push(
            &mut o,
            &format!(
                "_Driver `{}` (sha256 `{}`, {}) · ay `{}` via {} · Trust `{}` · ay tree `{}`{} · load {:?} → {:?}_\n",
                att.driver_path,
                att.driver_sha256,
                att.driver_version,
                att.ay_binary_path,
                att.ay_binary_source,
                short(&att.trust_toolchain_commit),
                short(&att.ay_tree_head),
                if att.ay_tree_dirty == Some(true) { " (dirty)" } else { "" },
                att.load_average_start,
                att.load_average_end,
            ),
        );
    }
    push(&mut o, "## Headline\n");
    push(
        &mut o,
        &format!(
            "| Metric | Parity | of which no-checks | Denominator | % | |\n|---|---:|---:|---:|---:|---|\n\
             | **Verification verdict parity** (primary) | {} | {} | {} | {:.1}% | `{}` |\n\
             | **Full-corpus parity** (outer) | {} | {} | {} | {:.1}% | `{}` |",
            s.verification.parity, s.verification.parity_no_checks, s.verification.denominator(), s.verification.pct(), bar(s.verification.pct()),
            s.full.parity, s.full.parity_no_checks, s.full.denominator(), s.full.pct(), bar(s.full.pct()),
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
    if s.full.fixme > 0 || !s.fixme_missed_bugs.is_empty() {
        push(
            &mut o,
            &format!(
                "\n_Denominators exclude {} upstream-ignored `fixme` unit(s) (Kani's compiletest never runs them; own column below, by class: {}). Missed bugs on such units stay counted: {}._",
                s.full.fixme,
                count_line(&s.fixme_by_class),
                if s.fixme_missed_bugs.is_empty() { "none".to_string() } else { s.fixme_missed_bugs.join(", ") },
            ),
        );
    }
    push(
        &mut o,
        &format!(
            "\n**Soundness flags:** missed-bugs (oracle=fail, trust-mc=success) **{}** {} · exceeds-oracle (Kani-unsupported artifact, trust-mc proves) {} · genuine false-positives {} · CHC-encoding gaps {} · unsupported-construct gaps {} · unsound-fallback passes {} · trivial-safe passes (no error rule) {} · unattributed passes (chc.0 only) {} · unknown/inconclusive {} · error {} · crash {} · build-unavailable {} · timeout {}",
            s.full.missed_bug,
            if s.full.missed_bug > 0 { "⛔ CRITICAL" } else { "✅" },
            s.full.exceeds_oracle,
            s.full.false_positive,
            s.full.encoding_gap,
            s.full.unsupported,
            s.full.unsound_pass,
            s.full.trivial_safe_pass,
            s.full.unattributed_pass,
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
        push(&mut o, "| Suite | parity | parity-no-checks | exceeds | enc-gap | unsupported | false-pos | missed-bug | unsound | trivial-safe | unattributed | unknown | error | crash | build-unavail | corpus-inv | fixme | timeout | total | % |");
        push(&mut o, "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
        for (name, scope, r) in &s.by_suite {
            if scope.as_str() != title.to_lowercase() {
                continue;
            }
            push(
                &mut o,
                &format!(
                    "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {:.1}% |",
                    name, r.parity, r.parity_no_checks, r.exceeds_oracle, r.encoding_gap, r.unsupported,
                    r.false_positive, r.missed_bug, r.unsound_pass, r.trivial_safe_pass, r.unattributed_pass,
                    r.unknown, r.error, r.crash,
                    r.build_unavailable, r.corpus_invalid, r.fixme, r.timeout, r.total, r.pct(),
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
    if let Some(engine) = engine_line(p) {
        o.push_str(&format!("  {engine}\n"));
    }
    if let Some(att) = &p.attestation {
        o.push_str(&format!(
            "  driver {} (sha256 {}) · ay {} [{}] · jobs {} · load {:?} -> {:?}\n",
            att.driver_path, short(&att.driver_sha256), att.ay_binary_path, att.ay_binary_source,
            p.jobs, att.load_average_start, att.load_average_end,
        ));
        o.push_str(&host_load_lines(att.load_start.as_ref(), att.load_end.as_ref()));
    }
    if let Some(att) = &p.kani_attestation {
        o.push_str(&format!(
            "  kani {} (sha256 {}) [{}] · cargo-kani sha256 {} · home {} · toolchain {} · jobs {} · load {:?} -> {:?}\n",
            att.kani_path, short(&att.kani_sha256), att.kani_source, short(&att.cargo_kani_sha256),
            att.kani_home.as_deref().unwrap_or("<unknown>"), att.kani_toolchain.as_deref().unwrap_or("<unknown>"),
            p.jobs, att.load_average_start, att.load_average_end,
        ));
        o.push_str(&host_load_lines(att.load_start.as_ref(), att.load_end.as_ref()));
    }
    o.push_str(&format!(
        "  VERIFICATION parity : {:>5}/{:<5} {:>5.1}%  {}  (parity-no-checks {})\n",
        s.verification.parity, s.verification.denominator(), s.verification.pct(), bar(s.verification.pct()),
        s.verification.parity_no_checks
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
    if s.full.fixme > 0 || !s.fixme_missed_bugs.is_empty() {
        o.push_str(&format!(
            "  (denominators exclude {} upstream-ignored fixme unit(s), by class: {}; missed bugs on such units stay counted: {})\n",
            s.full.fixme,
            count_line(&s.fixme_by_class),
            if s.fixme_missed_bugs.is_empty() { "none".to_string() } else { s.fixme_missed_bugs.join(", ") },
        ));
    }
    o.push_str(&format!(
        "  missed-bugs={} exceeds-oracle={} false-pos={} enc-gap={} unsupported={} unsound-pass={} trivial-safe-pass={} unattributed-pass={} unknown={} vacuous={} error={} crash={} build-unavail={} corpus-invalid={} fixme={} timeout={} skipped={}\n",
        s.full.missed_bug, s.full.exceeds_oracle, s.full.false_positive, s.full.encoding_gap,
        s.full.unsupported, s.full.unsound_pass, s.full.trivial_safe_pass, s.full.unattributed_pass,
        s.full.unknown, s.full.vacuous, s.full.error, s.full.crash,
        s.full.build_unavailable, s.full.corpus_invalid, s.full.fixme, s.full.timeout, s.full.skipped
    ));
    o.push_str(&format!("  {} tiebreak-applied={}\n", scorer_version_line(s), s.tiebreak_applied));
    if !s.rekey.is_empty() {
        o.push_str(&format!("  surface=native re-key: {}\n", rekey_line(&s.rekey)));
    }
    if !s.demoted_by_class.is_empty() {
        o.push_str(&format!("  demoted-proof rows (FAILED with no counterexample) by class: {}\n", count_line(&s.demoted_by_class)));
        if let Some(n) = s.demoted_by_class.get("parity") {
            o.push_str(&format!(
                "  ⚠️  {n} PARITY row(s) rest on a demoted proof, not a counterexample — parity credited against a fail oracle with no cex\n"
            ));
        }
        o.push_str(&format!("  demotion reasons: {}\n", count_line(&s.demotion_reasons)));
    }
    if !s.unknown_reasons.is_empty() {
        o.push_str(&format!("  inconclusive reasons: {}\n", count_line(&s.unknown_reasons)));
        let budget = s.unknown_reasons.get("PreSolveDeadline").copied().unwrap_or(0);
        if budget > 0 {
            o.push_str(&format!(
                "    ^ {budget} of these are BUDGET-bound (deadline expired before solving began)\n"
            ));
        }
    }
    if !s.unknown_categories.is_empty() {
        o.push_str(&format!("  inconclusive categories: {}\n", count_line(&s.unknown_categories)));
    }
    o.push_str("  ---- by suite ----\n");
    for (name, _scope, r) in &s.by_suite {
        o.push_str(&format!(
            "  {:<16} {:>4}/{:<4} {:>5.1}%  (pnc={} exc={} enc={} unsup={} fp={} miss={} uns={} tsp={} uap={} unk={} err={} crash={} bu={} ci={} fixme={} to={} skip={})\n",
            name, r.parity, r.denominator(), r.pct(), r.parity_no_checks, r.exceeds_oracle,
            r.encoding_gap, r.unsupported, r.false_positive, r.missed_bug, r.unsound_pass,
            r.trivial_safe_pass, r.unattributed_pass, r.unknown, r.error, r.crash, r.build_unavailable, r.corpus_invalid, r.fixme, r.timeout, r.skipped
        ));
    }
    if !s.parity_no_checks_units.is_empty() {
        o.push_str("  ---- parity-no-checks (parity on a compiler-certified obligation-free harness) ----\n");
        for unit in &s.parity_no_checks_units {
            o.push_str(&format!("  {unit}\n"));
        }
    }
    if !s.fixme_units.is_empty() {
        o.push_str("  ---- fixme column (upstream-ignored, outside the denominator) ----\n");
        for unit in &s.fixme_units {
            o.push_str(&format!("  {unit}\n"));
        }
    }
    o
}

/// `  host load start: … · end: …`, or a line saying it was not recorded.
fn host_load_lines(start: Option<&crate::model::HostLoad>, end: Option<&crate::model::HostLoad>) -> String {
    let show = |l: Option<&crate::model::HostLoad>| l.map(crate::env::host_load_line).unwrap_or_else(|| "not recorded".into());
    format!("  host load start: {} · end: {}\n", show(start), show(end))
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
        "verification": { "parity": s.verification.parity, "parity_no_checks": s.verification.parity_no_checks, "total": s.verification.total, "denominator": s.verification.denominator(), "pct": round1(s.verification.pct()) },
        "full": { "parity": s.full.parity, "parity_no_checks": s.full.parity_no_checks, "total": s.full.total, "denominator": s.full.denominator(), "pct": round1(s.full.pct()) },
        "missed_bugs": s.full.missed_bug,
        "exceeds_oracle": s.full.exceeds_oracle,
        "false_positives": s.full.false_positive,
        "encoding_gap": s.full.encoding_gap,
        "unsupported": s.full.unsupported,
        "unsound_pass": s.full.unsound_pass,
        "trivial_safe_pass": s.full.trivial_safe_pass,
        "unattributed_pass": s.full.unattributed_pass,
        "unknown": s.full.unknown,
        "error": s.full.error,
        "crash": s.full.crash,
        "build_unavailable": s.full.build_unavailable,
        "corpus_invalid": s.full.corpus_invalid,
        "timeout": s.full.timeout,
        "scorer_version": scorer_version_json(s),
        "tiebreak_applied": s.tiebreak_applied,
    });
    if let Some(surface) = &p.surface {
        row["surface"] = serde_json::json!(surface);
    }
    if let Some(route) = &p.route {
        row["route"] = serde_json::json!(route);
    }
    if let Some(route_attestation) = &p.route_attestation {
        row["route_attestation"] = serde_json::json!(route_attestation);
    }
    if let Some(att) = &p.attestation {
        row["jobs"] = serde_json::json!(p.jobs);
        row["attestation"] = serde_json::json!(att);
    }
    // Only a non-default engine names itself, so trust-mc rows are unchanged.
    // (Such a row is printed by `burndown`, never appended — `ledger_refusal`.)
    if p.engine() != Engine::TrustMc {
        row["engine"] = serde_json::json!(p.engine().as_str());
        row["engine_version"] = serde_json::json!(p.engine_version);
        row["engine_sha256"] = serde_json::json!(p.engine_sha256);
        row["jobs"] = serde_json::json!(p.jobs);
        row["kani_attestation"] = serde_json::json!(p.kani_attestation);
    }
    if !s.rekey.is_empty() {
        row["rekey"] = serde_json::json!(s.rekey);
    }
    if !s.demoted_by_class.is_empty() {
        row["demoted_by_class"] = serde_json::json!(s.demoted_by_class);
        row["demotion_reasons"] = serde_json::json!(s.demotion_reasons);
    }
    if !s.unknown_reasons.is_empty() {
        row["unknown_reasons"] = serde_json::json!(s.unknown_reasons);
    }
    if !s.unknown_categories.is_empty() {
        row["unknown_categories"] = serde_json::json!(s.unknown_categories);
    }
    // Additive: a file with no upstream-ignored row keeps the older schema.
    if s.full.fixme > 0 || !s.fixme_missed_bugs.is_empty() {
        row["fixme"] = serde_json::json!(s.full.fixme);
        row["fixme_by_class"] = serde_json::json!(s.fixme_by_class);
        row["fixme_missed_bugs"] = serde_json::json!(s.fixme_missed_bugs);
    }
    row
}

/// The one compiler route every row of a report ran on, which must also be the
/// route its provenance declares. A report whose rows mix routes, or disagree
/// with their sidecar, has no denominator: the routes are different
/// measurements, so scoring refuses rather than blend them. Rows and sidecars
/// written before `--route` existed are DevCli.
pub fn report_route(results: &[TestResult], prov: &Provenance) -> anyhow::Result<String> {
    let declared = route_or_legacy(prov.route.as_deref());
    let mut seen: BTreeMap<&str, u64> = BTreeMap::new();
    for r in results {
        *seen.entry(route_or_legacy(r.route.as_deref())).or_default() += 1;
    }
    if seen.keys().any(|route| *route != declared) {
        anyhow::bail!(
            "the report's rows mix compiler routes or disagree with its provenance (rows per route {seen:?}; \
             provenance declares {declared}): a denominator never mixes routes"
        );
    }
    if declared == crate::route::Route::Trustc.as_str() && prov.route_attestation.is_none() {
        anyhow::bail!("a trustc report without a route attestation cannot be scored");
    }
    Ok(declared.to_string())
}

/// Why a run's ledger row must not be appended: a Trustc run whose route
/// preflight failed (every row is `error`), one whose tuple-check did not pass
/// (a row from other inputs is not a row of `tools/tuple.toml`), or one on a
/// non-parity KEY (T1-D5: smoke rows never count). Each reason is named; an
/// uncounted attestation with none of them is refused too, since `counted` is
/// the authority. `None` for every DevCli run.
///
/// Before any of those, the engine: the ledger is trust-mc's trend line, and
/// a Kani row on it would read as a trust-mc measurement (a trust-mc file,
/// explicit or written before `--engine` existed, is never refused for it).
pub fn ledger_refusal(p: &Provenance) -> Option<String> {
    if p.engine() == Engine::Kani {
        return Some(format!(
            "this results file was produced by engine `kani` ({}); the burndown ledger tracks trust-mc only. \
             Print without appending (`--no-append` or `--ledger none`), or `compare` it against a trust-mc file.",
            p.engine_version.as_deref().unwrap_or("<unknown version>")
        ));
    }
    // Plan D18: a counted row records the host load it was measured under.
    if let Some(att) = &p.attestation {
        if att.load_start.is_none() || att.load_end.is_none() {
            return Some(format!(
                "its attestation records no host load at {} (plan D18: load average and concurrent \
                 cargo/rustc/trust-mc-driver/kani-driver processes at start and end); a sidecar written before \
                 2026-09-14, or an interrupted run, cannot be a counted row — re-run it",
                match (&att.load_start, &att.load_end) {
                    (None, None) => "start or end",
                    (None, Some(_)) => "start",
                    _ => "end",
                }
            ));
        }
    }
    let Some(ra) = &p.route_attestation else {
        return (route_or_legacy(p.route.as_deref()) != crate::route::LEGACY_ROUTE)
            .then(|| "its route has no attestation".to_string());
    };
    if !ra.preflight_errors.is_empty() {
        return Some(format!("its route preflight failed: {}", ra.preflight_errors.join("; ")));
    }
    if ra.tuple_check.as_deref() != Some(crate::route::TUPLE_CHECK_PASS) {
        return Some(format!(
            "its tuple-check is {}, not pass; a row from other inputs is not a row of tools/tuple.toml",
            ra.tuple_check.as_deref().unwrap_or("<none>")
        ));
    }
    if ra.library_mode.as_deref() != Some(crate::route::PARITY_LIBRARY_MODE) {
        return Some(format!("its KEY's library_mode is {:?}, not parity; smoke rows never count", ra.library_mode));
    }
    if !ra.counted {
        return Some("its route attestation is marked uncounted".to_string());
    }
    None
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
/// `k=v` pairs, highest count first, name-tiebroken. Used for the
/// demoted-proof instrumentation rollups.
fn count_line(counts: &BTreeMap<String, u64>) -> String {
    let mut entries: Vec<(&String, &u64)> = counts.iter().collect();
    entries.sort_by(|a, b| (std::cmp::Reverse(a.1), a.0).cmp(&(std::cmp::Reverse(b.1), b.0)));
    entries.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(" ")
}

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
            observed: Some(Verdict::Success),
            classification: Some(Classification::Parity),
            proof_marker: true,
            duration_ms: 1,
            wall_ms: 1,
            max_rss_kb: 1,
            exit_code: Some(0),
            rekey: rekey.map(str::to_string),
            ..TestResult::blank("expected", "x.rs", Verdict::Success)
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
            attestation: None,
            engine: None,
            engine_version: None,
            engine_path: None,
            engine_sha256: None,
            kani_attestation: None,
            scorer_version: crate::model::SCORER_VERSION,
            log_root: None,
            rescored_from: None,
            route: None,
            route_attestation: None,
        }
    }

    /// Every ledger row names the scorer version its rows were scored under
    /// and how many rows the Kani tiebreak upgraded; a file whose rows carry
    /// two versions is refused a single row, and both reports print both.
    #[test]
    fn ledger_row_carries_scorer_version_and_tiebreak_count() {
        let mut tb = result(None);
        tb.tiebreak_applied = true;
        let s = summarize(&[result(None), tb]);
        assert_eq!(s.tiebreak_applied, 1);
        let row = ledger_row(&s, &prov(None));
        assert_eq!(row["scorer_version"], crate::model::SCORER_VERSION);
        assert_eq!(row["tiebreak_applied"], 1);
        assert!(mixed_scorer_versions(&s).is_none());
        let text = format_text(&s, &prov(None));
        assert!(text.contains(&format!("scorer_version={} tiebreak-applied=1", crate::model::SCORER_VERSION)), "{text}");
        assert!(format_markdown(&s, &prov(None)).contains("Kani tiebreak applied on 1 row(s)"));

        // A row written before the field existed reads as version 1; mixing
        // it with a current row is refused.
        let mut old = result(None);
        old.scorer_version = 1;
        let mixed = summarize(&[result(None), old]);
        let why = mixed_scorer_versions(&mixed).expect("mixed");
        assert!(why.contains("v1: 1 row(s)") && why.contains("rescore"), "{why}");
        assert_eq!(ledger_row(&mixed, &prov(None))["scorer_version"]["1"], 1);
        assert!(format_text(&mixed, &prov(None))
            .contains(&format!("scorer_version=MIXED[v1=1 v{}=1]", crate::model::SCORER_VERSION)));
    }

    /// A Kani results file may be scored and printed but never enters the
    /// trust-mc burndown ledger; a trust-mc file (explicit or pre-`--engine`)
    /// is not refused, and its ledger row carries no `engine` key.
    #[test]
    fn kani_rows_never_enter_the_ledger() {
        let mut kani = prov(None);
        kani.engine = Some(Engine::Kani);
        kani.engine_version = Some("kani 0.67.0".into());
        let refusal = ledger_refusal(&kani).expect("kani is refused");
        assert!(refusal.contains("kani 0.67.0"), "{refusal}");
        assert!(ledger_refusal(&prov(None)).is_none());
        let mut explicit = prov(None);
        explicit.engine = Some(Engine::TrustMc);
        assert!(ledger_refusal(&explicit).is_none());
        let s = summarize(&[result(None)]);
        assert!(ledger_row(&s, &explicit).get("engine").is_none());
        assert_eq!(ledger_row(&s, &kani)["engine"], "kani");
        assert!(format_text(&s, &kani).contains("engine kani 0.67.0"));
        assert!(!format_text(&s, &explicit).contains("engine "));
    }

    /// Legacy runs must keep the exact pre-`--surface` ledger row: no
    /// `surface` / `rekey` keys at all.
    #[test]
    fn ledger_row_is_additive_only() {
        let legacy = summarize(&[result(None)]);
        let row = ledger_row(&legacy, &prov(None));
        assert!(row.get("surface").is_none());
        assert!(row.get("rekey").is_none());
        assert!(row.get("attestation").is_none());
        assert!(row.get("jobs").is_none());

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

    /// A run that carries the runner attestation writes it (and `jobs`) into
    /// its ledger row, so the row names the exact driver and ay binaries.
    #[test]
    fn ledger_row_carries_the_runner_attestation_when_present() {
        let mut p = prov(None);
        p.attestation = Some(crate::model::RunnerAttestation {
            driver_path: "/b/bin/trust-mc-driver".into(),
            driver_sha256: "ab".repeat(32),
            driver_version: "trust-mc 0.6.0".into(),
            compiler_path: Some("/b/bin/trust-mc-compiler".into()),
            compiler_sha256: Some("cd".repeat(32)),
            sysroot: "/b".into(),
            ay_binary_path: "/c/ay".into(),
            ay_binary_source: "AY_BIN".into(),
            trust_toolchain: "trust".into(),
            trust_toolchain_commit: "25ccaf01f".into(),
            trust_toolchain_override: Some("/store/trust/8560".into()),
            trust_sysroot: Some("/store/trust/8560".into()),
            trust_seal_build: Some("8560".into()),
            trust_artifact_driver_sha256: Some("c2".repeat(32)),
            ay_tree: "/ay".into(),
            ay_tree_head: "94bf24d0f".into(),
            ay_tree_dirty: Some(false),
            kani_dir: "/cache/kani".into(),
            load_average_start: Some([1.0, 2.0, 3.0]),
            load_average_end: Some([4.0, 5.0, 6.0]),
            load_start: Some(crate::model::HostLoad { loadavg: Some([1.0, 2.0, 3.0]), competing: Some([("rustc".to_string(), 2)].into()), own_excluded: 0, source: "/proc".into() }),
            load_end: Some(crate::model::HostLoad { loadavg: Some([4.0, 5.0, 6.0]), competing: Some([("rustc".to_string(), 0)].into()), own_excluded: 0, source: "/proc".into() }),
            trust_mc_jobs: Some(1),
            child_env_scrubbed: vec!["RUSTFLAGS".into()],
        });
        let row = ledger_row(&summarize(&[result(None)]), &p);
        assert_eq!(row["jobs"], p.jobs);
        assert_eq!(row["attestation"]["driver_sha256"], "ab".repeat(32));
        assert_eq!(row["attestation"]["ay_binary_path"], "/c/ay");
        assert_eq!(row["attestation"]["load_average_end"][2], 6.0);
        assert_eq!(row["attestation"]["load_start"]["competing"]["rustc"], 2);
        assert_eq!(row["attestation"]["trust_mc_jobs"], 1);
        assert_eq!(ledger_refusal(&p), None);
        assert!(format_text(&summarize(&[result(None)]), &p).contains("host load start: 1.00/2.00/3.00 rustc=2 (own 0) · end: 4.00/5.00/6.00 rustc=0 (own 0)"));
        // Plan D18: an attested run without both samples is never a counted row.
        let mut no_end = p.clone();
        no_end.attestation.as_mut().unwrap().load_end = None;
        assert!(ledger_refusal(&no_end).unwrap().contains("no host load at end"), "{:?}", ledger_refusal(&no_end));
        let mut legacy = p.clone();
        legacy.attestation.as_mut().unwrap().load_start = None;
        legacy.attestation.as_mut().unwrap().load_end = None;
        assert!(ledger_refusal(&legacy).unwrap().contains("plan D18"));
        assert!(format_text(&summarize(&[result(None)]), &legacy).contains("host load start: not recorded"));
        assert_eq!(row["attestation"]["ay_tree_dirty"], false);
        assert_eq!(row["attestation"]["trust_toolchain_override"], "/store/trust/8560");
        assert_eq!(row["attestation"]["trust_seal_build"], "8560");
        assert_eq!(row["attestation"]["trust_artifact_driver_sha256"], "c2".repeat(32));
    }

    #[test]
    fn a_report_never_mixes_routes() {
        let mut p = prov(None);
        let legacy = vec![result(None), result(None)];
        assert_eq!(report_route(&legacy, &p).unwrap(), "dev-cli");
        let trustc_row = TestResult { route: Some("trustc".into()), ..result(None) };
        let dev_cli_row = TestResult { route: Some("dev-cli".into()), ..result(None) };
        assert_eq!(report_route(&[result(None), dev_cli_row.clone()], &p).unwrap(), "dev-cli");
        let error = report_route(&[dev_cli_row, trustc_row.clone()], &p).unwrap_err().to_string();
        assert!(error.contains("mix compiler routes"), "{error}");

        p.route = Some("trustc".into());
        assert!(report_route(&[trustc_row.clone()], &p).is_err(), "a trustc report needs its attestation");
        p.route_attestation = Some(crate::model::RouteAttestation { route: "trustc".into(), counted: true, ..Default::default() });
        assert_eq!(report_route(&[trustc_row.clone()], &p).unwrap(), "trustc");
        assert!(report_route(&legacy, &p).is_err(), "DevCli rows under a trustc sidecar");
        assert!(report_route(&[trustc_row, result(None)], &p).is_err());
    }

    #[test]
    fn ledger_row_carries_the_route_and_refuses_uncounted_trustc_runs() {
        let mut p = prov(None);
        let s = summarize(&[result(None)]);
        let row = ledger_row(&s, &p);
        assert!(row.get("route").is_none() && row.get("route_attestation").is_none());
        assert_eq!(ledger_refusal(&p), None);
        p.route = Some("dev-cli".into());
        assert_eq!(ledger_row(&s, &p)["route"], "dev-cli");
        assert_eq!(ledger_refusal(&p), None);

        p.route = Some("trustc".into());
        assert!(ledger_refusal(&p).unwrap().contains("no attestation"));
        let mut ra = crate::model::RouteAttestation {
            route: "trustc".into(),
            backend_dylib_sha256: Some("6edf".into()),
            library_mode: Some("parity".into()),
            tuple_check: Some("pass".into()),
            counted: true,
            ..Default::default()
        };
        p.route_attestation = Some(ra.clone());
        let row = ledger_row(&s, &p);
        assert_eq!(row["route"], "trustc");
        assert_eq!(row["route_attestation"]["backend_dylib_sha256"], "6edf");
        assert_eq!(ledger_refusal(&p), None);

        // A run on another seal: attested, scored, never a row of this tuple.
        ra.counted = false;
        ra.tuple_check = Some("fail: trust_rev,trust_seal_build".into());
        p.route_attestation = Some(ra.clone());
        let refusal = ledger_refusal(&p).unwrap();
        assert!(refusal.contains("tuple-check is fail: trust_rev,trust_seal_build"), "{refusal}");
        ra.tuple_check = None;
        p.route_attestation = Some(ra.clone());
        assert!(ledger_refusal(&p).unwrap().contains("tuple-check is <none>"));
        ra.tuple_check = Some("unavailable: no tools/tuple-check".into());
        p.route_attestation = Some(ra.clone());
        assert!(ledger_refusal(&p).unwrap().contains("unavailable"));

        ra.tuple_check = Some("pass".into());
        ra.library_mode = Some("smoke".into());
        p.route_attestation = Some(ra.clone());
        assert!(ledger_refusal(&p).unwrap().contains("library_mode"));
        // An uncounted attestation is refused even when no named reason applies.
        ra.library_mode = Some("parity".into());
        p.route_attestation = Some(ra.clone());
        assert!(ledger_refusal(&p).unwrap().contains("uncounted"));
        ra.preflight_errors = vec!["KEY driver_sha256 differs".into()];
        p.route_attestation = Some(ra);
        assert!(ledger_refusal(&p).unwrap().contains("preflight failed"));
    }

    fn result_with(class: Classification) -> TestResult {
        TestResult { classification: Some(class), ..result(None) }
    }

    /// `corpus_invalid` is excluded from the parity denominator (it measures
    /// the corpus, not trust-mc) while staying visible: in `total`, in its own
    /// ledger key, and in both report formats. 1 parity + 1 corpus_invalid =
    /// 100% of a denominator of 1, never 50% of 2 — and the exclusion is
    /// printed, not silent.
    /// Every classification a row can carry must survive the per-suite ->
    /// full rollup.
    ///
    /// `Roll::merge` sums each counter by hand, so a variant added to
    /// `Classification` and to `Roll::add` but NOT to `merge` reports the right
    /// per-suite count and a silent ZERO in the headline. That is exactly how
    /// `vacuous` first shipped: 11 rows classified correctly, `vacuous=0`
    /// printed. Comparing `total` against the sum of the parts catches the
    /// next one without needing to remember to update this test.
    #[test]
    fn merge_sums_every_class_counter() {
        const ALL: &[Classification] = &[
            Classification::Parity,
            Classification::UnsoundPass,
            Classification::TrivialSafePass,
            Classification::UnattributedPass,
            Classification::FalsePositive,
            Classification::Unsupported,
            Classification::EncodingGap,
            Classification::MissedBug,
            Classification::ExceedsOracle,
            Classification::Unknown,
            Classification::Error,
            Classification::Vacuous,
            Classification::Crash,
            Classification::BuildUnavailable,
            Classification::CorpusInvalid,
            Classification::Timeout,
            Classification::Skipped,
        ];
        let mut a = Roll::default();
        let mut b = Roll::default();
        for c in ALL {
            a.add(*c, false, false);
            b.add(*c, false, false);
        }
        // One upstream-ignored row per side: the `fixme` counter must survive
        // the merge as well.
        a.add(Classification::Parity, true, false);
        b.add(Classification::Unknown, true, false);
        a.add(Classification::Parity, false, true);
        a.merge(&b);

        let summed = a.parity
            + a.unsound_pass
            + a.trivial_safe_pass
            + a.unattributed_pass
            + a.false_positive
            + a.unsupported
            + a.encoding_gap
            + a.missed_bug
            + a.exceeds_oracle
            + a.unknown
            + a.error
            + a.vacuous
            + a.crash
            + a.build_unavailable
            + a.corpus_invalid
            + a.timeout
            + a.skipped
            + a.fixme;
        assert_eq!(
            summed, a.total,
            "a Classification variant is missing from Roll::merge — it will \
             report zero in the rollup while per-suite counts look correct"
        );
        assert_eq!(a.total, 2 * ALL.len() as u64 + 3);
        assert_eq!(a.parity_no_checks, 1, "parity_no_checks must survive merge");
        assert_eq!(a.vacuous, 2, "vacuous specifically must survive merge");
        assert_eq!(a.fixme, 2, "fixme must survive merge");
    }

    /// An upstream-ignored row (plan D1) sits in the `fixme` column, outside
    /// the denominator and every class counter, whatever its class — except a
    /// missed bug, which stays in the denominator, the soundness count and the
    /// report. 1 parity + 1 ignored parity + 1 ignored unknown = 100% of 1.
    #[test]
    fn upstream_ignored_rows_are_the_fixme_column_but_missed_bugs_stay() {
        let ignored = |class: Classification, file: &str| TestResult {
            classification: Some(class),
            upstream_ignored: true,
            file: file.to_string(),
            ..result(None)
        };
        let s = summarize(&[
            result(None),
            ignored(Classification::Parity, "loop-contract/fixme_box.rs"),
            ignored(Classification::Unknown, "uninit/fixme_unions.rs"),
        ]);
        assert_eq!((s.verification.total, s.verification.fixme, s.verification.parity), (3, 2, 1));
        assert_eq!(s.verification.unknown, 0, "an ignored row is in no class counter");
        assert_eq!(s.verification.denominator(), 1);
        assert!((s.verification.pct() - 100.0).abs() < 1e-9);
        assert_eq!(s.fixme_by_class.get("parity"), Some(&1));
        assert_eq!(s.fixme_units, vec!["expected/loop-contract/fixme_box.rs parity", "expected/uninit/fixme_unions.rs unknown"]);
        let text = format_text(&s, &prov(None));
        assert!(text.contains("fixme=2"), "{text}");
        assert!(text.contains("denominators exclude 2 upstream-ignored fixme unit(s)"), "{text}");
        assert!(text.contains("  expected/uninit/fixme_unions.rs unknown"), "{text}");
        assert!(format_markdown(&s, &prov(None)).contains("| fixme |"));
        let row = ledger_row(&s, &prov(None));
        assert_eq!((row["fixme"].as_u64(), row["verification"]["denominator"].as_u64()), (Some(2), Some(1)));

        // A missed bug on an ignored unit is still a missed bug, in the denominator.
        let s = summarize(&[result(None), ignored(Classification::MissedBug, "kani/fixme_lib.rs")]);
        assert_eq!((s.verification.missed_bug, s.verification.fixme, s.verification.denominator()), (1, 0, 2));
        assert_eq!(s.fixme_missed_bugs, vec!["expected/kani/fixme_lib.rs"]);
        assert!(format_text(&s, &prov(None)).contains("missed-bugs=1"));
        assert_eq!(ledger_row(&s, &prov(None))["fixme_missed_bugs"][0], "expected/kani/fixme_lib.rs");

        // A file with no ignored row keeps the older ledger schema.
        assert!(ledger_row(&summarize(&[result(None)]), &prov(None)).get("fixme").is_none());
    }

    /// A parity row on a compiler-certified no-checks harness stays parity
    /// and is also shown in the `parity-no-checks` sub-column, in every
    /// report and the ledger row; any other class never enters it.
    #[test]
    fn parity_no_checks_is_a_visible_sub_column_of_parity() {
        let certified = |class: Classification, file: &str| TestResult {
            classification: Some(class),
            certified_no_checks: 1,
            file: file.to_string(),
            ..result(None)
        };
        let s = summarize(&[
            result(None),
            certified(Classification::Parity, "empty/main.rs"),
            certified(Classification::MissedBug, "fail/main.rs"),
        ]);
        assert_eq!((s.verification.parity, s.verification.parity_no_checks, s.verification.missed_bug), (2, 1, 1));
        assert_eq!(s.verification.denominator(), 3);
        assert_eq!(s.parity_no_checks_units, vec!["expected/empty/main.rs"]);
        let text = format_text(&s, &prov(None));
        assert!(text.contains("(parity-no-checks 1)") && text.contains("pnc=1") && text.contains("  expected/empty/main.rs\n"), "{text}");
        let md = format_markdown(&s, &prov(None));
        assert!(md.contains("| parity-no-checks |") && md.contains("of which no-checks"), "{md}");
        let row = ledger_row(&s, &prov(None));
        assert_eq!(row["verification"]["parity_no_checks"], 1);
    }

    /// A qualified pass (scorer version 5) is its own visible column in
    /// every report and the ledger row, inside the denominator, never parity.
    #[test]
    fn qualified_passes_are_visible_columns_outside_parity() {
        let s = summarize(&[
            result(None),
            result_with(Classification::TrivialSafePass),
            result_with(Classification::UnattributedPass),
            result_with(Classification::UnattributedPass),
        ]);
        let v = &s.verification;
        assert_eq!((v.parity, v.trivial_safe_pass, v.unattributed_pass, v.denominator()), (1, 1, 2, 4));
        let text = format_text(&s, &prov(None));
        assert!(text.contains("trivial-safe-pass=1 unattributed-pass=2") && text.contains("tsp=1 uap=2"), "{text}");
        let md = format_markdown(&s, &prov(None));
        assert!(md.contains("| trivial-safe | unattributed |") && md.contains("trivial-safe passes (no error rule) 1"), "{md}");
        let row = ledger_row(&s, &prov(None));
        assert_eq!((row["trivial_safe_pass"].as_u64(), row["unattributed_pass"].as_u64()), (Some(1), Some(2)));
        assert_eq!(Classification::TrivialSafePass.as_str(), "trivial_safe_pass");
        assert_eq!(serde_json::to_string(&Classification::UnattributedPass).unwrap(), "\"unattributed_pass\"");
    }

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

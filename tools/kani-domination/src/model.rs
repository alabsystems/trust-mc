// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core data model for the Kani-domination parity harness: verdicts, the
//! per-test classification taxonomy, run reports and provenance.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// Which verifier a run drives over the corpus. Every unit is discovered,
/// invoked (same file, same header flags, same cwd, same watchdog) and scored
/// against the same oracle whichever engine runs it, so two results files
/// produced under different engines are comparable row for row (`compare`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize, clap::ValueEnum)]
#[serde(rename_all = "kebab-case")]
pub enum Engine {
    /// `trust-mc-driver` on the AY backend (the default; byte-identical to
    /// runs before `--engine` existed).
    #[default]
    TrustMc,
    /// Upstream Kani (`kani` / `cargo kani` on CBMC), as the reference.
    Kani,
}

impl Engine {
    pub fn as_str(self) -> &'static str {
        match self {
            Engine::TrustMc => "trust-mc",
            Engine::Kani => "kani",
        }
    }
}

/// The version of the classification rules in `runner::score_unit`. Stamped on
/// every row, sidecar and ledger row a run writes, so rows scored under
/// different rules can never be read as one series.
///
/// * **1** — every row before the field existed (ledger rows 1-62).
/// * **2** — fail-closed scoring (2026-09-12): the cargo / diagnostic
///   `contains_lines` arms are quality-gated and can only confirm a verdict
///   that agrees with the oracle; `unsupported` is never taken over a genuine
///   counterexample; the Kani `contains_lines` tiebreak credits parity only
///   when the expected file itself names exactly the harnesses that failed;
///   a multi-harness parity needs every sibling success to be clean.
/// * **3** — the Kani engine is scored by Kani's own compiletest criterion
///   per suite (2026-09-13, `runner::classify_kani`): exit status for the
///   `kani`-mode suites, `contains_lines` for the `expected` / `cargo-kani`
///   ones; Kani's `unsupported_construct` lines never decide a class; a
///   kani-driver panic is `error`; a file Kani finds no harness in is
///   `vacuous`. The trust-mc rules are identical to version 2, so a
///   trust-mc file rescored from 2 to 3 moves no class.
/// * **4** — 2026-09-14: upstream-ignored units (`fixme` / `ignore` paths and
///   the spec's `fixme` class) score in a `fixme` column outside the
///   denominator, missed bugs excepted; diagnostic-only and ICE expected files
///   are compile-fail oracles, parity only on a failed compile with that
///   diagnostic; a file-level success needs every harness SUCCESSFUL and a
///   self-report taints only the SUCCESSFUL harness that printed it; a failure
///   on exactly Kani's unsupported-construct check the expected file names is
///   parity; certified no-checks successes are counted (`certified_no_checks`)
///   and never `exceeds_oracle`. A version-3 row compares with a version-4 row
///   only after `rescore` (its log suffices; the oracle is re-derived from the
///   logged expected file).
/// * **5** — 2026-09-14: the driver's `[AY:PROOF_QUALIFIERS:…]` marker is read
///   per harness section. `clean` and `no_checks=compiler_certified_obligation_free`
///   leave a success clean; `trivial_safe=no_error_rule` scores
///   `trivial_safe_pass` and `unattributed_check=chc.0` scores
///   `unattributed_pass` (both outside parity, `missed_bug` against a fail
///   oracle, never `exceeds_oracle`); `sound_fallback=N` and every qualifier
///   the scorer does not recognise score `unsound_pass`, named in the note.
///   New row field: `proof_qualifiers`. The Kani engine prints no qualifiers,
///   so a Kani file rescored from 4 to 5 moves no class.
///
/// `1` is what a row without the field deserializes to.
pub const SCORER_VERSION: u32 = 5;

fn scorer_version_before_the_field() -> u32 {
    1
}

/// The verification verdict for a single test, either the *oracle* (what Kani
/// expects) or what trust-mc actually *observed*.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    /// Verification is expected to / did succeed (no failing property).
    Success,
    /// Verification is expected to / did find a failing property (counterexample).
    Fail,
    /// No determinate verdict (solver `unknown`, gave up, or could not decide).
    Unknown,
}

/// How a single test's observed result compares to the Kani oracle. This is the
/// atomic unit the burndown is computed over.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Classification {
    /// Observed verdict matches the oracle AND (if a success) it is a genuine
    /// proof with zero soundness fallback. This is the only class that counts
    /// toward real "domination".
    Parity,
    /// Oracle = success, observed = success, BUT the success was reached via a
    /// sound over-approximation / fallback (`[AY:SOUND_FALLBACK]` /
    /// `[AY:EFFECTIVE_SUCCESS]` / the `sound_fallback=N` proof qualifier), or a
    /// SUCCESSFUL harness carries a proof qualifier the scorer does not
    /// recognise (fail-closed; the note names it). Verdict matches but it is
    /// not a real proof.
    UnsoundPass,
    /// Oracle = success, observed = success, BUT a SUCCESSFUL harness carries
    /// the driver's `trivial_safe=no_error_rule` proof qualifier: its CHC
    /// problem queries `error` and no rule derives it, so the driver reported
    /// SUCCESSFUL without solving, every registered property SUCCESS. The
    /// compiler names that shape "registered properties but no error rules
    /// (lost checks, not proved checks)". Not a proof; never parity (scorer
    /// version 5). Against a fail oracle the same success is `missed_bug`.
    TrivialSafePass,
    /// Oracle = success, observed = success, BUT a SUCCESSFUL harness carries
    /// the driver's `unattributed_check=chc.0` proof qualifier: every non-cover
    /// check is the anonymous `chc.0` fallback, which names no property, so the
    /// proof cannot show that the expected properties reached the encoding.
    /// Never parity (scorer version 5); `missed_bug` against a fail oracle.
    UnattributedPass,
    /// Oracle = success, observed = fail. trust-mc reports a counterexample
    /// where Kani proves safety. Conservative (no missed bug) but a parity miss.
    FalsePositive,
    /// trust-mc hit an **unsupported construct** (codegen panic / "unsupported
    /// constructs" warning) and conservatively reported failure. Distinct from
    /// a genuine false positive: the root cause is a missing feature, not a
    /// solver disagreement. The clearest trust-mc codegen-gap signal.
    Unsupported,
    /// trust-mc reported FAILED, but the underlying CTREX is **not genuine** —
    /// the CHC the trust-mc compiler emitted was ill-sorted / unparseable
    /// (e.g. "expected argument sort … got …", "ay-chc inconclusive",
    /// `CTREX_CAT:EncodingGap`). AY correctly returned UNKNOWN; trust-mc mapped
    /// it to FAILED. This is a **trust-mc CHC-encoding gap**, not a real
    /// counterexample and not an AY-solver weakness.
    EncodingGap,
    /// Oracle = fail, observed = success. trust-mc proves safe where Kani
    /// expects a failure — a potential **unsoundness / missed bug**. Most severe.
    MissedBug,
    /// Oracle = fail, observed = success, **but the oracle's failure is a Kani
    /// unsupported-construct artifact**: the expected file records the failure
    /// only because Kani cannot handle the construct ("… is not currently
    /// supported by Kani …"), not because the program has a bug. trust-mc
    /// encodes the construct and produces a clean marker-backed proof of the
    /// (genuinely true) assertions, i.e. it *exceeds* the oracle. Counted out
    /// of `missed_bug` but kept out of `parity` too — its own visible column,
    /// per the measurement-honesty rule.
    ExceedsOracle,
    /// trust-mc returned an indeterminate verdict (solver `unknown`).
    Unknown,
    /// trust-mc failed to produce a verdict: compile error, unsupported
    /// flag, or no `VERIFICATION:-` line at all.
    Error,
    /// The harness produced NO verification conditions, so trust-mc honestly
    /// refused to call it proven (`[AY:VACUOUS:no-checks]`,
    /// `VERIFICATION:- INCONCLUSIVE (no checks)`).
    ///
    /// This is a trust-mc **encoding** gap — Kani generates checks for these
    /// harnesses and we generate none — but it is emphatically NOT breakage,
    /// and keeping it inside `Error` was actively misleading: a 2026-08-22 run
    /// showed `error=46` of which **33 were vacuity refusals and only 3 were
    /// real compile failures**, so the headline read like a crash wave when it
    /// was mostly the tool being honest.
    ///
    /// Non-parity either way, and it stays in the denominator: Kani verifies
    /// these files, so failing to emit checks is our gap to close, not a
    /// corpus defect to quarantine.
    Vacuous,
    /// The verifier (or its compiler subprocess) died on a signal (SIGABRT,
    /// SIGSEGV, …) — a real trust-mc crash, kept distinct from generic
    /// `Error` so the burndown points at hard defects.
    Crash,
    /// A cargo-project test whose dependencies cannot be built in this
    /// environment (network-restricted registry, unresolvable deps). Not a
    /// verifier defect; distinct from `Error` so it reads as "environment",
    /// not "broken".
    BuildUnavailable,
    /// The corpus *source itself* is invalid on the pinned toolchain for
    /// reasons external to any verifier: it uses intrinsics/features that
    /// rustc has since removed, or plants an unresolvable symbol / missing
    /// import, or cannot even be parsed by Kani's own contract macros. No
    /// tool — Kani included — can compile these files today; Kani's
    /// compiletest additionally skips them (`fixme` paths are ignored).
    /// Membership is an **explicit, evidence-quoted quarantine manifest**
    /// ([`crate::quarantine::CORPUS_INVALID`]), never a heuristic, and the
    /// class is only applied to rows that would otherwise be `Error` — a
    /// run that produces a verdict always classifies normally. Own visible
    /// ledger column; excluded from the parity denominator.
    CorpusInvalid,
    /// The outer process watchdog killed the run before a verdict.
    Timeout,
    /// Not run (e.g. a cargo-project suite under the single-file engine, or
    /// excluded by `--limit`).
    Skipped,
}

impl Classification {
    /// Whether this class counts as genuine parity (real domination).
    pub fn is_parity(self) -> bool {
        matches!(self, Classification::Parity)
    }
    /// Whether this class is a soundness-critical defect (trust-mc gave the
    /// wrong-and-dangerous answer).
    pub fn is_critical(self) -> bool {
        matches!(self, Classification::MissedBug)
    }
    pub fn as_str(self) -> &'static str {
        match self {
            Classification::Parity => "parity",
            Classification::UnsoundPass => "unsound_pass",
            Classification::TrivialSafePass => "trivial_safe_pass",
            Classification::UnattributedPass => "unattributed_pass",
            Classification::FalsePositive => "false_positive",
            Classification::Unsupported => "unsupported",
            Classification::EncodingGap => "encoding_gap",
            Classification::MissedBug => "missed_bug",
            Classification::ExceedsOracle => "exceeds_oracle",
            Classification::Unknown => "unknown",
            Classification::Error => "error",
            Classification::Vacuous => "vacuous",
            Classification::Crash => "crash",
            Classification::BuildUnavailable => "build_unavailable",
            Classification::CorpusInvalid => "corpus_invalid",
            Classification::Timeout => "timeout",
            Classification::Skipped => "skipped",
        }
    }
}

/// Which lane a Kani test suite belongs to. Drives the *layered* denominator:
/// `Verification` is the primary parity number; everything except `Excluded`
/// forms the outer full-corpus denominator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Scope {
    /// Single-verdict verification suites — the primary parity denominator.
    Verification,
    /// Performance/benchmark suite (verdict + wall-clock).
    Benchmark,
    /// Diagnostic / UI / coverage / cargo lanes (coverage denominator only).
    Diagnostic,
    /// Known-failing-upstream or empty lanes; never counted.
    Excluded,
}

impl Scope {
    pub fn as_str(self) -> &'static str {
        match self {
            Scope::Verification => "verification",
            Scope::Benchmark => "benchmark",
            Scope::Diagnostic => "diagnostic",
            Scope::Excluded => "excluded",
        }
    }
}

/// One Kani test, after discovery + oracle classification + (optionally) a run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestResult {
    /// Suite name (e.g. `expected`, `kani`).
    pub suite: String,
    /// Suite-relative POSIX path of the entry file.
    pub file: String,
    /// What Kani expects.
    pub oracle: Verdict,
    /// What trust-mc observed (None until run).
    #[serde(default)]
    pub observed: Option<Verdict>,
    /// Comparison class (None until run).
    #[serde(default)]
    pub classification: Option<Classification>,
    /// Sum of `[AY:SOUND_FALLBACK:n]` over the run.
    #[serde(default)]
    pub sound_fallback: u32,
    /// Saw an `[AY:EFFECTIVE_SUCCESS:...]` marker.
    #[serde(default)]
    pub effective_success: bool,
    /// Saw an `[AY:PROOF]` marker (a genuine CHC proof was produced).
    #[serde(default)]
    pub proof_marker: bool,
    /// The native proof was accepted as replayable evidence
    /// (`[AY:NATIVE_PROOF_GRADE:accepted...]`) — the strictest quality bar.
    #[serde(default)]
    pub native_proof_accepted: bool,
    /// trust-mc's own CTREX category for a FAILED verdict, parsed from
    /// `[AY:CTREX_CAT:…]` / the "CTREX breakdown" line: `Genuine`,
    /// `EncodingGap`, `OverApproximation`, or `Unknown`.
    #[serde(default)]
    pub ctrex_category: Option<String>,
    /// EVERY raw `[AY:CTREX_CAT:…]` value in the run, detail included.
    ///
    /// [`Self::ctrex_category`] keeps only the leading token, so
    /// `OverApproximation:chc_translation_drop=4` is recorded as bare
    /// `OverApproximation` — which names the SYMPTOM and discards the CAUSE.
    /// A 2026-08-22 audit of the 52 fastest non-parity rows had to re-run the
    /// driver on every one of them to recover a string the run had already
    /// printed; 33 of the 52 were blanked this way.
    ///
    /// A LIST rather than one string on purpose: a multi-harness file prints
    /// one marker per failing harness, and `reattribute_multi_harness_markers`
    /// rewrites `ctrex_category` to the first FAILING harness. A single detail
    /// string could therefore describe a different harness than the category
    /// beside it. Keeping all of them cannot disagree with anything.
    ///
    /// Measurement ONLY — feeds no classification, and `ctrex_category` is
    /// untouched so every existing rollup keys exactly as before.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ctrex_categories_raw: Vec<String>,
    /// Every `[AY:TRANSLATION_DROP_REASON:<fn>:<why>=<n>]` line in the run.
    ///
    /// These name the exact construct the compiler could not translate
    /// (`iter_fold_advance_failed`, `str_chars_nth_no_backing`,
    /// `boxnew_payload_store_drop`, …), which is the natural cluster key for
    /// the encoding-gap population — the single largest source of non-parity
    /// rows. The driver has always printed them (`trust-mc-driver
    /// src/main.rs:580`) and the scoreboard parsed them nowhere, so the gate
    /// could count the bucket but never say what was IN it.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub translation_drops: Vec<String>,
    /// Every `[AY:AGGREGATE_GAP_REASON:<fn>:<reason>=<n>]` line.
    ///
    /// For the nested-call lane the reason carries the CALLEE
    /// (`inline_nested_call_fallback_symbolic@<callee_path>`), which is the
    /// natural cluster key for the largest non-parity population in the corpus:
    /// a 2026-08-23 run had `nested_call_overapprox` on 62 non-parity rows, 42
    /// of them `oracle=success, observed=fail` — spurious counterexamples built
    /// on an invented return value. Measurement ONLY; feeds no classification.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub aggregate_gap_reasons: Vec<String>,
    /// The run emitted `[AY:VACUOUS:…]` — at least one harness produced no
    /// verification conditions, so any "proof" of it is vacuous.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub vacuous: bool,
    /// The run verified nothing because no harness was discovered
    /// (`[AY:NO_HARNESSES]`, printed with `VERIFICATION:- INCONCLUSIVE`).
    ///
    /// This is a harness-DISCOVERY gap — a `cfg`-ed-out or commented-out
    /// `#[kani::proof]` — not an indeterminate solver verdict, but it lands in
    /// the same `unknown` bucket and is indistinguishable there. Recorded so
    /// the two can be told apart. Measurement ONLY; classification unchanged.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub no_harnesses: bool,
    /// `[AY:UNKNOWN_REASON:…]` (e.g. `SolverError`, `Timeout`,
    /// `PreSolveDeadline`, `UndecidedModel`).
    ///
    /// NOTE: this is a CHC-SOLVER-ERROR field, not a general "why is this row
    /// not parity" field. Its only producing site is the `Err(e)` arm at
    /// `trust-mc-driver src/call_ay.rs:348`; every path where the solver
    /// actually ANSWERS hardcodes `None`. A row with a definite verdict that
    /// was later demoted therefore has no reason to lose, and `None` here is
    /// correct rather than missing. Use [`Self::ctrex_category_detail`] /
    /// [`Self::translation_drops`] / [`Self::demotion_reasons`] for those.
    #[serde(default)]
    pub unknown_reason: Option<String>,
    /// NORMALIZED `[AY:UNKNOWN-CATEGORY]` key — `ArrayParamLimit`, `PdrTimeout`,
    /// `SolverError`, `NoErrorRule`, `Uncategorized`, or `Other`.
    ///
    /// The driver already computes a precise reason for an inconclusive CHC run
    /// and prints it, but the scoreboard used to discard it, leaving the largest
    /// bucket in the gate unactionable. Normalized because the raw line embeds
    /// predicate names and counts (`predicate=main__bb0, array_sorts=6`), which
    /// would fragment every rollup into singletons. Measurement ONLY — it feeds
    /// no classification.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unknown_category: Option<String>,
    /// The raw `[AY:UNKNOWN-CATEGORY]` text, kept so the specific limit is
    /// recoverable without a re-run (e.g. WHICH predicate hit the array ceiling).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unknown_category_detail: Option<String>,
    /// `[AY:DEMOTION_REASONS:a,b]` — the driver demoted an original PROOF to
    /// FAILURE because an unsoundness counter fired. Recorded for measurement
    /// ONLY; it feeds no classification.
    ///
    /// Why it matters: the driver classifies CTREX only for *non-demoted*
    /// failures, so a demoted proof carries no `[AY:CTREX_CAT:…]` marker at
    /// all. Without this field a demoted proof is indistinguishable from a
    /// genuine counterexample — which is how a `FAILED` with no counterexample
    /// can be credited against a `fail` oracle. This field makes that
    /// population countable instead of invisible.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub demotion_reasons: Vec<String>,
    /// trust-mc printed a self-reported-unsoundness confession in the run
    /// (e.g. "created fresh unconstrained symbolic", `pointee_synthesis_fallback`,
    /// `unconstrained_assignment`, "UNSOUND verification"). A SUCCESS carrying one
    /// of these is not a clean proof — the audit's "how false proofs masquerade".
    #[serde(default)]
    pub self_reported_unsound: bool,
    /// Wall-clock of the trust-mc invocation, milliseconds — the whole unit,
    /// INCLUDING a retry after an outer-watchdog kill (see `run_one`).
    #[serde(default)]
    pub duration_ms: u64,
    /// Wall time of the attempt whose output was classified, spawn to reap,
    /// milliseconds. Differs from `duration_ms` only on a retried unit, where
    /// it excludes the killed first attempt. 0 on rows written before the
    /// field existed (`compare` treats 0 as "no data").
    #[serde(default)]
    pub wall_ms: u64,
    /// `ru_maxrss` of the direct child as `wait4` reports it, in KB (macOS
    /// reports bytes; normalized). The direct child is the driver / the `kani`
    /// launcher, so on its own this can be far below the tree's peak: on Linux
    /// the kernel folds in the peak of the descendants the child itself
    /// reaped, as the LARGEST single-process peak, never a sum. Exact, not
    /// sampled. 0 on rows written before the field existed.
    #[serde(default)]
    pub max_rss_kb: u64,
    /// Peak resident memory of the WHOLE process tree the unit spawned, in KB:
    /// the maximum over 50 ms samples of the sum of `VmHWM` across every live
    /// descendant (Linux `/proc` only; absent elsewhere). Never below
    /// `max_rss_kb`. Sampled, so read the README's limits before quoting it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tree_peak_rss_kb: Option<u64>,
    /// trust-mc process exit code (None if killed by watchdog).
    #[serde(default)]
    pub exit_code: Option<i32>,
    /// The kani-flags that were forwarded to trust-mc.
    #[serde(default)]
    pub flags: Vec<String>,
    /// Free-text note (skip reason, error head, etc.).
    #[serde(default)]
    pub note: String,
    /// Native-surface re-key provenance for this unit (`--surface native`
    /// runs only): `rekey:native` when the unit ran in the native
    /// `#[kani::harness]` spelling, `rekey:legacy(<reason>)` when it was left
    /// in the legacy spelling. Absent on legacy-surface runs, keeping their
    /// rows byte-identical to the pre-`--surface` schema.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rekey: Option<String>,
    /// The classification rules this row was scored under
    /// ([`SCORER_VERSION`]); a row written before the field existed reads as
    /// 1. A results file never mixes versions (`run` refuses to resume across
    /// one; `rescore` rewrites a whole file under the current rules).
    #[serde(default = "scorer_version_before_the_field")]
    pub scorer_version: u32,
    /// The Kani `contains_lines` tiebreak fired and changed this row's
    /// classification (false positive -> parity). Under scorer version 2 that
    /// needs the expected file to name exactly the harnesses that failed; the
    /// run summary and the ledger row print the count.
    #[serde(default)]
    pub tiebreak_applied: bool,
    /// The unit's driver log (argv, cwd, environment, exit code, timings,
    /// the expected file, and the full stdout and stderr), relative to the
    /// reports directory the sidecar's `log_root` names. `rescore` reads it.
    /// Absent on rows written before logs were captured.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub log_path: Option<String>,
    /// Every `[AY:ROUTE_LIMITATION:<id> route=<route>]` marker of the run:
    /// an OPTIONAL step the active compiler route could not take, named by the
    /// driver, in a run that still produced its verdict.
    ///
    /// This is the difference between "this route cannot do it yet, and here is
    /// its name" and "this route is broken". The T1 S7 acceptance chain could
    /// make neither call: the driver's two-lane loop-contract retry spawned
    /// lane children the Trustc route refuses, and the child's refusal text,
    /// quoted in the parent's diagnostic, was read as the PARENT refusing — so
    /// four attested, verdict-bearing CHC rows were scored `route error`.
    ///
    /// Measurement ONLY: it feeds no classification and is not compared across
    /// routes, so a limitation alone never makes two rows differ. An acceptance
    /// gate reads it to tell a NAMED, known limitation from an unexplained one.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub route_limitations: Vec<String>,
    /// The compiler route that produced this row (`dev-cli` or `trustc`,
    /// `--route`). Absent on rows written before the flag existed, which all ran
    /// the DevCli route (`route::route_or_legacy`). A report or ledger
    /// denominator never mixes routes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub route: Option<String>,
    /// Upstream Kani's compiletest never runs this unit (its path carries
    /// `fixme` / `ignore`, or the generated spec classifies it `fixme`), so no
    /// upstream verdict exists for it. The row keeps its real classification
    /// and is counted in the burndown's `fixme` column, outside the parity
    /// denominator — except a `missed_bug`, which stays in the denominator
    /// and in the soundness count (plan D1). Absent (false) on rows written
    /// before scorer version 4.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub upstream_ignored: bool,
    /// How many harnesses of the run the driver settled as compiler-certified
    /// obligation-free (D16): `[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]`
    /// or `VERIFICATION:- SUCCESSFUL (no checks — compiler-certified
    /// obligation-free)`, whichever count is larger. Such a success proves
    /// nothing because there was nothing to prove; it still scores `parity`
    /// against a success oracle (Kani reports the shape SUCCESSFUL) and
    /// `missed_bug` against a fail oracle, and the burndown shows it in the
    /// `parity-no-checks` sub-column. Absent (0) on rows written before
    /// scorer version 4, which never parsed it.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub certified_no_checks: u32,
    /// Every proof qualifier the driver printed for the run
    /// (`[AY:PROOF_QUALIFIERS:<q>,…]`), distinct, in first-seen order, a lone
    /// `clean` omitted. Recorded whatever it did to the class, so a qualified
    /// row stays auditable. Absent (empty) on rows written before scorer
    /// version 5 and on every Kani row.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub proof_qualifiers: Vec<String>,
}

fn is_zero(n: &u32) -> bool {
    *n == 0
}

impl TestResult {
    /// A row for `(suite, file, oracle)` before anything ran: every
    /// measurement at its "no data" value and no classification. The single
    /// place a row is born, so a new field is added here and nowhere else.
    pub fn blank(suite: &str, file: &str, oracle: Verdict) -> Self {
        TestResult {
            suite: suite.to_string(),
            file: file.to_string(),
            oracle,
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
            route_limitations: Vec::new(),
            self_reported_unsound: false,
            duration_ms: 0,
            wall_ms: 0,
            max_rss_kb: 0,
            tree_peak_rss_kb: None,
            exit_code: None,
            flags: Vec::new(),
            note: String::new(),
            rekey: None,
            scorer_version: SCORER_VERSION,
            tiebreak_applied: false,
            log_path: None,
            route: None,
            upstream_ignored: false,
            certified_no_checks: 0,
            proof_qualifiers: Vec::new(),
        }
    }
}

/// The authority tuple recorded with every run (per the project's
/// replacement-proof discipline).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Provenance {
    pub generated_unix: u64,
    pub generated_iso: String,
    /// trust-mc `git rev-parse HEAD`.
    pub trust_mc_head: String,
    /// trust-mc working tree dirty?
    pub trust_mc_dirty: bool,
    /// The pinned `ay` rev from trust-mc's Cargo.toml.
    pub ay_pin: String,
    /// `ay --version` of the binary actually used for the SMT path.
    pub ay_binary_version: String,
    /// Whether the ay binary's rev matches the pin (reproducibility flag).
    pub ay_rev_matches_pin: bool,
    /// Kani upstream rev the corpus was cloned at.
    pub kani_rev: String,
    pub kani_repo: String,
    pub backend: String,
    pub harness_timeout_s: u64,
    pub jobs: usize,
    /// Which scopes were run.
    pub scopes: Vec<String>,
    /// Harness spelling surface for the run: `"native"` when
    /// `--surface native` re-keyed expressible units to `#[kani::harness]`.
    /// Absent for legacy runs (byte-identical sidecars/ledger rows).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub surface: Option<String>,
    /// Which binaries and host state produced the run. Absent on sidecars
    /// written before the attestation existed (their ledger rows keep the
    /// older schema), and on `--engine kani` runs, which carry
    /// [`Self::kani_attestation`] instead.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub attestation: Option<RunnerAttestation>,
    /// The engine that produced every row. Absent on sidecars written before
    /// `--engine` existed, which were all trust-mc runs (see [`Self::engine`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine: Option<Engine>,
    /// First line of the engine's `--version` (`trust-mc-driver --version`,
    /// or `kani --version`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine_version: Option<String>,
    /// The engine binary that ran every unit, and its sha256.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine_sha256: Option<String>,
    /// The Kani install and host state of a `--engine kani` run; the
    /// counterpart of [`Self::attestation`]. Absent on trust-mc runs.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kani_attestation: Option<KaniAttestation>,
    /// The classification rules every row in the file was scored under
    /// ([`SCORER_VERSION`]); 1 for a sidecar written before the field existed.
    #[serde(default = "scorer_version_before_the_field")]
    pub scorer_version: u32,
    /// The reports directory each row's `log_path` is relative to. Absent on
    /// sidecars written before logs were captured.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub log_root: Option<String>,
    /// For a file `rescore` wrote: the results file it was scored from.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rescored_from: Option<String>,
    /// The compiler route of the run (`--route`). Absent on sidecars written
    /// before the flag existed (DevCli runs).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub route: Option<String>,
    /// What a `--route trustc` run compiled with. Absent on DevCli runs.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub route_attestation: Option<RouteAttestation>,
}

impl Provenance {
    /// The engine that produced the run: the recorded one, or trust-mc for a
    /// sidecar written before the field existed.
    pub fn engine(&self) -> Engine {
        self.engine.unwrap_or(Engine::TrustMc)
    }
}

/// The host's load at one instant (plan D18): what else was competing for the
/// machine while a run was measured, so a wall time can be read against it.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
pub struct HostLoad {
    /// 1/5/15-minute load average (`/proc/loadavg`; `sysctl vm.loadavg` on macOS).
    pub loadavg: Option<[f64; 3]>,
    /// Live processes per name in `env::COMPETING_PROCESS_NAMES` (`cargo`,
    /// `rustc`, `trust-mc-driver`, `kani-driver`), EXCLUDING this runner and
    /// its own descendants — i.e. the host's other builds and verifiers.
    /// `None` where `/proc` is unavailable.
    pub competing: Option<BTreeMap<String, u64>>,
    /// Matching processes that were this run's own descendants, left out of
    /// `competing`.
    pub own_excluded: u64,
    /// Where the sample came from: `/proc` or `sysctl`.
    pub source: String,
}

/// The Kani install a `--engine kani` run used, and the host state around it.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct KaniAttestation {
    /// The `kani` launcher that ran every single-file unit, and its sha256.
    pub kani_path: String,
    pub kani_sha256: String,
    /// First line of `kani --version`.
    pub kani_version: String,
    /// How the launcher was found: `KANI_BIN` or `~/.cargo/bin`.
    pub kani_source: String,
    /// The `cargo-kani` beside it (cargo units), and its sha256.
    pub cargo_kani_path: String,
    pub cargo_kani_sha256: String,
    /// The Kani home the launcher dispatches into (`$KANI_HOME`, else
    /// `~/.kani/kani-<version>`), when it exists.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kani_home: Option<String>,
    /// That home's `rust-toolchain-version`: the nightly Kani compiles with.
    /// The runner never forces a toolchain on a Kani child.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kani_toolchain: Option<String>,
    /// The Kani corpus checkout the run read.
    pub kani_dir: String,
    /// 1/5/15-minute load average when the run started and finished.
    pub load_average_start: Option<[f64; 3]>,
    #[serde(default)]
    pub load_average_end: Option<[f64; 3]>,
    /// Host load when the run started and when it finished (plan D18): load
    /// average plus the concurrent cargo / rustc / trust-mc-driver /
    /// kani-driver processes outside the run. Absent on sidecars written before
    /// 2026-09-14; `burndown` refuses to ledger an attested run without both.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_start: Option<HostLoad>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_end: Option<HostLoad>,
    /// `TRUST_MC_JOBS` as exported to every verifier child (the run's
    /// `--jobs`). The driver sizes its in-process solver's memory cap by it, so
    /// a resume across a different value is refused. Absent on sidecars written
    /// before 2026-09-14, whose children did not receive it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_mc_jobs: Option<usize>,
    /// Toolchain/cargo selectors present in the runner's environment and
    /// removed from every Kani child (see `env::SCRUBBED_CHILD_ENV`).
    #[serde(default)]
    pub child_env_scrubbed: Vec<String>,
}

/// The artifacts a `--route trustc` run compiled with, read and cross-checked
/// before the first unit (`route::attest_trustc`). Every unit's
/// `[AY:COMPILER_ROUTE]` marker must name the same trustc, commit, rustc driver,
/// backend sha256 and KEY, or its row is `error`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
pub struct RouteAttestation {
    /// Always `trustc`.
    pub route: String,
    /// The canonical trustc passed as `--trustc`, its sha256 and `-vV` commit-hash.
    pub trustc_path: String,
    #[serde(default)]
    pub trustc_sha256: Option<String>,
    #[serde(default)]
    pub trustc_commit: Option<String>,
    /// `trustc --print sysroot`, and the numbered seal build that directory is.
    #[serde(default)]
    pub trust_sysroot: Option<String>,
    #[serde(default)]
    pub trust_seal_build: Option<String>,
    /// The seal PROVENANCE: its sha256, `reported_commit` and `artifact_driver_sha256`.
    #[serde(default)]
    pub seal_provenance_sha256: Option<String>,
    #[serde(default)]
    pub seal_reported_commit: Option<String>,
    #[serde(default)]
    pub seal_artifact_driver_sha256: Option<String>,
    /// The sysroot's one `lib/librustc_driver-*` and the sha256 of its installed bytes.
    #[serde(default)]
    pub rustc_driver_name: Option<String>,
    #[serde(default)]
    pub installed_driver_sha256: Option<String>,
    /// The KEY directory exported as `TRUST_MC_SYSROOT`, and from its `KEY.json`:
    /// the file's sha256, the KEY name, where the KEY came from (`key_source`,
    /// the seal PROVENANCE and its class), the driver sha256 it is keyed by, the
    /// installed driver sha256 it is bound to, and the library grade.
    pub key_dir: String,
    #[serde(default)]
    pub key: Option<String>,
    #[serde(default)]
    pub key_json_sha256: Option<String>,
    #[serde(default)]
    pub key_source: Option<String>,
    /// KEY.json `source.kind`: where the Kani library's sources came from
    /// (`seal-trust-src`, the component the seal ships, or a trust checkout).
    #[serde(default)]
    pub key_source_kind: Option<String>,
    #[serde(default)]
    pub key_driver_sha256: Option<String>,
    #[serde(default)]
    pub key_installed_driver_sha256: Option<String>,
    #[serde(default)]
    pub key_provenance: Option<String>,
    #[serde(default)]
    pub key_provenance_class: Option<String>,
    /// `parity` (build-std) or `smoke` (prebuilt dist std); only parity counts (T1-D5).
    #[serde(default)]
    pub library_mode: Option<String>,
    /// The trust-mc HEAD and dirty state `build-keyed` recorded for the KEY.
    #[serde(default)]
    pub key_trust_mc_head: Option<String>,
    #[serde(default)]
    pub key_trust_mc_dirty: Option<bool>,
    /// The KEY's target (harness posture) and host rustflags.
    #[serde(default)]
    pub harness_posture: Vec<String>,
    #[serde(default)]
    pub host_posture: Vec<String>,
    /// The backend dylib passed as `--backend-dylib`, its sha256 and the
    /// `librustc_driver-*` it links.
    pub backend_dylib_path: String,
    #[serde(default)]
    pub backend_dylib_sha256: Option<String>,
    #[serde(default)]
    pub backend_linked_rustc_driver: Option<String>,
    /// `tools/tuple-check --json` with the route's sysroot held: `pass`,
    /// `fail: <ids>` or `unavailable: <why>`. Anything but `pass` makes the run
    /// uncounted: a row from other inputs is not a row of the tuple.
    #[serde(default)]
    pub tuple_check: Option<String>,
    /// No preflight error, a parity KEY and a passing tuple-check. Only counted
    /// runs append to the ledger (`score::ledger_refusal` names which of the
    /// three failed).
    #[serde(default)]
    pub counted: bool,
    /// Why the runner's preflight rejects these artifacts. Non-empty means every
    /// row of the run is `error` and the driver never ran.
    #[serde(default)]
    pub preflight_errors: Vec<String>,
    /// How the runner rewrote harness names before scoring (temporary; see
    /// `route::strip_crate_qualified_harness_names`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub harness_name_normalization: Option<String>,
}

/// The runner attestation: the exact verifier and solver binaries a run used
/// and the host state around it, so a ledger row can be tied to artifacts and
/// never to "whatever was on PATH". Kept separate from the historical tuple
/// fields so older sidecars still deserialize.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct RunnerAttestation {
    /// The `trust-mc-driver` binary that ran every unit.
    pub driver_path: String,
    pub driver_sha256: String,
    /// First line of `trust-mc-driver --version`.
    pub driver_version: String,
    /// The `trust-mc-compiler` the driver runs as `RUSTC` (the driver's
    /// sibling, else `<sysroot>/bin`) and its sha256. Most of a verdict is
    /// produced there, so a rebuilt compiler behind an unchanged driver must
    /// not attest identically.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compiler_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compiler_sha256: Option<String>,
    /// The `TRUST_MC_SYSROOT` exported to the driver.
    pub sysroot: String,
    /// The `ay` binary put first on the driver's PATH and exported to it as
    /// `TRUST_MC_AY_BIN`.
    pub ay_binary_path: String,
    /// How it was found: `AY_BIN`, `TRUST_MC_AY_BIN`, `pinned-cache`, `sibling`, or `PATH`.
    pub ay_binary_source: String,
    /// trust-mc's pinned toolchain channel (`rust-toolchain.toml`).
    pub trust_toolchain: String,
    /// `commit-hash` of the trustc `scripts/resolve-trust-tool.sh trustc` resolved:
    /// the channel's, or the `TRUST_MC_TRUST_TOOLCHAIN` override's when one is set.
    pub trust_toolchain_commit: String,
    /// `TRUST_MC_TRUST_TOOLCHAIN` when the run held a Trust build with it. Absent
    /// when unset, and on sidecars written before it was recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_toolchain_override: Option<String>,
    /// The resolved Trust sysroot (`scripts/resolve-trust-tool.sh sysroot`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_sysroot: Option<String>,
    /// The seal build that sysroot is, when it is a numbered seal directory.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_seal_build: Option<String>,
    /// `artifact_driver_sha256` from that sysroot's PROVENANCE.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_artifact_driver_sha256: Option<String>,
    /// The ay checkout trust-mc's `[patch]` links, its HEAD and dirty flag.
    pub ay_tree: String,
    pub ay_tree_head: String,
    pub ay_tree_dirty: Option<bool>,
    /// The Kani corpus checkout the run read.
    pub kani_dir: String,
    /// 1/5/15-minute load average when the run started and finished.
    pub load_average_start: Option<[f64; 3]>,
    #[serde(default)]
    pub load_average_end: Option<[f64; 3]>,
    /// Host load when the run started and when it finished (plan D18): load
    /// average plus the concurrent cargo / rustc / trust-mc-driver /
    /// kani-driver processes outside the run. Absent on sidecars written before
    /// 2026-09-14; `burndown` refuses to ledger an attested run without both.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_start: Option<HostLoad>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_end: Option<HostLoad>,
    /// `TRUST_MC_JOBS` as exported to every verifier child (the run's
    /// `--jobs`). The driver sizes its in-process solver's memory cap by it, so
    /// a resume across a different value is refused. Absent on sidecars written
    /// before 2026-09-14, whose children did not receive it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_mc_jobs: Option<usize>,
    /// Toolchain/cargo selectors present in the runner's environment and
    /// removed from every verifier child (see `env::SCRUBBED_CHILD_ENV`).
    #[serde(default)]
    pub child_env_scrubbed: Vec<String>,
}

/// A complete run report: provenance + every test's result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunReport {
    pub schema_version: u32,
    pub artifact_kind: String,
    pub provenance: Provenance,
    pub results: Vec<TestResult>,
}

/// Render a unix-epoch second count as a UTC ISO-8601 string, with no external
/// dependency (days-from-civil algorithm, Howard Hinnant).
pub fn iso8601_utc(secs: u64) -> String {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (h, mi, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    // civil_from_days: days since 1970-01-01 -> (y, m, d)
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}-{m:02}-{d:02}T{h:02}:{mi:02}:{s:02}Z")
}

/// Why the rows already in a results file cannot share `current`'s
/// attestation: every field that decides a verdict and differs from the run
/// that wrote them (`prior`). Empty means a resume may keep those rows under
/// the new attestation. `prior` must carry an attestation; one that does not
/// cannot vouch for its rows at all (the caller then records none).
///
/// The engine is compared first and always: a results file never mixes rows
/// from two engines, and a sidecar written before `--engine` existed is a
/// trust-mc file. For a Kani run the Kani install (version, launcher and
/// `cargo-kani` sha256) plays the role the driver attestation plays for
/// trust-mc.
pub fn resume_mismatch(prior: &Provenance, current: &Provenance) -> Vec<String> {
    let mut diff = Vec::new();
    let mut check = |name: &str, a: &dyn std::fmt::Debug, b: &dyn std::fmt::Debug| {
        let (a, b) = (format!("{a:?}"), format!("{b:?}"));
        if a != b {
            diff.push(format!("{name}: {a} -> {b}"));
        }
    };
    check("scorer_version", &prior.scorer_version, &current.scorer_version);
    check("engine", &prior.engine().as_str(), &current.engine().as_str());
    check("backend", &prior.backend, &current.backend);
    check("harness_timeout_s", &prior.harness_timeout_s, &current.harness_timeout_s);
    check("surface", &prior.surface, &current.surface);
    check("ay_binary_version", &prior.ay_binary_version, &current.ay_binary_version);
    match (&prior.attestation, &current.attestation) {
        (Some(a), Some(b)) => {
            check("driver_sha256", &a.driver_sha256, &b.driver_sha256);
            check("compiler_sha256", &a.compiler_sha256, &b.compiler_sha256);
            check("sysroot", &a.sysroot, &b.sysroot);
            check("ay_binary_path", &a.ay_binary_path, &b.ay_binary_path);
            check("trust_mc_jobs", &a.trust_mc_jobs, &b.trust_mc_jobs);
        }
        (None, None) => {}
        (a, b) => check("attestation", &a.is_some(), &b.is_some()),
    }
    match (&prior.kani_attestation, &current.kani_attestation) {
        (Some(a), Some(b)) => {
            check("kani_version", &a.kani_version, &b.kani_version);
            check("kani_sha256", &a.kani_sha256, &b.kani_sha256);
            check("cargo_kani_sha256", &a.cargo_kani_sha256, &b.cargo_kani_sha256);
            check("trust_mc_jobs", &a.trust_mc_jobs, &b.trust_mc_jobs);
        }
        (None, None) => {}
        (a, b) => check("kani_attestation", &a.is_some(), &b.is_some()),
    }
    check(
        "route",
        &crate::route::route_or_legacy(prior.route.as_deref()),
        &crate::route::route_or_legacy(current.route.as_deref()),
    );
    match (&prior.route_attestation, &current.route_attestation) {
        (Some(a), Some(b)) => {
            check("trustc_path", &a.trustc_path, &b.trustc_path);
            check("trustc_commit", &a.trustc_commit, &b.trustc_commit);
            check(
                "installed_driver_sha256",
                &a.installed_driver_sha256,
                &b.installed_driver_sha256,
            );
            check("key_dir", &a.key_dir, &b.key_dir);
            check("key_json_sha256", &a.key_json_sha256, &b.key_json_sha256);
            check("library_mode", &a.library_mode, &b.library_mode);
            check("backend_dylib_sha256", &a.backend_dylib_sha256, &b.backend_dylib_sha256);
        }
        (a, b) => check("route_attestation", &a.is_some(), &b.is_some()),
    }
    diff
}

#[cfg(test)]
mod tests {
    use super::*;

    fn attested(driver_sha: &str) -> Provenance {
        serde_json::from_value(serde_json::json!({
            "generated_unix": 1, "generated_iso": "x", "trust_mc_head": "h", "trust_mc_dirty": false,
            "ay_pin": "p", "ay_binary_version": "ay 0.26.0", "ay_rev_matches_pin": true,
            "kani_rev": "k", "kani_repo": "r", "backend": "chc", "harness_timeout_s": 15, "jobs": 2,
            "scopes": ["verification"], "scorer_version": SCORER_VERSION,
            "attestation": {
                "driver_path": "/b/bin/trust-mc-driver", "driver_sha256": driver_sha,
                "driver_version": "trust-mc 0.6.0", "compiler_path": "/b/bin/trust-mc-compiler",
                "compiler_sha256": "cc", "sysroot": "/b", "ay_binary_path": "/c/ay",
                "ay_binary_source": "AY_BIN", "trust_toolchain": "trust", "trust_toolchain_commit": "t",
                "ay_tree": "/ay", "ay_tree_head": "a", "ay_tree_dirty": false, "kani_dir": "/k",
                "load_average_start": [1.0, 1.0, 1.0]
            }
        }))
        .expect("attested provenance should deserialize")
    }

    /// A resume that swapped the driver (or anything else that decides a
    /// verdict) must not re-attest rows the old binaries produced; load and
    /// jobs are host state, not verifier identity.
    #[test]
    fn resume_mismatch_names_verifier_identity_changes_only() {
        let prior = attested("aa");
        let mut same = attested("aa");
        same.jobs = 8;
        same.attestation.as_mut().unwrap().load_average_start = Some([9.0, 9.0, 9.0]);
        assert!(resume_mismatch(&prior, &same).is_empty());

        // The children's TRUST_MC_JOBS sizes the driver's solver memory: a
        // different value is a different verifier configuration.
        let mut other_jobs = attested("aa");
        other_jobs.attestation.as_mut().unwrap().trust_mc_jobs = Some(3);
        let mut prior_jobs = attested("aa");
        prior_jobs.attestation.as_mut().unwrap().trust_mc_jobs = Some(6);
        assert_eq!(resume_mismatch(&prior_jobs, &other_jobs), vec!["trust_mc_jobs: Some(6) -> Some(3)".to_string()]);

        let rebuilt = attested("bb");
        let diff = resume_mismatch(&prior, &rebuilt);
        assert_eq!(diff.len(), 1, "{diff:?}");
        assert!(diff[0].starts_with("driver_sha256"), "{diff:?}");

        let mut other_compiler = attested("aa");
        other_compiler.attestation.as_mut().unwrap().compiler_sha256 = Some("dd".into());
        other_compiler.backend = "bmc".into();
        assert_eq!(resume_mismatch(&prior, &other_compiler).len(), 2);

        // A legacy sidecar (written before `compiler_*` existed) still parses.
        let mut legacy = serde_json::to_value(attested("aa")).unwrap();
        legacy["attestation"].as_object_mut().unwrap().remove("compiler_sha256");
        legacy["attestation"].as_object_mut().unwrap().remove("compiler_path");
        let legacy: Provenance = serde_json::from_value(legacy).unwrap();
        assert_eq!(legacy.attestation.unwrap().compiler_sha256, None);
    }

    fn kani_attested(kani_sha: &str) -> Provenance {
        let mut p = attested("aa");
        p.attestation = None;
        p.engine = Some(Engine::Kani);
        p.engine_version = Some("kani 0.67.0".into());
        p.engine_path = Some("/h/.cargo/bin/kani".into());
        p.engine_sha256 = Some(kani_sha.into());
        p.backend = "cbmc".into();
        p.ay_binary_version = "<n/a>".into();
        p.kani_attestation = Some(KaniAttestation {
            kani_path: "/h/.cargo/bin/kani".into(),
            kani_sha256: kani_sha.into(),
            kani_version: "kani 0.67.0".into(),
            kani_source: "~/.cargo/bin".into(),
            cargo_kani_path: "/h/.cargo/bin/cargo-kani".into(),
            cargo_kani_sha256: "ck".into(),
            kani_home: Some("/h/.kani/kani-0.67.0".into()),
            kani_toolchain: Some("nightly-2025-11-21".into()),
            kani_dir: "/k".into(),
            load_average_start: Some([1.0, 1.0, 1.0]),
            load_average_end: None,
            load_start: None,
            load_end: None,
            trust_mc_jobs: Some(2),
            child_env_scrubbed: Vec::new(),
        });
        p
    }

    fn trustc_run(backend_sha: &str) -> Provenance {
        let mut p = attested("aa");
        p.route = Some("trustc".into());
        p.route_attestation = Some(RouteAttestation {
            route: "trustc".into(),
            trustc_path: "/s/8571/bin/trustc".into(),
            trustc_commit: Some("45dc60873c4fef21649ae277a93cc8cc9cf39191".into()),
            key_dir: "/K/driver-948b36c62eacc5d1".into(),
            key_json_sha256: Some("9bd2".into()),
            library_mode: Some("parity".into()),
            backend_dylib_path: "/K/codegen-backends/librustc_codegen_trust_mc.dylib".into(),
            backend_dylib_sha256: Some(backend_sha.into()),
            counted: true,
            ..Default::default()
        });
        p
    }

    /// A results file never mixes engines: a sidecar written before `--engine`
    /// existed is a trust-mc file and refuses a Kani resume, and vice versa;
    /// two Kani runs resume only on the same Kani install.
    #[test]
    fn resume_mismatch_includes_the_engine() {
        // Pre-`--engine` sidecar (engine absent) == trust-mc: no diff.
        let legacy = attested("aa");
        assert_eq!(legacy.engine(), Engine::TrustMc);
        let mut explicit = attested("aa");
        explicit.engine = Some(Engine::TrustMc);
        assert!(resume_mismatch(&legacy, &explicit).is_empty());

        // trust-mc file, Kani run: refused, and the engine is named.
        let diff = resume_mismatch(&legacy, &kani_attested("k1"));
        assert!(diff.iter().any(|d| d.starts_with("engine: \"trust-mc\" -> \"kani\"")), "{diff:?}");

        // Same Kani install resumes; a different one does not.
        assert!(resume_mismatch(&kani_attested("k1"), &kani_attested("k1")).is_empty());
        let diff = resume_mismatch(&kani_attested("k1"), &kani_attested("k2"));
        assert!(diff.iter().any(|d| d.starts_with("kani_sha256")), "{diff:?}");
        let mut other_cargo_kani = kani_attested("k1");
        other_cargo_kani.kani_attestation.as_mut().unwrap().cargo_kani_sha256 = "zz".into();
        let diff = resume_mismatch(&kani_attested("k1"), &other_cargo_kani);
        assert_eq!(diff, vec!["cargo_kani_sha256: \"ck\" -> \"zz\""]);

        // The engine field round-trips through serde in kebab-case.
        let json = serde_json::to_value(kani_attested("k1")).unwrap();
        assert_eq!(json["engine"], "kani");
        assert!(json.get("attestation").is_none());
        assert!(serde_json::to_value(&legacy).unwrap().get("engine").is_none());
    }

    /// A results file never mixes scorer versions: a sidecar written before
    /// the field existed is version 1 and refuses a resume by the current
    /// scorer, and the row-level field reads as 1 when absent.
    #[test]
    fn resume_mismatch_includes_the_scorer_version() {
        let mut legacy = serde_json::to_value(attested("aa")).unwrap();
        legacy.as_object_mut().unwrap().remove("scorer_version");
        let legacy: Provenance = serde_json::from_value(legacy).unwrap();
        assert_eq!(legacy.scorer_version, 1);
        let diff = resume_mismatch(&legacy, &attested("aa"));
        assert_eq!(diff, vec![format!("scorer_version: 1 -> {SCORER_VERSION}")]);
        assert!(resume_mismatch(&attested("aa"), &attested("aa")).is_empty());
        let row: TestResult = serde_json::from_str(
            r#"{"suite":"kani","file":"a.rs","oracle":"success","classification":"parity"}"#,
        )
        .unwrap();
        assert_eq!(row.scorer_version, 1);
        assert!(!row.tiebreak_applied);
        assert_eq!(row.log_path, None);
    }

    /// Rows written before the resource fields existed still parse, with the
    /// additive fields at their "no data" values.
    #[test]
    fn old_rows_parse_without_resource_fields() {
        let row: TestResult = serde_json::from_str(
            r#"{"suite":"kani","file":"a.rs","oracle":"success","observed":"success","classification":"parity","duration_ms":12}"#,
        )
        .unwrap();
        assert_eq!((row.wall_ms, row.max_rss_kb, row.tree_peak_rss_kb), (0, 0, None));
        assert_eq!((row.certified_no_checks, row.upstream_ignored), (0, false));
        // And a serialized row without a tree sample omits the key.
        let json = serde_json::to_value(&row).unwrap();
        assert!(json.get("tree_peak_rss_kb").is_none());
        assert!(json.get("certified_no_checks").is_none() && json.get("upstream_ignored").is_none());
        assert_eq!(json["wall_ms"], 0);
    }

    /// A resume across routes, a rebuilt backend, another trustc or another KEY
    /// must not re-attest rows the earlier artifacts produced.
    #[test]
    fn resume_mismatch_names_route_and_backend_changes() {
        let prior = trustc_run("6edf");
        assert!(resume_mismatch(&prior, &trustc_run("6edf")).is_empty());

        let diff = resume_mismatch(&prior, &trustc_run("0000"));
        assert_eq!(
            diff,
            vec!["backend_dylib_sha256: Some(\"6edf\") -> Some(\"0000\")".to_string()]
        );

        let mut dev_cli = attested("aa");
        dev_cli.route = Some("dev-cli".into());
        let diff = resume_mismatch(&prior, &dev_cli);
        assert!(diff.iter().any(|d| d.starts_with("route: \"trustc\" -> \"dev-cli\"")), "{diff:?}");
        assert!(diff.iter().any(|d| d.starts_with("route_attestation")), "{diff:?}");

        let mut other = trustc_run("6edf");
        let att = other.route_attestation.as_mut().unwrap();
        att.trustc_commit = Some("25ccaf01f102fe3b4127dabeffbeba7f55516b5a".into());
        att.key_json_sha256 = Some("ffff".into());
        att.library_mode = Some("smoke".into());
        let diff = resume_mismatch(&prior, &other);
        for field in ["trustc_commit", "key_json_sha256", "library_mode"] {
            assert!(diff.iter().any(|d| d.starts_with(field)), "{field}: {diff:?}");
        }

        // A sidecar written before `--route` (no route) is a DevCli run.
        let mut legacy = attested("aa");
        legacy.route = None;
        assert!(resume_mismatch(&legacy, &dev_cli).is_empty());
    }

    /// A v2 sidecar (runner attestation, no route fields) still loads, reads as
    /// DevCli, and serializes back without route keys.
    #[test]
    fn provenance_v2_sidecar_loads() {
        let v2 = serde_json::to_value(attested("aa")).unwrap();
        assert!(v2.get("route").is_none() && v2.get("route_attestation").is_none());
        let loaded: Provenance = serde_json::from_value(v2.clone()).unwrap();
        assert_eq!(loaded.route, None);
        assert_eq!(crate::route::route_or_legacy(loaded.route.as_deref()), "dev-cli");
        assert!(loaded.route_attestation.is_none());
        assert_eq!(serde_json::to_value(&loaded).unwrap(), v2);

        let v3 = serde_json::to_value(trustc_run("6edf")).unwrap();
        assert_eq!(v3["route"], "trustc");
        assert_eq!(v3["route_attestation"]["backend_dylib_sha256"], "6edf");
        let back: Provenance = serde_json::from_value(v3).unwrap();
        assert_eq!(back.route_attestation, trustc_run("6edf").route_attestation);

        // A row written before `--route` loads with no route.
        let row: TestResult = serde_json::from_str(
            r#"{"suite":"kani","file":"a.rs","oracle":"success","observed":"success","classification":"parity"}"#,
        )
        .unwrap();
        assert_eq!(row.route, None);
    }
}

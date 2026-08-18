// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core data model for the Kani-domination parity harness: verdicts, the
//! per-test classification taxonomy, run reports and provenance.

use serde::{Deserialize, Serialize};

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
    /// `[AY:EFFECTIVE_SUCCESS]`). Verdict matches but it is not a real proof.
    UnsoundPass,
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
            Classification::FalsePositive => "false_positive",
            Classification::Unsupported => "unsupported",
            Classification::EncodingGap => "encoding_gap",
            Classification::MissedBug => "missed_bug",
            Classification::ExceedsOracle => "exceeds_oracle",
            Classification::Unknown => "unknown",
            Classification::Error => "error",
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
    /// `[AY:UNKNOWN_REASON:…]` (e.g. `SolverError`, `Timeout`,
    /// `PreSolveDeadline`, `UndecidedModel`).
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
    /// Wall-clock of the trust-mc invocation, milliseconds.
    #[serde(default)]
    pub duration_ms: u64,
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

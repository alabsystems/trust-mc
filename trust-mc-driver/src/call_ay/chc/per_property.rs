// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Per-property (BSEM-18) CHC solve seam.
//!
//! # What this replaces
//!
//! The native CHC lane used to solve ONE aggregate `(query error)` problem and
//! reduce it to a single all-or-nothing harness verdict: a harness with twenty
//! checks was PROVED only if the conjunction was proved, and a single
//! undecidable check made all twenty undetermined with no way to say which one
//! was the problem.
//!
//! AY exposes the exact decomposition instead. [`ChcProblem::query_obligations`]
//! unfolds the BSEM-18 encoding
//!
//! ```text
//! error_p0 => error
//! error_p1 => error
//! error     => false
//! ```
//!
//! into one independently solvable, backwards-sliced problem per `error_pN`,
//! each carrying a stable [`ay::chc::ChcQueryObligationId`] whose `label` is
//! exactly the `error_pN` relation the VC artifact records for that check. That
//! label is the correlation key back to the per-property report table.
//!
//! # Fail-closed reduction (the whole point)
//!
//! * **Any `Unsafe` row fails the harness.** A validated counterexample for one
//!   property refutes the harness whatever the other rows did.
//! * **PROOF only when EVERY row is proved with acceptable evidence.** A row is
//!   proved only when AY's own [`ChcProofRunStopReason::Definitive`] accompanies
//!   a `Safe` result, and (unless `--ay-chc-skip-verify`) only after that row's
//!   invariant model passes the independent external re-validation gate against
//!   that row's own problem.
//! * **`Unknown` rows and row errors stay visible.** They are printed as
//!   `[AY:CHC-ROW:…]` lines and recorded in the execution envelope. They are
//!   never replaced by "the last result", and they never round up to a proof.
//! * **`Ok([])`** is AY's documented all-queries-pruned case. It carries no
//!   surviving property IDs, so it is bound through Trust-MC's existing
//!   source-property / vacuity accounting (`interpret_chc_trivial_safe`, which
//!   reads the VC artifact table and honours the vacuous-checks marker) rather
//!   than by manufacturing credited per-property solver rows here.
//! * **An AY-rejected problem stays an encoder defect.** `query_obligations`
//!   validates before slicing; its typed error is reported with the
//!   `Failed to parse CHC problem` wording that
//!   [`crate::verification_provenance::SolverUnknownReason::from_chc_error`]
//!   files as `ChcParseError`, not as an undecided solve.
//!
//! # Why not `ay_encode::invoke::solve_query_obligations_with_cancellation`
//!
//! That helper is exactly `problem.query_obligations()?` followed by
//! `solve_with_cancellation` per row, and it hands back an `AyVerdict` — the
//! frontend-neutral verdict — for each. Under `ProofMode::None` an `AyVerdict`
//! carries no certificate, no `stop_reason`, no adaptive trace, and no
//! problem-bound `ChcPdrProofRun`. Consuming it would have thrown away three
//! things this driver is required to keep:
//!
//! 1. the checked transcript/digest/replay metadata that
//!    `harness_runner::trust_trust_mc_chc_pdr_evidence_payload` validates
//!    (Trust-MC's existing fail-closed proof consumer);
//! 2. the `stop_reason()`/`adaptive_trace()` classification that gives the
//!    `[AY:UNKNOWN-CATEGORY]` line a real budget report instead of the `None`
//!    the old seam always passed;
//! 3. the "acceptable evidence" bar for a proved row, which is defined in terms
//!    of AY's own `ChcProofRunStopReason::Definitive`.
//!
//! So this module performs the same slicing with the same public API call
//! (`query_obligations`, which is that helper's first line) and then drives each
//! row through `solve_with_proof_report_with_cancellation`, the authoritative
//! proof-and-telemetry entry point. That is ONE solve per row — no reporting-only
//! re-solve — and every field describes the invocation that produced the row's
//! verdict.
//!
//! # Cancellation (adoption step 7)
//!
//! Every row is solved through
//! [`ay_encode::invoke::solve_with_proof_report_with_cancellation`], which
//! constructs the portfolio with `AdaptivePortfolio::new_for_solve_with_cancellation`
//! — the parent token and the authoritative clock therefore exist BEFORE
//! constructor preprocessing (dead-end stripping, array scalarization), so a
//! guard that fires during preprocessing stops it at the next stage boundary.
//!
//! The invocation is JOINED: it runs synchronously on this thread, so the batch
//! never advances to the next obligation — nor the driver to the next harness —
//! while a cancelled solve is still winding down. This deliberately retires the
//! old detached-thread guard (`std::thread::spawn` + `recv_timeout` + cancel +
//! bounded drain + orphan). That workaround bought liveness by letting an
//! abandoned solve overlap the work that came after it; AY's guidance is
//! explicit that a consumer must not do that, because the synchronous isolation
//! barrier may exceed the nominal timeout.
//!
//! The liveness backstop that made the drain-and-orphan hack tolerable is still
//! in place and is now the ONLY one: [`crate::wall_clock_watchdog`] is armed
//! from `main()` in its own thread, prints honest UNKNOWN markers and hard-exits
//! the process if a non-cooperative engine wedges. Panic isolation is preserved
//! without a thread by `catch_unwind` around each row.
//!
//! # Budget
//!
//! `EncodeConfig::timeout` is a PER-OBLIGATION budget, so a naive batch of `N`
//! rows would cost `N * timeout`. The batch is therefore bounded by the same
//! total solve budget the aggregate solve used to get: each row is given
//! `min(cap, batch_remaining / rows_left)`, so unused time from an easy row
//! rolls forward to the hard ones and the whole batch still fits inside the
//! per-harness deadline.

use std::collections::HashSet;
use std::time::{Duration, Instant};

use ay::chc::{
    AdaptiveExecutionMode, CancellationToken, ChcProblem, ChcProofRunStopReason, LemmaHint,
    VerifiedChcResult, VerifiedCounterexample, VerifiedInvariant,
};

use super::native::{
    BudgetSummary, RowModelValidation, panic_payload_message, reject_false_proof,
    validate_row_invariant_model,
};
use super::row_export::{RowExport, RowGrant, RowQuery};

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        if !crate::args::common::quiet_output() {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            let _ = writeln!(handle, $($arg)*);
        }
    }};
}

/// Schema of the per-property execution envelope published on
/// `VerificationResult::proof_transcript_metadata` for a multi-row batch.
///
/// DELIBERATELY NOT `ay.chc-proof-transcript/v1`: that schema means "this
/// object describes the one solve that decided this harness", and
/// `harness_runner::trust_trust_mc_chc_pdr_evidence_payload` reads
/// `accepted_as_proof` / `result` / `replay.status` / `transcript.status` out of
/// it to decide Route-B admission. Publishing one row's transcript under that
/// schema for an N-row harness would let evidence about ONE property admit a
/// claim about all N — fail-open. A multi-row batch therefore publishes this
/// schema instead, which the checked consumer rejects (`unexpected_schema`)
/// while still carrying every row's disposition for diagnosis.
pub(super) const PER_PROPERTY_ENVELOPE_SCHEMA: &str = "trust_mc.chc-per-property-solve/v1";

/// Key under which a single-row batch attaches the execution envelope to that
/// row's own AY transcript metadata. Additive: the checked consumer reads only
/// the AY fields it knows, so its behaviour on a single-property harness is
/// byte-for-byte what it was before per-property solving.
pub(super) const EXECUTION_ENVELOPE_KEY: &str = "trust_mc_per_property";

/// Env override for deterministic engine ordering, checked after the CLI flag.
pub(super) const DETERMINISTIC_ENV: &str = "TRUST_MC_AY_CHC_DETERMINISTIC";
/// AY's own deterministic switch, which `AdaptiveConfig::default()` honours
/// implicitly. The driver reads it explicitly so the selection is recorded.
pub(super) const AY_DETERMINISTIC_ENV: &str = "AY_DETERMINISTIC";

/// Grace added to the batch budget before the cooperative cancellation clock
/// fires. Mirrors the `+5s` the retired detached-thread guard used.
const BATCH_GUARD_GRACE: Duration = Duration::from_secs(5);

/// Stable phrase that marks a BUDGET-bound undecided batch.
///
/// The retired detached-thread guard bailed with "exceeded guard timeout", which
/// [`crate::verification_provenance::SolverUnknownReason::from_chc_error`] files
/// as `Timeout`. The cooperative batch clock never produces that wording, so it
/// publishes this phrase instead and `from_chc_error` matches it — otherwise a
/// decomposed timeout would be counted as a solver error.
pub(super) const BATCH_BUDGET_EXHAUSTED_PHRASE: &str = "solve budget exhausted: ";

/// Cap on adaptive-trace stages recorded per row, so a long portfolio run
/// cannot blow up the hex-encoded metadata marker.
const MAX_RECORDED_STAGES: usize = 16;

// ─────────────────────────────────────────────────────────────────────────────
// Deterministic mode as an explicit gate input (adoption step 6)
// ─────────────────────────────────────────────────────────────────────────────

/// Where the deterministic-mode decision came from. Recorded in the envelope so
/// a reproducibility run can be told apart from an ordinary adaptive one after
/// the fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DeterministicSource {
    /// `--ay-chc-deterministic` on the command line.
    Cli,
    /// `TRUST_MC_AY_CHC_DETERMINISTIC` in the environment.
    TrustMcEnv,
    /// `AY_DETERMINISTIC` in the environment (AY's own switch).
    AyEnv,
    /// Nothing asked for determinism; adaptive parallel is the default.
    Default,
}

impl DeterministicSource {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Cli => "cli:--ay-chc-deterministic",
            Self::TrustMcEnv => "env:TRUST_MC_AY_CHC_DETERMINISTIC",
            Self::AyEnv => "env:AY_DETERMINISTIC",
            Self::Default => "default",
        }
    }
}

/// The resolved execution policy for this run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ExecutionEnvelope {
    pub(super) mode: AdaptiveExecutionMode,
    pub(super) source: DeterministicSource,
}

impl ExecutionEnvelope {
    pub(super) fn mode_label(self) -> &'static str {
        match self.mode {
            AdaptiveExecutionMode::DeterministicSequential => "deterministic-sequential",
            AdaptiveExecutionMode::AdaptiveParallel => "adaptive-parallel",
        }
    }

    pub(super) fn is_deterministic(self) -> bool {
        matches!(self.mode, AdaptiveExecutionMode::DeterministicSequential)
    }
}

/// AY's truthiness spelling for its own `AY_DETERMINISTIC` switch, reused so a
/// value that turns determinism on for AY turns it on here too.
fn env_flag_is_true(value: &str) -> bool {
    matches!(value.trim().to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on")
}

/// Resolve deterministic mode from the explicit driver inputs, most specific
/// first. ADAPTIVE PARALLEL STAYS THE DEFAULT for ordinary runs; determinism is
/// only ever selected because a caller asked for it.
pub(super) fn resolve_execution_envelope(
    cli_flag: bool,
    trust_mc_env: Option<&str>,
    ay_env: Option<&str>,
) -> ExecutionEnvelope {
    let source = if cli_flag {
        DeterministicSource::Cli
    } else if trust_mc_env.is_some_and(env_flag_is_true) {
        DeterministicSource::TrustMcEnv
    } else if ay_env.is_some_and(env_flag_is_true) {
        DeterministicSource::AyEnv
    } else {
        DeterministicSource::Default
    };
    let mode = match source {
        DeterministicSource::Default => AdaptiveExecutionMode::AdaptiveParallel,
        _ => AdaptiveExecutionMode::DeterministicSequential,
    };
    ExecutionEnvelope { mode, source }
}

/// Read the resolved execution envelope from the process environment plus the
/// CLI flag.
pub(super) fn execution_envelope_from_env(cli_flag: bool) -> ExecutionEnvelope {
    let trust_mc = std::env::var(DETERMINISTIC_ENV).ok();
    let ay = std::env::var(AY_DETERMINISTIC_ENV).ok();
    resolve_execution_envelope(cli_flag, trust_mc.as_deref(), ay.as_deref())
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-row classification (adoption steps 3 + 4)
// ─────────────────────────────────────────────────────────────────────────────

/// The shape of one row's verified result, decoupled from AY's sealed types so
/// the classifier is unit-testable without a solver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RowResultShape {
    Safe,
    Unsafe,
    Unknown,
}

/// What one obligation row contributes to the harness verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RowOutcomeKind {
    /// Proved with acceptable evidence.
    Proved,
    /// Refuted by a validated counterexample.
    Refuted,
    /// Not decided. Never rounds up to either of the above.
    Unknown,
    /// The invocation itself failed (typed AY error, panic, cancelled before
    /// start). Visible, and blocks a proof exactly like `Unknown`.
    Error,
}

impl RowOutcomeKind {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Refuted => "refuted",
            Self::Unknown => "unknown",
            Self::Error => "error",
        }
    }
}

pub(super) fn stop_reason_label(stop: ChcProofRunStopReason) -> &'static str {
    match stop {
        ChcProofRunStopReason::Definitive => "definitive",
        ChcProofRunStopReason::BudgetExhausted => "budget-exhausted",
        ChcProofRunStopReason::ExternallyCancelled => "externally-cancelled",
        ChcProofRunStopReason::Inconclusive => "inconclusive",
        _ => "unclassified",
    }
}

/// Classify one row from AY's `stop_reason()` and the verified result shape.
///
/// FAIL-CLOSED RULES:
/// * `Safe` counts as proved ONLY under `Definitive`. AY's own classifier gives
///   a definitive verdict precedence over a concurrent cancellation request, so
///   a `Safe` result reached under a cancellation race is still definitive; a
///   `Safe` that AY did NOT call definitive is a contradiction we refuse to
///   credit rather than resolve in the solver's favour.
/// * `Unsafe` refutes the harness under every stop reason. AY documents that
///   cancellation "can never flip Safe/Unsafe", so a counterexample is a
///   counterexample; suppressing it would hide a real bug.
/// * Everything else is `Unknown`, carrying the stop reason as its detail so
///   budget exhaustion, external cancellation and genuine inconclusiveness stay
///   distinguishable in the report.
pub(super) fn classify_row(
    shape: RowResultShape,
    stop: ChcProofRunStopReason,
) -> (RowOutcomeKind, String) {
    match shape {
        RowResultShape::Unsafe => {
            (RowOutcomeKind::Refuted, format!("counterexample ({})", stop_reason_label(stop)))
        }
        RowResultShape::Safe if matches!(stop, ChcProofRunStopReason::Definitive) => {
            (RowOutcomeKind::Proved, "definitive safe".to_string())
        }
        RowResultShape::Safe => (
            RowOutcomeKind::Unknown,
            format!(
                "safe result was not definitive (stop_reason={}) — refusing to credit it",
                stop_reason_label(stop)
            ),
        ),
        RowResultShape::Unknown => {
            (RowOutcomeKind::Unknown, format!("undecided ({})", stop_reason_label(stop)))
        }
    }
}

/// One obligation's recorded disposition. Pure data — this is what lands in the
/// per-harness report where the all-or-nothing conjunction verdict used to be.
#[derive(Clone, Debug)]
pub(super) struct RowRecord {
    /// AY's stable obligation label (`error_pN` for BSEM-18 encodings).
    pub(super) label: String,
    /// The VC-artifact relation this row adjudicates, when the label correlates.
    pub(super) relation: Option<String>,
    /// SHA-256 of the row's deterministic normalized CHC input.
    pub(super) content_sha256: String,
    pub(super) outcome: RowOutcomeKind,
    pub(super) detail: String,
    pub(super) stop_reason: Option<&'static str>,
    pub(super) cancellation_requested: bool,
    pub(super) elapsed_ms: u128,
    pub(super) budget_ms: u128,
    pub(super) adaptive_stages: Vec<String>,
    /// Compact digest of the row's AY transcript metadata (never the whole
    /// object: a multi-row envelope is hex-encoded into a stdout marker).
    pub(super) ay_metadata: Option<serde_json::Value>,
}

impl RowRecord {
    /// An undecided row whose stop reason is the budget (including a row the
    /// batch could not fund at all): the second pass's candidates.
    fn is_budget_bound_unknown(&self) -> bool {
        self.outcome == RowOutcomeKind::Unknown && self.stop_reason == Some("budget-exhausted")
    }

    fn ident(&self) -> RowIdent {
        RowIdent {
            label: self.label.clone(),
            relation: self.relation.clone(),
            content_sha256: self.content_sha256.clone(),
        }
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "label": self.label,
            "relation": self.relation,
            "content_sha256": self.content_sha256,
            "outcome": self.outcome.label(),
            "detail": self.detail,
            "stop_reason": self.stop_reason,
            "cancellation_requested_at_return": self.cancellation_requested,
            "elapsed_ms": self.elapsed_ms,
            "budget_ms": self.budget_ms,
            "adaptive_stages": self.adaptive_stages,
            "ay_transcript_metadata": self.ay_metadata,
        })
    }

    fn marker_line(&self) -> String {
        format!(
            "[AY:CHC-ROW:{outcome}] {label}{relation} — {detail} \
             (stop_reason={stop}, {elapsed}ms/{budget}ms)",
            outcome = self.outcome.label(),
            label = self.label,
            relation = self
                .relation
                .as_deref()
                .filter(|relation| *relation != self.label)
                .map(|relation| format!(" [{relation}]"))
                .unwrap_or_default(),
            detail = self.detail,
            stop = self.stop_reason.unwrap_or("none"),
            elapsed = self.elapsed_ms,
            budget = self.budget_ms,
        )
    }
}

/// The harness-level reduction of a batch of rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum BatchVerdict {
    /// Index of the first refuting row. Any `Unsafe` row fails the harness.
    Refuted(usize),
    /// Every required row was proved with acceptable evidence.
    Proved,
    /// Not a proof and not a refutation; the string summarises why.
    Undecided(String),
}

/// Reduce per-row outcomes to the harness verdict.
///
/// PRECEDENCE: refutation first (a validated counterexample stands whatever the
/// other rows did), then the all-proved conjunction, then undecided. An empty
/// row list is UNDECIDED here — `Ok([])` is handled by the caller through the
/// vacuity accounting and never reaches this function as "vacuously proved".
pub(super) fn reduce_rows(rows: &[RowRecord]) -> BatchVerdict {
    if let Some(index) = rows.iter().position(|row| row.outcome == RowOutcomeKind::Refuted) {
        return BatchVerdict::Refuted(index);
    }
    if rows.is_empty() {
        return BatchVerdict::Undecided("no query obligations survived to be solved".to_string());
    }
    if rows.iter().all(|row| row.outcome == RowOutcomeKind::Proved) {
        return BatchVerdict::Proved;
    }
    let unknown = rows.iter().filter(|row| row.outcome == RowOutcomeKind::Unknown).count();
    let errored = rows.iter().filter(|row| row.outcome == RowOutcomeKind::Error).count();
    let proved = rows.iter().filter(|row| row.outcome == RowOutcomeKind::Proved).count();
    let blocking = || {
        rows.iter()
            .filter(|row| matches!(row.outcome, RowOutcomeKind::Unknown | RowOutcomeKind::Error))
    };
    let first_blocking = blocking()
        .next()
        .map(|row| format!("{} ({})", row.label, row.detail))
        .unwrap_or_else(|| "unattributed".to_string());
    // Attribution parity with the retired guard: when every blocking row ran out
    // of clock rather than failing, say so with the stable phrase
    // `SolverUnknownReason::from_chc_error` files as budget-bound. Without it a
    // decomposed timeout would be bucketed as a solver error, which is the
    // mislabelling that made `SolverError` a catch-all in the first place.
    let budget_bound = blocking().all(|row| {
        matches!(row.stop_reason, Some("budget-exhausted") | Some("externally-cancelled"))
    });
    let prefix = if budget_bound { BATCH_BUDGET_EXHAUSTED_PHRASE } else { "" };
    BatchVerdict::Undecided(format!(
        "{prefix}{proved}/{total} properties proved, {unknown} undecided, {errored} errored; \
         first blocking obligation: {first_blocking}",
        total = rows.len(),
    ))
}

// ─────────────────────────────────────────────────────────────────────────────
// Correlation back to the VC property artifact
// ─────────────────────────────────────────────────────────────────────────────

/// Recover the VC-artifact relation name (`error_p{id}`) from AY's obligation
/// label.
///
/// AY labels an unfolded BSEM-18 obligation with the nullary marker's own name
/// (`error_p7`). If the marker itself had to be unfolded a second level — which
/// happens when the problem reaching AY has already had `error => false`
/// expanded away — the label becomes `error_p7_definition_3`. Both forms
/// correlate to the same artifact row, so the trailing `_definition_<n>` is
/// stripped.
///
/// Returns `None` for anything that is not a per-property error relation (a
/// direct false-head query, an `error`-only encoding, a pre-BSEM-18 artifact),
/// so the caller falls back to the legacy aggregate report line rather than
/// inventing a correlation.
pub(super) fn vc_relation_for_obligation_label(label: &str) -> Option<String> {
    if !label.starts_with("error_p") {
        return None;
    }
    let base = match label.rsplit_once("_definition_") {
        Some((base, suffix))
            if !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()) =>
        {
            base
        }
        _ => label,
    };
    if base.len() <= "error_p".len() { None } else { Some(base.to_string()) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Budget allocation
// ─────────────────────────────────────────────────────────────────────────────

/// Budget for the next obligation: an even share of what is left of the batch
/// budget, capped by the configured per-solve timeout.
///
/// Sharing what REMAINS (rather than a fixed `total / N`) lets time unused by an
/// easy row roll forward to the hard ones, while the batch as a whole can never
/// exceed the budget the aggregate solve used to receive — which is what keeps
/// the per-harness deadline honest under decomposition.
pub(super) fn per_obligation_budget(
    batch_remaining: Duration,
    rows_left: usize,
    cap: Duration,
) -> Duration {
    if rows_left == 0 {
        return Duration::ZERO;
    }
    let divisor = u32::try_from(rows_left).unwrap_or(u32::MAX);
    (batch_remaining / divisor).min(cap)
}

/// How the post-row re-validation of proved models is budgeted.
#[derive(Clone, Copy, Debug)]
enum ValidationPhase {
    /// Every row proved: the models decide the verdict, so each validation
    /// keeps the per-harness deadline (`row_validation_timeout`).
    DecidesTheVerdict,
    /// The batch is undecided whatever the models say: the whole phase draws
    /// from one batch budget, and a row it cannot fund is not credited.
    UndecidedBatch { phase_deadline: crate::deadline::Deadline },
}

/// AY's own validation default, kept as the cap.
pub(super) const ROW_VALIDATION_CAP: Duration = Duration::from_secs(30);
/// The least a validation is ever given, even on a spent deadline: the
/// harness deadline sits 10s inside the process watchdog, and a validation
/// that is not run cannot be counted as passed — so it is run, briefly, and
/// a timeout fails closed through the established wording.
pub(super) const ROW_VALIDATION_FLOOR: Duration = Duration::from_secs(5);

/// Budget for re-validating one proved row's model: what is left of the
/// per-harness deadline, never above AY's 30s default and never below the
/// floor.
pub(super) fn row_validation_timeout(deadline_remaining: Duration) -> Duration {
    deadline_remaining.min(ROW_VALIDATION_CAP).max(ROW_VALIDATION_FLOOR)
}

// ─────────────────────────────────────────────────────────────────────────────
// Execution envelope / transcript metadata
// ─────────────────────────────────────────────────────────────────────────────

pub(super) fn build_execution_envelope(
    execution: ExecutionEnvelope,
    strict_proofs: bool,
    batch_budget: Duration,
    rows: &[RowRecord],
) -> serde_json::Value {
    serde_json::json!({
        "schema": PER_PROPERTY_ENVELOPE_SCHEMA,
        "execution": {
            "mode": execution.mode_label(),
            "deterministic": execution.is_deterministic(),
            "deterministic_source": execution.source.label(),
            "solve_seam": "ay_encode::invoke::solve_with_proof_report_with_cancellation",
            "cancellation": "parent-linked-before-constructor-preprocessing; joined",
            "strict_proofs": strict_proofs,
            "batch_budget_ms": batch_budget.as_millis(),
            "obligation_count": rows.len(),
            "proved": rows.iter().filter(|r| r.outcome == RowOutcomeKind::Proved).count(),
            "refuted": rows.iter().filter(|r| r.outcome == RowOutcomeKind::Refuted).count(),
            "undecided": rows.iter().filter(|r| r.outcome == RowOutcomeKind::Unknown).count(),
            "errored": rows.iter().filter(|r| r.outcome == RowOutcomeKind::Error).count(),
        },
        "rows": rows.iter().map(RowRecord::to_json).collect::<Vec<_>>(),
    })
}

/// Choose what to publish on `VerificationResult::proof_transcript_metadata`.
///
/// * ONE row: that row's own AY transcript metadata, with the execution
///   envelope attached under [`EXECUTION_ENVELOPE_KEY`]. The metadata still
///   describes exactly the problem that decided the harness, so the checked
///   transcript/digest/replay consumer keeps working unchanged — the added key
///   is invisible to it.
/// * More than one row: the envelope alone, under
///   [`PER_PROPERTY_ENVELOPE_SCHEMA`]. See that constant for why a single row's
///   AY transcript must NOT be promoted to speak for the whole harness.
pub(super) fn transcript_metadata_for_batch(
    rows: &[RowRecord],
    single_row_full_metadata: Option<serde_json::Value>,
    envelope: serde_json::Value,
) -> Option<serde_json::Value> {
    if rows.len() == 1
        && let Some(serde_json::Value::Object(mut metadata)) = single_row_full_metadata
    {
        metadata.insert(EXECUTION_ENVELOPE_KEY.to_string(), envelope);
        return Some(serde_json::Value::Object(metadata));
    }
    Some(envelope)
}

/// Compact per-row digest of AY's transcript metadata. Keeps the fields the
/// checked consumer keys on so a rejection reason stays diagnosable, without
/// carrying N full transcripts into a hex-encoded stdout marker.
fn compact_ay_metadata(metadata: &serde_json::Value) -> serde_json::Value {
    let field = |path: &[&str]| -> serde_json::Value {
        let mut cursor = metadata;
        for key in path {
            match cursor.get(key) {
                Some(next) => cursor = next,
                None => return serde_json::Value::Null,
            }
        }
        cursor.clone()
    };
    serde_json::json!({
        "schema": field(&["schema"]),
        "result": field(&["result"]),
        "accepted_as_proof": field(&["accepted_as_proof"]),
        "proof_status": field(&["proof_status"]),
        "normalized_input_sha256": field(&["normalized_input_sha256"]),
        "replay_status": field(&["replay", "status"]),
        "transcript_status": field(&["transcript", "status"]),
        "transcript_metadata_only": field(&["transcript", "metadata_only"]),
        "trust_full_verifier_admissible": field(&["trust_full_verifier_admissible"]),
    })
}

/// Derive the UNKNOWN-classification budget summary from the per-row stop
/// reasons and traces of the same authoritative invocations (adoption step 4).
///
/// The old seam had no `BudgetReport` at all on this path, so `classify_unknown`
/// always fell through to `Uncategorized`. Rows carry the stop reason now, so a
/// budget-bound batch is reported as `PdrTimeout` and a batch that ran off into
/// inconclusive/error states as `SolverError`.
pub(super) fn budget_summary_from_rows(rows: &[RowRecord]) -> BudgetSummary {
    let completed = rows.iter().filter(|row| row.stop_reason == Some("definitive")).count();
    let timed_out = rows.iter().filter(|row| row.stop_reason == Some("budget-exhausted")).count();
    let total_elapsed_ms = rows.iter().map(|row| row.elapsed_ms).sum();
    let first_non_completed =
        rows.iter().find(|row| row.stop_reason != Some("definitive")).map(|row| {
            (
                format!("adaptive-portfolio[{}]", row.label),
                row.stop_reason.unwrap_or("none").to_string(),
            )
        });
    BudgetSummary { completed, timed_out, total_elapsed_ms, first_non_completed }
}

// ─────────────────────────────────────────────────────────────────────────────
// Driver-facing seam
// ─────────────────────────────────────────────────────────────────────────────

/// Which CHC transforms to re-apply to each sliced obligation, mirroring the
/// aggregate path's `--ay-chc-transform` handling so the engines see the same
/// problem shape they used to.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct ObligationTransforms {
    pub(super) scalarize: bool,
    pub(super) split_ite: bool,
    pub(super) split_or: bool,
}

impl ObligationTransforms {
    pub(super) fn from_args(enabled: bool, selected: &[String]) -> Self {
        if !enabled {
            return Self::default();
        }
        let all = selected.is_empty() || selected.iter().any(|s| s.as_str() == "all");
        Self {
            scalarize: all || selected.iter().any(|s| s.as_str() == "scalarize"),
            split_ite: all || selected.iter().any(|s| s.as_str() == "split-ite"),
            split_or: all || selected.iter().any(|s| s.as_str() == "split-or"),
        }
    }

    fn apply(self, problem: &mut ChcProblem, verbose: bool) {
        if self.scalarize {
            problem.try_scalarize_const_array_selects();
        }
        if self.split_ite {
            problem.try_split_ites_in_clauses(8, verbose);
        }
        if self.split_or {
            problem.try_split_ors_in_clauses(8, verbose);
        }
    }
}

pub(super) struct PerPropertySolveOptions<'a> {
    pub(super) verbose: bool,
    /// `--ay-chc-skip-verify`: turns off both AY's `strict_proofs` and the
    /// driver's independent external invariant re-validation, exactly as on the
    /// aggregate path.
    pub(super) skip_verify: bool,
    /// Total budget for the whole batch — the same figure the aggregate solve
    /// used to receive, already clamped to the per-harness deadline.
    pub(super) batch_budget: Duration,
    /// Per-obligation cap. Never larger than `batch_budget`.
    pub(super) per_row_cap: Duration,
    pub(super) deadline: crate::deadline::Deadline,
    pub(super) execution: ExecutionEnvelope,
    pub(super) lemma_hints: &'a [LemmaHint],
    pub(super) transforms: ObligationTransforms,
    /// The harness's memory envelope (AY ask R2, `resource_envelope`), handed
    /// to every row as `EncodeConfig::with_memory_budget`. Rows run one at a
    /// time, so each row's portfolio may use all of it, and AY divides it
    /// across that portfolio's live engines. `None`: AY's defaults.
    pub(super) memory_budget: Option<usize>,
    /// `TRUST_MC_CHC_ROW_EXPORT_DIR`: record every row's exact query, grant
    /// and config (`row_export`). `None` (the default) records nothing.
    pub(super) row_export: Option<&'a RowExport>,
}

/// Reporting fields every decided or undecided batch carries back.
pub(super) struct PerPropertyReport {
    pub(super) proof_transcript_metadata: Option<serde_json::Value>,
    pub(super) budget_summary: BudgetSummary,
    /// Relations named by the decided rows, correlated from AY's stable
    /// obligation labels. On the refutation path this is what tells the report
    /// WHICH check failed even though the sliced problem no longer routes the
    /// counterexample trace through `error_pN`.
    pub(super) correlated_relations: HashSet<String>,
}

pub(super) enum PerPropertyOutcome {
    /// AY validated the problem and simplified every query away as vacuously
    /// safe. No surviving property IDs, so the caller binds this through the
    /// existing source-property / vacuity accounting.
    AllQueriesPruned,
    /// Every required row proved with acceptable evidence.
    Proved {
        invariant: VerifiedInvariant,
        /// The row's own sliced problem, which its invariant model interprets.
        problem: ChcProblem,
        report: PerPropertyReport,
    },
    /// At least one row produced a validated counterexample.
    Refuted {
        counterexample: VerifiedCounterexample,
        /// The refuting row's sliced problem, so counterexample-step predicate
        /// resolution keeps working.
        problem: ChcProblem,
        report: PerPropertyReport,
    },
    /// Neither a proof nor a refutation. `summary` names the blocking rows.
    Undecided { summary: String, report: PerPropertyReport },
}

// ─────────────────────────────────────────────────────────────────────────────
// One row's solve, shared by both passes
// ─────────────────────────────────────────────────────────────────────────────

/// `TRUST_MC_CHC_ROWS_AFTER_REFUTATION=solve` keeps solving the rows after the
/// first refutation (the measurement counterfactual; default: skip them).
pub(super) const ROWS_AFTER_REFUTATION_ENV: &str = "TRUST_MC_CHC_ROWS_AFTER_REFUTATION";

fn rows_after_refutation_are_solved(value: Option<&str>) -> bool {
    value.is_some_and(|v| v.trim().eq_ignore_ascii_case("solve"))
}

fn rows_after_refutation_are_solved_from_env() -> bool {
    rows_after_refutation_are_solved(std::env::var(ROWS_AFTER_REFUTATION_ENV).ok().as_deref())
}

/// The least a second-pass share is worth starting for.
pub(super) const SECOND_PASS_MIN_BUDGET: Duration = Duration::from_millis(250);

/// A second-pass share is useful when it clears the floor and is at least
/// 1.5x the share the row already ran out of: re-solving with the same budget
/// would only repeat the first answer.
pub(super) fn second_pass_budget_is_useful(budget: Duration, previous: Duration) -> bool {
    budget >= SECOND_PASS_MIN_BUDGET && budget.as_millis() * 2 >= previous.as_millis() * 3
}

/// Which pass recorded a row (the second pass says so on its marker line).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowPass {
    First,
    Second,
}

/// A row the first pass left budget-bound, kept for the second pass.
struct SecondPassRow {
    index: usize,
    /// Already through `prepare_row_problem`.
    problem: ChcProblem,
    previous_budget: Duration,
}

/// The identity fields a row record carries.
struct RowIdent {
    label: String,
    relation: Option<String>,
    content_sha256: String,
}

/// What one AY invocation returned, before it is recorded.
enum RowSolve {
    Report {
        result: VerifiedChcResult,
        stop: ChcProofRunStopReason,
        cancellation_requested: bool,
        adaptive_stages: Vec<String>,
        full_metadata: serde_json::Value,
    },
    /// The invocation failed (typed AY error or panic); the detail says which.
    Failed(String),
}

/// Same preprocessing the aggregate problem used to receive, applied to the
/// slice so the engines see an equivalent shape.
fn prepare_row_problem(problem: &mut ChcProblem, options: &PerPropertySolveOptions<'_>) {
    problem.expand_nullary_fail_queries(options.verbose);
    options.transforms.apply(problem, options.verbose);
}

/// The `EncodeConfig` one row is solved under.
fn row_encode_config(
    budget: Duration,
    options: &PerPropertySolveOptions<'_>,
) -> ay_encode::invoke::EncodeConfig {
    let mut config = ay_encode::invoke::EncodeConfig::new()
        .with_timeout(budget)
        // Adoption step 6: the execution policy is an explicit input, carried
        // on EncodeConfig rather than inherited from AY's env default.
        .with_execution_mode(options.execution.mode)
        // Parity with the aggregate path: `strict_proofs` on unless
        // `--ay-chc-skip-verify` (ay#8585 — reject trust-proof fallbacks).
        .with_strict_validation(!options.skip_verify)
        .with_lemma_hints(options.lemma_hints.to_vec());
    if let Some(bytes) = options.memory_budget {
        config = config.with_memory_budget(bytes);
    }
    config
}

/// The batch-level inputs the row export records once per harness.
fn batch_export_record(options: &PerPropertySolveOptions<'_>, total: usize) -> serde_json::Value {
    serde_json::json!({
        "obligation_count": total,
        "slicing": "ChcProblem::query_obligations() on the problem as parsed from source.smt2 \
                    (before expand_nullary_fail_queries)",
        "row_preparation": {
            "expand_nullary_fail_queries": true,
            "transforms": format!("{:?}", options.transforms),
        },
        "execution": {
            "mode": options.execution.mode_label(),
            "requested_by": options.execution.source.label(),
            "env": {
                DETERMINISTIC_ENV: std::env::var(DETERMINISTIC_ENV).ok(),
                AY_DETERMINISTIC_ENV: std::env::var(AY_DETERMINISTIC_ENV).ok(),
            },
        },
        "batch_budget_ms": options.batch_budget.as_millis(),
        "per_row_cap_ms": options.per_row_cap.as_millis(),
        "batch_guard_grace_ms": BATCH_GUARD_GRACE.as_millis(),
        "harness_deadline_remaining_ms_at_batch_start": options.deadline.remaining().as_millis(),
        "skip_verify": options.skip_verify,
        "memory_budget_bytes": options.memory_budget,
        "rows_after_refutation": if rows_after_refutation_are_solved_from_env() { "solve" } else { "skip" },
        "second_pass": format!(
            "rows left budget-bound are re-solved from what the batch clock has left when the new \
             share is >= {} ms and >= 1.5x the previous share",
            SECOND_PASS_MIN_BUDGET.as_millis()
        ),
        "row_validation": if options.skip_verify {
            "none (--ay-chc-skip-verify)"
        } else {
            "each proved row's invariant model is re-validated against its own problem after the rows run"
        },
    })
}

/// Solve one prepared row under `budget` on THIS thread (join, never detach).
fn solve_row(
    problem: ChcProblem,
    budget: Duration,
    options: &PerPropertySolveOptions<'_>,
    parent: &CancellationToken,
) -> (RowSolve, u128) {
    let config = row_encode_config(budget, options);

    let started = Instant::now();
    // Panic isolation WITHOUT a thread: AY-classified panics already come back
    // as a typed error from ay-encode; this catches the programmer-error kind
    // that used to be absorbed by the detached thread's boundary.
    let invocation = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ay_encode::invoke::solve_with_proof_report_with_cancellation(problem, &config, parent)
    }));
    let elapsed_ms = started.elapsed().as_millis();
    let solve = match invocation {
        Ok(Ok(report)) => {
            let stop = report.stop_reason();
            let cancellation_requested = report.cancellation_requested_at_return();
            let adaptive_stages: Vec<String> = report
                .adaptive_trace()
                .observations()
                .iter()
                .take(MAX_RECORDED_STAGES)
                .map(|observation| format!("{}:{:?}", observation.stage, observation.outcome))
                .collect();
            let run = report.proof_run();
            RowSolve::Report {
                result: run.result().clone(),
                stop,
                cancellation_requested,
                adaptive_stages,
                full_metadata: run.metadata().to_json_value(),
            }
        }
        Ok(Err(err)) => RowSolve::Failed(format!("ay-encode invocation error: {err}")),
        Err(panic_payload) => RowSolve::Failed(format!(
            "ay-chc panic during adaptive-portfolio: {}",
            panic_payload_message(panic_payload.as_ref())
        )),
    };
    (solve, elapsed_ms)
}

/// The batch's recorded rows and the sealed AY evidence the reduction needs.
struct BatchRows {
    rows: Vec<RowRecord>,
    proved: Vec<(usize, VerifiedInvariant, ChcProblem)>,
    refuted: Option<(usize, VerifiedCounterexample, ChcProblem)>,
    single_row_metadata: Option<serde_json::Value>,
}

impl BatchRows {
    /// Record one solved row at `index`: pushed on the first pass, replacing
    /// the budget-bound record on the second. Returns the row's problem when
    /// no evidence kept it (the row stayed undecided), so the caller can keep
    /// it for the second pass.
    #[allow(clippy::too_many_arguments)]
    fn absorb(
        &mut self,
        index: usize,
        total: usize,
        ident: RowIdent,
        row_problem: ChcProblem,
        budget: Duration,
        solve: RowSolve,
        elapsed_ms: u128,
        parent_cancelled: bool,
        pass: RowPass,
    ) -> anyhow::Result<Option<ChcProblem>> {
        let RowIdent { label, relation, content_sha256 } = ident;
        let mut returned = None;
        let record = match solve {
            RowSolve::Report {
                result,
                stop,
                cancellation_requested,
                adaptive_stages,
                full_metadata,
            } => {
                let shape = match &result {
                    VerifiedChcResult::Safe(_) => RowResultShape::Safe,
                    VerifiedChcResult::Unsafe(_) => RowResultShape::Unsafe,
                    _ => RowResultShape::Unknown,
                };
                let (outcome, detail) = classify_row(shape, stop);
                match (outcome, result) {
                    (RowOutcomeKind::Proved, VerifiedChcResult::Safe(invariant)) => {
                        self.proved.push((index, invariant, row_problem));
                    }
                    (RowOutcomeKind::Refuted, VerifiedChcResult::Unsafe(counterexample)) => {
                        if counterexample.counterexample().steps.is_empty() {
                            // Part of #4182: a 0-step counterexample from ay-chc
                            // is not trustworthy. `interpret_chc_unsafe` refuses
                            // it with this exact wording, and that wording is
                            // load-bearing — it does NOT match
                            // `native_chc_error_allows_external_proof_fallback`,
                            // so a suspect counterexample cannot open the
                            // external proof-only fallback that a plain
                            // inconclusive batch may open.
                            solver_stdout!(
                                "[AY-chc] 0-step counterexample on obligation {label} — \
                                 returning UNKNOWN"
                            );
                            anyhow::bail!("ay-chc 0-step counterexample — inconclusive");
                        }
                        if self.refuted.is_none() {
                            self.refuted = Some((index, counterexample, row_problem));
                        }
                    }
                    _ => returned = Some(row_problem),
                }
                if total == 1 {
                    self.single_row_metadata = Some(full_metadata.clone());
                }
                RowRecord {
                    label,
                    relation,
                    content_sha256,
                    outcome,
                    detail,
                    stop_reason: Some(stop_reason_label(stop)),
                    cancellation_requested,
                    elapsed_ms,
                    budget_ms: budget.as_millis(),
                    adaptive_stages,
                    ay_metadata: Some(compact_ay_metadata(&full_metadata)),
                }
            }
            RowSolve::Failed(detail) => RowRecord {
                label,
                relation,
                content_sha256,
                outcome: RowOutcomeKind::Error,
                detail,
                stop_reason: None,
                cancellation_requested: parent_cancelled,
                elapsed_ms,
                budget_ms: budget.as_millis(),
                adaptive_stages: Vec::new(),
                ay_metadata: None,
            },
        };
        match pass {
            RowPass::First => solver_stdout!("{}", record.marker_line()),
            RowPass::Second => solver_stdout!("{} [second pass]", record.marker_line()),
        }
        if index < self.rows.len() {
            self.rows[index] = record;
        } else {
            self.rows.push(record);
        }
        Ok(returned)
    }
}

/// Solve every BSEM-18 property obligation of `source_problem` independently.
///
/// `source_problem` must be the problem as parsed, BEFORE
/// `expand_nullary_fail_queries`: that is the `error_pN -> error -> false` shape
/// AY's slicer unfolds into exactly one obligation per property. Each sliced
/// obligation then receives the same nullary expansion and transform passes the
/// aggregate problem used to get, so the engines see an equivalent problem.
pub(super) fn solve_chc_per_property(
    source_problem: &ChcProblem,
    options: &PerPropertySolveOptions<'_>,
) -> anyhow::Result<PerPropertyOutcome> {
    let obligations = match source_problem.query_obligations() {
        Ok(obligations) => obligations,
        Err(err) => {
            // Step 9: AY rejecting the query is an ENCODER defect, not an
            // undecided solve. The wording is what `SolverUnknownReason::
            // from_chc_error` files as `ChcParseError`.
            solver_stdout!(
                "[AY-chc] AY rejected the per-property query slice — encoder defect, not an \
                 undecided solve: {err}"
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            anyhow::bail!("Failed to parse CHC problem: AY rejected the query slice: {err}");
        }
    };

    if obligations.is_empty() {
        // AY's documented `Ok([])`: a validated problem whose queries were all
        // simplified away as vacuously Safe. There are no surviving property
        // IDs to credit, so we hand the disposition to the caller's existing
        // source-property/vacuity accounting instead of minting rows.
        solver_stdout!(
            "[AY-chc] AY validated the problem and pruned every safety query as vacuously \
             safe — binding through source-property/vacuity accounting (no solver rows credited)"
        );
        if let Some(export) = options.row_export {
            export.note("per_property_batch", serde_json::json!({"obligations": [], "disposition": "all queries pruned (Ok([]))"}));
        }
        return Ok(PerPropertyOutcome::AllQueriesPruned);
    }

    let total = obligations.len();
    if options.verbose {
        solver_stdout!(
            "[AY-chc] Per-property solve: {total} query obligation(s), mode={}, source={}, \
             batch budget {:?}",
            options.execution.mode_label(),
            options.execution.source.label(),
            options.batch_budget,
        );
    }

    // Adoption step 7: the parent token exists before ANY portfolio is
    // constructed, and the batch clock is armed on it. `cancel_after` returns a
    // guard whose Drop stops and joins the timer thread, so no timer outlives
    // this call.
    let parent = CancellationToken::new();
    let _batch_guard = parent.cancel_after(options.batch_budget + BATCH_GUARD_GRACE);
    let batch_deadline = crate::deadline::Deadline::after(options.batch_budget);

    if let Some(export) = options.row_export {
        let identities: Vec<(String, String)> = obligations
            .iter()
            .map(|o| (o.id().label().to_string(), o.id().content_sha256().to_string()))
            .collect();
        export.begin_batch(
            batch_export_record(options, total),
            &identities,
            options.lemma_hints,
            source_problem,
            &|problem: &mut ChcProblem| prepare_row_problem(problem, options),
        );
    }

    let mut batch = BatchRows {
        rows: Vec::with_capacity(total),
        proved: Vec::new(),
        refuted: None,
        single_row_metadata: None,
    };
    // Rows the first pass left budget-bound, with their prepared problems.
    let mut second_pass: Vec<SecondPassRow> = Vec::new();
    let solve_rows_after_refutation = rows_after_refutation_are_solved_from_env();
    let mut skipped_after_refutation = 0usize;
    // Row identities for the export's second-pass records (empty unless the
    // export is on).
    let mut export_identities: Vec<serde_json::Value> = Vec::new();

    for (index, obligation) in obligations.into_iter().enumerate() {
        let (id, mut problem) = obligation.into_parts();
        let label = id.label().to_string();
        let relation = vc_relation_for_obligation_label(&label);
        let content_sha256 = id.content_sha256().to_string();
        let export_identity = options.row_export.map(|_| {
            serde_json::json!({
                "label": label,
                "relation": relation,
                "content_sha256": content_sha256,
                "source_query_ordinal": id.source_query_ordinal(),
                "query_clause_index": id.query_clause_index(),
                "defining_clause_index": id.defining_clause_index(),
            })
        });
        if let Some(identity) = &export_identity {
            export_identities.push(identity.clone());
        }

        // A refutation fails the harness, and the report names only the FIRST
        // refuted row (`reduce_rows` takes the lowest refuting index, and
        // `interpret_chc_unsafe` reports that row's relation FAILURE and every
        // other check UNDETERMINED), so a row solved after it cannot change a
        // status, a Failed Checks line or the verdict — it can only spend the
        // clock, bail on a 0-step counterexample (also FAILED) or never return
        // (measured: kani/Panic/prove_safety_only.rs `div0` refuted error_p6 and
        // error_p7 in 22ms and 24ms, then sat in error_p8 until the watchdog
        // fired at 94s). Recorded, not dropped, so the row list stays complete.
        if batch.refuted.is_some() && !solve_rows_after_refutation {
            let record = RowRecord {
                label,
                relation,
                content_sha256,
                outcome: RowOutcomeKind::Unknown,
                detail: "not solved: an earlier obligation refuted the harness".to_string(),
                stop_reason: Some("skipped-after-refutation"),
                cancellation_requested: false,
                elapsed_ms: 0,
                budget_ms: 0,
                adaptive_stages: Vec::new(),
                ay_metadata: None,
            };
            solver_stdout!("{}", record.marker_line());
            if let (Some(export), Some(identity)) = (options.row_export, export_identity) {
                let slot = export.row(index, "first", identity, None, None);
                export.row_outcome(slot, record.to_json());
            }
            batch.rows.push(record);
            skipped_after_refutation += 1;
            continue;
        }

        let rows_left = total - index;
        let batch_remaining = batch_deadline.remaining();
        let harness_remaining = options.deadline.remaining();
        let remaining = batch_remaining.min(harness_remaining);
        let budget = per_obligation_budget(remaining, rows_left, options.per_row_cap);
        let grant = RowGrant {
            budget,
            rows_left,
            batch_remaining,
            harness_deadline_remaining: harness_remaining,
        };

        if budget.is_zero() || parent.is_cancelled() {
            // Never start a portfolio we cannot fund. Recorded, not skipped:
            // an unfunded obligation is an undecided obligation, and it must
            // stay visible so a batch that ran out of clock cannot look like a
            // batch that proved everything it was asked about.
            let cancelled = parent.is_cancelled();
            let (detail, stop_reason) = if cancelled {
                ("batch cancelled before this obligation started", "externally-cancelled")
            } else {
                // Budget-bound, not a solver failure: keep the label that makes
                // `classify_unknown` report PdrTimeout rather than SolverError.
                ("no budget left in the batch for this obligation", "budget-exhausted")
            };
            let record = RowRecord {
                label,
                relation,
                content_sha256,
                outcome: RowOutcomeKind::Unknown,
                detail: detail.to_string(),
                stop_reason: Some(stop_reason),
                cancellation_requested: cancelled,
                elapsed_ms: 0,
                budget_ms: 0,
                adaptive_stages: Vec::new(),
                ay_metadata: None,
            };
            solver_stdout!("{}", record.marker_line());
            if let (Some(export), Some(identity)) = (options.row_export, export_identity) {
                let slot = export.row(index, "first", identity, Some(&grant), None);
                export.row_outcome(slot, record.to_json());
            }
            batch.rows.push(record);
            if !cancelled {
                prepare_row_problem(&mut problem, options);
                second_pass.push(SecondPassRow { index, problem, previous_budget: Duration::ZERO });
            }
            continue;
        }

        // Same preprocessing the aggregate problem used to receive, applied to
        // the slice so the engines see an equivalent shape.
        let slice_sha = options.row_export.map(|_| problem.normalized_input_sha256());
        prepare_row_problem(&mut problem, options);
        let row_problem = problem.clone();
        let export_slot = match (options.row_export, export_identity) {
            (Some(export), Some(identity)) => export.row(
                index,
                "first",
                identity,
                Some(&grant),
                Some(RowQuery {
                    prepared: &row_problem,
                    slice_normalized_sha256: slice_sha,
                    config: &row_encode_config(budget, options),
                }),
            ),
            _ => None,
        };
        let (solve, elapsed_ms) = solve_row(problem, budget, options, &parent);
        let ident = RowIdent { label, relation, content_sha256 };
        let returned = batch.absorb(
            index,
            total,
            ident,
            row_problem,
            budget,
            solve,
            elapsed_ms,
            parent.is_cancelled(),
            RowPass::First,
        )?;
        if let Some(export) = options.row_export {
            export.row_outcome(export_slot, batch.rows[index].to_json());
        }
        if let Some(problem) = returned
            && batch.rows[index].is_budget_bound_unknown()
        {
            second_pass.push(SecondPassRow { index, problem, previous_budget: budget });
        }
    }

    if skipped_after_refutation > 0 {
        crate::stage_timing::record_elapsed(
            "rows-after-refutation",
            Duration::ZERO,
            &format!("skipped={skipped_after_refutation}"),
        );
    }

    // Second pass: what the first pass left of the batch clock goes to the
    // rows it left budget-bound. `per_obligation_budget` shares what remains
    // over the rows still to come ONCE, so time an easy late row did not use
    // was never seen by a hard early one (measured: `kani/Pointers_InAssert`
    // gave error_p6 2.9s and then left 11.5s of the batch unused). Same batch
    // clock and cancellation token — nothing here extends the batch — and a
    // row is re-solved only when its new share is materially larger than the
    // one it ran out of (`second_pass_budget_is_useful`). Not run once a row
    // refuted: the harness fails whatever the remaining rows would say.
    if batch.refuted.is_none() && !second_pass.is_empty() {
        let pass_started = Instant::now();
        let candidates = std::mem::take(&mut second_pass);
        let count = candidates.len();
        let mut rerun = 0usize;
        for (position, candidate) in candidates.into_iter().enumerate() {
            if parent.is_cancelled() {
                break;
            }
            let batch_remaining = batch_deadline.remaining();
            let harness_remaining = options.deadline.remaining();
            let remaining = batch_remaining.min(harness_remaining);
            let budget = per_obligation_budget(remaining, count - position, options.per_row_cap);
            if !second_pass_budget_is_useful(budget, candidate.previous_budget) {
                continue;
            }
            let ident = batch.rows[candidate.index].ident();
            let export_slot =
                match (options.row_export, export_identities.get(candidate.index).cloned()) {
                    (Some(export), Some(identity)) => export.row(
                        candidate.index,
                        "second",
                        identity,
                        Some(&RowGrant {
                            budget,
                            rows_left: count - position,
                            batch_remaining,
                            harness_deadline_remaining: harness_remaining,
                        }),
                        Some(RowQuery {
                            prepared: &candidate.problem,
                            slice_normalized_sha256: None,
                            config: &row_encode_config(budget, options),
                        }),
                    ),
                    _ => None,
                };
            let (solve, elapsed_ms) =
                solve_row(candidate.problem.clone(), budget, options, &parent);
            batch.absorb(
                candidate.index,
                total,
                ident,
                candidate.problem,
                budget,
                solve,
                elapsed_ms,
                parent.is_cancelled(),
                RowPass::Second,
            )?;
            if let Some(export) = options.row_export {
                export.row_outcome(export_slot, batch.rows[candidate.index].to_json());
            }
            rerun += 1;
            if batch.refuted.is_some() {
                break;
            }
        }
        crate::stage_timing::record(
            "per-property-second-pass",
            pass_started,
            &format!("rows={rerun}/{count}"),
        );
    }
    let BatchRows { rows, proved, refuted, single_row_metadata } = batch;

    // Same independent external re-validation the aggregate Safe path runs
    // (ay#8578), applied per proved row against the row's OWN problem; a
    // rejected model bails the whole harness with the established "false proof
    // detected" wording, exactly as when it ran inside the row loop. It runs
    // once the rows have had their shares of the batch clock (charged inside
    // the loop it starved the rows still to come), and it is skipped when a
    // row REFUTED the harness: the refutation fails the harness whatever the
    // proved rows' models are, and a rejected model would only have turned
    // that `VERIFICATION:- FAILED` into an UNKNOWN that also prints it.
    //
    // Budget (`ValidationPhase`): when EVERY row proved, the models decide the
    // verdict, so each validation keeps the harness deadline
    // (`row_validation_timeout`: min(30s, left), floored). When the batch is
    // undecided anyway, the whole phase gets at most one batch budget, and a
    // proved row whose validation does not fit is demoted to an undecided,
    // budget-bound row — never credited unvalidated, which is what main did
    // when such a row starved in the loop.
    let mut proved = proved;
    let mut rows = rows;
    if !options.skip_verify && refuted.is_none() && !proved.is_empty() {
        let validation_started = Instant::now();
        let all_proved = rows.iter().all(|row| row.outcome == RowOutcomeKind::Proved);
        let phase = if all_proved {
            ValidationPhase::DecidesTheVerdict
        } else {
            ValidationPhase::UndecidedBatch {
                phase_deadline: crate::deadline::Deadline::after(options.batch_budget),
            }
        };
        let mut kept = Vec::with_capacity(proved.len());
        let mut demoted = 0usize;
        for (index, invariant, row_problem) in proved {
            let timeout = match phase {
                ValidationPhase::DecidesTheVerdict => {
                    Some(row_validation_timeout(options.deadline.remaining()))
                }
                ValidationPhase::UndecidedBatch { phase_deadline } => phase_deadline
                    .stage_budget(ROW_VALIDATION_CAP, crate::deadline::MIN_USEFUL_STAGE_BUDGET)
                    .map(|budget| budget.min(options.deadline.remaining().max(budget))),
            };
            let Some(timeout) = timeout else {
                let row = &mut rows[index];
                row.outcome = RowOutcomeKind::Unknown;
                row.stop_reason = Some("budget-exhausted");
                row.detail = "proved, but the batch had no budget left to re-validate its model — \
                              not credited"
                    .to_string();
                solver_stdout!("{} [validation budget]", row.marker_line());
                demoted += 1;
                continue;
            };
            if let Some(export) = options.row_export {
                export.validation_begin(index);
            }
            let validation_started = Instant::now();
            let validation = validate_row_invariant_model(
                &row_problem,
                invariant.model(),
                options.verbose,
                timeout,
            );
            if let Some(export) = options.row_export {
                export.validation(
                    index,
                    &rows[index].label,
                    &invariant.model().to_smtlib(&row_problem),
                    timeout,
                    validation_started.elapsed(),
                    match &validation {
                        Ok(RowModelValidation::Valid) => Ok(()),
                        Ok(RowModelValidation::Rejected) => Err("rejected".to_string()),
                        Ok(RowModelValidation::BudgetExhausted) => {
                            Err("budget-exhausted (AY returned false at its budget)".to_string())
                        }
                        Err(err) => Err(err.to_string()),
                    },
                );
            }
            match validation? {
                RowModelValidation::Valid => kept.push((index, invariant, row_problem)),
                RowModelValidation::Rejected => return Err(reject_false_proof()),
                RowModelValidation::BudgetExhausted => {
                    // AY's validator answers `false` on an expired budget, so
                    // this row's model is unconfirmed, not refuted: demote it
                    // like a row whose validation never fit, and keep going.
                    let row = &mut rows[index];
                    row.outcome = RowOutcomeKind::Unknown;
                    row.stop_reason = Some("budget-exhausted");
                    row.detail = format!(
                        "proved, but its model re-validation ran out of its {timeout:?} budget \
                         (AY's validator returns false on budget expiry) — not credited"
                    );
                    solver_stdout!("{} [validation budget]", row.marker_line());
                    demoted += 1;
                }
            }
        }
        proved = kept;
        crate::stage_timing::record(
            "row-validation",
            validation_started,
            &format!("rows={} demoted={demoted}", proved.len() + demoted),
        );
        if let Some(export) = options.row_export {
            export.note(
                "row_validation",
                serde_json::json!({
                    "what": "independent external re-validation of each proved row's invariant \
                             model against that row's own problem \
                             (validate_row_invariant_model; a false at the budget is \
                             budget-exhausted, not a false proof)",
                    "phase": if all_proved { "decides-the-verdict" } else { "undecided-batch" },
                    "validated_rows": proved.len(),
                    "demoted_rows": demoted,
                    "elapsed_ms": validation_started.elapsed().as_millis(),
                }),
            );
        }
    }
    if let Some(export) = options.row_export {
        export.note("batch_reduction", serde_json::json!(format!("{:?}", reduce_rows(&rows))));
    }

    let envelope = build_execution_envelope(
        options.execution,
        !options.skip_verify,
        options.batch_budget,
        &rows,
    );
    let budget_summary = budget_summary_from_rows(&rows);
    let proof_transcript_metadata =
        transcript_metadata_for_batch(&rows, single_row_metadata, envelope);

    // The `if refuted.is_some()` / `if !proved.is_empty()` guards below can never
    // fail: a Refuted or Proved reduction can only come from a row that stored
    // its sealed AY evidence. They are there so that IF a future refactor breaks
    // that pairing, the batch falls through to the fail-closed catch-all and
    // reports undecided, instead of panicking or — far worse — reporting a
    // verdict it cannot back with evidence.
    match reduce_rows(&rows) {
        BatchVerdict::Refuted(index) if refuted.is_some() => {
            let (_, counterexample, problem) = refuted.expect("guarded by the match arm above");
            let mut correlated_relations = HashSet::new();
            if let Some(relation) = rows[index].relation.clone() {
                correlated_relations.insert(relation);
            }
            Ok(PerPropertyOutcome::Refuted {
                counterexample,
                problem,
                report: PerPropertyReport {
                    proof_transcript_metadata,
                    budget_summary,
                    correlated_relations,
                },
            })
        }
        BatchVerdict::Proved if !proved.is_empty() => {
            let (_, invariant, problem) =
                proved.into_iter().next().expect("guarded by the match arm above");
            let correlated_relations =
                rows.iter().filter_map(|row| row.relation.clone()).collect::<HashSet<_>>();
            Ok(PerPropertyOutcome::Proved {
                invariant,
                problem,
                report: PerPropertyReport {
                    proof_transcript_metadata,
                    budget_summary,
                    correlated_relations,
                },
            })
        }
        BatchVerdict::Undecided(summary) => {
            solver_stdout!("[AY-chc] Per-property batch undecided: {summary}");
            Ok(PerPropertyOutcome::Undecided {
                summary,
                report: PerPropertyReport {
                    proof_transcript_metadata,
                    budget_summary,
                    correlated_relations: HashSet::new(),
                },
            })
        }
        // Fail-closed catch-all: a decided reduction whose sealed evidence went
        // missing is treated as undecided, never as the verdict it claimed.
        decided => Ok(PerPropertyOutcome::Undecided {
            summary: format!(
                "batch reduced to {decided:?} but the corresponding AY evidence was not \
                 retained — refusing to report that verdict"
            ),
            report: PerPropertyReport {
                proof_transcript_metadata,
                budget_summary,
                correlated_relations: HashSet::new(),
            },
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(label: &str, outcome: RowOutcomeKind, stop: Option<&'static str>) -> RowRecord {
        RowRecord {
            label: label.to_string(),
            relation: vc_relation_for_obligation_label(label),
            content_sha256: "0".repeat(64),
            outcome,
            detail: "test".to_string(),
            stop_reason: stop,
            cancellation_requested: false,
            elapsed_ms: 5,
            budget_ms: 10,
            adaptive_stages: Vec::new(),
            ay_metadata: None,
        }
    }

    // ── stop_reason mapping (adoption step 4) ────────────────────────────────

    #[test]
    fn definitive_safe_is_the_only_proved_row_shape() {
        assert_eq!(
            classify_row(RowResultShape::Safe, ChcProofRunStopReason::Definitive).0,
            RowOutcomeKind::Proved
        );
        for stop in [
            ChcProofRunStopReason::BudgetExhausted,
            ChcProofRunStopReason::ExternallyCancelled,
            ChcProofRunStopReason::Inconclusive,
        ] {
            let (outcome, detail) = classify_row(RowResultShape::Safe, stop);
            assert_eq!(
                outcome,
                RowOutcomeKind::Unknown,
                "a non-definitive Safe must never be credited ({stop:?})"
            );
            assert!(detail.contains("not definitive"), "detail should explain: {detail}");
        }
    }

    #[test]
    fn every_unsafe_row_refutes_regardless_of_stop_reason() {
        for stop in [
            ChcProofRunStopReason::Definitive,
            ChcProofRunStopReason::BudgetExhausted,
            ChcProofRunStopReason::ExternallyCancelled,
            ChcProofRunStopReason::Inconclusive,
        ] {
            assert_eq!(
                classify_row(RowResultShape::Unsafe, stop).0,
                RowOutcomeKind::Refuted,
                "cancellation can never flip Unsafe ({stop:?})"
            );
        }
    }

    #[test]
    fn unknown_rows_keep_their_stop_reason_visible() {
        let (outcome, detail) =
            classify_row(RowResultShape::Unknown, ChcProofRunStopReason::BudgetExhausted);
        assert_eq!(outcome, RowOutcomeKind::Unknown);
        assert!(detail.contains("budget-exhausted"), "{detail}");
        let (_, detail) =
            classify_row(RowResultShape::Unknown, ChcProofRunStopReason::ExternallyCancelled);
        assert!(detail.contains("externally-cancelled"), "{detail}");
    }

    #[test]
    fn stop_reason_labels_are_stable() {
        assert_eq!(stop_reason_label(ChcProofRunStopReason::Definitive), "definitive");
        assert_eq!(stop_reason_label(ChcProofRunStopReason::BudgetExhausted), "budget-exhausted");
        assert_eq!(
            stop_reason_label(ChcProofRunStopReason::ExternallyCancelled),
            "externally-cancelled"
        );
        assert_eq!(stop_reason_label(ChcProofRunStopReason::Inconclusive), "inconclusive");
    }

    // ── batch reduction (adoption step 3) ────────────────────────────────────

    #[test]
    fn any_unsafe_row_fails_the_harness_even_beside_proved_rows() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Refuted, Some("definitive")),
            row("error_p2", RowOutcomeKind::Unknown, Some("budget-exhausted")),
        ];
        assert_eq!(reduce_rows(&rows), BatchVerdict::Refuted(1));
    }

    #[test]
    fn refutation_wins_over_an_earlier_error_row() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Error, None),
            row("error_p1", RowOutcomeKind::Refuted, Some("definitive")),
        ];
        assert_eq!(reduce_rows(&rows), BatchVerdict::Refuted(1));
    }

    #[test]
    fn proof_requires_every_row_proved() {
        let all_proved = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Proved, Some("definitive")),
        ];
        assert_eq!(reduce_rows(&all_proved), BatchVerdict::Proved);

        let one_unknown = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Unknown, Some("inconclusive")),
        ];
        let BatchVerdict::Undecided(summary) = reduce_rows(&one_unknown) else {
            panic!("a single undecided row must block the proof");
        };
        assert!(summary.contains("1/2 properties proved"), "{summary}");
        assert!(summary.contains("error_p1"), "the blocking row stays visible: {summary}");
    }

    #[test]
    fn an_error_row_blocks_the_proof_and_stays_visible() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p7", RowOutcomeKind::Error, None),
        ];
        let BatchVerdict::Undecided(summary) = reduce_rows(&rows) else {
            panic!("an errored row must block the proof");
        };
        assert!(summary.contains("1 errored"), "{summary}");
        assert!(summary.contains("error_p7"), "{summary}");
    }

    #[test]
    fn a_budget_bound_batch_keeps_its_timeout_attribution() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Unknown, Some("budget-exhausted")),
            row("error_p2", RowOutcomeKind::Unknown, Some("externally-cancelled")),
        ];
        let BatchVerdict::Undecided(summary) = reduce_rows(&rows) else {
            panic!("a budget-bound batch is undecided");
        };
        assert!(summary.starts_with(BATCH_BUDGET_EXHAUSTED_PHRASE), "{summary}");
        // The driver bails with this summary embedded; it must keep its
        // BUDGET-bound bucket rather than falling into the SolverError catch-all,
        // and it must still open the external proof-only fallback the retired
        // guard-timeout path opened.
        let err = anyhow::anyhow!(
            "ay-chc adaptive-portfolio returned Unknown - verification inconclusive ({summary})"
        );
        assert_eq!(
            crate::verification_provenance::SolverUnknownReason::from_chc_error(&err),
            crate::verification_provenance::SolverUnknownReason::Timeout,
        );
    }

    #[test]
    fn a_capability_bound_batch_is_not_reported_as_a_timeout() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Unknown, Some("budget-exhausted")),
            row("error_p1", RowOutcomeKind::Unknown, Some("inconclusive")),
        ];
        let BatchVerdict::Undecided(summary) = reduce_rows(&rows) else {
            panic!("an inconclusive batch is undecided");
        };
        assert!(
            !summary.starts_with(BATCH_BUDGET_EXHAUSTED_PHRASE),
            "one genuinely inconclusive row means the batch was not purely budget-bound: \
             {summary}"
        );
    }

    #[test]
    fn an_empty_row_list_is_never_a_proof() {
        let BatchVerdict::Undecided(summary) = reduce_rows(&[]) else {
            panic!("an empty batch must never reduce to Proved");
        };
        assert!(summary.contains("no query obligations"), "{summary}");
    }

    // ── correlation back to the VC artifact ──────────────────────────────────

    #[test]
    fn obligation_labels_correlate_to_vc_relations() {
        assert_eq!(vc_relation_for_obligation_label("error_p7").as_deref(), Some("error_p7"));
        assert_eq!(
            vc_relation_for_obligation_label("error_p7_definition_3").as_deref(),
            Some("error_p7")
        );
        assert_eq!(
            vc_relation_for_obligation_label("error_p12_definition_0").as_deref(),
            Some("error_p12")
        );
    }

    #[test]
    fn non_property_labels_do_not_invent_a_correlation() {
        assert_eq!(vc_relation_for_obligation_label("query_0"), None);
        assert_eq!(vc_relation_for_obligation_label("error"), None);
        assert_eq!(vc_relation_for_obligation_label("error_p"), None);
        assert_eq!(vc_relation_for_obligation_label("fail_definition_1"), None);
        // A non-numeric `_definition_` suffix is part of the relation name, not
        // an unfolding marker, so it is kept rather than truncated.
        assert_eq!(
            vc_relation_for_obligation_label("error_p3_definition_x").as_deref(),
            Some("error_p3_definition_x")
        );
    }

    // ── budget allocation ────────────────────────────────────────────────────

    #[test]
    fn rows_after_a_refutation_are_skipped_unless_asked_for() {
        assert!(!rows_after_refutation_are_solved(None));
        assert!(!rows_after_refutation_are_solved(Some("")));
        assert!(!rows_after_refutation_are_solved(Some("skip")));
        assert!(rows_after_refutation_are_solved(Some(" SOLVE ")));
    }

    #[test]
    fn a_refutation_still_reduces_to_the_first_refuted_row_beside_skipped_rows() {
        let rows = [
            row("error_p6", RowOutcomeKind::Refuted, Some("definitive")),
            row("error_p7", RowOutcomeKind::Unknown, Some("skipped-after-refutation")),
            row("error_p8", RowOutcomeKind::Unknown, Some("skipped-after-refutation")),
        ];
        assert_eq!(reduce_rows(&rows), BatchVerdict::Refuted(0));
    }

    #[test]
    fn second_pass_reruns_only_on_a_materially_larger_share() {
        // An unfunded row takes any share above the floor.
        assert!(second_pass_budget_is_useful(Duration::from_millis(250), Duration::ZERO));
        assert!(!second_pass_budget_is_useful(Duration::from_millis(249), Duration::ZERO));
        // The measured Pointers_InAssert shape: 2.9s spent, 11.6s left.
        assert!(second_pass_budget_is_useful(
            Duration::from_millis(11_632),
            Duration::from_millis(2_938)
        ));
        // The same budget again would only repeat the first answer.
        assert!(!second_pass_budget_is_useful(Duration::from_secs(3), Duration::from_secs(3)));
        assert!(second_pass_budget_is_useful(Duration::from_millis(4_500), Duration::from_secs(3)));
    }

    #[test]
    fn a_budget_bound_row_is_a_second_pass_candidate_and_nothing_else_is() {
        let mut exhausted = row("error_p0", RowOutcomeKind::Unknown, Some("budget-exhausted"));
        assert!(exhausted.is_budget_bound_unknown());
        exhausted.stop_reason = Some("inconclusive");
        assert!(!exhausted.is_budget_bound_unknown());
        assert!(
            !row("error_p1", RowOutcomeKind::Proved, Some("definitive")).is_budget_bound_unknown()
        );
        assert!(
            !row("error_p2", RowOutcomeKind::Unknown, Some("externally-cancelled"))
                .is_budget_bound_unknown()
        );
    }

    #[test]
    fn row_validation_timeout_is_the_deadline_remainder_between_floor_and_cap() {
        assert_eq!(row_validation_timeout(Duration::from_secs(60)), ROW_VALIDATION_CAP);
        assert_eq!(row_validation_timeout(Duration::from_secs(12)), Duration::from_secs(12));
        assert_eq!(row_validation_timeout(Duration::ZERO), ROW_VALIDATION_FLOOR);
    }

    #[test]
    fn per_obligation_budget_shares_what_remains_and_respects_the_cap() {
        assert_eq!(
            per_obligation_budget(Duration::from_secs(120), 4, Duration::from_secs(120)),
            Duration::from_secs(30)
        );
        // Unused time rolls forward: two rows left, 100s remaining → 50s each.
        assert_eq!(
            per_obligation_budget(Duration::from_secs(100), 2, Duration::from_secs(120)),
            Duration::from_secs(50)
        );
        // The per-solve cap still binds.
        assert_eq!(
            per_obligation_budget(Duration::from_secs(600), 1, Duration::from_secs(120)),
            Duration::from_secs(120)
        );
        assert_eq!(
            per_obligation_budget(Duration::ZERO, 3, Duration::from_secs(120)),
            Duration::ZERO
        );
        assert_eq!(
            per_obligation_budget(Duration::from_secs(10), 0, Duration::from_secs(120)),
            Duration::ZERO
        );
    }

    // ── deterministic mode as an explicit gate input (adoption step 6) ───────

    #[test]
    fn adaptive_parallel_is_the_default_for_ordinary_runs() {
        let envelope = resolve_execution_envelope(false, None, None);
        assert_eq!(envelope.mode, AdaptiveExecutionMode::AdaptiveParallel);
        assert_eq!(envelope.source, DeterministicSource::Default);
        assert!(!envelope.is_deterministic());
        assert_eq!(envelope.mode_label(), "adaptive-parallel");
    }

    #[test]
    fn the_cli_flag_selects_deterministic_sequential() {
        let envelope = resolve_execution_envelope(true, None, None);
        assert_eq!(envelope.mode, AdaptiveExecutionMode::DeterministicSequential);
        assert_eq!(envelope.source, DeterministicSource::Cli);
        assert_eq!(envelope.mode_label(), "deterministic-sequential");
    }

    #[test]
    fn env_switches_select_deterministic_and_are_ranked() {
        for value in ["1", "true", "YES", "on"] {
            let envelope = resolve_execution_envelope(false, Some(value), None);
            assert_eq!(
                envelope.source,
                DeterministicSource::TrustMcEnv,
                "TRUST_MC_AY_CHC_DETERMINISTIC={value} should select determinism"
            );
            assert!(envelope.is_deterministic());
        }
        let envelope = resolve_execution_envelope(false, None, Some("1"));
        assert_eq!(envelope.source, DeterministicSource::AyEnv);
        assert!(envelope.is_deterministic());
        // A falsy value is not a request.
        for value in ["0", "false", "", "off"] {
            let envelope = resolve_execution_envelope(false, Some(value), Some(value));
            assert_eq!(envelope.source, DeterministicSource::Default, "value={value}");
            assert_eq!(envelope.mode, AdaptiveExecutionMode::AdaptiveParallel);
        }
        // The CLI flag outranks the environment.
        assert_eq!(
            resolve_execution_envelope(true, Some("0"), Some("0")).source,
            DeterministicSource::Cli
        );
    }

    #[test]
    fn the_execution_envelope_records_the_deterministic_selection() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Unknown, Some("budget-exhausted")),
        ];
        let envelope = build_execution_envelope(
            resolve_execution_envelope(true, None, None),
            true,
            Duration::from_secs(30),
            &rows,
        );
        assert_eq!(envelope["schema"], PER_PROPERTY_ENVELOPE_SCHEMA);
        assert_eq!(envelope["execution"]["mode"], "deterministic-sequential");
        assert_eq!(envelope["execution"]["deterministic"], true);
        assert_eq!(envelope["execution"]["deterministic_source"], "cli:--ay-chc-deterministic");
        assert_eq!(envelope["execution"]["strict_proofs"], true);
        assert_eq!(envelope["execution"]["batch_budget_ms"], 30_000);
        assert_eq!(envelope["execution"]["obligation_count"], 2);
        assert_eq!(envelope["execution"]["proved"], 1);
        assert_eq!(envelope["execution"]["undecided"], 1);
        assert_eq!(envelope["rows"][1]["label"], "error_p1");
        assert_eq!(envelope["rows"][1]["outcome"], "unknown");
        assert_eq!(envelope["rows"][1]["stop_reason"], "budget-exhausted");
    }

    #[test]
    fn an_ordinary_run_records_adaptive_parallel_in_the_envelope() {
        let rows = vec![row("error_p0", RowOutcomeKind::Proved, Some("definitive"))];
        let envelope = build_execution_envelope(
            resolve_execution_envelope(false, None, None),
            true,
            Duration::from_secs(10),
            &rows,
        );
        assert_eq!(envelope["execution"]["mode"], "adaptive-parallel");
        assert_eq!(envelope["execution"]["deterministic"], false);
        assert_eq!(envelope["execution"]["deterministic_source"], "default");
    }

    // ── transcript metadata handoff (keeps the checked consumer working) ─────

    #[test]
    fn a_single_row_batch_publishes_the_rows_own_ay_transcript() {
        let rows = vec![row("error_p0", RowOutcomeKind::Proved, Some("definitive"))];
        let ay_metadata = serde_json::json!({
            "schema": "ay.chc-proof-transcript/v1",
            "accepted_as_proof": true,
            "result": "safe",
            "replay": {"status": "replayable"},
            "transcript": {"status": "replayable", "uri": "ay://t.json"},
        });
        let envelope = build_execution_envelope(
            resolve_execution_envelope(false, None, None),
            true,
            Duration::from_secs(10),
            &rows,
        );
        let published =
            transcript_metadata_for_batch(&rows, Some(ay_metadata), envelope).expect("metadata");
        // The checked consumer's keys are untouched...
        assert_eq!(published["schema"], "ay.chc-proof-transcript/v1");
        assert_eq!(published["replay"]["status"], "replayable");
        assert_eq!(published["transcript"]["status"], "replayable");
        // ...and the execution envelope rides alongside them.
        assert_eq!(published[EXECUTION_ENVELOPE_KEY]["execution"]["mode"], "adaptive-parallel");
    }

    #[test]
    fn a_multi_row_batch_never_publishes_one_rows_transcript_for_the_harness() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Proved, Some("definitive")),
        ];
        let ay_metadata = serde_json::json!({
            "schema": "ay.chc-proof-transcript/v1",
            "accepted_as_proof": true,
            "result": "safe",
        });
        let envelope = build_execution_envelope(
            resolve_execution_envelope(false, None, None),
            true,
            Duration::from_secs(10),
            &rows,
        );
        let published =
            transcript_metadata_for_batch(&rows, Some(ay_metadata), envelope).expect("metadata");
        assert_eq!(
            published["schema"], PER_PROPERTY_ENVELOPE_SCHEMA,
            "one row's transcript must never speak for an N-row harness"
        );
        assert_eq!(published["rows"].as_array().expect("rows").len(), 2);
    }

    // ── budget summary feeding the UNKNOWN classifier ────────────────────────

    #[test]
    fn budget_summary_reports_a_fully_timed_out_batch() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Unknown, Some("budget-exhausted")),
            row("error_p1", RowOutcomeKind::Unknown, Some("budget-exhausted")),
        ];
        let summary = budget_summary_from_rows(&rows);
        assert_eq!(summary.completed, 0);
        assert_eq!(summary.timed_out, 2);
        assert_eq!(summary.total_elapsed_ms, 10);
        let (engine, stop) = summary.first_non_completed.clone().expect("a non-completed row");
        assert_eq!(engine, "adaptive-portfolio[error_p0]");
        assert_eq!(stop, "budget-exhausted");
        // This is the shape `classify_unknown` turns into `PdrTimeout`.
        assert!(matches!(
            super::super::native::classify_unknown(&[], Some(&summary), true, None),
            super::super::native::UnknownCategory::PdrTimeout { timed_out_engines: 2, .. }
        ));
    }

    #[test]
    fn budget_summary_reports_an_inconclusive_batch_as_a_solver_error() {
        let rows = vec![row("error_p0", RowOutcomeKind::Unknown, Some("inconclusive"))];
        let summary = budget_summary_from_rows(&rows);
        assert_eq!(summary.completed, 0);
        assert_eq!(summary.timed_out, 0);
        assert!(matches!(
            super::super::native::classify_unknown(&[], Some(&summary), true, None),
            super::super::native::UnknownCategory::SolverError { .. }
        ));
    }

    #[test]
    fn budget_summary_counts_definitive_rows_as_completed() {
        let rows = vec![
            row("error_p0", RowOutcomeKind::Proved, Some("definitive")),
            row("error_p1", RowOutcomeKind::Proved, Some("definitive")),
        ];
        let summary = budget_summary_from_rows(&rows);
        assert_eq!(summary.completed, 2);
        assert!(summary.first_non_completed.is_none());
    }

    // ── transform selection parity with the aggregate path ──────────────────

    #[test]
    fn obligation_transforms_mirror_the_aggregate_selection() {
        let off = ObligationTransforms::from_args(false, &["scalarize".to_string()]);
        assert!(!off.scalarize && !off.split_ite && !off.split_or);

        let default_set = ObligationTransforms::from_args(true, &[]);
        assert!(default_set.scalarize && default_set.split_ite && default_set.split_or);

        let all = ObligationTransforms::from_args(true, &["all".to_string()]);
        assert!(all.scalarize && all.split_ite && all.split_or);

        let only_ite = ObligationTransforms::from_args(true, &["split-ite".to_string()]);
        assert!(!only_ite.scalarize && only_ite.split_ite && !only_ite.split_or);
    }

    // ── end-to-end batches over real BSEM-18 problems ───────────────────────

    fn test_options() -> PerPropertySolveOptions<'static> {
        PerPropertySolveOptions {
            verbose: false,
            skip_verify: false,
            batch_budget: Duration::from_secs(10),
            per_row_cap: Duration::from_secs(10),
            deadline: crate::deadline::Deadline::after(Duration::from_secs(60)),
            // Deterministic so the row ordering and stop reasons are stable.
            execution: resolve_execution_envelope(true, None, None),
            lemma_hints: &[],
            transforms: ObligationTransforms::default(),
            memory_budget: None,
            row_export: None,
        }
    }

    /// `error_p0` and `error_p1` are both unreachable: `Inv` holds only `x = 0`.
    const TWO_SAFE_PROPERTIES: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(declare-var x Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (< x 0)) error_p0))
(rule (=> (and (Inv x) (> x 100)) error_p1))
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

    /// Same shape, but `Inv` counts up and `error_p1` IS reachable at `x = 3`
    /// (three transitions in, so the counterexample carries real steps rather
    /// than the 0-step shape the #4182 guard refuses).
    const ONE_UNSAFE_PROPERTY: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(declare-var x Int)
(declare-var x1 Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (< x 5) (= x1 (+ x 1))) (Inv x1)))
(rule (=> (and (Inv x) (< x 0)) error_p0))
(rule (=> (and (Inv x) (= x 3)) error_p1))
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

    /// The export records each row exactly as it is handed to AY, and turning
    /// it on changes no verdict.
    #[test]
    fn the_row_export_records_every_row_as_handed_to_ay() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("h.smt2");
        std::fs::write(&smt_file, ONE_UNSAFE_PROPERTY).expect("fixture");
        let export = RowExport::begin(root.path(), "h", &smt_file, ONE_UNSAFE_PROPERTY)
            .expect("export dir is writable");
        let problem = ay::chc::ChcParser::parse(ONE_UNSAFE_PROPERTY).expect("fixture parses");
        let mut options = test_options();
        options.row_export = Some(&export);
        let exported = solve_chc_per_property(&problem, &options).expect("batch runs");
        let plain = solve_chc_per_property(&problem, &test_options()).expect("batch runs");
        assert!(matches!(exported, PerPropertyOutcome::Refuted { .. }));
        assert!(matches!(plain, PerPropertyOutcome::Refuted { .. }));

        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(root.path().join("h").join("manifest.json"))
                .expect("manifest"),
        )
        .expect("json");
        let batch = &manifest["per_property_batch"];
        assert_eq!(batch["reparse_check"]["status"], "ok");
        assert_eq!(batch["obligation_count"], 2);
        assert_eq!(batch["execution"]["mode"], "deterministic-sequential");
        let rows = manifest["rows"].as_array().expect("rows");
        assert_eq!(rows.len(), 2, "one record per row, solved or not");
        for row in rows {
            let identity = &row["identity"];
            assert_eq!(row["outcome"]["label"], identity["label"]);
            assert_eq!(row["outcome"]["content_sha256"], identity["content_sha256"]);
            if row["prepared_problem"].is_null() {
                continue;
            }
            assert_eq!(row["prepared_matches_reparse"], true);
            assert_eq!(
                row["slice_normalized_sha256"], identity["content_sha256"],
                "the recorded slice is the one AY's obligation digest names"
            );
            assert_eq!(row["solve_call"]["timeout_ms"], row["grant"]["row_budget_ms"]);
            assert_eq!(row["solve_call"]["proof_mode"], "None");
            assert_eq!(row["solve_call"]["strict_validation"], true);
            assert_eq!(row["solve_call"]["execution_mode"], "DeterministicSequential");
        }
        let solved: Vec<_> = rows.iter().filter(|row| !row["prepared_problem"].is_null()).collect();
        assert!(!solved.is_empty());
        assert!(
            rows.iter().any(|row| row["outcome"]["outcome"] == "refuted"),
            "the refuting row's outcome is recorded"
        );
        assert!(manifest["batch_reduction"].as_str().expect("reduction").starts_with("Refuted"));
    }

    #[test]
    fn a_two_property_problem_yields_one_solved_row_per_property() {
        let problem = ay::chc::ChcParser::parse(TWO_SAFE_PROPERTIES).expect("fixture parses");
        let outcome = solve_chc_per_property(&problem, &test_options()).expect("batch runs");
        let PerPropertyOutcome::Proved { report, .. } = outcome else {
            panic!("both properties are unreachable, so the batch must reduce to Proved");
        };
        // Both relations correlate back to the VC artifact table.
        assert_eq!(
            report.correlated_relations,
            ["error_p0".to_string(), "error_p1".to_string()].into_iter().collect::<HashSet<_>>()
        );
        // Multi-row batch: the envelope, never one row's AY transcript.
        let published = report.proof_transcript_metadata.expect("envelope is published");
        assert_eq!(published["schema"], PER_PROPERTY_ENVELOPE_SCHEMA);
        assert_eq!(published["execution"]["mode"], "deterministic-sequential");
        assert_eq!(published["execution"]["obligation_count"], 2);
        assert_eq!(published["execution"]["proved"], 2);
        let rows = published["rows"].as_array().expect("rows");
        assert_eq!(rows.len(), 2, "one row per property, not one aggregate verdict");
        for row in rows {
            assert_eq!(row["outcome"], "proved");
            assert_eq!(row["stop_reason"], "definitive");
            assert_eq!(row["relation"], row["label"]);
            assert_eq!(
                row["content_sha256"].as_str().expect("digest").len(),
                64,
                "each row is bound to the digest of its own sliced problem"
            );
        }
        assert_eq!(rows[0]["label"], "error_p0");
        assert_eq!(rows[1]["label"], "error_p1");
        assert_eq!(report.budget_summary.completed, 2);
    }

    #[test]
    fn a_refuted_property_fails_the_harness_and_names_its_relation() {
        let problem = ay::chc::ChcParser::parse(ONE_UNSAFE_PROPERTY).expect("fixture parses");
        let outcome = solve_chc_per_property(&problem, &test_options()).expect("batch runs");
        let PerPropertyOutcome::Refuted { counterexample, report, .. } = outcome else {
            panic!("a reachable error_p1 must refute the harness even though error_p0 is safe");
        };
        assert!(!counterexample.counterexample().steps.is_empty());
        assert_eq!(
            report.correlated_relations,
            ["error_p1".to_string()].into_iter().collect::<HashSet<_>>(),
            "the refutation must name the property that actually failed"
        );
        let published = report.proof_transcript_metadata.expect("envelope is published");
        assert_eq!(published["execution"]["refuted"], 1);
        let rows = published["rows"].as_array().expect("rows");
        // The safe sibling stays visible as its own proved row rather than being
        // swallowed by the harness-level failure.
        let p0 = rows.iter().find(|row| row["label"] == "error_p0").expect("error_p0 row");
        assert_eq!(p0["outcome"], "proved");
        let p1 = rows.iter().find(|row| row["label"] == "error_p1").expect("error_p1 row");
        assert_eq!(p1["outcome"], "refuted");
    }

    /// AY ask R2: the harness envelope reaches every row as
    /// `EncodeConfig::with_memory_budget`, which AY lowers onto the row
    /// portfolio's `AdaptiveConfig::memory_budget` (divided there across the
    /// portfolio's live engines). No envelope leaves AY's default untouched.
    #[test]
    fn the_memory_envelope_reaches_every_rows_portfolio_config() {
        let budget = Duration::from_secs(5);
        let unbudgeted = row_encode_config(budget, &test_options());
        assert_eq!(unbudgeted.memory_budget, None);
        assert_eq!(unbudgeted.to_adaptive_config().memory_budget(), None);

        let options = PerPropertySolveOptions { memory_budget: Some(3 << 30), ..test_options() };
        let config = row_encode_config(budget, &options);
        assert_eq!(config.memory_budget, Some(3 << 30));
        assert_eq!(config.to_adaptive_config().memory_budget(), Some(3 << 30));
        // The rest of the row policy is unchanged by the envelope.
        assert_eq!(config.timeout, Some(budget));
        assert_eq!(config.strict_validation, unbudgeted.strict_validation);
    }

    /// A generous envelope leaves the verdicts exactly as unbudgeted, and a
    /// zero envelope can only cost a verdict, never invent one.
    #[test]
    fn a_memory_envelope_never_changes_a_verdict_into_a_wrong_one() {
        let gib = 1024 * 1024 * 1024;
        let safe = ay::chc::ChcParser::parse(TWO_SAFE_PROPERTIES).expect("fixture parses");
        let refuted = ay::chc::ChcParser::parse(ONE_UNSAFE_PROPERTY).expect("fixture parses");
        let generous = PerPropertySolveOptions { memory_budget: Some(gib), ..test_options() };
        assert!(matches!(
            solve_chc_per_property(&safe, &generous).expect("batch runs"),
            PerPropertyOutcome::Proved { .. }
        ));
        assert!(matches!(
            solve_chc_per_property(&refuted, &generous).expect("batch runs"),
            PerPropertyOutcome::Refuted { .. }
        ));
        let zero = PerPropertySolveOptions { memory_budget: Some(0), ..test_options() };
        assert!(
            !matches!(solve_chc_per_property(&safe, &zero), Ok(PerPropertyOutcome::Refuted { .. })),
            "a safe problem must never refute, whatever the envelope"
        );
        assert!(
            !matches!(
                solve_chc_per_property(&refuted, &zero),
                Ok(PerPropertyOutcome::Proved { .. })
            ),
            "an unsafe problem must never prove, whatever the envelope"
        );
    }

    #[test]
    fn all_queries_pruned_binds_to_the_vacuity_accounting() {
        // The single query's body constraint simplifies to `false`, so AY prunes
        // it as vacuously safe and returns `Ok([])` — a validated problem with
        // no surviving property IDs.
        let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) false) false)))
(check-sat)
"#;
        let problem = ay::chc::ChcParser::parse(smt2).expect("fixture parses");
        assert_eq!(problem.query_obligations().expect("validated").len(), 0);
        let outcome = solve_chc_per_property(&problem, &test_options()).expect("batch runs");
        assert!(
            matches!(outcome, PerPropertyOutcome::AllQueriesPruned),
            "Ok([]) must be handed to the source-property/vacuity accounting, never \
             credited as a solved-and-proved row"
        );
    }

    #[test]
    fn an_ay_rejected_problem_stays_an_encoder_defect() {
        // No query at all: AY's `validate()` rejects the problem. That is our
        // encoding being wrong, not the solver declining to decide.
        let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#;
        let problem = ay::chc::ChcParser::parse(smt2).expect("fixture parses");
        let Err(err) = solve_chc_per_property(&problem, &test_options()) else {
            panic!("a problem AY rejects must not come back as a solve outcome");
        };
        assert!(
            format!("{err}").contains("Failed to parse CHC problem"),
            "the encoder-defect wording is load-bearing for SolverUnknownReason: {err}"
        );
        assert_eq!(
            crate::verification_provenance::SolverUnknownReason::from_chc_error(&err),
            crate::verification_provenance::SolverUnknownReason::ChcParseError,
        );
    }

    // ── row rendering stays diagnosable ─────────────────────────────────────

    #[test]
    fn row_marker_lines_name_the_property_and_the_stop_reason() {
        let mut record =
            row("error_p4_definition_2", RowOutcomeKind::Unknown, Some("inconclusive"));
        record.detail = "undecided (inconclusive)".to_string();
        let line = record.marker_line();
        assert!(line.starts_with("[AY:CHC-ROW:unknown]"), "{line}");
        assert!(line.contains("error_p4_definition_2"), "{line}");
        assert!(line.contains("[error_p4]"), "the correlated relation is shown: {line}");
        assert!(line.contains("stop_reason=inconclusive"), "{line}");
    }
}

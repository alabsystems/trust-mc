// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Native `ay-chc` portfolio backend entrypoint for CHC integration.

use std::collections::HashSet;
use std::path::Path;
use std::sync::OnceLock;
use std::time::Duration;

use ay::chc::engines;
use ay::chc::{
    AdaptiveConfig, AdaptivePortfolio, BmcConfig, CancellationToken, ChcExpr, ChcParser, ChcSort,
    ChcStatistics, InvariantModel, LemmaHint, PredicateId,
};
use ay_chc::ChcPdrProofRun;
use regex::Regex;
use trust_mc_metadata::HarnessMetadata;

use crate::args::AYChcEngine;
use crate::ay_parse::{load_loop_hints, vc_artifact_path_for_smt};
use crate::deadline::{Deadline, MIN_USEFUL_STAGE_BUDGET};
use crate::session::KaniSession;
use crate::verification_provenance::BUDGET_EXHAUSTED_BEFORE_STAGE;

use super::native_nullary::{
    constraint_free_nullary_error_derivation_relations,
    satisfiable_acyclic_error_derivation_witness_exported,
};
use super::owned_lane::{LaneExit, LaneJoinReport, LaneOutcome, OwnedLane, bmc_retry_budget};
use super::per_property::{
    ObligationTransforms, PerPropertyOutcome, PerPropertyReport, PerPropertySolveOptions,
    execution_envelope_from_env, solve_chc_per_property,
};
use super::resource_envelope::{HarnessMemoryEnvelope, bmc_with_envelope};
use super::row_export::RowExport;
use super::smt_analysis::{
    smt_error_query_has_false_error_obligation, smt_error_query_is_trivially_safe,
};
use super::{ChcSolverResult, acyclicity, auto_invariants, loop_hints, proof_core};

/// How long a cancelled solve lane may take to exit (AY's three-second
/// driver drain, asks T2/B2 and R1).
///
/// Cancellation in ay-chc is cooperative: the token is polled at stage
/// boundaries and inside the engine loops, so a lane stops promptly but not
/// instantly. Every lane is an [`OwnedLane`]: it is JOINED before the driver
/// starts another lane or returns to another harness, on every arm. A
/// cancelled lane still alive after this long is a FAILED drain, AY's
/// acceptance failure: it is reported (`[AY:LANE-DRAIN-FAILED]`) and still
/// joined (Rust cannot kill a thread, and returning would leave it beside the
/// next lane). Once joined it is gone, so the harness then goes on exactly as
/// after a lane that wound down in time: the acyclic shortcut falls through,
/// a forced lane ends in its guard-timeout UNKNOWN, and the external-fallback
/// gate applies as before. It used to be logged and abandoned, which is
/// exactly the overlap AY asked us to remove.
///
/// The join is bounded by the harness deadline: a lane still alive then is
/// quarantined (`[AY:LANE-ABANDONED]`, see `owned_lane`), and the harness ends
/// UNKNOWN with [`LANE_ABANDONED_PHRASE`].
const GUARD_CANCEL_DRAIN_SECS: u64 = 3;

/// Grace a guard allows a lane beyond the lane's OWN budget before abandoning
/// it. A cooperatively cancelled engine stops at a stage boundary, so a small
/// overshoot is normal and must not be read as a wedge.
const GUARD_GRACE: Duration = Duration::from_secs(5);

/// How long a guard may wait for a lane that was handed `lane_budget`.
///
/// `lane_budget + GUARD_GRACE`, CLAMPED to what is left of the per-harness
/// deadline. The clamp is the point: every lane budget here is
/// `deadline.clamp(...)`, computed BEFORE the lane starts, so `budget + grace`
/// sits *past* the deadline by construction — on a 15 s per-call budget the
/// acyclic-BMC guard is 20 s, and measured on this corpus (2026-09-14,
/// `kani/Intrinsics/bitreverse.rs`, `kani/ArithOperators/rem_float.rs`) it
/// spends all 20 s and then reports
/// `Acyclic BMC lane exceeded guard timeout (20s) — cancelled (still winding
/// down)`, leaving a cancelled-but-live lane competing with the decision
/// procedure that still has to run inside the same deadline.
///
/// This is the same rule the acyclic-witness search above already applies to
/// itself ("An optimisation must not be able to starve the decision procedure
/// behind it"), stated once for every guard in this file.
///
/// SHRINK-ONLY with respect to `lane_budget + GUARD_GRACE`, so it is
/// fail-closed: a guard that fires earlier only abandons a lane, and abandoning
/// a lane never asserts a verdict — the acyclic-BMC guard falls through to the
/// portfolio, and the forced-engine guard returns UNKNOWN. It cannot turn an
/// UNKNOWN into a proof.
///
/// # The clamp takes back the GRACE, not the lane's own budget (D4)
///
/// `lane_budget` is itself `deadline.clamp(...)`, computed BEFORE the lane
/// started; `remaining` is read HERE. So whenever the earlier clamp bound the
/// budget, any wall clock `T` spent since leaves `remaining` exactly `T` short
/// of a budget the lane was already promised, and a plain `min` would cut the
/// lane off before its own time ran out — discarding a verdict it may have been
/// about to produce. That can only LOSE a verdict, never mint one (see the
/// fail-closed note above), but losing verdicts is the bucket this whole branch
/// is trying to empty.
///
/// Below `GUARD_CANCEL_DRAIN_SECS` the cut buys nothing anyway: abandoning the
/// lane spends up to that long draining it. So a shortfall inside the drain
/// window keeps the promise — the guard may outlive the deadline by at most
/// `GUARD_CANCEL_DRAIN_SECS` — and a larger shortfall means the deadline has
/// genuinely moved on and is honoured.
pub(super) fn guard_timeout_within_deadline(
    lane_budget: Duration,
    deadline: &crate::deadline::Deadline,
) -> Duration {
    let with_grace = lane_budget + GUARD_GRACE;
    let remaining = deadline.remaining();
    if remaining >= with_grace {
        return with_grace;
    }
    if remaining >= lane_budget {
        // The clamp eats only the grace. This is the case the clamp was added
        // for, and the only one that ever fires on this corpus's 80 s harness
        // deadlines.
        return remaining;
    }
    let shortfall = lane_budget - remaining;
    if shortfall <= Duration::from_secs(GUARD_CANCEL_DRAIN_SECS) { lane_budget } else { remaining }
}

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        // Honor `--quiet` ("no output, just an exit code and requested
        // artifacts"): this macro used to write straight to stdout, so a quiet
        // run still printed `[AY:PROOF] CHC verification: ...` and the other
        // solver markers. The gate lives in the macro rather than at the ~70
        // call sites because several of them are free functions with no
        // `&KaniSession` in reach. Only the WRITE is skipped — the verdict and
        // the exit code are untouched — and with `--quiet` absent the bytes
        // are identical to before, which is what `scripts/ay-compiletest.sh`
        // parses.
        if !crate::args::common::quiet_output() {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            let _ = writeln!(handle, $($arg)*);
        }
    }};
}

/// Stable phrase of a lane abandoned at the harness deadline (see
/// [`GUARD_CANCEL_DRAIN_SECS`] and `owned_lane`'s quarantine).
///
/// Deliberately matches NEITHER phrase that opens the external `ay` proof
/// fallback (`call_ay::native_chc_error_allows_external_proof_fallback`:
/// "exceeded guard timeout", "returned Unknown - verification inconclusive"):
/// the lane is still alive, so nothing else may start beside it, and the
/// harness deadline has passed anyway. `SolverUnknownReason::from_chc_error`
/// files it as `Timeout`: the harness ran out of its deadline.
pub(crate) const LANE_ABANDONED_PHRASE: &str = "lane abandoned at the harness deadline";

/// How the harness goes on after one of its lanes has finished.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LaneDisposition {
    /// The lane has been joined (it is gone), whether or not a cancelled
    /// lane's drain failed: act on its outcome, on the remaining deadline.
    Continue,
    /// The lane was abandoned at the harness deadline and is quarantined, on
    /// whatever arm it ended: end the harness UNKNOWN with
    /// [`LANE_ABANDONED_PHRASE`], and use nothing the lane delivered.
    EndHarness,
}

/// The one rule both lane guards (the acyclic-BMC shortcut and the
/// forced-engine lanes) apply to a finished lane, on EVERY arm — result
/// delivered, guard timeout, disconnect.
///
/// A failed drain is reported (it is AY's acceptance failure), but it does not
/// end the harness: the lane was joined before this runs, so forfeiting the
/// harness's remaining lanes would prevent no overlap and would make the
/// harness's route depend on which side of the 3-s limit the lane's exit fell.
///
/// An ABANDONED lane ends the harness whatever it delivered. Abandonment means
/// the thread was still alive at the harness deadline (`OwnedLane::join_after`
/// holds until then, and never less than the drain limit), so the harness has
/// no time left and a lane is running. A lane that delivered its value and then
/// lingered in cleanup is no exception: using that value means post-solve work
/// (re-validation, cross-check, cover and vacuity queries) beside a live lane
/// and past the deadline. Before review round 2 the acyclic shortcut ended the
/// harness in that case (with a message that claimed a cancellation), while
/// the forced-engine path went on into `finish_native_chc_solve`. Both now end
/// it the same way, with wording that says what happened.
pub(super) fn lane_disposition(join: &LaneJoinReport) -> LaneDisposition {
    if join.abandoned() { LaneDisposition::EndHarness } else { LaneDisposition::Continue }
}

/// A finished lane, sorted by [`lane_disposition`]: what a guard acts on.
#[derive(Debug)]
pub(super) enum SettledLane<T> {
    /// Joined: act on the lane's own arm.
    Joined(LaneOutcome<T>),
    /// Abandoned at the harness deadline: end the harness with
    /// [`lane_abandoned_error`]. The outcome is kept only so the run log can
    /// name what the lane delivered; it is never used as a verdict.
    Abandoned(LaneOutcome<T>),
}

/// Apply [`lane_disposition`] to a finished lane. Both production guards call
/// this before they look at the lane's value.
pub(super) fn settle_lane<T>(outcome: LaneOutcome<T>, join: &LaneJoinReport) -> SettledLane<T> {
    match lane_disposition(join) {
        LaneDisposition::Continue => SettledLane::Joined(outcome),
        LaneDisposition::EndHarness => SettledLane::Abandoned(outcome),
    }
}

/// What the acyclic-BMC export records as the lane's cancellation contract.
/// Built from [`owned_lane::LANE_DRAIN_LIMIT`] so the number cannot drift.
/// Before review round 2 it said "the driver then waits up to 3000 ms (drain
/// limit) for the thread to exit", which stopped being true at `a8ea18162`.
fn acyclic_lane_cancellation_contract() -> String {
    format!(
        "the lane's CancellationToken (BmcConfig::with_cancellation) is cancelled when the guard \
         fires; the driver then waits for the thread to exit, reports a failed drain past {} ms \
         (the drain limit), and quarantines a lane still alive at the harness deadline",
        super::owned_lane::LANE_DRAIN_LIMIT.as_millis()
    )
}

/// How the guard-timeout lines describe the lane's wind-down.
fn lane_wind_down(join: &LaneJoinReport) -> String {
    if join.abandoned() {
        "still winding down at the harness deadline; quarantined".to_string()
    } else if join.drained_within_limit() {
        "wound down".to_string()
    } else {
        format!(
            "drain failed, wound down after {} ms of {} ms, joined",
            join.drain.as_millis(),
            join.drain_limit.as_millis()
        )
    }
}

/// Put one lane's join record in the run log: the `[AY:LANE-JOIN]` marker
/// always, the stage-timing line when enabled, `[AY:LANE-DRAIN-FAILED]` when a
/// cancelled lane outlived the drain, and `[AY:LANE-ABANDONED]` when it was
/// still alive at the harness deadline.
fn report_lane_join(join: &LaneJoinReport) {
    solver_stdout!("{}", join.marker_line());
    crate::stage_timing::record_elapsed(
        &format!("lane-join-{}", join.lane),
        join.drain,
        &join.stage_label(),
    );
    if join.drain_failed() {
        solver_stdout!(
            "[AY:LANE-DRAIN-FAILED] lane={} drain_ms={} drain_limit_ms={} then={} — the cancelled \
             lane outlived the drain (AY R1/B2 acceptance failure); {}",
            join.lane,
            join.drain.as_millis(),
            join.drain_limit.as_millis(),
            if join.abandoned() { "abandoned" } else { "joined" },
            if join.abandoned() {
                "it was still alive at the harness deadline"
            } else {
                "it was joined before anything else ran, and the harness continues on its \
                 remaining deadline"
            },
        );
    }
    if join.abandoned() {
        solver_stdout!(
            "[AY:LANE-ABANDONED] lane={} after_ms={} — still alive at the harness deadline: \
             quarantined (kept, and joined once it exits); no harness starts work while it \
             lives, and this harness ends UNKNOWN",
            join.lane,
            join.drain.as_millis(),
        );
    }
}

/// The harness-level UNKNOWN an abandoned lane ends in, worded for the arm
/// the lane ended on (only a timed-out lane was cancelled). Prints the UNKNOWN
/// marker the other bounded bails print.
fn lane_abandoned_error(join: &LaneJoinReport) -> anyhow::Error {
    solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
    anyhow::anyhow!("{}", lane_abandoned_message(join))
}

/// The wording of [`lane_abandoned_error`], without its marker (tests).
fn lane_abandoned_message(join: &LaneJoinReport) -> String {
    let what = match join.exit {
        LaneExit::TimedOut => format!(
            "the cancelled lane was still running {} ms after its cancellation",
            join.drain.as_millis()
        ),
        LaneExit::Completed => format!(
            "the lane delivered its result, but its thread was still running {} ms later, at \
             the harness deadline; nothing was cancelled, and the delivered result is not used",
            join.drain.as_millis()
        ),
        LaneExit::Disconnected | LaneExit::Panicked => format!(
            "the lane ended without a result, but its thread was still running {} ms later, at \
             the harness deadline",
            join.drain.as_millis()
        ),
    };
    format!(
        "ay-chc {} {LANE_ABANDONED_PHRASE}: {what}; it is quarantined, and no further solve work \
         starts for this harness",
        join.lane,
    )
}

/// The error a forced-engine lane's guard timeout ends in once the lane has
/// been joined (a failed drain included): the ordinary, fallback-eligible
/// guard-timeout UNKNOWN. An abandoned lane never gets here: `settle_lane`
/// ends the harness first.
fn forced_lane_timeout_error(label: &str, guard_timeout: Duration) -> anyhow::Error {
    anyhow::anyhow!("ay-chc {label} exceeded guard timeout ({guard_timeout:?})")
}

/// Re-validate a forced-engine lane's invariant model against the WHOLE
/// problem (ay#8578: verifier-side array scalarization off, so a
/// back-translated model is checked against the submitted CHC signature),
/// under `timeout`.
///
/// The caller draws `timeout` from the harness deadline with the row path's
/// policy (`per_property::row_validation_timeout`: what is left, capped at
/// AY's 30-s default, never below the 5-s floor that sits inside the
/// watchdog's headroom). Before review round 2 this call passed `None`, which
/// is AY's own fresh 30 s whatever was left of the harness, and it ran only
/// when the BMC cross-check had a budget, so a forced-lane proof with less
/// than the useful floor left was credited without it. It now always runs
/// (unless `--ay-chc-skip-verify`), bounded, and an expired budget is told
/// apart from a rejection exactly as for a proved row (`836e67d96`): a
/// rejection is a false proof, an expiry leaves the proof uncredited (the
/// established, fallback-eligible "validation ... timed out" wording), and
/// neither is ever credited.
fn revalidate_forced_lane_model(
    problem: &ay::chc::ChcProblem,
    model: &InvariantModel,
    verbose: bool,
    label: &str,
    timeout: Duration,
) -> anyhow::Result<()> {
    let started = std::time::Instant::now();
    let validation = validate_row_invariant_model(problem, model, verbose, timeout);
    crate::stage_timing::record(
        "forced-model-revalidation",
        started,
        match &validation {
            Ok(RowModelValidation::Valid) => "valid",
            Ok(RowModelValidation::Rejected) => "rejected",
            Ok(RowModelValidation::BudgetExhausted) => "budget-exhausted",
            Err(_) => "error",
        },
    );
    match validation? {
        RowModelValidation::Valid => Ok(()),
        RowModelValidation::Rejected => Err(reject_false_proof()),
        RowModelValidation::BudgetExhausted => {
            solver_stdout!(
                "[AY-chc] {label}: the invariant model re-validation ran out of its {timeout:?} \
                 budget (drawn from the harness deadline; AY's validator returns false on budget \
                 expiry) — the proof is not credited. Demoting to UNKNOWN."
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            Err(anyhow::anyhow!(
                "ay-chc external invariant model validation failed: the {label} model \
                 re-validation timed out at its {timeout:?} budget, drawn from the harness deadline"
            ))
        }
    }
}

/// A stable label for what the acyclic-BMC lane delivered (the stage-timing
/// outcome and the export's lane record). With `evidence`, a Safe also says
/// whether its evidence is proof-grade: used for the value a cancelled lane
/// delivered while winding down.
fn acyclic_lane_value_label(
    value: &std::thread::Result<AcyclicLaneResult>,
    evidence: bool,
) -> &'static str {
    match value {
        Ok(AcyclicLaneResult::Solved {
            result: ay::chc::VerifiedChcResult::Safe(_),
            proof_transcript_metadata,
            ..
        }) => {
            if !evidence
                || acyclic_bmc_safe_metadata_is_proof_grade(proof_transcript_metadata.as_ref())
            {
                "safe"
            } else {
                "safe-metadata-only"
            }
        }
        Ok(AcyclicLaneResult::Solved { result: ay::chc::VerifiedChcResult::Unsafe(_), .. }) => {
            "unsafe"
        }
        Ok(AcyclicLaneResult::Solved { .. }) => "inconclusive",
        Ok(AcyclicLaneResult::Refused(_)) => "retry-refused",
        Err(_) => "panic",
    }
}

/// What the acyclic-BMC lane hands back across its thread boundary.
enum AcyclicLaneResult {
    /// A BMC verdict: from the evidence run, or from the verdict-only retry
    /// (`retry` says why, and no evidence is published for it).
    Solved {
        result: ay::chc::VerifiedChcResult,
        proof_transcript_metadata: Option<serde_json::Value>,
        retry: Option<String>,
    },
    /// The evidence run failed and the retry was refused because the
    /// attempt's authority had closed: inconclusive, never a verdict.
    Refused(String),
}

/// Fail-closed pre-solve deadline gate.
///
/// The per-harness [`crate::deadline::Deadline`] was historically first
/// consulted only when computing the solve budget (`deadline.clamp` in
/// `try_ay_chc_solver`), so every pre-solve phase — SMT file read, bv2int
/// rewrite, CHC parse, nullary-fail expansion, the exact acyclic-witness
/// search, and the scalarize/split transforms — could run unbounded past the
/// harness budget until the process watchdog wall-killed the driver (missing
/// verdict, no markers). This gate is checked between phases: on an exhausted
/// budget it bails to the same honest bounded UNKNOWN shape a solver
/// guard-timeout takes (the caller in `call_ay.rs` converts the error into an
/// UNKNOWN verdict with `SolverUnknownReason::SolverError`).
///
/// Placement rule (fail-closed by construction): the first checks run BEFORE
/// the trivially-safe short-circuit PROOF paths, so an exhausted deadline can
/// never fall through into a success path. The bail message deliberately does
/// NOT match `native_chc_error_allows_external_proof_fallback` — with the
/// budget exhausted, an external proof fallback could only be a zero-budget
/// subprocess spawn.
fn bail_unknown_if_deadline_exhausted(
    deadline: crate::deadline::Deadline,
    phase: &str,
) -> anyhow::Result<()> {
    if !deadline.remaining().is_zero() {
        return Ok(());
    }
    solver_stdout!(
        "[AY-chc] per-harness deadline exhausted before pre-solve phase '{phase}' — \
         returning UNKNOWN"
    );
    solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
    anyhow::bail!("ay-chc per-harness deadline exhausted before pre-solve phase '{phase}'")
}

/// Deduplicate lemma hints by `(predicate, formula)` while preserving order.
pub(super) fn dedup_lemma_hints(hints: Vec<LemmaHint>) -> (Vec<LemmaHint>, usize) {
    let mut deduped = Vec::with_capacity(hints.len());
    let mut seen: HashSet<(PredicateId, ChcExpr)> = HashSet::new();
    let mut dropped = 0usize;

    for hint in hints {
        let key = (hint.predicate, hint.formula.clone());
        if seen.insert(key) {
            deduped.push(hint);
        } else {
            dropped += 1;
        }
    }

    (deduped, dropped)
}

/// Classification of why the CHC portfolio returned UNKNOWN.
///
/// Observability-only — used to emit a human-readable category tag alongside
/// the existing `[AY:UNKNOWN]` marker so users can triage without reading SMT.
/// Part of #4304 / #4301.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum UnknownCategory {
    /// The solve ran with LESS than its nominal per-call budget (or none at
    /// all) because the per-harness deadline had been spent before it —
    /// by the pre-solve phases, the acyclic-BMC shortcut, or an earlier
    /// harness of the same file. BUDGET-bound by construction, whatever the
    /// VC looks like, which is why this check precedes `ArrayParamLimit`: a
    /// row that never got its budget says nothing about array ceilings.
    BudgetExhausted { granted_ms: u128, nominal_ms: u128 },
    /// ≥2 Array-sorted state parameters on any predicate.
    ///
    /// DESCRIPTIVE, NOT CAUSAL. This records a structural property of the VC.
    /// It does NOT mean ay hit an array-parameter ceiling — measured
    /// 2026-08-02, that claim is false: ay proves a real 2-array VC
    /// (`check_pin`, 70 predicates → `sat`) and proves synthetic array-content
    /// problems with 2, 3 and 4 array params in both `(Array Int Int)` and
    /// `(Array (_ BitVec 64) (_ BitVec 32))`, with `AY_CHC_ARRAY_INV` on and
    /// off. The rows carrying this label ARE feature-bound (44/46 re-run at 8×
    /// budget converted nothing), but the responsible factor is unisolated:
    /// the unsolved VCs differ in array count AND predicate count (93–142 vs
    /// 45–70) simultaneously. See docs/ay-asks/2026-08-02-array-scale.
    ///
    /// Do not "fix" this by reordering it behind the `PdrTimeout` check —
    /// that would relabel these rows `PdrTimeout`, which is equally untrue of
    /// them: they timed out AT THE FULL budget. Only `BudgetExhausted` (the
    /// solve was starved of its nominal budget) legitimately precedes it.
    /// Remediation pointer: #4259 (heap-to-scalar promotion).
    ArrayParamLimit { predicate: String, array_sort_count: usize },
    /// Portfolio engines ran out of budget (PDR invariant synthesis timeout).
    PdrTimeout { timed_out_engines: usize, elapsed_ms: u128 },
    /// No engine completed and none timed out — all ran off into NotApplicable /
    /// Disabled / Unknown states.
    SolverError { engine_name: String, stop_reason: String },
    /// Problem had no rule deriving error — VC may be vacuously safe / encoding gap.
    /// Remediation pointer: #4284.
    NoErrorRule,
    /// None of the above matched.
    Uncategorized,
}

impl UnknownCategory {
    /// Render a single-line diagnostic suitable for stdout.
    pub(super) fn tag_line(&self) -> String {
        match self {
            Self::BudgetExhausted { granted_ms, nominal_ms } => format!(
                "[AY:UNKNOWN-CATEGORY] per-harness budget exhausted: the solve was granted \
                 {granted_ms}ms of its nominal {nominal_ms}ms"
            ),
            Self::ArrayParamLimit { predicate, array_sort_count } => format!(
                "[AY:UNKNOWN-CATEGORY] ≥2 Array-sorted state parameters \
                 (predicate={predicate}, array_sorts={array_sort_count}) — see #4259"
            ),
            Self::PdrTimeout { timed_out_engines, elapsed_ms } => format!(
                "[AY:UNKNOWN-CATEGORY] PDR invariant synthesis timeout \
                 ({elapsed_ms}ms, {timed_out_engines} engine(s) timed out)"
            ),
            Self::SolverError { engine_name, stop_reason } => format!(
                "[AY:UNKNOWN-CATEGORY] solver error (engine={engine_name}, \
                 stop_reason={stop_reason})"
            ),
            Self::NoErrorRule => {
                String::from("[AY:UNKNOWN-CATEGORY] no error rule encoded (see #4284)")
            }
            Self::Uncategorized => {
                String::from("[AY:UNKNOWN-CATEGORY] uncategorized — see verbose output")
            }
        }
    }
}

/// Return the count of `Array` sorts (recursively — `Array<_,Array<_,_>>`
/// counts as two) in a predicate's argument list.
fn count_array_sorts(sorts: &[ChcSort]) -> usize {
    fn walk(s: &ChcSort, acc: &mut usize) {
        if let ChcSort::Array(k, v) = s {
            *acc += 1;
            walk(k, acc);
            walk(v, acc);
        }
    }
    let mut n = 0;
    for s in sorts {
        walk(s, &mut n);
    }
    n
}

pub(super) fn scalar_acyclic_bmc_counterexample_is_trusted(
    problem: &ay::chc::ChcProblem,
    demoted_fallback_count: usize,
) -> bool {
    if demoted_fallback_count != 0 {
        return false;
    }

    fn is_scalar_sort(sort: &ChcSort) -> bool {
        matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_))
    }

    problem.predicates().iter().all(|predicate| predicate.arg_sorts.iter().all(is_scalar_sort))
}

/// Safe analogue of [`scalar_acyclic_bmc_counterexample_is_trusted`].
///
/// The acyclic-BMC lane's `solve_bmc_only` returns Safe only when it has a
/// COMPLETE bounded proof: the ay side already gated it behind
/// `bmc_only_safe_is_complete_bounded_proof` (acyclic + exhausted_search +
/// !budget_exhausted + full depth) and `bmc_only_empty_safe_is_proof_grade`
/// (scalar Bool/Int/BV + finite datatypes; arrays/reals/recursive datatypes
/// excluded). `exhausted_search` is set ONLY on a definite full-DAG UNSAT
/// (SMT-unknown and SAT never set it), and a definite UNSAT of the fully
/// unrolled acyclic query disjunction is a complete safety proof for those
/// decidable finite-value theories — including bit-vectors. We additionally
/// require scalar predicate sorts (mirroring the CTREX gate, so arrays/reals/
/// datatypes never reach this trust boundary here) and no demoted fallbacks;
/// the crate-wide `demote_for_all_unsoundness` pass still backstops every other
/// unsoundness category post-hoc, so an under-constrained encoding cannot slip
/// through as a false proof.
pub(super) fn scalar_acyclic_bmc_safe_is_trusted(
    problem: &ay::chc::ChcProblem,
    demoted_fallback_count: usize,
) -> bool {
    if demoted_fallback_count != 0 {
        return false;
    }

    fn is_scalar_sort(sort: &ChcSort) -> bool {
        matches!(sort, ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(_))
    }

    problem.predicates().iter().all(|predicate| predicate.arg_sorts.iter().all(is_scalar_sort))
}

pub(super) fn panic_payload_message(panic_payload: &(dyn std::any::Any + Send)) -> &str {
    panic_payload
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .or_else(|| panic_payload.downcast_ref::<&str>().copied())
        .unwrap_or("<non-string panic>")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NativeSolveMode {
    AdaptivePortfolio,
    PrimaryEngineOnly,
    BmcOnly,
}

impl NativeSolveMode {
    fn label(self) -> &'static str {
        match self {
            Self::AdaptivePortfolio => "adaptive-portfolio",
            Self::PrimaryEngineOnly => "primary-engine-only",
            Self::BmcOnly => "bmc-only",
        }
    }
}

pub(super) fn select_native_solve_mode(engine: AYChcEngine, no_retry: bool) -> NativeSolveMode {
    match (engine, no_retry) {
        (AYChcEngine::Bmc, _) => NativeSolveMode::BmcOnly,
        (AYChcEngine::Pdr, _) | (AYChcEngine::Auto, true) => NativeSolveMode::PrimaryEngineOnly,
        (AYChcEngine::Auto, false) => NativeSolveMode::AdaptivePortfolio,
    }
}

pub(super) fn native_bmc_per_depth_timeout(total_budget: Duration) -> Duration {
    if total_budget.is_zero() {
        return Duration::from_millis(1);
    }

    let floor = total_budget.min(Duration::from_secs(1));
    (total_budget / 4).min(Duration::from_secs(10)).max(floor)
}

fn native_bmc_cross_check_budget(total_budget: Duration) -> Duration {
    total_budget.min(Duration::from_secs(30))
}

/// `TRUST_MC_CHC_BMC_CROSSCHECK=always` restores the whole-problem BMC
/// cross-check on per-property verdicts (the measurement counterfactual).
pub(super) const BMC_CROSSCHECK_ENV: &str = "TRUST_MC_CHC_BMC_CROSSCHECK";

fn bmc_crosscheck_forced_from_env() -> bool {
    std::env::var(BMC_CROSSCHECK_ENV).is_ok_and(|v| v.trim().eq_ignore_ascii_case("always"))
}

/// Whether the BMC cross-check of a native PROOF or CTREX runs at all
/// (before its budget is asked for).
///
/// * `--ay-chc-skip-verify` turns every post-solve defence off, as before.
/// * A per-property verdict (`per_row_validated`) already stands on two
///   validations: AY's portfolio pipeline built the `VerifiedInvariant` /
///   `VerifiedCounterexample` (its constructors are crate-private to that
///   pipeline), and every proved row's model was re-validated by the driver
///   against the row's own problem (`validate_row_invariant_model`).
///   The cross-check could only DEMOTE such a verdict to UNKNOWN; across the
///   1134-row CHC corpus run of 2026-09-13 it never did (no `FALSE PROOF
///   DETECTED: BMC cross-check` and no `SPURIOUS CTREX DETECTED` line in any
///   log), while it cost up to min(T, 30s) on every decided harness. A
///   demoted CTREX prints `VERIFICATION:- FAILED` exactly like the CTREX it
///   replaces, so skipping that half cannot move a verdict line at all.
/// * One-shot forced-engine lanes keep it: they have only the first layer,
///   plus the whole-problem model re-validation
///   (`revalidate_forced_lane_model`), which does not depend on it.
fn bmc_crosscheck_runs(skip_verify: bool, per_row_validated: bool, forced: bool) -> bool {
    !skip_verify && (forced || !per_row_validated)
}

/// Where the acyclic-BMC shortcut runs relative to the per-property batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AcyclicBmcOrder {
    /// In front of the batch (the order before 2026-09-14).
    First,
    /// Only when the batch did not decide the harness (undecided, or an
    /// error such as a rejected proof): the default. Every harness the
    /// shortcut could decide before, it can still decide — it merely no
    /// longer taxes the harnesses the batch decides on its own.
    AfterUndecidedBatch,
}

/// `TRUST_MC_CHC_ACYCLIC_BMC_ORDER=first` restores the old order.
pub(super) const ACYCLIC_BMC_ORDER_ENV: &str = "TRUST_MC_CHC_ACYCLIC_BMC_ORDER";

fn parse_acyclic_bmc_order(value: Option<&str>) -> AcyclicBmcOrder {
    match value.map(|v| v.trim().to_ascii_lowercase()) {
        Some(v) if v == "first" => AcyclicBmcOrder::First,
        _ => AcyclicBmcOrder::AfterUndecidedBatch,
    }
}

fn acyclic_bmc_order_from_env() -> AcyclicBmcOrder {
    parse_acyclic_bmc_order(std::env::var(ACYCLIC_BMC_ORDER_ENV).ok().as_deref())
}

/// Budget for AY's post-solve CHECKED replay pass (parity-wishlist item 7).
///
/// `VerifiedChcResult::checked_proof_transcript_metadata` renders the sealed
/// result's proof obligations, re-executes every one on a FRESH executor
/// within this budget, and only on success emits the full Route-B admission
/// field set (`replay.status=replayable`, `transcript.{status,uri,sha256}`,
/// `replay.sha256`, `checked_report.sha256`) that
/// `harness_runner::trust_trust_mc_chc_pdr_evidence_payload` validates.
/// FAIL-CLOSED: a zero/exhausted budget, executor error/panic/unknown, wrong
/// obligation verdict, or digest mismatch yields the exact pre-existing
/// metadata-only (non-admissible) metadata — i.e. the historical
/// `[AY:NATIVE_PROOF_GRADE:rejected:replay_not_replayable]` outcome. The
/// checked pass can therefore never upgrade a bad proof, only admit a
/// re-verified one.
///
/// Policy: by default, a third of the harness solve budget capped at 20s
/// (replay is typically much cheaper than the original solve). An explicit
/// `TRUST_MC_AY_CHECKED_REPLAY_SECS` integer replaces that default, capped by
/// the current solve budget so replay cannot outlive its authority envelope;
/// `0` disables the replay pass entirely and AY fail-closes to the old
/// metadata-only path. Invalid overrides are ignored.
fn checked_replay_budget_from_override(
    full_timeout: Duration,
    override_value: Option<&str>,
) -> Duration {
    if let Some(raw) = override_value {
        if let Ok(secs) = raw.trim().parse::<u64>() {
            return Duration::from_secs(secs).min(full_timeout);
        }
    }
    (full_timeout / 3).min(Duration::from_secs(20))
}

fn checked_replay_budget(full_timeout: Duration) -> Duration {
    let override_value = std::env::var("TRUST_MC_AY_CHECKED_REPLAY_SECS").ok();
    checked_replay_budget_from_override(full_timeout, override_value.as_deref())
}

fn bounded_native_bmc_config(
    config: BmcConfig,
    total_budget: Duration,
    verbose: bool,
) -> BmcConfig {
    config
        .with_time_budget(total_budget)
        .with_per_depth_timeout(native_bmc_per_depth_timeout(total_budget))
        .with_verbose(verbose)
}

/// `budget` is already the cross-check's own budget — see
/// `KaniSession::cross_check_budget`, which caps it and clamps it to the
/// per-harness deadline.
fn native_bmc_cross_check_config(budget: Duration, verbose: bool) -> BmcConfig {
    bounded_native_bmc_config(BmcConfig::cross_check(), budget, verbose)
}

/// Summary of the ay-chc budget report, reduced to primitive fields so the
/// classifier can be unit-tested without depending on `BudgetReport` types
/// (which are not re-exported from the `ay::chc` facade).
#[derive(Debug, Clone, Default)]
pub(super) struct BudgetSummary {
    pub(super) completed: usize,
    pub(super) timed_out: usize,
    pub(super) total_elapsed_ms: u128,
    /// First non-completed engine, used for the SolverError tag.
    /// `(engine_name, stop_reason_display)`.
    pub(super) first_non_completed: Option<(String, String)>,
}

fn json_bytes(value: &serde_json::Value) -> Vec<u8> {
    serde_json::to_vec(value).unwrap_or_else(|_| value.to_string().into_bytes())
}

fn acyclic_bmc_safe_metadata_is_proof_grade(metadata: Option<&serde_json::Value>) -> bool {
    let Some(metadata) = metadata else {
        return false;
    };
    metadata.get("accepted_as_proof").and_then(serde_json::Value::as_bool) == Some(true)
        && metadata.get("result").and_then(serde_json::Value::as_str) == Some("safe")
        && metadata
            .get("replay")
            .and_then(|value| value.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("replayable")
        && metadata
            .get("transcript")
            .and_then(|value| value.get("status"))
            .and_then(serde_json::Value::as_str)
            == Some("replayable")
        && metadata
            .get("transcript")
            .and_then(|value| value.get("metadata_only"))
            .and_then(serde_json::Value::as_bool)
            != Some(true)
}

fn ay_chc_proof_run_artifact_descriptor(
    artifact: &ay_chc::ChcProofRunArtifact,
) -> serde_json::Value {
    serde_json::json!({
        "schema": artifact.schema(),
        "role": artifact.role(),
        "digest": artifact.digest().to_json_value(),
    })
}

fn pdr_proof_run_verdict(
    run: &ChcPdrProofRun,
    problem: &ay_chc::ChcProblem,
    obligation_id: &str,
) -> trust_mc_core::FullVerificationVerdict {
    let metadata = run.metadata().to_json_value();
    if !run.accepted_as_proof() || !run.metadata().accepted_as_proof() {
        return trust_mc_core::FullVerificationVerdict::Unknown {
            reason: "ay ChcPdrProofRun was not accepted_as_proof".to_string(),
        };
    }

    match &run.result() {
        ay_chc::VerifiedChcResult::Safe(verified_inv) => {
            let normalized_input = ay_chc::normalized_chc_input(problem);
            let obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
                obligation_id,
                trust_mc_core::MirObligationKind::Assertion,
                &normalized_input,
            );
            if obligation.normalized_input_hash.value != run.metadata().normalized_input_sha256() {
                return trust_mc_core::FullVerificationVerdict::Unknown {
                    reason: "ay normalized input hash does not match trust-mc evidence hash"
                        .to_string(),
                };
            }

            let stats = trust_mc_core::ChcPdrStats {
                relation_count: problem.predicates().len(),
                clause_count: problem.clauses().len(),
            };
            let proof_run_artifacts = run.proof_run_artifacts();
            let Some(invariant_model_artifact) =
                proof_run_artifacts.quantifier_free_invariant_model()
            else {
                return trust_mc_core::FullVerificationVerdict::Unknown {
                    reason:
                        "ay Safe result has no strict replayable quantifier-free invariant artifact"
                            .to_string(),
                };
            };
            let transcript_bytes = proof_run_artifacts.replay_transcript().bytes().to_vec();
            let transcript_hash = trust_mc_core::EvidenceHash::sha256_bytes(&transcript_bytes);
            let invariant_model_bytes = invariant_model_artifact.bytes().to_vec();
            let consumer_evidence = run.consumer_evidence().to_json_value();
            let replay = serde_json::json!({
                "schema": "trust_mc.chc-pdr-proof-replay/v3",
                "source": "ay_chc::ChcPdrProofRun::proof_run_artifacts",
                "ay_candidate_accepted": run.accepted_as_proof(),
                "normalized_input_sha256": run.metadata().normalized_input_sha256(),
                "referenced_solver_transcript": {
                    "kind": "solver_transcript",
                    "algorithm": transcript_hash.algorithm,
                    "value": transcript_hash.value,
                },
                "ay_artifacts": {
                    "quantifier_free_invariant_model": ay_chc_proof_run_artifact_descriptor(
                        invariant_model_artifact
                    ),
                    "diagnostic_model_metadata": ay_chc_proof_run_artifact_descriptor(
                        &proof_run_artifacts.model()
                    ),
                    "replay_transcript": ay_chc_proof_run_artifact_descriptor(
                        &proof_run_artifacts.replay_transcript()
                    ),
                },
                "ay_consumer_evidence": consumer_evidence.clone(),
                "ay_transcript_metadata": metadata.clone(),
            });
            let replay_bytes = json_bytes(&replay);
            let replay_log_hash = trust_mc_core::EvidenceHash::sha256_bytes(&replay_bytes);
            let checked_report = serde_json::json!({
                "schema": "trust_mc.chc-pdr-checked-proof-report/v3",
                "ay_candidate_accepted": run.accepted_as_proof(),
                "problem_kind": "chc-pdr",
                "proof_status": run.metadata().proof_status(),
                "result": run.metadata().result(),
                "replay_check_status": {
                    "replay": "not-run-by-private-consumer",
                    "check": "unknown",
                    "fresh_private_consumer_replay_required": true,
                    "authoritative": false,
                },
                "checked_artifacts": {
                    "quantifier_free_invariant_model": ay_chc_proof_run_artifact_descriptor(
                        invariant_model_artifact
                    ),
                    "diagnostic_model_metadata": ay_chc_proof_run_artifact_descriptor(
                        &proof_run_artifacts.model()
                    ),
                    "replay_transcript": ay_chc_proof_run_artifact_descriptor(
                        &proof_run_artifacts.replay_transcript()
                    ),
                    "replay_log": {
                        "algorithm": replay_log_hash.algorithm,
                        "value": replay_log_hash.value,
                        "bytes": replay_bytes.len(),
                    },
                },
                "referenced_solver_transcript": {
                    "kind": "solver_transcript",
                    "algorithm": transcript_hash.algorithm,
                    "value": transcript_hash.value,
                },
                "referenced_replay_log": {
                    "kind": "replay_log",
                    "algorithm": replay_log_hash.algorithm,
                    "value": replay_log_hash.value,
                },
                "stats": {
                    "relation_count": stats.relation_count,
                    "clause_count": stats.clause_count,
                },
                "ay_consumer_evidence": consumer_evidence,
                "ay_transcript_metadata": metadata.clone(),
            });
            let checked_report_bytes = json_bytes(&checked_report);

            let Ok(proof) =
                trust_mc_core::ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
                    obligation,
                    stats,
                    verified_inv.model().len(),
                    ("ay://chc-pdr/proof-run-replay-transcript.json", &transcript_bytes),
                    ("trust_mc://chc-pdr/replay-log.json", &replay_bytes),
                    ("trust_mc://chc-pdr/checked-proof-report.json", &checked_report_bytes),
                    ("ay://chc-pdr/pdr-invariant-model.json", &invariant_model_bytes),
                )
            else {
                return trust_mc_core::FullVerificationVerdict::Unknown {
                    reason: "AY proof artifacts were empty or exceeded the materialization limit"
                        .to_string(),
                };
            };
            trust_mc_core::FullVerificationVerdict::Proved {
                evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
            }
        }
        ay_chc::VerifiedChcResult::Unsafe(verified_cex) => {
            let counterexample = serde_json::json!({
                "schema": "trust_mc.chc-pdr-counterexample/v1",
                "accepted_as_proof": run.accepted_as_proof(),
                "step_count": verified_cex.counterexample().steps.len(),
                "counterexample_debug": format!("{:?}", verified_cex.counterexample()),
                "ay_metadata": metadata.clone(),
            });
            let counterexample_bytes = json_bytes(&counterexample);
            trust_mc_core::FullVerificationVerdict::Failed {
                counterexample_artifacts: vec![
                    trust_mc_core::FullVerificationArtifact::from_bytes(
                        trust_mc_core::FullVerificationArtifactKind::CounterexampleTrace,
                        "ay://chc-pdr/counterexample.json",
                        &counterexample_bytes,
                    ),
                ],
            }
        }
        ay_chc::VerifiedChcResult::Unknown(marker) => {
            trust_mc_core::FullVerificationVerdict::Unknown {
                reason: format!("ay ChcPdrProofRun returned Unknown: {:?}", marker.reason()),
            }
        }
        _ => trust_mc_core::FullVerificationVerdict::Unknown {
            reason: "ay ChcPdrProofRun returned an unsupported result variant".to_string(),
        },
    }
}

/// What a budgeted re-validation of a proved row's invariant model found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RowModelValidation {
    /// AY's external validator accepted the model.
    Valid,
    /// The validator rejected the model before its budget ran out: a false
    /// proof, and the harness is demoted exactly as before.
    Rejected,
    /// The validator returned "not valid" only once its budget had run out.
    /// AY's `validate_external_invariant_model` answers `Ok(false)` both for
    /// a rejected model and for an expired validation budget (its
    /// `verify_model_with_budget` treats expiry as rejection), so a `false`
    /// that arrives at or past the budget does not show the model is wrong.
    /// Measured on `expected/uninit/alloc-to-slice` `error_p17` at ay
    /// 22db3bcc1: the same invariant is `Ok(false)` at a 1136 ms budget (after
    /// 1137-1163 ms) and `Ok(true)` in 0.9-1.6 s at 5, 30 and 120 s. The row
    /// is not credited; it is not reported as a false proof either.
    BudgetExhausted,
}

/// Re-validate a proved row's model under `timeout`, telling a rejection
/// apart from an expired budget (see [`RowModelValidation`]).
///
/// AY sets the validation deadline after building its verifier, so a `false`
/// caused by the deadline always arrives at or past `timeout` on this
/// clock; a rejection that happens to land there too is classified as
/// budget-exhausted, which still leaves the row uncredited (fail-closed).
pub(super) fn validate_row_invariant_model(
    problem: &ay::chc::ChcProblem,
    model: &InvariantModel,
    verbose: bool,
    timeout: Duration,
) -> anyhow::Result<RowModelValidation> {
    let mut pdr_config = ay::chc::PdrConfig::default();
    pdr_config.verbose = verbose;
    pdr_config.solve_timeout = Some(timeout);
    let started = std::time::Instant::now();
    match engines::validate_external_invariant_model(problem, model, &pdr_config) {
        Ok(true) => Ok(RowModelValidation::Valid),
        Ok(false) if started.elapsed() >= timeout => Ok(RowModelValidation::BudgetExhausted),
        Ok(false) => Ok(RowModelValidation::Rejected),
        Err(err) => {
            solver_stdout!(
                "[AY-chc] PDR invariant model external validation failed closed ({err}). \
                 Demoting to UNKNOWN."
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            anyhow::bail!("ay-chc external invariant model validation failed: {err}");
        }
    }
}

/// The false-proof demotion a rejected model gets (the wording is what the
/// unknown-reason classifier reads as `FalseProofRejected`).
pub(super) fn reject_false_proof() -> anyhow::Error {
    solver_stdout!(
        "[AY-chc] FALSE PROOF DETECTED: external invariant model failed \
         full clause verification in fresh solver (ay#8578). Demoting to UNKNOWN."
    );
    solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
    anyhow::anyhow!(
        "ay-chc false proof detected: external invariant model fails clause verification"
    )
}

/// `timeout`: the validator's solve budget. `None` keeps AY's own default
/// (`PDR_PROOF_VALIDATION_TIMEOUT`, 30s).
///
/// Test-only since review round 2: every production re-validation now goes
/// through [`validate_row_invariant_model`], which takes an explicit budget
/// drawn from the harness deadline and tells an expired budget apart from a
/// rejection. The tests below keep pinning AY's validator contract through it.
#[cfg(test)]
pub(super) fn validate_external_pdr_invariant_model(
    problem: &ay::chc::ChcProblem,
    model: &InvariantModel,
    verbose: bool,
    timeout: Option<Duration>,
) -> anyhow::Result<()> {
    let mut pdr_config = ay::chc::PdrConfig::default();
    pdr_config.verbose = verbose;
    if timeout.is_some() {
        pdr_config.solve_timeout = timeout;
    }

    match engines::validate_external_invariant_model(problem, model, &pdr_config) {
        Ok(true) => Ok(()),
        Ok(false) => {
            solver_stdout!(
                "[AY-chc] FALSE PROOF DETECTED: external invariant model failed \
                 full clause verification in fresh solver (ay#8578). Demoting to UNKNOWN."
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            anyhow::bail!(
                "ay-chc false proof detected: external invariant model fails clause verification"
            );
        }
        Err(err) => {
            solver_stdout!(
                "[AY-chc] PDR invariant model external validation failed closed ({err}). \
                 Demoting to UNKNOWN."
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            anyhow::bail!("ay-chc external invariant model validation failed: {err}");
        }
    }
}

/// What the solve was actually allowed to run for, against what
/// `--harness-timeout` nominally grants one call. `granted < nominal` means
/// the per-harness deadline clamped the solve — it was starved, and its
/// UNKNOWN is budget-bound whatever the engines reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct SolveBudgetGrant {
    pub(super) granted: Duration,
    pub(super) nominal: Duration,
}

impl SolveBudgetGrant {
    /// `Deadline::clamp` returns the cap itself (not a recomputed duration)
    /// whenever the remainder covers it, so this comparison is exact: no
    /// clock noise can make a fully funded solve look starved.
    pub(super) fn starved(&self) -> bool {
        self.granted < self.nominal
    }
}

/// Pure classifier for UNKNOWN outcomes. Tested independently of the solver.
///
/// `predicate_array_counts` is `(predicate_name, array_sort_count)` per predicate,
/// typically collected from `ChcProblem::predicates()` before the problem is
/// moved into the solver.
///
/// Priority order (most specific first):
/// 1. No error rule → degenerate VC
/// 2. The solve was starved of its nominal budget by the per-harness
///    deadline → budget exhausted (see `UnknownCategory::BudgetExhausted`;
///    this precedes every structural label because a starved row says
///    nothing about the VC)
/// 3. ≥2 Array-sorted state params on any predicate → structural label only
///    (see `UnknownCategory::ArrayParamLimit`; this is NOT a proven solver
///    ceiling, and it deliberately preempts the FULL-budget timeout check
///    because those rows are not budget-bound either — measured)
/// 4. All engines either timed out or yielded inconclusive results:
///    - at least one timeout → PDR timeout
///    - otherwise (NotApplicable / Disabled / Unknown only) → solver error
/// 5. Fallthrough → uncategorized
pub(super) fn classify_unknown(
    predicate_array_counts: &[(String, usize)],
    budget: Option<&BudgetSummary>,
    has_error_rule: bool,
    grant: Option<SolveBudgetGrant>,
) -> UnknownCategory {
    // 1. Degenerate VC (no rule derives error).
    if !has_error_rule {
        return UnknownCategory::NoErrorRule;
    }

    // 2. The solve never got its budget: budget-bound before anything
    //    structural can be said.
    if let Some(grant) = grant.filter(SolveBudgetGrant::starved) {
        return UnknownCategory::BudgetExhausted {
            granted_ms: grant.granted.as_millis(),
            nominal_ms: grant.nominal.as_millis(),
        };
    }

    // 3. ≥2 Array-sorted state params on any predicate.
    if let Some((name, n)) = predicate_array_counts.iter().find(|(_, n)| *n >= 2) {
        return UnknownCategory::ArrayParamLimit { predicate: name.clone(), array_sort_count: *n };
    }

    // 4/5. Budget-summary-driven classification.
    if let Some(b) = budget {
        if b.completed == 0 && b.timed_out > 0 {
            return UnknownCategory::PdrTimeout {
                timed_out_engines: b.timed_out,
                elapsed_ms: b.total_elapsed_ms,
            };
        }
        if b.completed == 0 {
            if let Some((engine_name, stop_reason)) = &b.first_non_completed {
                return UnknownCategory::SolverError {
                    engine_name: engine_name.clone(),
                    stop_reason: stop_reason.clone(),
                };
            }
        }
    }

    UnknownCategory::Uncategorized
}

/// What a native CHC lane decided, normalized across the per-property batch and
/// the forced-engine one-shots.
///
/// Deliberately NOT `ay::chc::VerifiedChcResult`: the per-property lane reduces
/// N independently verified rows, and there is no single AY result object that
/// honestly represents that reduction. Keeping the driver's own three-way
/// verdict makes it impossible to accidentally present one row's sealed result
/// as if AY had produced it for the whole harness.
enum NativeSolveVerdict {
    Safe(ay::chc::VerifiedInvariant),
    Unsafe(ay::chc::VerifiedCounterexample),
    /// Neither proved nor refuted. `summary` explains why, and is appended to
    /// the UNKNOWN bail message so per-row detail survives into the report.
    Undecided {
        summary: String,
    },
}

/// Everything the shared post-solve interpretation needs, so the two lanes
/// cannot drift apart on the fail-closed defences.
struct NativeSolveFinish<'a> {
    smt_file: &'a Path,
    smt_content: &'a str,
    solver_smt_content: &'a str,
    harness: &'a HarnessMetadata,
    demoted_fallback_count: usize,
    solve_mode: NativeSolveMode,
    timeout: Duration,
    /// The per-harness deadline every post-solve stage budgets against.
    deadline: Deadline,
    /// What the solve was granted against its nominal budget, for
    /// `classify_unknown`.
    grant: SolveBudgetGrant,
    verbose: bool,
    has_error_rule: bool,
    predicate_array_snapshot: &'a [(String, usize)],
    budget_summary: Option<BudgetSummary>,
    proof_transcript_metadata: Option<serde_json::Value>,
    native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
    /// Problem to re-validate a claimed invariant model against, or `None` when
    /// that gate has ALREADY run against the problem the model interprets.
    revalidate_invariant_against: Option<&'a ay::chc::ChcProblem>,
    /// The verdict comes from the per-property batch, whose every row was
    /// validated by AY's portfolio pipeline (a `VerifiedInvariant` /
    /// `VerifiedCounterexample` cannot be constructed otherwise) AND, for a
    /// proved row, re-validated by the driver against the row's own problem.
    /// The whole-problem BMC cross-check is then a third layer over two, and
    /// is skipped unless `TRUST_MC_CHC_BMC_CROSSCHECK=always` — see
    /// [`bmc_crosscheck_runs`].
    per_row_validated: bool,
    /// Problem used to resolve counterexample steps to predicate names.
    counterexample_problem: &'a ay::chc::ChcProblem,
    /// Per-property relations the solve seam correlated independently of the
    /// counterexample trace (BSEM-18 obligation labels).
    correlated_failing_relations: &'a HashSet<String>,
    /// The harness's memory envelope, for the BMC cross-check (AY ask R2).
    memory_envelope: Option<HarnessMemoryEnvelope>,
}

impl KaniSession {
    /// Try to run CHC verification using native ay-chc portfolio solver.
    ///
    /// This method uses ay-chc's native Rust API to solve CHC problems with a
    /// portfolio of engines (PDR, BMC, PDKIND, TPA) running in parallel.
    /// AY is the sole CHC solver — no external subprocess needed.
    ///
    /// Part of #632.
    ///
    /// Returns a structured CHC solver result on success.
    pub(in crate::call_ay) fn try_ay_chc_solver(
        &self,
        smt_file: &Path,
        _harness: &HarnessMetadata,
        demoted_fallback_count: usize,
        deadline: crate::deadline::Deadline,
    ) -> anyhow::Result<ChcSolverResult> {
        if self.args.common_args.verbose {
            solver_stdout!("[AY-chc] Using native ay-chc portfolio solver");
        }

        // Pre-solve deadline enforcement (fail-closed): the harness budget may
        // already be spent by earlier attempts before any pre-solve work runs.
        bail_unknown_if_deadline_exhausted(deadline, "read_smt_file")?;

        let smt_content = std::fs::read_to_string(smt_file)
            .map_err(|e| anyhow::anyhow!("Failed to read SMT file: {e}"))?;

        // Part of #3258: Simplify `(bv2int #xNNNN)` to integer literals before
        // native parsing. The ay-chc parser does not support `bv2int` as a
        // function. These appear in int-lift mode when BV constants are wrapped.
        let smt_content = {
            static BV2INT_RE: OnceLock<Regex> = OnceLock::new();
            let re = BV2INT_RE
                .get_or_init(|| Regex::new(r"\(bv2int #x([0-9a-fA-F]+)\)").expect("valid regex"));
            let rewritten = re.replace_all(&smt_content, |caps: &regex::Captures<'_>| {
                let hex_str = &caps[1];
                u128::from_str_radix(hex_str, 16)
                    .map(|v| v.to_string())
                    .unwrap_or_else(|_| caps[0].to_string())
            });
            if self.args.common_args.verbose && rewritten != smt_content {
                solver_stdout!(
                    "[AY-chc] bv2int simplification: rewrote constant bv2int expressions"
                );
            }
            rewritten.into_owned()
        };
        let solver_smt_content = crate::smt_io::strip_cover_assertions_for_chc_solver(&smt_content);
        if self.args.common_args.verbose && solver_smt_content.len() != smt_content.len() {
            solver_stdout!("[AY-chc] stripped cover metadata from main CHC solver input");
        }
        // Opt-in exact export of the queries handed to AY (AY asks R20/R21/W5/W6;
        // `TRUST_MC_CHC_ROW_EXPORT_DIR`). `None` unless the knob is set.
        let row_export = RowExport::from_env(&_harness.pretty_name, smt_file, &solver_smt_content);

        // CRITICAL placement: this deadline bail must come BEFORE the
        // trivially-safe short-circuit PROOF paths below — an exhausted
        // budget must yield a bounded UNKNOWN, never fall into a success path.
        bail_unknown_if_deadline_exhausted(deadline, "trivial_safety_check")?;

        // No-derivation shortcut: the CHC system queries `error` and no
        // satisfiable rule derives it. A false-bodied `(rule (=> false error))`
        // is the compiler's certified discharge (straight-line proof, TIC) and
        // stays a proof. Without one, registered checks were LOST, not proved:
        // `interpret_chc_trivial_safe` reports INCONCLUSIVE with
        // `[AY:UNKNOWN_REASON:LostErrorRules]` unless nothing was registered.
        let has_error_query = solver_smt_content.contains("(query error)");
        let has_error_rule =
            has_error_query && !smt_error_query_is_trivially_safe(&solver_smt_content);
        if has_error_query && !has_error_rule {
            if smt_error_query_has_false_error_obligation(&solver_smt_content) {
                if self.args.common_args.verbose {
                    solver_stdout!(
                        "[AY-chc] False error obligation - trivially safe (short-circuit PROOF)"
                    );
                }
                return self.interpret_chc_false_error_safe(
                    smt_file,
                    &smt_content,
                    _harness,
                    deadline,
                );
            }
            if self.args.common_args.verbose {
                solver_stdout!(
                    "[AY-chc] No rule derives error — no solver runs (lost checks unless none registered)"
                );
            }
            return self.interpret_chc_trivial_safe(smt_file, &smt_content, _harness, deadline);
        }

        bail_unknown_if_deadline_exhausted(deadline, "chc_parse")?;
        let mut problem = ChcParser::parse(&solver_smt_content)
            .map_err(|e| anyhow::anyhow!("Failed to parse CHC problem: {e}"))?;
        if let Some(export) = &row_export {
            export.source_problem(&problem);
        }

        if self.args.common_args.verbose {
            solver_stdout!(
                "[AY-chc] Parsed problem: {} predicates, {} clauses",
                problem.predicates().len(),
                problem.clauses().len()
            );
        }

        // BSEM-18 per-property solving needs the problem in its AS-PARSED shape
        // — `error_pN => error`, `error => false` — because that is what AY's
        // `query_obligations()` slicer unfolds into exactly ONE obligation per
        // property, labelled with the `error_pN` relation the VC artifact
        // records. Once `expand_nullary_fail_queries` below has rewritten the
        // queries, the same slicer unfolds a level deeper and produces one
        // obligation per *definition* of each `error_pN`, which is both finer
        // than the report wants and no longer labelled by the relation name.
        // Snapshot before the rewrite; each slice then gets the same expansion
        // and transform passes applied to it individually.
        let pre_expansion_problem = problem.clone();

        // Expand nullary fail predicates (e.g., error()) into direct queries.
        // PDR does this internally, but other portfolio engines (TPA, BMC, etc.) do not.
        // Part of #3050.
        bail_unknown_if_deadline_exhausted(deadline, "expand_nullary_fail_queries")?;
        problem.expand_nullary_fail_queries(self.args.common_args.verbose);
        if let Some(derived_relations) =
            constraint_free_nullary_error_derivation_relations(&problem)
        {
            if self.args.common_args.verbose {
                solver_stdout!(
                    "[AY-chc] Propositional zero-arity derivation reaches error — \
                     short-circuiting CTREX (path relations: {derived_relations:?})"
                );
            }
            return self.interpret_chc_trivial_unsafe(
                &smt_content,
                smt_file,
                &problem,
                _harness,
                Some(&derived_relations),
            );
        }
        // The exact acyclic-witness search below is SMT-backed and can blow up
        // combinatorially on large problems (confirmed >330s pre-solve
        // wall-kills) — gate its entry AND bound the search itself by the
        // per-harness deadline (an aborted search returns `None`, which only
        // skips a CTREX shortcut; it never asserts safety).
        bail_unknown_if_deadline_exhausted(deadline, "acyclic_witness_search")?;
        // Bound the search to a SLICE of the remaining budget, not all of it.
        // This is a counterexample shortcut that "never asserts safety" (see
        // above), but it sits in front of the COMPLETE acyclic-BMC decision
        // lane. Given the whole deadline it can spend every second enumerating
        // up to 1024 fact combinations per clause across (preds+clauses)
        // rounds, and then the lane that could actually have decided the
        // harness never runs -- the row comes back PreSolveDeadline having
        // proved nothing. An optimisation must not be able to starve the
        // decision procedure behind it.
        //
        // Aborting early only forfeits a CTREX shortcut, so this cannot turn a
        // proof into a miss; the worst case is a counterexample found later by
        // the normal path.
        let witness_budget =
            std::cmp::min(deadline.remaining() / 5, std::time::Duration::from_secs(3));
        let witness_deadline = crate::deadline::Deadline::after(witness_budget);
        let witness_started = std::time::Instant::now();
        let witness = if acyclicity::is_acyclic_problem(&problem) {
            let witness = satisfiable_acyclic_error_derivation_witness_exported(
                &problem,
                witness_deadline,
                row_export.as_ref(),
            );
            crate::stage_timing::record(
                "acyclic-witness",
                witness_started,
                if witness.is_some() { "witness" } else { "none" },
            );
            if let Some(export) = &row_export {
                // A witness returns the harness before any row runs, so the
                // search's queries must reach manifest.json here.
                export.note(
                    "acyclic_witness_outcome",
                    serde_json::json!(if witness.is_some() {
                        "witness: the driver reports a counterexample from this search \
                         (interpret_chc_trivial_unsafe); no per-property row runs"
                    } else {
                        "none: the harness continues to the per-property rows"
                    }),
                );
            }
            witness
        } else {
            None
        };
        if let Some(witness) = witness {
            if self.args.common_args.verbose {
                solver_stdout!(
                    "[AY-chc] Exact acyclic derivation reaches error — short-circuiting CTREX \
                     (path relations: {:?}, model: {})",
                    witness.derived_relations,
                    witness.model_json
                );
            }
            return self.interpret_chc_trivial_unsafe(
                &smt_content,
                smt_file,
                &problem,
                _harness,
                Some(&witness.derived_relations),
            );
        }

        bail_unknown_if_deadline_exhausted(deadline, "chc_transforms")?;
        let transforms = &self.args.ay_chc_transforms;
        if self.args.ay_chc_transform {
            let verbose = self.args.common_args.verbose;
            let all = transforms.is_empty() || transforms.iter().any(|s| s.as_str() == "all");
            if all || transforms.iter().any(|s| s.as_str() == "scalarize") {
                let before_clauses = problem.clauses().len();
                problem.try_scalarize_const_array_selects();
                if verbose {
                    let after_clauses = problem.clauses().len();
                    solver_stdout!(
                        "[AY-chc] Scalarize: {before_clauses} → {after_clauses} clauses"
                    );
                }
            }
            if all || transforms.iter().any(|s| s.as_str() == "split-ite") {
                let before = problem.clauses().len();
                problem.try_split_ites_in_clauses(8, verbose);
                if verbose {
                    let after = problem.clauses().len();
                    solver_stdout!("[AY-chc] Split-ITE: {before} → {after} clauses");
                }
            }
            if all || transforms.iter().any(|s| s.as_str() == "split-or") {
                let before = problem.clauses().len();
                problem.try_split_ors_in_clauses(8, verbose);
                if verbose {
                    let after = problem.clauses().len();
                    solver_stdout!("[AY-chc] Split-OR: {before} → {after} clauses");
                }
            }
        }
        if let Some(export) = &row_export {
            export.aggregate_problem(
                &problem,
                serde_json::json!({
                    "enabled": self.args.ay_chc_transform,
                    "selected": self.args.ay_chc_transforms,
                }),
            );
        }

        // ── Acyclic BMC lane (Part of #4264) ────────────────────────────────
        // If the predicate dependency graph is acyclic, BMC at depth =
        // num_predicates is complete (every path is bounded). Try BMC first
        // and return early on Safe. Fall through to portfolio on Unknown or
        // Unsafe so CTREX results still cross the validated portfolio boundary.
        // Per-call solver budget, clamped to the per-harness deadline: the
        // acyclic-BMC lane, the portfolio budget, the guard timeout, and the
        // BMC cross-check budgets below all derive from this value, so a
        // harness that already burned wall clock gets a smaller solve budget
        // instead of restarting from a full one.
        bail_unknown_if_deadline_exhausted(deadline, "solve")?;
        let full_timeout =
            deadline.clamp(super::super::solver_timeout_duration(self.args.harness_timeout));
        let solve_mode =
            select_native_solve_mode(self.args.ay_chc_engine, self.args.ay_chc_no_retry);
        if self.args.common_args.verbose && solve_mode != NativeSolveMode::AdaptivePortfolio {
            if self.args.ay_chc_engine == AYChcEngine::Pdr {
                solver_stdout!(
                    "[AY-chc] Native solve mode forced to {} (PDR proof solver)",
                    solve_mode.label()
                );
            } else {
                solver_stdout!("[AY-chc] Native solve mode forced to {}", solve_mode.label());
            }
        }

        // One caller-owned memory envelope for every lane of this harness
        // (AY ask R2; see `resource_envelope`). Built once, before the first
        // lane, from the armed process cap less the driver's measured
        // footprint; `None` (no cap armed) leaves AY's defaults untouched.
        let memory_envelope = HarnessMemoryEnvelope::for_current_harness();
        if let Some(envelope) = &memory_envelope {
            solver_stdout!("{}", envelope.marker_line());
        }

        // The acyclic-BMC shortcut runs here only under
        // `TRUST_MC_CHC_ACYCLIC_BMC_ORDER=first`; by default it runs after an
        // undecided per-property batch (see `try_acyclic_bmc_shortcut`).
        let acyclic_bmc_order = acyclic_bmc_order_from_env();
        if solve_mode == NativeSolveMode::AdaptivePortfolio
            && acyclic_bmc_order == AcyclicBmcOrder::First
            && let Some(decided) = self.try_acyclic_bmc_shortcut(
                &problem,
                &smt_content,
                smt_file,
                _harness,
                demoted_fallback_count,
                full_timeout,
                deadline,
                memory_envelope,
                row_export.as_ref(),
            )
        {
            return decided;
        }

        // Part of #4207: Budget percentage for ay-chc portfolio solver.
        //
        // Configurable via TRUST_MC_NATIVE_CHC_BUDGET_PCT (default: 100, range: 10-100).
        // Raised from 50→100: the trivial-safe short-circuit (above) handles the
        // case that motivated the original 50% guard (portfolio wasting budget on
        // trivially safe problems). With that guard in place, 50% just starves the
        // portfolio of solve time — btreemap_struct, btreemap_dual_get, and NIA
        // harnesses flip UNKNOWN→PROOF when given the full budget.
        let budget_pct: u64 = std::env::var("TRUST_MC_NATIVE_CHC_BUDGET_PCT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(100)
            .clamp(10, 100);
        // Budget against what is LEFT of the per-harness deadline: the
        // acyclic-BMC lane above may have consumed real wall clock (up to its
        // guard timeout), and `full_timeout` was clamped BEFORE that lane
        // ran. Fail-closed: shrink-only, so the portfolio can never extend
        // past the deadline — and below the useful floor it is not started at
        // all, but reported as a budget-exhausted UNKNOWN. `nominal` is what
        // one call is entitled to; the grant records how much of it the
        // deadline actually allowed, so the UNKNOWN category can say
        // "starved" before it says anything structural.
        let nominal = super::super::solver_timeout_duration(self.args.harness_timeout)
            * budget_pct as u32
            / 100;
        // Snapshot per-predicate array-sort counts for UNKNOWN classification
        // BEFORE the problem is moved into AdaptivePortfolio — and before the
        // budget decision, whose UNKNOWN is classified from it. Part of #4304.
        let predicate_array_snapshot: Vec<(String, usize)> = problem
            .predicates()
            .iter()
            .map(|p| (p.name.clone(), count_array_sorts(&p.arg_sorts)))
            .collect();
        let Some(timeout) = deadline.stage_budget(nominal, MIN_USEFUL_STAGE_BUDGET) else {
            solver_stdout!(
                "[AY-chc] {:?} of the per-harness deadline left, {:?} needed — the {} solve \
                 is not started; returning UNKNOWN",
                deadline.remaining(),
                MIN_USEFUL_STAGE_BUDGET,
                solve_mode.label()
            );
            solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            let grant = SolveBudgetGrant { granted: Duration::ZERO, nominal };
            let category =
                classify_unknown(&predicate_array_snapshot, None, has_error_rule, Some(grant));
            solver_stdout!("{}", category.tag_line());
            anyhow::bail!(
                "ay-chc {BUDGET_EXHAUSTED_BEFORE_STAGE} '{}' ({:?} left, {:?} needed)",
                solve_mode.label(),
                deadline.remaining(),
                MIN_USEFUL_STAGE_BUDGET
            );
        };
        let grant = SolveBudgetGrant { granted: timeout, nominal };
        let mut adaptive_config =
            AdaptiveConfig::with_budget(timeout, self.args.common_args.verbose);
        // The forced-engine portfolio shares the harness envelope across its
        // live engines (AY divides `memory_budget` per concurrent worker).
        if let Some(envelope) = memory_envelope {
            adaptive_config = adaptive_config.with_memory_budget(envelope.allowance);
        }
        // ay#8585: validation is now always-on in ay-chc. Use strict_proofs
        // to reject trust-proof fallbacks — more conservative than the old
        // validate flag. Disabled when --ay-chc-skip-verify is passed.
        adaptive_config.strict_proofs = !self.args.ay_chc_skip_verify;
        if solve_mode == NativeSolveMode::PrimaryEngineOnly {
            adaptive_config = adaptive_config.with_max_engines(Some(1));
        }

        if self.args.common_args.verbose {
            let solver_kind = match solve_mode {
                NativeSolveMode::AdaptivePortfolio => "AdaptivePortfolio solver",
                NativeSolveMode::PrimaryEngineOnly => "Primary-engine-only solver",
                NativeSolveMode::BmcOnly => "BMC-only solver",
            };
            solver_stdout!(
                "[AY-chc] {} (budget: {:?}, full: {:?}, pct: {}%)",
                solver_kind,
                timeout,
                full_timeout,
                budget_pct
            );
        }

        // Part of #972/#2762/#2899/#2875: Merge all hint sources in priority order.
        // Merge order: (1) user artifact hints, (2) proof-core hints, (3) auto-invariant hints.
        // Single dedup + inject pass prevents set_pdr_user_hints overwrite bug.
        let vc_path = vc_artifact_path_for_smt(smt_file);
        let raw_hints = load_loop_hints(&vc_path);
        let verbose = self.args.common_args.verbose;
        let mut merged_hints = Vec::new();
        let mut applicable_loop_hints = 0usize;

        if !raw_hints.is_empty() {
            let converted =
                loop_hints::convert_loop_hints_to_lemma_hints(&problem, &raw_hints, verbose);
            applicable_loop_hints = converted.len();
            merged_hints.extend(converted);
        }

        let (pc_stats, pc_hints) =
            proof_core::run_proof_core_distillation(&problem, self.args.ay_chc_proof_core, verbose);
        let pc_injected = pc_hints.len();
        merged_hints.extend(pc_hints);

        let (auto_hints, auto_stats) = auto_invariants::generate_auto_invariant_hints(
            &problem,
            self.args.ay_chc_auto_invariants,
        );
        let auto_generated = auto_stats.generated;
        merged_hints.extend(auto_hints);

        if !merged_hints.is_empty() {
            let pre_dedup = merged_hints.len();
            let (deduped_hints, dedup_rejected) = dedup_lemma_hints(merged_hints);
            let injected = deduped_hints.len();

            if verbose {
                if !raw_hints.is_empty() {
                    solver_stdout!(
                        "[AY-chc] {}/{} loop hint(s) applicable",
                        applicable_loop_hints,
                        raw_hints.len()
                    );
                }
                solver_stdout!(
                    "[AY-chc] Auto-invariants mode: {:?} | recursive={} range_like={} generated={} widening={} budget_capped={}",
                    self.args.ay_chc_auto_invariants,
                    auto_stats.recursive_clauses,
                    auto_stats.range_like_clauses,
                    auto_generated,
                    auto_stats.widening_added,
                    auto_stats.budget_capped,
                );
                if pc_stats.obligations_total > 0 {
                    solver_stdout!(
                        "[AY-chc] Proof-core distillation: obligations={} unsat={} \
                         core_formulas={} rejected={} injected={}",
                        pc_stats.obligations_total,
                        pc_stats.unsat,
                        pc_stats.core_formulas,
                        pc_stats.rejected,
                        pc_stats.injected,
                    );
                }
                solver_stdout!(
                    "[AY-chc] Hint merge: user={} proof_core={} auto={} pre_dedup={} \
                     dedup_rejected={} injected={}",
                    applicable_loop_hints,
                    pc_injected,
                    auto_generated,
                    pre_dedup,
                    dedup_rejected,
                    injected,
                );
            }

            if !deduped_hints.is_empty() {
                adaptive_config.user_hints = deduped_hints;
            }
        } else if verbose {
            solver_stdout!(
                "[AY-chc] Auto-invariants mode: {:?} | no hints to inject",
                self.args.ay_chc_auto_invariants
            );
        }

        // Enable progress reporting for long solves.
        adaptive_config.progress_enabled = verbose;

        // ── Solve seam ───────────────────────────────────────────────────────
        //
        // DEFAULT (adaptive) MODE solves every BSEM-18 property obligation
        // INDEPENDENTLY through
        // `ay_encode::invoke::solve_with_proof_report_with_cancellation`. See
        // `per_property.rs` for the fail-closed reduction (any Unsafe row fails
        // the harness; PROOF only when every row is proved with acceptable
        // evidence; Unknown/error rows stay visible; `Ok([])` binds through the
        // vacuity accounting) and for why the invocation is joined rather than
        // detached.
        //
        // WHAT THAT RETIRED, and why the replacement is not a regression: this
        // used to be `AdaptivePortfolio::new` + `solve_proof_run()` on a
        // DETACHED thread, guarded by `recv_timeout`, with the guard-timeout
        // path cancelling the portfolio through `cancellation_handle()` and
        // then draining for at most GUARD_CANCEL_DRAIN_SECS before giving up
        // and orphaning the lane. That workaround existed because an orphaned
        // solve keeps burning CPU/memory while the driver moves on to the next
        // harness — under `--jobs N` the double-spend starves siblings, which
        // is how a SHORTER per-harness budget could cost more wall clock than a
        // longer one. Cancelling first made the overlap smaller; it did not
        // remove it, because a lane that did not wind down inside the drain was
        // still abandoned.
        //
        // The per-property seam removes the overlap outright: the parent token
        // and its clock are created BEFORE any portfolio is constructed (AY
        // links them ahead of constructor preprocessing), each row runs
        // synchronously on this thread, and the batch cannot advance — nor can
        // the driver reach the next harness — until the current invocation has
        // returned. Panic isolation moves from the thread boundary to a
        // `catch_unwind` around each row, so nothing is lost there.
        //
        // The liveness cost is deliberate and is exactly what AY's guidance
        // asks for: a synchronous isolation barrier may exceed the nominal
        // timeout, or block on a non-cooperative transform/engine, and a
        // consumer must not buy liveness back by detaching that work. The
        // backstop is unchanged and now the only one — `wall_clock_watchdog`,
        // armed from `main()` in its own thread, prints honest UNKNOWN markers
        // and hard-exits the process if a lane truly wedges.
        //
        // The two FORCED-ENGINE CLI modes keep their single-problem lanes and
        // the old thread guard below: they exist so `--ay-chc-engine=pdr|bmc`
        // drives one concrete engine, and decomposing them would change what
        // those switches mean.
        let external_validation_problem = problem.clone();
        let pdr_proof_problem = problem.clone();
        let mut pdr_proof_config = ay_chc::PdrConfig::production(self.args.common_args.verbose);
        pdr_proof_config.solve_timeout = Some(timeout);
        pdr_proof_config.user_hints = adaptive_config.user_hints.clone();
        let pdr_proof_obligation_id = _harness.pretty_name.clone();

        if solve_mode == NativeSolveMode::AdaptivePortfolio {
            let execution = execution_envelope_from_env(self.args.ay_chc_deterministic);
            if verbose {
                solver_stdout!(
                    "[AY-chc] Execution mode: {} (requested by {})",
                    execution.mode_label(),
                    execution.source.label(),
                );
            }
            let options = PerPropertySolveOptions {
                verbose,
                skip_verify: self.args.ay_chc_skip_verify,
                // The batch as a whole receives the budget the aggregate solve
                // used to get, so decomposition cannot inflate wall clock.
                batch_budget: timeout,
                per_row_cap: timeout,
                deadline,
                execution,
                lemma_hints: &adaptive_config.user_hints,
                transforms: ObligationTransforms::from_args(
                    self.args.ay_chc_transform,
                    &self.args.ay_chc_transforms,
                ),
                // Rows run one at a time, so each row's portfolio may use the
                // whole harness envelope; AY divides it across that
                // portfolio's live engines.
                memory_budget: memory_envelope.map(|envelope| envelope.allowance),
                row_export: row_export.as_ref(),
            };
            let (verdict, row_problem, report): (
                NativeSolveVerdict,
                Option<ay::chc::ChcProblem>,
                PerPropertyReport,
            ) = match {
                let batch_started = std::time::Instant::now();
                let batch = solve_chc_per_property(&pre_expansion_problem, &options);
                crate::stage_timing::record(
                    "per-property-batch",
                    batch_started,
                    match &batch {
                        Ok(PerPropertyOutcome::AllQueriesPruned) => "all-pruned",
                        Ok(PerPropertyOutcome::Proved { .. }) => "proved",
                        Ok(PerPropertyOutcome::Refuted { .. }) => "refuted",
                        Ok(PerPropertyOutcome::Undecided { .. }) => "undecided",
                        Err(_) => "error",
                    },
                );
                if acyclic_bmc_order == AcyclicBmcOrder::AfterUndecidedBatch
                    && matches!(batch, Ok(PerPropertyOutcome::Undecided { .. }) | Err(_))
                    && let Some(decided) = self.try_acyclic_bmc_shortcut(
                        &problem,
                        &smt_content,
                        smt_file,
                        _harness,
                        demoted_fallback_count,
                        full_timeout,
                        deadline,
                        memory_envelope,
                        row_export.as_ref(),
                    )
                {
                    return decided;
                }
                batch?
            } {
                PerPropertyOutcome::AllQueriesPruned => {
                    // No solver answered for any registered check, so the same
                    // fail-closed gate applies: registered obligations are
                    // reported INCONCLUSIVE (LostErrorRules), never SUCCESS.
                    // AY's documented all-queries-pruned case. No surviving
                    // property IDs, so this is bound through Trust-MC's own
                    // source-property/vacuity accounting — the artifact table
                    // supplies the report lines and the vacuous-checks marker
                    // still re-statuses them — rather than by manufacturing
                    // credited per-property solver rows.
                    return self.interpret_chc_trivial_safe(
                        smt_file,
                        &smt_content,
                        _harness,
                        deadline,
                    );
                }
                PerPropertyOutcome::Proved { invariant, problem, report } => {
                    (NativeSolveVerdict::Safe(invariant), Some(problem), report)
                }
                PerPropertyOutcome::Refuted { counterexample, problem, report } => {
                    (NativeSolveVerdict::Unsafe(counterexample), Some(problem), report)
                }
                PerPropertyOutcome::Undecided { summary, report } => {
                    (NativeSolveVerdict::Undecided { summary }, None, report)
                }
            };
            return self.finish_native_chc_solve(
                verdict,
                NativeSolveFinish {
                    smt_file,
                    smt_content: &smt_content,
                    solver_smt_content: &solver_smt_content,
                    harness: _harness,
                    demoted_fallback_count,
                    solve_mode,
                    timeout,
                    deadline,
                    grant,
                    verbose,
                    has_error_rule,
                    predicate_array_snapshot: &predicate_array_snapshot,
                    budget_summary: Some(report.budget_summary),
                    proof_transcript_metadata: report.proof_transcript_metadata,
                    native_full_verification_verdict: None,
                    // Each row's invariant was already re-validated against its
                    // OWN sliced problem inside the batch, so the whole-problem
                    // re-validation would be checking a model that does not
                    // describe this problem.
                    revalidate_invariant_against: None,
                    per_row_validated: true,
                    counterexample_problem: row_problem
                        .as_ref()
                        .unwrap_or(&external_validation_problem),
                    correlated_failing_relations: &report.correlated_relations,
                    memory_envelope,
                },
            );
        }

        let solver = AdaptivePortfolio::new(problem, adaptive_config);
        // Forced-engine lanes keep the cooperative cancellation and the
        // bounded drain: they are single-problem one-shots with no obligation
        // loop to serialize against, so the guard remains the only way to stop
        // paying for a solve whose answer has already been discarded.
        //
        // The engines run through AY's free functions (`solve_pdr_proof`,
        // `solve_bmc_proof_with_checked_replay`), which never see the
        // portfolio's token — so cancelling `portfolio_cancel` alone did not
        // stop them. `lane_cancel` is handed to both engine configs, and the
        // guard cancels both tokens.
        let portfolio_cancel = solver.cancellation_handle();
        let lane_cancel = CancellationToken::new();
        let pdr_proof_config = pdr_proof_config.with_cancellation_token(Some(lane_cancel.clone()));
        let guard_timeout = guard_timeout_within_deadline(timeout, &deadline);
        let bmc_verbose = self.args.common_args.verbose;
        let lane_deadline = Deadline::after(full_timeout);
        let retry_cancel = lane_cancel.clone();
        let lane = OwnedLane::spawn(
            solve_mode.label(),
            move || {
                portfolio_cancel.cancel();
                lane_cancel.cancel();
            },
            move || {
                let solve_result = ay::catch_ay_panics(
                    std::panic::AssertUnwindSafe(|| {
                        let (verified, report, bound_run, retry_note) = match solve_mode {
                            NativeSolveMode::AdaptivePortfolio => {
                                // Unreachable by construction: the adaptive mode
                                // returns above through the per-property seam. The
                                // old `solver.solve_proof_run()` call lived here;
                                // it is gone deliberately and must not come back —
                                // the authoritative solve is now
                                // `solve_proof_run_with_budget_report()` (reached
                                // through `ay_encode::invoke`), which carries the
                                // stop reason and adaptive trace of the SAME
                                // invocation that produced the verdict. Restoring a
                                // second, reporting-only solve here would break that
                                // binding.
                                return Err(
                                    "internal: adaptive portfolio must use the per-property seam"
                                        .to_string(),
                                );
                            }
                            NativeSolveMode::PrimaryEngineOnly => {
                                let run = match ay_chc::engines::solve_pdr_proof(
                                    pdr_proof_problem.clone(),
                                    pdr_proof_config,
                                ) {
                                    Ok(run) => run,
                                    Err(err) => {
                                        return Err(format!("ay-chc PDR proof run failed: {err}"));
                                    }
                                };
                                let native_full_verification_verdict = pdr_proof_run_verdict(
                                    &run,
                                    &pdr_proof_problem,
                                    &pdr_proof_obligation_id,
                                );
                                let proof_transcript_metadata =
                                    Some(run.metadata().to_json_value());
                                return Ok((
                                    run.result().clone(),
                                    None,
                                    proof_transcript_metadata,
                                    Some(native_full_verification_verdict),
                                    None,
                                ));
                            }
                            NativeSolveMode::BmcOnly => {
                                let bmc_config = bmc_with_envelope(
                                    bounded_native_bmc_config(
                                        BmcConfig::default(),
                                        full_timeout,
                                        bmc_verbose,
                                    )
                                    .with_cancellation(retry_cancel.clone()),
                                    memory_envelope,
                                );
                                match ay_chc::engines::solve_bmc_proof_with_checked_replay(
                                    solver.problem().clone(),
                                    bmc_config.clone(),
                                    checked_replay_budget(timeout),
                                ) {
                                    Ok(run) => (
                                        run.result().clone(),
                                        None::<ay_chc::BudgetReport>,
                                        Some(run),
                                        None,
                                    ),
                                    // Panic-caught internally. The verdict-only
                                    // retry (no evidence published, as before)
                                    // runs only while the attempt is open, on
                                    // what is LEFT of the lane (AY ask R1).
                                    Err(err) => match bmc_retry_budget(
                                        retry_cancel.is_cancelled(),
                                        lane_deadline.remaining(),
                                        deadline.remaining(),
                                        MIN_USEFUL_STAGE_BUDGET,
                                    ) {
                                        None => {
                                            return Err(format!(
                                                "ay-chc BMC evidence run failed internally \
                                                 ({err}); the verdict-only retry was not \
                                                 started: the attempt was cancelled or its \
                                                 deadline had closed"
                                            ));
                                        }
                                        Some(remaining) => (
                                            solver.solve_bmc_only(
                                                bmc_config
                                                    .with_time_budget(remaining)
                                                    .with_per_depth_timeout(
                                                        native_bmc_per_depth_timeout(remaining),
                                                    ),
                                            ),
                                            None,
                                            None,
                                            Some(format!(
                                                "the BMC evidence run failed internally ({err}); \
                                                 verdict-only retry on the remaining \
                                                 {remaining:?} of the lane"
                                            )),
                                        ),
                                    },
                                }
                            }
                        };
                        // Item-7 (portfolio path): the CHECKED replay pass now runs
                        // inside the bound solve, so the metadata read here is
                        // already the upgraded one, and is metadata-only whenever
                        // the replay fell short — the same fail-closed outcome the
                        // one-shot call used to produce.
                        let proof_transcript_metadata = match (&verified, &bound_run) {
                            (
                                ay::chc::VerifiedChcResult::Safe(_)
                                | ay::chc::VerifiedChcResult::Unsafe(_),
                                Some(run),
                            ) => Some(run.metadata().to_json_value()),
                            _ => None,
                        };
                        Ok((verified, report, proof_transcript_metadata, None, retry_note))
                    }),
                    |reason| Err(reason),
                );
                let stats: ChcStatistics = solver.statistics();
                (solve_result, stats)
            },
        );
        let lane = match lane {
            // The wait for the lane's exit is bounded by the harness deadline
            // (`owned_lane`'s quarantine).
            Ok(lane) => lane.abandon_at(deadline.instant()),
            Err(err) => {
                anyhow::bail!("ay-chc {} lane could not be spawned: {err}", solve_mode.label());
            }
        };
        let (outcome, join) = lane.finish(guard_timeout);
        report_lane_join(&join);
        // The rule both guards apply, on every arm (`lane_disposition`): a
        // lane abandoned at the harness deadline ends the harness, even one
        // that delivered its value before lingering in cleanup. Before review
        // round 2 this path checked only the timeout arm and took such a value
        // on into `finish_native_chc_solve`.
        let outcome = match settle_lane(outcome, &join) {
            SettledLane::Joined(outcome) => outcome,
            SettledLane::Abandoned(outcome) => {
                if matches!(outcome, LaneOutcome::TimedOut { .. }) {
                    solver_stdout!(
                        "[AY-chc] {} exceeded guard timeout ({:?}) — cancelled ({}), returning \
                         UNKNOWN",
                        solve_mode.label(),
                        guard_timeout,
                        lane_wind_down(&join)
                    );
                }
                return Err(lane_abandoned_error(&join));
            }
        };
        let (
            result,
            budget_report,
            forced_proof_transcript_metadata,
            forced_native_full_verification_verdict,
            chc_stats,
        ) = match outcome {
            LaneOutcome::Completed((solve_result, stats)) => match solve_result {
                Ok((verified, report, proof_transcript_metadata, native_verdict, retry_note)) => {
                    if let Some(note) = retry_note {
                        solver_stdout!("[AY-chc] {}: {note}", solve_mode.label());
                    }
                    (verified, report, proof_transcript_metadata, native_verdict, Some(stats))
                }
                Err(reason) => {
                    anyhow::bail!("ay-chc panic during {}: {reason}", solve_mode.label());
                }
            },
            LaneOutcome::Panicked(message) => {
                anyhow::bail!("ay-chc solver thread panicked: {message}");
            }
            LaneOutcome::Disconnected => {
                anyhow::bail!("ay-chc solver thread exited without producing a result");
            }
            LaneOutcome::TimedOut { .. } => {
                // The lane was cancelled and joined inside `finish` (an
                // abandoned one ended the harness above); the drained result,
                // if any, is deliberately unused.
                solver_stdout!(
                    "[AY-chc] {} exceeded guard timeout ({:?}) — \
                     cancelled ({}), returning UNKNOWN",
                    solve_mode.label(),
                    guard_timeout,
                    lane_wind_down(&join)
                );
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
                // No budget_report available on guard-timeout; still emit
                // Array-param / NoErrorRule classification from the snapshot.
                // Part of #4304.
                let category =
                    classify_unknown(&predicate_array_snapshot, None, has_error_rule, Some(grant));
                solver_stdout!("{}", category.tag_line());
                return Err(forced_lane_timeout_error(solve_mode.label(), guard_timeout));
            }
        };

        // Build a BudgetSummary for classification before reporting.
        // Part of #4304.
        let budget_summary: Option<BudgetSummary> = budget_report.as_ref().map(|report| {
            let completed = report.completed_count();
            let timed_out = report.timeout_count();
            // First non-completed entry: check `{:?}` format against "Completed".
            // We cannot name EngineStopReason (not re-exported via ay::chc), so
            // compare via Debug formatting, which maps Completed → "Completed".
            let first_non_completed = report.entries.iter().find_map(|e| {
                let sr = format!("{:?}", e.stop_reason);
                if sr == "Completed" { None } else { Some((e.engine.name().to_string(), sr)) }
            });
            BudgetSummary {
                completed,
                timed_out,
                total_elapsed_ms: report.total_elapsed.as_millis(),
                first_non_completed,
            }
        });

        if let Some(ref report) = budget_report {
            if verbose {
                solver_stdout!(
                    "[AY-chc] Budget report: {} engines ran, {} completed, {} timed out",
                    report.entries.len(),
                    report.completed_count(),
                    report.timeout_count(),
                );
                for entry in &report.entries {
                    solver_stdout!(
                        "[AY-chc]   {} — {:.1}s / {:.1}s ({:?})",
                        entry.engine.name(),
                        entry.elapsed.as_secs_f64(),
                        entry.budget_allocated.as_secs_f64(),
                        entry.stop_reason,
                    );
                }
            }
        }

        if let Some(ref stats) = chc_stats {
            if verbose {
                solver_stdout!(
                    "[AY-chc] ChcStatistics: iterations={} lemmas={} max_frame={} restarts={} \
                     smt_unknowns={} cache_hits={} cache_model_rej={} cache_solver_calls={} \
                     trust_proof_fallbacks={}",
                    stats.iterations,
                    stats.lemmas_learned,
                    stats.max_frame,
                    stats.restarts,
                    stats.smt_unknowns,
                    stats.cache_hits,
                    stats.cache_model_rejections,
                    stats.cache_solver_calls,
                    stats.trust_proof_fallbacks,
                );
            }
        }

        let verdict = match result {
            ay::chc::VerifiedChcResult::Safe(verified_inv) => {
                NativeSolveVerdict::Safe(verified_inv)
            }
            ay::chc::VerifiedChcResult::Unsafe(verified_cex) => {
                NativeSolveVerdict::Unsafe(verified_cex)
            }
            _ => NativeSolveVerdict::Undecided {
                summary: "the solver did not decide the aggregate query".to_string(),
            },
        };
        let no_correlated_relations = HashSet::new();
        self.finish_native_chc_solve(
            verdict,
            NativeSolveFinish {
                smt_file,
                smt_content: &smt_content,
                solver_smt_content: &solver_smt_content,
                harness: _harness,
                demoted_fallback_count,
                solve_mode,
                timeout,
                deadline,
                grant,
                verbose,
                has_error_rule,
                predicate_array_snapshot: &predicate_array_snapshot,
                budget_summary,
                proof_transcript_metadata: forced_proof_transcript_metadata,
                native_full_verification_verdict: forced_native_full_verification_verdict,
                // Forced-engine lanes solve the WHOLE problem, so the whole
                // problem is what their invariant model must be re-validated
                // against — unchanged from before the per-property split.
                revalidate_invariant_against: Some(&external_validation_problem),
                // One-shot engines carry only the portfolio's own validation:
                // the cross-check stays on for them.
                per_row_validated: false,
                counterexample_problem: &external_validation_problem,
                correlated_failing_relations: &no_correlated_relations,
                memory_envelope,
            },
        )
    }

    /// The acyclic-BMC shortcut: on an acyclic problem, BMC at depth =
    /// predicates is complete, so a Safe with replayable proof evidence (or a
    /// trusted scalar result) decides the harness without the portfolio.
    /// Returns `Some` only when it DECIDED; `None` forfeits the shortcut and
    /// the caller's verdict (or error) stands. Budgeted against what is left
    /// of the per-harness deadline, skipped with the typed
    /// `[AY:STAGE_SKIPPED:acyclic-bmc:…]` marker below the useful floor.
    ///
    /// Where it runs is [`AcyclicBmcOrder`]: by default AFTER a per-property
    /// batch that did not decide the harness, so a batch that proves or
    /// refutes in well under a second no longer waits behind a shortcut that
    /// can spend its full budget plus guard (measured on
    /// `kani/ArithOperators/unchecked.rs`: 19.4s inconclusive BMC in front of
    /// a 0.9s twelve-row proof).
    #[allow(clippy::too_many_arguments)]
    fn try_acyclic_bmc_shortcut(
        &self,
        problem: &ay::chc::ChcProblem,
        smt_content: &str,
        smt_file: &Path,
        _harness: &HarnessMetadata,
        demoted_fallback_count: usize,
        full_timeout: Duration,
        deadline: Deadline,
        memory_envelope: Option<HarnessMemoryEnvelope>,
        row_export: Option<&RowExport>,
    ) -> Option<anyhow::Result<ChcSolverResult>> {
        if !acyclicity::is_acyclic_problem(problem) {
            return None;
        }
        let Some(bmc_budget) = deadline.stage_budget(full_timeout, MIN_USEFUL_STAGE_BUDGET) else {
            solver_stdout!(
                "{} — the acyclic BMC shortcut is skipped; the portfolio decides",
                deadline.stage_skipped_marker("acyclic-bmc", MIN_USEFUL_STAGE_BUDGET)
            );
            return None;
        };
        let num_preds = problem.predicates().len();
        let depth = num_preds.max(1);
        if self.args.common_args.verbose {
            solver_stdout!(
                "[AY-chc] Acyclic problem detected ({} predicates, depth={}), \
                 trying BMC with acyclic_safe",
                num_preds,
                depth
            );
        }

        // Cancellable so the guard below can stop this lane, and the lane is
        // OWNED: it is joined before anything else runs (AY ask R1).
        let bmc_cancel = CancellationToken::new();
        let bmc_config = bmc_with_envelope(
            BmcConfig::default()
                .with_max_depth(depth)
                .with_acyclic_safe(true)
                .with_time_budget(bmc_budget)
                .with_per_depth_timeout(native_bmc_per_depth_timeout(bmc_budget))
                .with_cancellation(bmc_cancel.clone())
                .with_verbose(self.args.common_args.verbose),
            memory_envelope,
        );

        // Clone the problem so we can fall through to portfolio when BMC
        // cannot provide a trusted proof shortcut.
        // Wrap in catch_unwind: ay's BMC engine can panic on certain
        // predicate arity conditions (ay bug — argument index exceeds
        // declared arity after internal transformations). On panic, fall
        // through to the portfolio solver instead of crashing the driver.
        // Part of #4184.
        //
        // Run on an owned thread under a guard timeout. The guard is belt
        // and braces: the original reason was an ay bug where the BMC
        // engine ignored its time budget during exact/polynomial DAG
        // encoding construction (confirmed unbounded >150s hang on
        // coroutine-shaped acyclic problems, e.g. Coroutines
        // iterator-count). That bug is FIXED upstream — the inference
        // fixpoints and per-clause compile loops now poll the lane deadline
        // and bail (`ay-chc bmc/mod.rs`, `solve_acyclic_polynomial_dag_once`
        // and the `budget_exhausted` returns). We keep the guard because it
        // also covers panics and any future budget escape, not because the
        // lane is known to run away.
        //
        // On guard timeout the lane is cancelled and JOINED
        // (`OwnedLane::finish`): the thread is gone before the batch, the
        // external fallback or the next harness can start. A lane that
        // outlives the three-second drain is a failed drain: reported, and
        // once joined the harness falls through as after any guard timeout.
        // Only a lane still alive at the harness deadline is abandoned
        // (quarantined), and that ends the harness. Falling through is still
        // fail-closed: abandoning BMC only skips a shortcut and never asserts
        // a verdict.
        let replay_budget = checked_replay_budget(bmc_budget);
        if let Some(export) = row_export {
            export.acyclic_bmc_lane_begin(serde_json::json!({
                "entrypoint": "ay_chc::engines::solve_bmc_proof_with_checked_replay(problem, \
                               bmc_config, checked_replay_budget)",
                "problem": "the aggregate problem (aggregate.normalized)",
                "problem_normalized_sha256": problem.normalized_input_sha256(),
                "bmc_config": format!("{bmc_config:?}"),
                "max_depth": depth,
                "acyclic_safe": true,
                "time_budget_ms": bmc_budget.as_millis(),
                "per_depth_timeout_ms": native_bmc_per_depth_timeout(bmc_budget).as_millis(),
                "checked_replay_budget_ms": replay_budget.as_millis(),
                "memory_budget_bytes": memory_envelope.map(|e| e.allowance),
                "cancellation": acyclic_lane_cancellation_contract(),
                "harness_deadline_remaining_ms": deadline.remaining().as_millis(),
            }));
        }
        let problem_for_bmc = problem.clone();
        let lane_deadline = Deadline::after(bmc_budget);
        let retry_cancel = bmc_cancel.clone();
        let lane = OwnedLane::spawn(
            "acyclic-bmc",
            move || bmc_cancel.cancel(),
            move || {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                    // AY now binds a proof run to the problem it solved
                    // (`ChcPdrProofRun`), and its constructor is crate-private,
                    // so evidence can no longer be minted from a free-floating
                    // `VerifiedChcResult` — which is the point of the change: a
                    // certificate cannot describe a problem other than the one
                    // solved.
                    //
                    // `solve_bmc_proof_with_checked_replay` is AY's own
                    // replacement for the old
                    // `checked_proof_transcript_metadata(problem, "bmc-acyclic",
                    // budget)` one-shot: it runs BMC-only evidence mode and then
                    // the budget-capped CHECKED replay pass, failing closed to
                    // metadata-only exactly as before.
                    let bound = engines::solve_bmc_proof_with_checked_replay(
                        problem_for_bmc.clone(),
                        bmc_config.clone(),
                        replay_budget,
                    );
                    match bound {
                        Ok(run) => {
                            let metadata = match run.result() {
                                ay::chc::VerifiedChcResult::Safe(_)
                                | ay::chc::VerifiedChcResult::Unsafe(_) => {
                                    Some(run.metadata().to_json_value())
                                }
                                _ => None,
                            };
                            AcyclicLaneResult::Solved {
                                result: run.result().clone(),
                                proof_transcript_metadata: metadata,
                                retry: None,
                            }
                        }
                        // Only an internal panic reaches here (the call is
                        // panic-caught). The verdict-only retry (no evidence
                        // published, as before) runs ONLY while the attempt's
                        // authority is open, and only on what is LEFT of the
                        // lane's budget (AY ask R1): a failure never restarts
                        // full work after cancellation or the deadline.
                        Err(err) => match bmc_retry_budget(
                            retry_cancel.is_cancelled(),
                            lane_deadline.remaining(),
                            deadline.remaining(),
                            MIN_USEFUL_STAGE_BUDGET,
                        ) {
                            None => AcyclicLaneResult::Refused(format!(
                                "the evidence run failed internally ({err}); the verdict-only \
                                 retry was not started: the attempt was cancelled or its \
                                 deadline had closed"
                            )),
                            Some(remaining) => AcyclicLaneResult::Solved {
                                result: engines::solve_bmc_only(
                                    problem_for_bmc,
                                    bmc_config.with_time_budget(remaining).with_per_depth_timeout(
                                        native_bmc_per_depth_timeout(remaining),
                                    ),
                                ),
                                proof_transcript_metadata: None,
                                retry: Some(format!(
                                    "the evidence run failed internally ({err}); verdict-only \
                                     retry on the remaining {remaining:?} of the lane"
                                )),
                            },
                        },
                    }
                }))
            },
        );
        let lane = match lane {
            // The wait for the lane's exit is bounded by the harness deadline
            // (`owned_lane`'s quarantine).
            Ok(lane) => lane.abandon_at(deadline.instant()),
            Err(err) => {
                // Nothing started, so nothing can overlap: skip the shortcut.
                solver_stdout!(
                    "[AY-chc] Acyclic BMC lane could not be spawned ({err}) — shortcut skipped"
                );
                return None;
            }
        };
        // The guard's grace must not carry the lane past the deadline: the
        // portfolio behind it budgets against what is left.
        let bmc_guard_timeout = guard_timeout_within_deadline(bmc_budget, &deadline);
        let acyclic_started = std::time::Instant::now();
        let (outcome, join) = lane.finish(bmc_guard_timeout);
        report_lane_join(&join);
        // The rule both guards apply, on every arm (`lane_disposition`): an
        // abandoned lane ends the harness below, whatever it delivered.
        let (outcome, abandoned) = match settle_lane(outcome, &join) {
            SettledLane::Joined(outcome) => (outcome, false),
            SettledLane::Abandoned(outcome) => (outcome, true),
        };
        // What a cancelled lane delivered while winding down, if anything. It
        // is discarded (the guard has fired), but AY asked what the lane was
        // doing after its cancellation, so it is named in the run log.
        let mut drained_label = None;
        let bmc_result = match outcome {
            LaneOutcome::Completed(outcome) if abandoned => {
                // Delivered, then still alive at the harness deadline: named,
                // never used (see `lane_disposition`).
                let label = acyclic_lane_value_label(&outcome, true);
                drained_label = Some(label);
                solver_stdout!(
                    "[AY-chc] Acyclic BMC lane delivered {label}, then its thread was still \
                     running at the harness deadline — quarantined; the delivered result is not \
                     used, ending the harness"
                );
                None
            }
            LaneOutcome::Completed(outcome) => Some(outcome),
            LaneOutcome::TimedOut { drained } => {
                drained_label = drained.as_ref().map(|value| acyclic_lane_value_label(value, true));
                solver_stdout!(
                    "[AY-chc] Acyclic BMC lane exceeded guard timeout ({:?}) — \
                     cancelled ({}), abandoning BMC shortcut, {}; delivered while winding \
                     down: {} (discarded)",
                    bmc_guard_timeout,
                    lane_wind_down(&join),
                    if abandoned { "ending the harness" } else { "falling through to portfolio" },
                    drained_label.unwrap_or("nothing"),
                );
                None
            }
            LaneOutcome::Panicked(message) => {
                solver_stdout!(
                    "[AY-chc] Acyclic BMC thread panicked outside its catch ({message}) — \
                     falling through to portfolio"
                );
                None
            }
            LaneOutcome::Disconnected => {
                solver_stdout!(
                    "[AY-chc] Acyclic BMC thread exited without a result — \
                     falling through to portfolio"
                );
                None
            }
        };

        let lane_outcome_label = match &bmc_result {
            _ if abandoned => "abandoned",
            Some(value) => acyclic_lane_value_label(value, false),
            None => "guard-timeout",
        };
        if let Some(export) = row_export {
            export.acyclic_bmc_lane_end(
                lane_outcome_label,
                serde_json::json!({
                    "marker": join.marker_line(),
                    "guard_timeout_ms": bmc_guard_timeout.as_millis(),
                    "exit": join.exit.label(),
                    "cancel_requested": join.cancel_requested,
                    "waited_ms": join.waited.as_millis(),
                    "drain_ms": join.drain.as_millis(),
                    "drain_limit_ms": join.drain_limit.as_millis(),
                    "drain_failed": join.drain_failed(),
                    "abandoned": join.abandoned(),
                    // For a timed-out lane: what it delivered while winding
                    // down. For an abandoned lane that completed: what it
                    // delivered before lingering. Named, never used.
                    "delivered_while_winding_down": drained_label,
                }),
            );
        }
        crate::stage_timing::record("acyclic-bmc", acyclic_started, lane_outcome_label);
        // A failed drain was reported above and the lane has been joined, so
        // the harness goes on. Only a lane abandoned at the harness deadline
        // (quarantined, still alive) ends it, on any arm: nothing may start
        // beside it, and the error wording, `LANE_ABANDONED_PHRASE`, does not
        // open the external `ay` fallback.
        if abandoned {
            return Some(Err(lane_abandoned_error(&join)));
        }
        let bmc_result = match bmc_result {
            Some(Ok(AcyclicLaneResult::Solved { result, proof_transcript_metadata, retry })) => {
                if let Some(retry) = retry {
                    solver_stdout!("[AY-chc] Acyclic BMC: {retry}");
                }
                Some(Ok((result, proof_transcript_metadata)))
            }
            Some(Ok(AcyclicLaneResult::Refused(reason))) => {
                solver_stdout!("[AY-chc] Acyclic BMC: {reason} — falling through to portfolio");
                None
            }
            Some(Err(panic_payload)) => Some(Err(panic_payload)),
            None => None,
        };

        match bmc_result {
            Some(Ok((
                ay::chc::VerifiedChcResult::Safe(verified_inv),
                proof_transcript_metadata,
            ))) => {
                if acyclic_bmc_safe_metadata_is_proof_grade(proof_transcript_metadata.as_ref())
                    || scalar_acyclic_bmc_safe_is_trusted(&problem, demoted_fallback_count)
                {
                    if self.args.common_args.verbose {
                        solver_stdout!(
                            "[AY-chc] Acyclic BMC proved SAFE with complete-exhaustion proof evidence — skipping portfolio"
                        );
                    }
                    // BMC cross-checking a BMC result is tautological — skip it.
                    // PDR model re-verification is also skipped for proof-grade
                    // acyclic BMC evidence.
                    return Some(self.interpret_chc_safe(
                        verified_inv,
                        &smt_content,
                        smt_file,
                        _harness,
                        demoted_fallback_count,
                        proof_transcript_metadata,
                        None,
                        deadline,
                    ));
                }
                if self.args.common_args.verbose {
                    solver_stdout!(
                        "[AY-chc] Acyclic BMC SAFE lacks replayable proof evidence — falling through to validated portfolio"
                    );
                }
            }
            Some(Ok((
                ay::chc::VerifiedChcResult::Unsafe(verified_cex),
                proof_transcript_metadata,
            ))) => {
                if self.args.common_args.verbose {
                    solver_stdout!(
                        "[AY-chc] Acyclic BMC found counterexample ({} steps) — \
                         checking whether acyclic scalar result is complete",
                        verified_cex.counterexample().steps.len()
                    );
                }
                if scalar_acyclic_bmc_counterexample_is_trusted(&problem, demoted_fallback_count) {
                    if self.args.common_args.verbose {
                        solver_stdout!(
                            "[AY-chc] Acyclic scalar BMC counterexample accepted as complete"
                        );
                    }
                    return Some(self.interpret_chc_unsafe(
                        verified_cex,
                        &problem,
                        smt_file,
                        &smt_content,
                        _harness,
                        proof_transcript_metadata,
                        None,
                        // The acyclic-BMC lane solves the WHOLE problem, so
                        // its trace still walks through `error_p{id}`; it
                        // needs no seam-side correlation.
                        &HashSet::new(),
                    ));
                }
                // Acyclic BMC is used here as a fast proof shortcut, but it is
                // not a sufficient final CTREX authority. ay-chc can produce
                // spurious BMC counterexamples on otherwise UNSAT acyclic CHCs;
                // the validated portfolio path below is the trust boundary for
                // Unsafe results.
            }
            Some(Err(panic_payload)) => {
                let panic_msg = panic_payload_message(panic_payload.as_ref());
                solver_stdout!(
                    "[AY-chc] Acyclic BMC panicked (ay bug, falling through to portfolio): {}",
                    panic_msg
                );
                // Fall through to adaptive portfolio.
            }
            Some(Ok(_)) => {
                if self.args.common_args.verbose {
                    solver_stdout!(
                        "[AY-chc] Acyclic BMC inconclusive, falling through to portfolio"
                    );
                }
                // Fall through to adaptive portfolio.
            }
            // Guard timeout / thread loss — already reported above.
            None => {}
        }
        None
    }

    /// Budget for the BMC cross-check of a claimed PROOF or CTREX:
    /// `min(solve timeout, 30s)` as before, now clamped to what is left of
    /// the per-harness deadline, or `None` — with a typed marker — when
    /// less than the useful floor is left. The cross-check is defense in
    /// depth over an already-validated verdict, so skipping it keeps the
    /// verdict; before this clamp it always took its full budget after the
    /// deadline and pushed later harnesses into the watchdog.
    fn cross_check_budget(&self, ctx: &NativeSolveFinish<'_>) -> Option<Duration> {
        let cap = native_bmc_cross_check_budget(ctx.timeout);
        let budget = ctx.deadline.stage_budget(cap, MIN_USEFUL_STAGE_BUDGET);
        if budget.is_none() {
            solver_stdout!(
                "{} — the BMC cross-check of the {} verdict is skipped; the verdict stands on \
                 the solve's own validation",
                ctx.deadline.stage_skipped_marker("bmc-crosscheck", MIN_USEFUL_STAGE_BUDGET),
                ctx.solve_mode.label()
            );
        }
        budget
    }

    /// Shared post-solve interpretation for every native CHC lane.
    ///
    /// Both the per-property batch and the forced-engine one-shots land here, so
    /// the fail-closed defences (BMC cross-check on a claimed PROOF, spurious-
    /// CTREX cross-check on a counterexample, external invariant re-validation,
    /// UNKNOWN categorisation) are written once and cannot drift apart.
    fn finish_native_chc_solve(
        &self,
        verdict: NativeSolveVerdict,
        ctx: NativeSolveFinish<'_>,
    ) -> anyhow::Result<ChcSolverResult> {
        match verdict {
            NativeSolveVerdict::Safe(verified_inv) => {
                // Defense-in-depth: BMC cross-check replaces manual model re-verification.
                // Uses ay's purpose-built BmcConfig::cross_check() preset (ay#8412) —
                // runs BMC independently to search for counterexamples that would
                // contradict the claimed PROOF. If BMC finds Unsafe, the proof is false.
                // Budgeted against what is left of the per-harness deadline
                // (`cross_check_budget`); skipped, typed, below the floor. The
                // proof itself was validated by the solve (strict proofs, per-row
                // re-validation), so a skipped cross-check keeps the verdict
                // exactly as a cross-check that found nothing would have.
                let crosscheck_runs = bmc_crosscheck_runs(
                    self.args.ay_chc_skip_verify,
                    ctx.per_row_validated,
                    bmc_crosscheck_forced_from_env(),
                );
                if !crosscheck_runs && !self.args.ay_chc_skip_verify {
                    crate::stage_timing::record_elapsed(
                        "bmc-crosscheck",
                        Duration::ZERO,
                        "skipped-per-row-validated",
                    );
                }
                if crosscheck_runs && let Some(budget) = self.cross_check_budget(&ctx) {
                    if let Ok(verify_problem) = ChcParser::parse(ctx.solver_smt_content) {
                        let crosscheck_started = std::time::Instant::now();
                        let bmc_result =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                engines::solve_bmc_only(
                                    verify_problem,
                                    bmc_with_envelope(
                                        native_bmc_cross_check_config(budget, ctx.verbose),
                                        ctx.memory_envelope,
                                    ),
                                )
                            }));
                        crate::stage_timing::record(
                            "bmc-crosscheck",
                            crosscheck_started,
                            match &bmc_result {
                                Ok(ay::chc::VerifiedChcResult::Safe(_)) => "safe",
                                Ok(ay::chc::VerifiedChcResult::Unsafe(_)) => "unsafe",
                                Ok(_) => "inconclusive",
                                Err(_) => "panic",
                            },
                        );
                        if let Ok(ay::chc::VerifiedChcResult::Unsafe(_)) = bmc_result {
                            solver_stdout!(
                                "[AY-chc] FALSE PROOF DETECTED: BMC cross-check found \
                                 counterexample contradicting PROOF (ay#8412). Demoting to UNKNOWN."
                            );
                            solver_stdout!(
                                "[AY:UNKNOWN] CHC verification: solver returned unknown"
                            );
                            anyhow::bail!(
                                "ay-chc false proof detected: BMC cross-check contradicts proof"
                            );
                        }
                    }
                }
                // Secondary defense: external model re-verification via fresh PDR solver
                // (ay#8578). The ay API disables verifier-side array scalarization so
                // backtranslated models are checked against the submitted CHC signature.
                //
                // `None` means the model was ALREADY re-validated against the
                // problem it actually interprets (the per-property batch does
                // this per row); it never means the gate was skipped. It is no
                // longer nested under the cross-check's budget: a proof is not
                // credited unless its model re-validated, and the budget comes
                // from the harness deadline (`revalidate_forced_lane_model`).
                if !self.args.ay_chc_skip_verify
                    && let Some(problem) = ctx.revalidate_invariant_against
                {
                    revalidate_forced_lane_model(
                        problem,
                        verified_inv.model(),
                        self.args.common_args.verbose,
                        ctx.solve_mode.label(),
                        super::per_property::row_validation_timeout(ctx.deadline.remaining()),
                    )?;
                }
                self.interpret_chc_safe(
                    verified_inv,
                    ctx.smt_content,
                    ctx.smt_file,
                    ctx.harness,
                    ctx.demoted_fallback_count,
                    ctx.proof_transcript_metadata,
                    ctx.native_full_verification_verdict,
                    ctx.deadline,
                )
            }
            NativeSolveVerdict::Unsafe(verified_cex) => {
                // Defense-in-depth for UNSAFE: BMC cross-check for spurious counterexamples.
                // If BMC proves SAFE on the same problem, the portfolio's CTREX is false.
                // Part of #4272. Same deadline discipline as the PROOF cross-check.
                let crosscheck_runs = bmc_crosscheck_runs(
                    self.args.ay_chc_skip_verify,
                    ctx.per_row_validated,
                    bmc_crosscheck_forced_from_env(),
                );
                if !crosscheck_runs && !self.args.ay_chc_skip_verify {
                    crate::stage_timing::record_elapsed(
                        "bmc-crosscheck",
                        Duration::ZERO,
                        "skipped-per-row-validated",
                    );
                }
                if crosscheck_runs && let Some(budget) = self.cross_check_budget(&ctx) {
                    if let Ok(verify_problem) = ChcParser::parse(ctx.solver_smt_content) {
                        let crosscheck_started = std::time::Instant::now();
                        let bmc_result =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                engines::solve_bmc_only(
                                    verify_problem,
                                    bmc_with_envelope(
                                        native_bmc_cross_check_config(budget, ctx.verbose),
                                        ctx.memory_envelope,
                                    ),
                                )
                            }));
                        crate::stage_timing::record(
                            "bmc-crosscheck",
                            crosscheck_started,
                            match &bmc_result {
                                Ok(ay::chc::VerifiedChcResult::Safe(_)) => "safe",
                                Ok(ay::chc::VerifiedChcResult::Unsafe(_)) => "unsafe",
                                Ok(_) => "inconclusive",
                                Err(_) => "panic",
                            },
                        );
                        if let Ok(ay::chc::VerifiedChcResult::Safe(_)) = bmc_result {
                            solver_stdout!(
                                "[AY-chc] SPURIOUS CTREX DETECTED: BMC cross-check proved SAFE, \
                                 contradicting portfolio CTREX (ay#8412). Demoting to UNKNOWN."
                            );
                            solver_stdout!(
                                "[AY:UNKNOWN] CHC verification: solver returned unknown"
                            );
                            anyhow::bail!(
                                "ay-chc spurious counterexample: BMC cross-check proves safe"
                            );
                        }
                    }
                }
                self.interpret_chc_unsafe(
                    verified_cex,
                    ctx.counterexample_problem,
                    ctx.smt_file,
                    ctx.smt_content,
                    ctx.harness,
                    ctx.proof_transcript_metadata,
                    ctx.native_full_verification_verdict,
                    ctx.correlated_failing_relations,
                )
            }
            NativeSolveVerdict::Undecided { summary } => {
                if self.args.common_args.verbose {
                    solver_stdout!("[AY-chc] {}: {summary}", ctx.solve_mode.label());
                }
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
                let category = classify_unknown(
                    ctx.predicate_array_snapshot,
                    ctx.budget_summary.as_ref(),
                    ctx.has_error_rule,
                    Some(ctx.grant),
                );
                solver_stdout!("{}", category.tag_line());
                // The "returned Unknown - verification inconclusive" wording is
                // load-bearing: `native_chc_error_allows_external_proof_fallback`
                // matches it to allow the external ay proof fallback, and
                // `SolverUnknownReason::from_chc_error` buckets it. The
                // per-property summary is appended, never substituted.
                anyhow::bail!(
                    "ay-chc {} returned Unknown - verification inconclusive ({summary})",
                    ctx.solve_mode.label()
                )
            }
        }
    }
}

#[cfg(test)]
mod lane_timeout_tests {
    use super::super::owned_lane::LaneExit;
    use super::*;

    fn timed_out(drain_ms: u64, abandoned: bool) -> LaneJoinReport {
        LaneJoinReport {
            lane: "acyclic-bmc",
            exit: LaneExit::TimedOut,
            waited: Duration::from_secs(35),
            cancel_requested: true,
            drain: Duration::from_millis(drain_ms),
            drain_limit: Duration::from_secs(GUARD_CANCEL_DRAIN_SECS),
            abandoned,
        }
    }

    /// The review of fix/ay-consumer-alignment: a failed drain ended the
    /// harness although the lane had already been joined. On
    /// `negative/ref_index_ops.rs::loop_index_store_safe` [chc] the acyclic
    /// lane exits 3.0–9.4 s after cancellation, so the harness's route (the
    /// external fallback after the batch, or under ORDER=first the batch
    /// itself) depended on which side of 3 s the exit fell. A joined lane now
    /// lets the harness go on either way; only an abandoned one ends it.
    #[test]
    fn a_joined_lane_whose_drain_failed_does_not_end_the_harness() {
        for drain_ms in [5, 2964, 3459, 4480, 9438] {
            let join = timed_out(drain_ms, false);
            assert_eq!(join.drain_failed(), drain_ms > 3000, "{join:?}");
            assert_eq!(lane_disposition(&join), LaneDisposition::Continue);
        }
        assert_eq!(lane_disposition(&timed_out(91_000, true)), LaneDisposition::EndHarness);
    }

    fn abandoned_after(exit: LaneExit, drain_ms: u64) -> LaneJoinReport {
        LaneJoinReport {
            lane: "bmc-only",
            exit,
            waited: Duration::from_secs(20),
            cancel_requested: exit == LaneExit::TimedOut,
            drain: Duration::from_millis(drain_ms),
            drain_limit: Duration::from_secs(GUARD_CANCEL_DRAIN_SECS),
            abandoned: true,
        }
    }

    /// Review round 2: a lane that DELIVERED its value and then lingered past
    /// the harness deadline was handled two ways. The acyclic shortcut ended
    /// the harness with a message claiming a cancellation that never
    /// happened; the forced-engine path matched `Completed` directly and took
    /// the value on into `finish_native_chc_solve` — post-solve work past the
    /// deadline beside a quarantined lane. Both guards now go through
    /// `settle_lane`, which never hands an abandoned lane's value back, on
    /// any arm, and the wording names what happened.
    #[test]
    fn an_abandoned_lane_ends_the_harness_on_every_arm_and_says_what_happened() {
        let completed = abandoned_after(LaneExit::Completed, 21_000);
        match settle_lane(LaneOutcome::Completed(7_u8), &completed) {
            SettledLane::Abandoned(LaneOutcome::Completed(7)) => {}
            other => panic!("a delivered value of an abandoned lane was handed back: {other:?}"),
        }
        let message = lane_abandoned_message(&completed);
        assert!(message.contains("delivered its result"), "{message}");
        assert!(message.contains("nothing was cancelled"), "{message}");
        assert!(!message.contains("after its cancellation"), "{message}");

        let timed = abandoned_after(LaneExit::TimedOut, 3_000);
        assert!(matches!(
            settle_lane(LaneOutcome::<u8>::TimedOut { drained: Some(1) }, &timed),
            SettledLane::Abandoned(LaneOutcome::TimedOut { .. })
        ));
        assert!(lane_abandoned_message(&timed).contains("3000 ms after its cancellation"));

        let lost = abandoned_after(LaneExit::Disconnected, 4_000);
        assert!(matches!(
            settle_lane(LaneOutcome::<u8>::Disconnected, &lost),
            SettledLane::Abandoned(LaneOutcome::Disconnected)
        ));
        assert!(lane_abandoned_message(&lost).contains("ended without a result"));

        for join in [&completed, &timed, &lost] {
            let error = anyhow::anyhow!("{}", lane_abandoned_message(join));
            assert!(error.to_string().contains(LANE_ABANDONED_PHRASE));
            assert!(error.to_string().contains("no further solve work starts"));
            assert!(!crate::call_ay::native_chc_error_allows_external_proof_fallback(&error));
            assert_eq!(
                crate::verification_provenance::SolverUnknownReason::from_chc_error(&error),
                crate::verification_provenance::SolverUnknownReason::Timeout
            );
        }

        // A joined lane's value is handed back unchanged, on every arm.
        let mut joined = completed.clone();
        joined.abandoned = false;
        assert!(matches!(
            settle_lane(LaneOutcome::Completed(9_u8), &joined),
            SettledLane::Joined(LaneOutcome::Completed(9))
        ));
    }

    /// The acyclic export's cancellation contract (review round 2): it said
    /// "waits up to 3000 ms", which stopped being true at `a8ea18162`.
    #[test]
    fn the_exported_cancellation_contract_says_what_the_driver_does() {
        let text = acyclic_lane_cancellation_contract();
        assert!(!text.contains("waits up to"), "{text}");
        assert!(text.contains("waits for the thread to exit"), "{text}");
        assert!(text.contains("failed drain past 3000 ms"), "{text}");
        assert!(text.contains("quarantines a lane still alive at the harness deadline"), "{text}");
    }

    /// A forced lane whose drain failed but which was joined keeps the
    /// ordinary guard-timeout error, so the external-fallback gate applies to
    /// it as to any guard timeout; an abandoned lane does not open it.
    #[test]
    fn a_forced_lane_after_a_failed_drain_keeps_the_guard_timeout_route() {
        let guard = Duration::from_secs(35);
        let join = timed_out(4480, false);
        assert_eq!(lane_disposition(&join), LaneDisposition::Continue);
        let joined = forced_lane_timeout_error("bmc-only", guard);
        assert!(crate::call_ay::native_chc_error_allows_external_proof_fallback(&joined));
        assert_eq!(
            crate::verification_provenance::SolverUnknownReason::from_chc_error(&joined),
            crate::verification_provenance::SolverUnknownReason::Timeout
        );
        let abandoned_join = timed_out(91_000, true);
        assert_eq!(lane_disposition(&abandoned_join), LaneDisposition::EndHarness);
        let abandoned = anyhow::anyhow!("{}", lane_abandoned_message(&abandoned_join));
        assert!(!crate::call_ay::native_chc_error_allows_external_proof_fallback(&abandoned));
        assert!(abandoned.to_string().contains(LANE_ABANDONED_PHRASE));
        assert_eq!(
            crate::verification_provenance::SolverUnknownReason::from_chc_error(&abandoned),
            crate::verification_provenance::SolverUnknownReason::Timeout
        );
    }

    #[test]
    fn the_wind_down_wording_names_the_three_cases() {
        assert_eq!(lane_wind_down(&timed_out(5, false)), "wound down");
        assert!(lane_wind_down(&timed_out(4480, false)).starts_with("drain failed"));
        // Only a lane really left running is "still winding down" (B2's symptom).
        assert!(lane_wind_down(&timed_out(91_000, true)).starts_with("still winding down"));
    }
}

#[cfg(test)]
mod pdr_proof_run_tests {
    use super::*;

    #[test]
    fn acyclic_bmc_order_defaults_to_after_an_undecided_batch() {
        assert_eq!(parse_acyclic_bmc_order(None), AcyclicBmcOrder::AfterUndecidedBatch);
        assert_eq!(parse_acyclic_bmc_order(Some("")), AcyclicBmcOrder::AfterUndecidedBatch);
        assert_eq!(parse_acyclic_bmc_order(Some("FIRST ")), AcyclicBmcOrder::First);
        assert_eq!(parse_acyclic_bmc_order(Some("after")), AcyclicBmcOrder::AfterUndecidedBatch);
    }

    #[test]
    fn bmc_crosscheck_skips_only_per_row_validated_verdicts() {
        // skip_verify turns every defence off, forced or not.
        assert!(!bmc_crosscheck_runs(true, false, false));
        assert!(!bmc_crosscheck_runs(true, true, true));
        // One-shot engines keep the cross-check.
        assert!(bmc_crosscheck_runs(false, false, false));
        // Per-property verdicts skip it unless the env forces it back on.
        assert!(!bmc_crosscheck_runs(false, true, false));
        assert!(bmc_crosscheck_runs(false, true, true));
    }

    #[test]
    fn checked_replay_budget_defaults_to_one_third_with_twenty_second_cap() {
        assert_eq!(
            checked_replay_budget_from_override(Duration::from_secs(30), None),
            Duration::from_secs(10)
        );
        assert_eq!(
            checked_replay_budget_from_override(Duration::from_secs(300), None),
            Duration::from_secs(20)
        );
    }

    #[test]
    fn checked_replay_budget_honors_bounded_explicit_override() {
        assert_eq!(
            checked_replay_budget_from_override(Duration::from_secs(300), Some(" 0 ")),
            Duration::ZERO
        );
        assert_eq!(
            checked_replay_budget_from_override(Duration::from_secs(30), Some("45")),
            Duration::from_secs(30)
        );
        assert_eq!(
            checked_replay_budget_from_override(Duration::from_secs(30), Some("12")),
            Duration::from_secs(12)
        );
    }

    #[test]
    fn checked_replay_budget_ignores_invalid_override() {
        for raw in ["", "-1", "20seconds", "18446744073709551616"] {
            assert_eq!(
                checked_replay_budget_from_override(Duration::from_secs(30), Some(raw)),
                Duration::from_secs(10),
                "malformed override {raw:?} must use the default policy"
            );
        }
    }

    #[test]
    fn zero_budget_checked_replay_stays_non_admissible() {
        let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
        let problem = ay_chc::ChcParser::parse(smt2).expect("test CHC should parse");
        let run = ay_chc::engines::solve_pdr_proof(
            problem.clone(),
            ay_chc::PdrConfig::default().with_max_frames(8).with_max_iterations(100),
        )
        .expect("test CHC should solve");

        // `checked_proof_transcript_metadata` on a loose result is gone: AY now
        // seals the solved problem into the run. A zero replay budget cannot
        // upgrade the transcript, so the run's own metadata is exactly what the
        // old call produced here — metadata-only, not admissible.
        let metadata = run.metadata().to_json_value();

        assert_eq!(metadata["trust_full_verifier_admissible"], false);
        assert_ne!(metadata["replay"]["status"], "replayable");
        assert!(
            !acyclic_bmc_safe_metadata_is_proof_grade(Some(&metadata)),
            "a disabled checked replay must not cross the native proof-grade gate"
        );
    }

    #[test]
    fn pdr_proof_run_maps_to_digest_backed_trust_mc_evidence() {
        let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
        let problem = ay_chc::ChcParser::parse(smt2).expect("test CHC should parse");
        let run = ay_chc::engines::solve_pdr_proof(
            problem.clone(),
            ay_chc::PdrConfig::default().with_max_frames(8).with_max_iterations(100),
        )
        .expect("test CHC should solve");

        assert!(run.accepted_as_proof());
        let proof_run_artifacts = run.proof_run_artifacts();
        let expected_transcript_hash = trust_mc_core::EvidenceHash::sha256_bytes(
            proof_run_artifacts.replay_transcript().bytes(),
        );
        let expected_invariant = proof_run_artifacts
            .quantifier_free_invariant_model()
            .expect("Safe PDR run must carry its actual QF invariant");
        let expected_model_hash =
            trust_mc_core::EvidenceHash::sha256_bytes(expected_invariant.bytes());
        let verdict = pdr_proof_run_verdict(&run, &problem, "harness::pdr");

        let trust_mc_core::ProofGradeVerdict::NotProofGrade { reasons, .. } =
            trust_mc_core::classify_proof_grade_verdict(&verdict)
        else {
            panic!("ordinary AY PDR output must await fresh private consumer replay");
        };
        assert!(
            reasons
                .contains(&trust_mc_core::PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED.to_string())
        );
        let trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        } = verdict
        else {
            panic!("accepted PDR proof run should produce CHC/PDR proof evidence");
        };
        let transcript = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::SolverTranscript
            })
            .expect("solver transcript artifact");
        assert_eq!(transcript.digest.as_ref(), Some(&expected_transcript_hash));
        assert_eq!(
            transcript.byte_len,
            Some(proof_run_artifacts.replay_transcript().bytes().len() as u64)
        );
        assert_eq!(
            transcript.materialized_bytes(),
            Some(proof_run_artifacts.replay_transcript().bytes())
        );
        let replay = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::ReplayLog
            })
            .expect("replay artifact");
        let checked = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::CheckedProofReport
            })
            .expect("checked-report artifact");
        assert!(replay.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                expected_transcript_hash.clone(),
            )
        ));
        assert!(replay.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel,
                expected_model_hash.clone(),
            )
        ));
        assert!(checked.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::SolverTranscript,
                expected_transcript_hash.clone(),
            )
        ));
        assert!(checked.referenced_artifacts().contains(
            &trust_mc_core::FullVerificationArtifactReference::new(
                trust_mc_core::FullVerificationArtifactKind::ReplayLog,
                replay.digest.clone().expect("replay digest"),
            )
        ));
        let replay_payload: serde_json::Value =
            serde_json::from_slice(replay.materialized_bytes().expect("replay bytes"))
                .expect("replay JSON");
        let checked_payload: serde_json::Value =
            serde_json::from_slice(checked.materialized_bytes().expect("checked bytes"))
                .expect("checked JSON");
        assert_eq!(
            replay_payload["referenced_solver_transcript"]["value"],
            expected_transcript_hash.value
        );
        assert_eq!(
            checked_payload["referenced_solver_transcript"]["value"],
            expected_transcript_hash.value
        );
        assert_eq!(
            checked_payload["referenced_replay_log"]["value"],
            replay.digest.as_ref().expect("replay digest").value
        );
        assert_eq!(checked_payload["replay_check_status"]["authoritative"], false);
        assert_eq!(
            checked_payload["replay_check_status"]["fresh_private_consumer_replay_required"],
            true
        );
        let invariant_model = proof
            .artifacts
            .iter()
            .find(|artifact| {
                artifact.kind == trust_mc_core::FullVerificationArtifactKind::PdrInvariantModel
            })
            .expect("PDR invariant model artifact");
        assert_eq!(invariant_model.digest.as_ref(), Some(&expected_model_hash));
        assert_eq!(invariant_model.byte_len, Some(expected_invariant.bytes().len() as u64));
        assert_eq!(invariant_model.materialized_bytes(), Some(expected_invariant.bytes()));
        let artifact_json: serde_json::Value = serde_json::from_slice(
            invariant_model.materialized_bytes().expect("QF invariant bytes are materialized"),
        )
        .expect("QF invariant is a versioned JSON envelope");
        assert_eq!(artifact_json["schema"], ay_chc::CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA);
        ay_chc::parse_qf_invariant_model_artifact(
            &problem,
            invariant_model.materialized_bytes().expect("QF invariant bytes are materialized"),
        )
        .expect("transported PdrInvariantModel must pass AY's strict parser");
    }
}

#[cfg(test)]
mod external_validation_tests {
    use super::*;
    use ay::chc::{ChcExpr, ChcParser, ChcSort, ChcVar, PredicateInterpretation};

    fn model_with_formula(
        problem: &ay::chc::ChcProblem,
        predicate_formula: impl Fn(&str, &[ChcVar]) -> ChcExpr,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in problem.predicates() {
            let vars = ay::chc::canonical_vars_for_pred(problem, pred.id)
                .expect("predicate canonical vars should exist");
            let formula = if pred.name == "error" {
                ChcExpr::Bool(false)
            } else {
                predicate_formula(&pred.name, &vars)
            };
            model.set(pred.id, PredicateInterpretation::new(vars, formula));
        }
        model
    }

    #[test]
    fn external_pdr_invariant_validation_accepts_array_signature_model() {
        let smt2 = r#"
(set-logic HORN)
(declare-var a (Array (_ BitVec 32) (_ BitVec 32)))
(declare-rel P ((Array (_ BitVec 32) (_ BitVec 32))))
(declare-rel error ())
(rule (=> (= (select a #x00000000) #x00000000) (P a)))
(rule (=> (and (P a) (not (= (select a #x00000000) #x00000000))) error))
(query error)
"#;
        let problem = ChcParser::parse(smt2).expect("test CHC should parse");
        let model = model_with_formula(&problem, |_name, vars| {
            let array_var = vars
                .iter()
                .find(|var| matches!(var.sort, ChcSort::Array(_, _)))
                .expect("P should expose the Array argument");
            ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(array_var.clone()), ChcExpr::BitVec(0, 32)),
                ChcExpr::BitVec(0, 32),
            )
        });

        validate_external_pdr_invariant_model(&problem, &model, false, None)
            .expect("array-signature model should validate externally");
    }

    #[test]
    fn a_row_model_rejected_inside_its_budget_is_a_false_proof_and_an_expired_one_is_not() {
        let smt2 = r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel P (Int))
(declare-rel error ())
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (> x 0)) error))
(query error)
"#;
        let problem = ChcParser::parse(smt2).expect("test CHC should parse");
        let wrong = model_with_formula(&problem, |_name, _vars| ChcExpr::Bool(true));
        let right = model_with_formula(&problem, |_name, vars| {
            ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::Int(0))
        });
        let generous = Duration::from_secs(30);
        assert_eq!(
            validate_row_invariant_model(&problem, &right, false, generous).expect("validates"),
            RowModelValidation::Valid
        );
        assert_eq!(
            validate_row_invariant_model(&problem, &wrong, false, generous).expect("validates"),
            RowModelValidation::Rejected,
            "a model AY refutes well inside its budget stays a false proof"
        );
        // AY answers `Ok(false)` for an exhausted budget without looking at the
        // model; the valid model must not be reported as a false proof then.
        assert_eq!(
            validate_row_invariant_model(&problem, &right, false, Duration::ZERO)
                .expect("validates"),
            RowModelValidation::BudgetExhausted
        );
        assert!(reject_false_proof().to_string().contains("false proof detected"));
    }

    /// Review round 2: a forced-engine lane's whole-problem model
    /// re-validation ran under AY's fresh 30-s default (`None`) whatever was
    /// left of the harness, and only when the BMC cross-check had a budget.
    /// It now takes the row path's deadline-drawn budget, and an expiry
    /// leaves the proof uncredited with the fallback-eligible "timed out"
    /// wording — never credited, never a false proof.
    #[test]
    fn a_forced_lane_model_revalidation_is_bounded_by_the_harness_deadline() {
        use super::super::per_property::{ROW_VALIDATION_CAP, row_validation_timeout};
        // The budget follows the deadline: what is left, capped at AY's 30 s,
        // floored at 5 s inside the watchdog headroom.
        assert_eq!(row_validation_timeout(Duration::from_secs(12)), Duration::from_secs(12));
        assert_eq!(row_validation_timeout(Duration::from_secs(300)), ROW_VALIDATION_CAP);
        assert_eq!(row_validation_timeout(Duration::ZERO), Duration::from_secs(5));
        assert!(row_validation_timeout(Duration::from_secs(12)) < Duration::from_secs(30));

        let smt2 = r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel P (Int))
(declare-rel error ())
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (> x 0)) error))
(query error)
"#;
        let problem = ChcParser::parse(smt2).expect("test CHC should parse");
        let wrong = model_with_formula(&problem, |_name, _vars| ChcExpr::Bool(true));
        let right = model_with_formula(&problem, |_name, vars| {
            ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::Int(0))
        });
        let generous = Duration::from_secs(30);
        revalidate_forced_lane_model(&problem, &right, false, "primary-engine-only", generous)
            .expect("a valid model re-validates");
        let rejected =
            revalidate_forced_lane_model(&problem, &wrong, false, "primary-engine-only", generous)
                .expect_err("a refuted model is not credited");
        assert!(rejected.to_string().contains("false proof detected"), "{rejected}");
        let started = std::time::Instant::now();
        let expired =
            revalidate_forced_lane_model(&problem, &right, false, "bmc-only", Duration::ZERO)
                .expect_err("an unconfirmed model is not credited");
        assert!(started.elapsed() < Duration::from_secs(5), "the budget must bind");
        assert!(!expired.to_string().contains("false proof detected"), "{expired}");
        assert!(expired.to_string().contains("timed out"), "{expired}");
        assert!(crate::call_ay::native_chc_error_allows_external_proof_fallback(&expired));
    }

    #[test]
    fn external_pdr_invariant_validation_fails_closed_on_false() {
        let smt2 = r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel P (Int))
(declare-rel error ())
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (> x 0)) error))
(query error)
"#;
        let problem = ChcParser::parse(smt2).expect("test CHC should parse");
        let model = model_with_formula(&problem, |_name, _vars| ChcExpr::Bool(true));

        assert!(
            validate_external_pdr_invariant_model(&problem, &model, false, None).is_err(),
            "invalid invariant models must demote to UNKNOWN instead of being accepted"
        );
    }
}

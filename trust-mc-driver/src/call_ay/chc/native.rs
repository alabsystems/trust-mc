// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Native `ay-chc` portfolio backend entrypoint for CHC integration.

use std::collections::HashSet;
use std::path::Path;
use std::sync::OnceLock;
use std::sync::mpsc::RecvTimeoutError;
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
use crate::session::KaniSession;

use super::native_nullary::{
    constraint_free_nullary_error_derivation_relations,
    satisfiable_acyclic_error_derivation_witness,
};
use super::smt_analysis::{
    smt_error_query_has_false_error_obligation, smt_error_query_is_trivially_safe,
};
use super::{ChcSolverResult, acyclicity, auto_invariants, loop_hints, proof_core};

/// How long a guard waits for a cancelled solve lane to wind down.
///
/// Cancellation in ay-chc is cooperative: the token is polled at stage
/// boundaries and inside the engine loops, so a lane stops promptly but not
/// instantly. Waiting bounds the CPU overlap between an abandoned lane and
/// whatever runs next; the bound keeps a wedged engine from turning the guard
/// into a hang. Exceeding it is not an error — we log it and move on, which is
/// exactly the old orphaning behaviour, so this can only ever be an improvement
/// on it.
const GUARD_CANCEL_DRAIN_SECS: u64 = 3;

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
    /// Do not "fix" this by reordering it behind the budget check — that would
    /// relabel these rows `PdrTimeout`, which is equally untrue of them.
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

fn panic_payload_message(panic_payload: &(dyn std::any::Any + Send)) -> &str {
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

fn native_bmc_cross_check_config(total_budget: Duration, verbose: bool) -> BmcConfig {
    let budget = native_bmc_cross_check_budget(total_budget);
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

pub(super) fn validate_external_pdr_invariant_model(
    problem: &ay::chc::ChcProblem,
    model: &InvariantModel,
    verbose: bool,
) -> anyhow::Result<()> {
    let mut pdr_config = ay::chc::PdrConfig::default();
    pdr_config.verbose = verbose;

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

/// Pure classifier for UNKNOWN outcomes. Tested independently of the solver.
///
/// `predicate_array_counts` is `(predicate_name, array_sort_count)` per predicate,
/// typically collected from `ChcProblem::predicates()` before the problem is
/// moved into the solver.
///
/// Priority order (most specific first):
/// 1. No error rule → degenerate VC
/// 2. ≥2 Array-sorted state params on any predicate → structural label only
///    (see `UnknownCategory::ArrayParamLimit`; this is NOT a proven solver
///    ceiling, and it deliberately preempts the budget check because these
///    rows are not budget-bound either)
/// 3. All engines either timed out or yielded inconclusive results:
///    - at least one timeout → PDR timeout
///    - otherwise (NotApplicable / Disabled / Unknown only) → solver error
/// 4. Fallthrough → uncategorized
pub(super) fn classify_unknown(
    predicate_array_counts: &[(String, usize)],
    budget: Option<&BudgetSummary>,
    has_error_rule: bool,
) -> UnknownCategory {
    // 1. Degenerate VC (no rule derives error).
    if !has_error_rule {
        return UnknownCategory::NoErrorRule;
    }

    // 2. ≥2 Array-sorted state params on any predicate.
    if let Some((name, n)) = predicate_array_counts.iter().find(|(_, n)| *n >= 2) {
        return UnknownCategory::ArrayParamLimit { predicate: name.clone(), array_sort_count: *n };
    }

    // 3/4. Budget-summary-driven classification.
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

        // CRITICAL placement: this deadline bail must come BEFORE the
        // trivially-safe short-circuit PROOF paths below — an exhausted
        // budget must yield a bounded UNKNOWN, never fall into a success path.
        bail_unknown_if_deadline_exhausted(deadline, "trivial_safety_check")?;

        // Trivial safety check: if the CHC system queries `error` but no
        // satisfiable rule can derive `error`, the query is trivially unsat
        // (PROOF). False-bodied error rules such as `(rule (=> false error))`
        // are not derivations and should not force a portfolio solve.
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
                return self.interpret_chc_false_error_safe(smt_file, &smt_content, _harness);
            }
            if self.args.common_args.verbose {
                solver_stdout!(
                    "[AY-chc] No rule derives error — trivially safe (short-circuit PROOF)"
                );
            }
            return self.interpret_chc_trivial_safe(smt_file, &smt_content, _harness);
        }

        bail_unknown_if_deadline_exhausted(deadline, "chc_parse")?;
        let mut problem = ChcParser::parse(&solver_smt_content)
            .map_err(|e| anyhow::anyhow!("Failed to parse CHC problem: {e}"))?;

        if self.args.common_args.verbose {
            solver_stdout!(
                "[AY-chc] Parsed problem: {} predicates, {} clauses",
                problem.predicates().len(),
                problem.clauses().len()
            );
        }

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
        if acyclicity::is_acyclic_problem(&problem)
            && let Some(witness) =
                satisfiable_acyclic_error_derivation_witness(&problem, witness_deadline)
        {
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

        if solve_mode == NativeSolveMode::AdaptivePortfolio
            && acyclicity::is_acyclic_problem(&problem)
        {
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

            // Cancellable so the guard below can stop this lane instead of
            // orphaning it (see the twin comment on the portfolio guard).
            let bmc_cancel = CancellationToken::new();
            let bmc_config = BmcConfig::default()
                .with_max_depth(depth)
                .with_acyclic_safe(true)
                .with_time_budget(full_timeout)
                .with_per_depth_timeout(native_bmc_per_depth_timeout(full_timeout))
                .with_cancellation(bmc_cancel.clone())
                .with_verbose(self.args.common_args.verbose);

            // Clone the problem so we can fall through to portfolio when BMC
            // cannot provide a trusted proof shortcut.
            // Wrap in catch_unwind: ay's BMC engine can panic on certain
            // predicate arity conditions (ay bug — argument index exceeds
            // declared arity after internal transformations). On panic, fall
            // through to the portfolio solver instead of crashing the driver.
            // Part of #4184.
            //
            // Run on a guarded thread with a recv timeout. The guard is belt
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
            // The lane is cancellable (`BmcConfig::with_cancellation`), so on
            // guard timeout we cancel and briefly drain rather than orphan a
            // CPU-burning thread into the portfolio's lap. Falling through is
            // still fail-closed: abandoning BMC only skips a shortcut and never
            // asserts a verdict.
            let problem_for_bmc = problem.clone();
            let (bmc_tx, bmc_rx) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
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
                        checked_replay_budget(full_timeout),
                    );
                    let (result, proof_transcript_metadata) = match bound {
                        Ok(run) => {
                            let metadata = match run.result() {
                                ay::chc::VerifiedChcResult::Safe(_)
                                | ay::chc::VerifiedChcResult::Unsafe(_) => {
                                    Some(run.metadata().to_json_value())
                                }
                                _ => None,
                            };
                            (run.result().clone(), metadata)
                        }
                        // Only an internal panic reaches here (the call is
                        // panic-caught). Keep the pre-existing behaviour for
                        // that case: take the BMC verdict, publish no evidence.
                        Err(_) => (
                            engines::solve_bmc_only(problem_for_bmc.clone(), bmc_config),
                            None,
                        ),
                    };
                    (result, proof_transcript_metadata)
                }));
                let _ = bmc_tx.send(outcome);
            });
            let bmc_guard_timeout = full_timeout + Duration::from_secs(5);
            let bmc_result = match bmc_rx.recv_timeout(bmc_guard_timeout) {
                Ok(outcome) => Some(outcome),
                Err(RecvTimeoutError::Timeout) => {
                    // Cancel before falling through: the portfolio is about to
                    // start, and an orphaned BMC lane would compete with it for
                    // the same cores on the same problem.
                    bmc_cancel.cancel();
                    let wound_down = bmc_rx
                        .recv_timeout(Duration::from_secs(GUARD_CANCEL_DRAIN_SECS))
                        .is_ok();
                    solver_stdout!(
                        "[AY-chc] Acyclic BMC lane exceeded guard timeout ({:?}) — \
                         cancelled ({}), abandoning BMC shortcut, falling through \
                         to portfolio",
                        bmc_guard_timeout,
                        if wound_down {
                            "wound down"
                        } else {
                            "still winding down"
                        }
                    );
                    None
                }
                Err(RecvTimeoutError::Disconnected) => {
                    solver_stdout!(
                        "[AY-chc] Acyclic BMC thread exited without a result — \
                         falling through to portfolio"
                    );
                    None
                }
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
                        return self.interpret_chc_safe(
                            verified_inv,
                            &smt_content,
                            smt_file,
                            _harness,
                            demoted_fallback_count,
                            proof_transcript_metadata,
                            None,
                        );
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
                    if scalar_acyclic_bmc_counterexample_is_trusted(
                        &problem,
                        demoted_fallback_count,
                    ) {
                        if self.args.common_args.verbose {
                            solver_stdout!(
                                "[AY-chc] Acyclic scalar BMC counterexample accepted as complete"
                            );
                        }
                        return self.interpret_chc_unsafe(
                            verified_cex,
                            &problem,
                            smt_file,
                            &smt_content,
                            _harness,
                            proof_transcript_metadata,
                            None,
                        );
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
        // Re-clamp against the per-harness deadline: the acyclic-BMC lane
        // above may have consumed real wall clock (up to its guard timeout),
        // and `full_timeout` was clamped BEFORE that lane ran. Fail-closed:
        // shrink-only, so the portfolio can never extend past the deadline.
        let timeout = deadline.clamp(full_timeout * budget_pct as u32 / 100);
        let mut adaptive_config =
            AdaptiveConfig::with_budget(timeout, self.args.common_args.verbose);
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

        // Snapshot per-predicate array-sort counts for UNKNOWN classification
        // BEFORE the problem is moved into AdaptivePortfolio. Part of #4304.
        let predicate_array_snapshot: Vec<(String, usize)> = problem
            .predicates()
            .iter()
            .map(|p| (p.name.clone(), count_array_sorts(&p.arg_sorts)))
            .collect();

        // Run the selected native solve mode under panic isolation + timeout
        // guard. Default adaptive mode keeps budget reporting; forced modes use
        // dedicated single-lane solve paths so the CLI controls are concrete.
        let external_validation_problem = problem.clone();
        let pdr_proof_problem = problem.clone();
        let mut pdr_proof_config = ay_chc::PdrConfig::production(self.args.common_args.verbose);
        pdr_proof_config.solve_timeout = Some(timeout);
        pdr_proof_config.user_hints = adaptive_config.user_hints.clone();
        let pdr_proof_obligation_id = _harness.pretty_name.clone();
        let solver = AdaptivePortfolio::new(problem, adaptive_config);
        // COOPERATIVELY CANCELLABLE: the native CHC solve below runs in-process
        // on a detached thread, but we hold a cancellation handle for it, so
        // the guard-timeout path cancels instead of orphaning.
        //
        // This previously read KNOWN-UNCANCELLABLE ("ay's engine APIs expose
        // none"), which is stale: `AdaptivePortfolio::cancellation_handle`
        // exists and its own doc names *this* guard path as the motivating use
        // case. The token is observed by the adaptive stage scheduler at every
        // stage-boundary budget check and is linked upstream into the per-lane
        // engine tokens, so the running engine bails cooperatively too.
        //
        // Why it matters beyond tidiness: an orphaned solve keeps burning
        // CPU/memory until its internal budgets expire, *while* the driver goes
        // on to run the portfolio and then the next harness. Under `--jobs N`
        // that double-spend starves sibling harnesses, which is how a SHORTER
        // per-harness budget can cost more wall clock than a longer one.
        //
        // Cancellation can only degrade a verdict to Unknown, never flip
        // Safe/Unsafe, and we bail to UNKNOWN on this path regardless — so this
        // cannot change any answer, only stop paying for one we discarded.
        let portfolio_cancel = solver.cancellation_handle();
        let guard_timeout = timeout + Duration::from_secs(5);
        let bmc_verbose = self.args.common_args.verbose;
        let (tx, rx) = std::sync::mpsc::channel();
        let solver_thread = std::thread::spawn(move || {
            let solve_result = ay::catch_ay_panics(
                std::panic::AssertUnwindSafe(|| {
                    let (verified, report, bound_run) = match solve_mode {
                        NativeSolveMode::AdaptivePortfolio => {
                            // Match the production ay CLI validation path. The budget-report
                            // route has separate prepasses and must not be treated as the
                            // authoritative proof result for replacement evidence.
                            //
                            // `solve_proof_run` is the problem-BOUND form: AY
                            // seals the solved problem into the run so evidence
                            // cannot describe a different one. It replaces
                            // minting metadata from a loose `VerifiedChcResult`,
                            // which AY no longer permits.
                            let run = solver.solve_proof_run();
                            (run.result().clone(), None::<ay_chc::BudgetReport>, Some(run))
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
                            let proof_transcript_metadata = Some(run.metadata().to_json_value());
                            return Ok((
                                run.result().clone(),
                                None,
                                proof_transcript_metadata,
                                Some(native_full_verification_verdict),
                            ));
                        }
                        NativeSolveMode::BmcOnly => {
                            let bmc_config = bounded_native_bmc_config(
                                BmcConfig::default(),
                                full_timeout,
                                bmc_verbose,
                            );
                            match ay_chc::engines::solve_bmc_proof_with_checked_replay(
                                solver.problem().clone(),
                                bmc_config.clone(),
                                checked_replay_budget(timeout),
                            ) {
                                Ok(run) => (run.result().clone(), None, Some(run)),
                                // Panic-caught internally; keep the verdict and
                                // publish no evidence, as before.
                                Err(_) => (solver.solve_bmc_only(bmc_config), None, None),
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
                    Ok((verified, report, proof_transcript_metadata, None))
                }),
                |reason| Err(reason),
            );
            let stats: ChcStatistics = solver.statistics();
            let _ = tx.send((solve_result, stats));
        });
        let (
            result,
            budget_report,
            proof_transcript_metadata,
            native_full_verification_verdict,
            chc_stats,
        ) = match rx.recv_timeout(guard_timeout) {
            Ok((solve_result, stats)) => {
                let _ = solver_thread.join();
                match solve_result {
                    Ok((verified, report, proof_transcript_metadata, native_verdict)) => {
                        (verified, report, proof_transcript_metadata, native_verdict, Some(stats))
                    }
                    Err(reason) => {
                        anyhow::bail!("ay-chc panic during {}: {reason}", solve_mode.label());
                    }
                }
            }
            Err(RecvTimeoutError::Disconnected) => match solver_thread.join() {
                Err(panic_payload) => {
                    anyhow::bail!(
                        "ay-chc solver thread panicked: {}",
                        panic_payload_message(panic_payload.as_ref())
                    );
                }
                Ok(()) => {
                    anyhow::bail!("ay-chc solver thread exited without producing a result");
                }
            },
            Err(RecvTimeoutError::Timeout) => {
                // Stop paying for a solve whose answer we have already decided
                // to discard, before the next harness starts competing for the
                // same cores. Bounded drain so a wedged engine cannot convert
                // this into a hang; the drained result is deliberately unused.
                portfolio_cancel.cancel();
                let wound_down = rx
                    .recv_timeout(Duration::from_secs(GUARD_CANCEL_DRAIN_SECS))
                    .is_ok();
                solver_stdout!(
                    "[AY-chc] {} exceeded guard timeout ({:?}) — \
                     cancelled ({}), returning UNKNOWN",
                    solve_mode.label(),
                    guard_timeout,
                    if wound_down {
                        "wound down"
                    } else {
                        "still winding down"
                    }
                );
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
                // No budget_report available on guard-timeout; still emit
                // Array-param / NoErrorRule classification from the snapshot.
                // Part of #4304.
                let category = classify_unknown(&predicate_array_snapshot, None, has_error_rule);
                solver_stdout!("{}", category.tag_line());
                anyhow::bail!(
                    "ay-chc {} exceeded guard timeout ({:?})",
                    solve_mode.label(),
                    guard_timeout
                );
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

        match result {
            ay::chc::VerifiedChcResult::Safe(verified_inv) => {
                // Defense-in-depth: BMC cross-check replaces manual model re-verification.
                // Uses ay's purpose-built BmcConfig::cross_check() preset (ay#8412) —
                // runs BMC independently to search for counterexamples that would
                // contradict the claimed PROOF. If BMC finds Unsafe, the proof is false.
                if !self.args.ay_chc_skip_verify {
                    if let Ok(verify_problem) = ChcParser::parse(&solver_smt_content) {
                        let bmc_result =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                engines::solve_bmc_only(
                                    verify_problem,
                                    native_bmc_cross_check_config(timeout, verbose),
                                )
                            }));
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
                    // Secondary defense: external model re-verification via fresh PDR solver
                    // (ay#8578). The ay API disables verifier-side array scalarization so
                    // backtranslated models are checked against the submitted CHC signature.
                    validate_external_pdr_invariant_model(
                        &external_validation_problem,
                        verified_inv.model(),
                        self.args.common_args.verbose,
                    )?;
                }
                self.interpret_chc_safe(
                    verified_inv,
                    &smt_content,
                    smt_file,
                    _harness,
                    demoted_fallback_count,
                    proof_transcript_metadata,
                    native_full_verification_verdict,
                )
            }
            ay::chc::VerifiedChcResult::Unsafe(verified_cex) => {
                // Defense-in-depth for UNSAFE: BMC cross-check for spurious counterexamples.
                // If BMC proves SAFE on the same problem, the portfolio's CTREX is false.
                // Part of #4272.
                if !self.args.ay_chc_skip_verify {
                    if let Ok(verify_problem) = ChcParser::parse(&solver_smt_content) {
                        let bmc_result =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                engines::solve_bmc_only(
                                    verify_problem,
                                    native_bmc_cross_check_config(timeout, verbose),
                                )
                            }));
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
                    &external_validation_problem,
                    smt_file,
                    &smt_content,
                    _harness,
                    proof_transcript_metadata,
                    native_full_verification_verdict,
                )
            }
            ay::chc::VerifiedChcResult::Unknown(_) | _ => {
                if self.args.common_args.verbose {
                    solver_stdout!("[AY-chc] {} returned Unknown", solve_mode.label());
                }
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
                let category = classify_unknown(
                    &predicate_array_snapshot,
                    budget_summary.as_ref(),
                    has_error_rule,
                );
                solver_stdout!("{}", category.tag_line());
                anyhow::bail!(
                    "ay-chc {} returned Unknown - verification inconclusive",
                    solve_mode.label()
                )
            }
        }
    }
}

#[cfg(test)]
mod pdr_proof_run_tests {
    use super::*;

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

        validate_external_pdr_invariant_model(&problem, &model, false)
            .expect("array-signature model should validate externally");
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
            validate_external_pdr_invariant_model(&problem, &model, false).is_err(),
            "invalid invariant models must demote to UNKNOWN instead of being accepted"
        );
    }
}

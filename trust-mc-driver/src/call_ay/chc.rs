// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC solver integration extracted from call_ay.

use crate::property_model::Property;
use crate::verification_result::{FailedProperties, ProofCrosscheck, VerificationStatus};

#[cfg(feature = "ay-chc-native")]
mod acyclicity;
#[cfg(all(test, feature = "ay-chc-native"))]
pub(crate) mod api;
#[cfg(feature = "ay-chc-native")]
mod auto_invariants;
#[cfg(feature = "ay-direct")]
mod direct;
#[cfg(feature = "ay-chc-native")]
mod external;
#[cfg(feature = "ay-chc-native")]
mod loop_hints;
#[cfg(feature = "ay-chc-native")]
mod model_eval;

mod native;
#[cfg(feature = "ay-chc-native")]
mod native_nullary;
#[cfg(feature = "ay-chc-native")]
mod native_result;
#[cfg(feature = "ay-chc-native")]
mod owned_lane;
#[cfg(feature = "ay-chc-native")]
mod per_property;
#[cfg(feature = "ay-chc-native")]
pub(crate) mod proof_core;
#[cfg(feature = "ay-chc-native")]
mod property_report;
#[cfg(feature = "ay-chc-native")]
mod resource_envelope;
#[cfg(feature = "ay-chc-native")]
mod row_export;
#[cfg(all(test, feature = "ay-chc-native"))]
pub(crate) mod rewrite_concat;
mod smt_analysis;
pub(super) use smt_analysis::smt_translation_timeout_marker;
#[cfg(feature = "ay-chc-native")]
mod sort_helpers;
#[cfg(test)]
mod tests;
#[cfg(all(test, feature = "ay-chc-native"))]
mod tests_auto_invariants;
#[cfg(all(test, feature = "ay-chc-native"))]
mod tests_rewrite_concat;
#[cfg(feature = "ay-chc-native")]
mod vacuity_probe;
#[cfg(feature = "ay-chc-native")]
mod vacuity_witness;
mod verdict_policy;

pub(crate) const TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER: &str = "trivial_safe=no_error_rule";

pub(crate) struct ChcSolverResult {
    pub(crate) status: VerificationStatus,
    pub(crate) failed_properties: FailedProperties,
    pub(crate) properties: Vec<Property>,
    pub(crate) proof_crosscheck: ProofCrosscheck,
    pub(crate) proof_qualifiers: Vec<String>,
    pub(crate) proof_transcript_metadata: Option<serde_json::Value>,
    pub(crate) native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
    /// Why a non-proof result is inconclusive, when the CHC lane itself decided
    /// that without a solver answer (today only `LostErrorRules`). `None` keeps
    /// the caller's existing attribution.
    pub(crate) solver_unknown_reason: Option<crate::verification_provenance::SolverUnknownReason>,
    /// The CHC layer DERIVED the error state, it did not fail to decide.
    ///
    /// Set ONLY by [`KaniSession::interpret_chc_trivial_unsafe`], whose two
    /// callers each hold an exact derivation of `error` — the constraint-free
    /// zero-arity closure, or an SMT-model-backed acyclic derivation witness.
    /// Every other producer leaves it `false`, so absence of the signal keeps
    /// the historical fail-closed reading (a `Failure` the driver cannot
    /// attribute is an UNKNOWN, never a counterexample).
    ///
    /// Consumed by `harness_runner`'s CTREX classification, which otherwise
    /// reads `FailedProperties::Other` on the CHC path as "solver undecided".
    /// That reading is right for an aggregate solve and WRONG here: the legacy
    /// aggregate `chc.0` property carries the class of the reachable check
    /// (memory safety, pointer overflow, a valid-value check ⇒ `Other`), so an
    /// exactly derived non-panic counterexample was indistinguishable from a
    /// solver that gave up. This flag does not decide the category — it only
    /// routes the row to `classify_ctrex`, which still demotes it to
    /// `EncodingGap`/`OverApproximation` when the harness carries approximations.
    pub(crate) exact_counterexample: bool,
}

/// AY ask R1: before a harness starts any work, wait for every lane an earlier
/// harness abandoned at its deadline (`owned_lane`'s quarantine) to exit, and
/// join it, bounded by this harness's deadline. `Err` is the marker line to
/// print when one is still alive then; the harness must end UNKNOWN without
/// starting anything. Returns at once when nothing was ever abandoned.
#[cfg(feature = "ay-chc-native")]
pub(crate) fn await_lane_quarantine(deadline: &crate::deadline::Deadline) -> Result<(), String> {
    match owned_lane::LANE_QUARANTINE.wait_clear(deadline.instant()) {
        owned_lane::QuarantineWait::Clear { joined } => {
            if !crate::args::common::quiet_output() {
                for (lane, after) in joined {
                    println!(
                        "[AY:LANE-QUARANTINE-JOINED] lane={lane} after_ms={} — an abandoned lane \
                         exited and was joined before this harness started",
                        after.as_millis()
                    );
                }
            }
            Ok(())
        }
        owned_lane::QuarantineWait::Busy { lanes, oldest } => Err(format!(
            "[AY:LANE-QUARANTINE] lanes={} oldest_ms={} — a lane an earlier harness abandoned at \
             its deadline is still running; this harness starts no work beside it and ends \
             UNKNOWN at its own deadline",
            lanes.join(","),
            oldest.as_millis()
        )),
    }
}

/// The abandoned-lane wording (AY ask R1), for the fallback gate's tests.
#[cfg(all(test, feature = "ay-chc-native"))]
pub(crate) use native::LANE_ABANDONED_PHRASE;
/// The row export's hooks for the loop-contract retry (review round 3).
#[cfg(feature = "ay-chc-native")]
pub(crate) use row_export::{record_loop_contract_retry, retry_lane_export_dir};

// Re-export helpers for tests after the D3/D4 engine splits.
#[cfg(all(test, feature = "ay-chc-native"))]
use native::dedup_lemma_hints;
#[cfg(all(test, feature = "ay-chc-native"))]
use native::{BudgetSummary, UnknownCategory, classify_unknown};

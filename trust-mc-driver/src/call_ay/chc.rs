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
pub(crate) mod proof_core;
#[cfg(feature = "ay-chc-native")]
mod property_report;
#[cfg(all(test, feature = "ay-chc-native"))]
pub(crate) mod rewrite_concat;
mod smt_analysis;
#[cfg(feature = "ay-chc-native")]
mod sort_helpers;
#[cfg(test)]
mod tests;
#[cfg(all(test, feature = "ay-chc-native"))]
mod tests_auto_invariants;
#[cfg(all(test, feature = "ay-chc-native"))]
mod tests_rewrite_concat;
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
}

// Re-export helpers for tests after the D3/D4 engine splits.
#[cfg(all(test, feature = "ay-chc-native"))]
use native::dedup_lemma_hints;
#[cfg(all(test, feature = "ay-chc-native"))]
use native::{BudgetSummary, UnknownCategory, classify_unknown};

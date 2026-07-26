// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Verification result types and formatting used by the AY backend and harness runner.

use std::env;
use std::fmt::Write;
use std::time::Duration;

use console::style;
use strum_macros::Display;

use crate::args::OutputFormat;
use crate::coverage::cov_results::CoverageResults;
use crate::demotion::is_effective_manual_success;
use crate::property_model::{CheckStatus, Property};
pub(crate) use crate::verification_provenance::SolverUnknownReason;
use format_helpers::{
    UNSUPPORTED_CONSTRUCT_DESC, build_failure_message, has_check_failure,
    has_unwinding_assertion_failures,
};
pub(crate) use proof_crosscheck::ProofCrosscheck;

#[path = "verification_result_format_helpers.rs"]
mod format_helpers;
#[path = "verification_result_proof_crosscheck.rs"]
mod proof_crosscheck;

const EFFECTIVE_SUCCESS_MARKER_ENV: &str = "TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS";
const SHOULD_PANIC_PANICS_ONLY_EFFECTIVE_SUCCESS: &str = "should_panic_panics_only";

#[derive(Clone, Copy, Debug, Display, PartialEq, Eq)]
pub(crate) enum VerificationStatus {
    Success,
    Failure,
}

/// Represents failed properties in three different categories.
/// This simplifies the process to determine and format verification results.
#[derive(Clone, Copy, Debug)]
pub(crate) enum FailedProperties {
    // No failures
    None,
    // One or more panic-related failures
    PanicsOnly,
    // One or more failures that aren't panic-related
    Other,
}

/// Logic tier classification for verification queries: `TierA` is linear/validated,
/// `TierB` is non-linear/best-effort.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum LogicTier {
    /// Linear arithmetic only - results are fully trusted
    #[default]
    TierA,
    /// Non-linear arithmetic detected - best-effort, results demoted unless proven
    TierB,
}

impl LogicTier {
    /// Returns the appropriate validation status for this logic tier.
    ///
    /// TierA (linear) results are fully validated; TierB (NIA) results are
    /// unvalidated because the solver is incomplete for non-linear arithmetic.
    pub(crate) fn validation_status(self) -> ValidationStatus {
        match self {
            Self::TierA => ValidationStatus::Validated,
            Self::TierB => ValidationStatus::Unvalidated,
        }
    }
}

/// Validation status for verification results.
///
/// Indicates whether a verification result should be trusted or has been demoted
/// due to solver limitations (e.g., NIA incompleteness).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum ValidationStatus {
    /// Result is validated - solver is complete for this logic tier
    #[default]
    Validated,
    /// Result is unvalidated - solver may be incomplete (NIA detected, no proof artifact)
    Unvalidated,
}

/// Classification of a CTREX (counterexample) verdict's likely root cause (#3128).
///
/// When PDR returns SAT, this classifies whether the counterexample is likely
/// genuine or an artifact of encoding gaps. Mirrors the PROOF demotion pipeline
/// but runs in the SAT direction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CtrexCategory {
    /// Harness has nonzero unsoundness counts in DEMOTED_CATEGORIES.
    /// The encoding gap likely made the problem too weak, allowing a
    /// spurious counterexample. Lists all triggered category names.
    EncodingGap { categories: Vec<String> },
    /// Harness has nonzero SOUND_APPROXIMATION counts but zero DEMOTED counts.
    /// The over-approximation (unconstrained symbolic values) may have allowed an
    /// impossible counterexample — the solver found a SAT assignment using values
    /// that the real program can never produce. Lists triggered categories.
    OverApproximation { categories: Vec<String> },
    /// Harness has zero unsoundness counts. The counterexample is likely genuine
    /// (the assertion is actually violated) or caused by a stub that doesn't
    /// track unsoundness counts.
    Genuine,
    /// Solver returned UNKNOWN (timeout, resource exhaustion, etc.) — no actual
    /// counterexample exists. Distinct from Genuine to avoid conflating "real bug"
    /// with "solver couldn't decide" (#3374).
    Unknown,
}

impl CtrexCategory {
    /// Short human-readable tag for diagnostics (e.g. the pre-certification
    /// category logged when an EncodingGap/OverApproximation CTREX is upgraded
    /// to Genuine).
    pub(crate) fn label(&self) -> &'static str {
        match self {
            Self::EncodingGap { .. } => "EncodingGap",
            Self::OverApproximation { .. } => "OverApproximation",
            Self::Genuine => "Genuine",
            Self::Unknown => "Unknown",
        }
    }
}

/// Quality classification for solver UNKNOWN results.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum UnknownQuality {
    /// No known encoding or approximation gaps are attached to this UNKNOWN.
    Clean,
    /// The harness already carries known encoding gaps.
    EncodingGap { reasons: Vec<String> },
    /// The harness carries only sound over-approximation signals.
    OverApproximation { reasons: Vec<String> },
    /// Both encoding-gap and over-approximation signals are attached.
    Mixed { reasons: Vec<String> },
}

impl UnknownQuality {
    pub(crate) fn label(&self) -> &'static str {
        match self {
            Self::Clean => "Clean",
            Self::EncodingGap { .. } => "EncodingGap",
            Self::OverApproximation { .. } => "OverApproximation",
            Self::Mixed { .. } => "Mixed",
        }
    }

    pub(crate) fn details(&self) -> Option<String> {
        let reasons = match self {
            Self::Clean => return None,
            Self::EncodingGap { reasons }
            | Self::OverApproximation { reasons }
            | Self::Mixed { reasons } => reasons,
        };
        (!reasons.is_empty()).then(|| reasons.join(","))
    }
}

/// Backend-neutral verification result.
#[derive(Debug)]
pub(crate) struct VerificationResult {
    /// Whether verification succeeded or failed.
    pub status: VerificationStatus,
    /// The compact representation for failed properties
    pub failed_properties: FailedProperties,
    /// The verification properties (checks, assertions, cover statements).
    pub results: Vec<Property>,
    /// The runtime duration of this verification invocation.
    pub runtime: Duration,
    /// Whether concrete playback generated a test
    pub generated_concrete_test: bool,
    /// The coverage results
    pub coverage_results: Option<CoverageResults>,
    /// Logic tier classification (LIA vs NIA), used to enforce demotion invariants.
    pub logic_tier: LogicTier,
    /// Validation status for results (Validated or Unvalidated)
    pub validation_status: ValidationStatus,
    /// Unsoundness demotion categories triggered (#3099); "category=count" entries.
    pub demotion_reasons: Vec<String>,
    /// CTREX classification when verdict is SAT (#3128).
    pub ctrex_category: Option<CtrexCategory>,
    /// Quality classification for solver UNKNOWN verdicts (#2985).
    pub unknown_quality: Option<UnknownQuality>,
    /// Driver-side reason for a final solver UNKNOWN verdict (#3838).
    pub solver_unknown_reason: Option<SolverUnknownReason>,
    /// Per-harness kani::mem over-approximation count (#3165).
    pub kani_mem_overapprox_count: usize,
    /// Per-harness sound fallback count (#3476).
    pub sound_fallback_count: usize,
    /// Proof cross-check provenance (#2574).
    pub proof_crosscheck: ProofCrosscheck,
    /// Additional proof qualifiers surfaced by the driver/reporting seam.
    pub proof_qualifiers: Vec<String>,
    /// Optional native AY CHC proof/transcript metadata.
    ///
    /// This is metadata only. It records solver-produced binding data for
    /// downstream consumers without changing report gate enforcement.
    pub proof_transcript_metadata: Option<serde_json::Value>,
    /// Optional native full-verification verdict with digest-backed evidence.
    pub native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
}

impl VerificationResult {
    pub(crate) fn render(&self, output_format: &OutputFormat, should_panic: bool) -> String {
        let results = &self.results;
        let status = self.status;
        let failed_properties = self.failed_properties;
        let validation_status = self.validation_status;
        debug_assert!(
            !(validation_status == ValidationStatus::Unvalidated
                && self.logic_tier == LogicTier::TierA),
            "linear logic results must remain validated"
        );
        let show_checks = matches!(output_format, OutputFormat::Regular);

        let mut result = if let Some(cov_results) = &self.coverage_results {
            format_coverage(
                results,
                cov_results,
                status,
                should_panic,
                failed_properties,
                show_checks,
                validation_status,
            )
        } else {
            format_result(
                results,
                status,
                should_panic,
                failed_properties,
                show_checks,
                validation_status,
            )
        };
        // Part of #3476: qualify PROOF results with sound fallback count.
        if self.sound_fallback_count > 0 && status == VerificationStatus::Success {
            let _ = writeln!(
                result,
                "** NOTE: PROOF with {} sound fallback(s) — some constraints over-approximated",
                self.sound_fallback_count
            );
        }
        // BMC cross-check was removed as part of Z3 elimination (#4223).
        // ProofCrosscheck is always NotRun now.
        let ProofCrosscheck::NotRun = &self.proof_crosscheck;
        let _ = writeln!(result, "Verification Time: {}s", self.runtime.as_secs_f32());
        result
    }
}

/// V4 detection (pure): `true` iff the harness has ≥1 non-cover check and EVERY
/// non-cover check is `Unreachable`. This is the unsatisfiable-assumption signature:
/// under contradictory preconditions (`kani::assume(false)`, an over-constrained
/// precondition) every downstream assertion is provably unreachable, so the proof
/// "passed" only vacuously. Conservative by construction — a GENUINE counterexample
/// leaves a `Failure`-status check and a solver timeout leaves `Undetermined`, so
/// both break the all-unreachable signature (no false positives on real failures or
/// inconclusive runs). `code_coverage` (`Covered`/`Uncovered`) and `cover` properties
/// are not verification checks and are excluded.
pub(crate) fn is_unsat_assumption_vacuous(properties: &[Property]) -> bool {
    let mut checks = 0usize;
    let mut unreachable = 0usize;
    for p in properties {
        if p.is_cover_property() {
            continue;
        }
        if matches!(p.status, CheckStatus::Covered | CheckStatus::Uncovered) {
            continue;
        }
        checks += 1;
        if p.status == CheckStatus::Unreachable {
            unreachable += 1;
        }
    }
    checks > 0 && unreachable == checks
}

/// V5 detection (pure): `true` iff the harness declares a `cover(...)` the solver
/// PROVED `Unsatisfiable` or `Unreachable` — a definitive negative (NOT an
/// `Undetermined` timeout). Such a cover is a vacuous witness: the harness claims to
/// exercise a behavior it provably never reaches.
pub(crate) fn has_unsatisfiable_cover(properties: &[Property]) -> bool {
    properties.iter().any(|p| {
        p.is_cover_property()
            && matches!(p.status, CheckStatus::Unsatisfiable | CheckStatus::Unreachable)
    })
}

/// V5 conformance tier (pure): `true` iff the harness has at least one `cover(...)`
/// the solver proved `Satisfied`. A CONFORMANCE harness MUST have one — it is the
/// witness that the harness actually reached the behavior it claims to exercise.
/// `false` (no covers, or every cover unsatisfiable/unreachable/undetermined) means
/// the conformance claim is vacuous.
pub(crate) fn has_satisfied_cover(properties: &[Property]) -> bool {
    properties.iter().any(|p| p.is_cover_property() && p.status == CheckStatus::Satisfied)
}

pub(crate) fn format_result(
    properties: &[Property],
    status: VerificationStatus,
    should_panic: bool,
    failed_properties: FailedProperties,
    show_checks: bool,
    validation_status: ValidationStatus,
) -> String {
    let mut result_str = String::new();
    let mut number_checks_failed = 0;
    let mut number_checks_unreachable = 0;
    let mut number_checks_undetermined = 0;
    let mut failed_tests: Vec<&Property> = vec![];

    let mut number_covers_satisfied = 0;
    let mut number_covers_undetermined = 0;
    let mut number_covers_unreachable = 0;
    let mut number_covers_unsatisfiable = 0;

    let mut index = 1;

    if show_checks {
        result_str.push_str("\nRESULTS:\n");
    }

    for prop in properties {
        let name = prop.property_name();
        let status = &prop.status;
        let description = &prop.description;
        let location = &prop.source_location;

        match status {
            CheckStatus::Failure => {
                number_checks_failed += 1;
                failed_tests.push(prop);
            }
            CheckStatus::Undetermined => {
                if prop.is_cover_property() {
                    number_covers_undetermined += 1;
                } else {
                    number_checks_undetermined += 1;
                }
            }
            CheckStatus::Unreachable => {
                if prop.is_cover_property() {
                    number_covers_unreachable += 1;
                } else {
                    number_checks_unreachable += 1;
                }
            }
            CheckStatus::Satisfied => {
                assert!(prop.is_cover_property());
                number_covers_satisfied += 1;
            }
            CheckStatus::Unsatisfiable => {
                assert!(prop.is_cover_property());
                number_covers_unsatisfiable += 1;
            }
            // These statuses require no summary counting:
            // - Success: normal passing check (counted implicitly as total - failures - other)
            // - Covered/Uncovered: code_coverage counted separately
            // - Unknown: inconclusive due to other UB failures
            CheckStatus::Success
            | CheckStatus::Covered
            | CheckStatus::Uncovered
            | CheckStatus::Unknown => (),
        }

        if show_checks {
            let _ = writeln!(result_str, "Check {index}: {name}");
            let _ = writeln!(result_str, "\t - Status: {status}");
            let _ = writeln!(result_str, "\t - Description: \"{description}\"");

            if !location.is_missing() {
                let _ = writeln!(result_str, "\t - Location: {location}");
            }
            result_str.push('\n');
        }

        index += 1;
    }

    if show_checks {
        result_str.push_str("\nSUMMARY:");
    } else {
        result_str.push_str("\nVERIFICATION RESULT:");
    }

    let number_cover_properties = number_covers_satisfied
        + number_covers_unreachable
        + number_covers_unsatisfiable
        + number_covers_undetermined;

    let number_properties = properties.len() - number_cover_properties;

    let _ = write!(result_str, "\n ** {number_checks_failed} of {number_properties} failed");

    let mut other_status = Vec::<String>::new();
    if number_checks_undetermined > 0 {
        let undetermined_str = format!("{number_checks_undetermined} undetermined");
        other_status.push(undetermined_str);
    }
    if number_checks_unreachable > 0 {
        let unreachable_str = format!("{number_checks_unreachable} unreachable");
        other_status.push(unreachable_str);
    }
    if !other_status.is_empty() {
        result_str.push_str(" (");
        result_str.push_str(&other_status.join(","));
        result_str.push(')');
    }
    result_str.push('\n');

    if number_cover_properties > 0 {
        let _ = write!(
            result_str,
            "\n ** {number_covers_satisfied} of {number_cover_properties} cover properties satisfied"
        );
        let mut other_status = Vec::<String>::new();
        if number_covers_undetermined > 0 {
            let undetermined_str = format!("{number_covers_undetermined} undetermined");
            other_status.push(undetermined_str);
        }
        if number_covers_unreachable > 0 {
            let unreachable_str = format!("{number_covers_unreachable} unreachable");
            other_status.push(unreachable_str);
        }
        if !other_status.is_empty() {
            result_str.push_str(" (");
            result_str.push_str(&other_status.join(","));
            result_str.push(')');
        }
        result_str.push('\n');
        result_str.push('\n');
    }

    for prop in failed_tests {
        let failure_message = build_failure_message(&prop.description, &prop.trace);
        result_str.push_str(&failure_message);
    }

    let effective_success = is_effective_manual_success(status, should_panic, failed_properties);
    let verification_result = if effective_success
        && validation_status == ValidationStatus::Unvalidated
    {
        style("SUCCESSFUL (UNVALIDATED)").yellow()
    } else if effective_success {
        style("SUCCESSFUL").green()
    } else if !should_panic && is_unsat_assumption_vacuous(properties) {
        // V4 vacuity gate: the harness_runner flipped this to Failure because every
        // check is provably unreachable (unsatisfiable assumptions). Report it as
        // VACUOUS, not FAILED — nothing was actually disproved; nothing was proved.
        style("VACUOUS (proof discharged under unsatisfiable assumptions — nothing verified)").red()
    } else if number_properties == 0 {
        // #4216: A proof with 0 checks (no assertions to verify) is inconclusive,
        // not failed — there is nothing to disprove.
        style("INCONCLUSIVE (no checks)").yellow()
    } else if validation_status == ValidationStatus::Unvalidated {
        style("UNVALIDATED (DT+BV)").yellow()
    } else {
        style("FAILED").red()
    };
    let should_panic_info = if should_panic {
        match failed_properties {
            FailedProperties::None => " (encountered no panics, but at least one was expected)",
            FailedProperties::PanicsOnly => " (encountered one or more panics as expected)",
            FailedProperties::Other => {
                " (encountered failures other than panics, which were unexpected)"
            }
        }
    } else {
        ""
    };
    let _ = write!(result_str, "\nVERIFICATION:- {verification_result}{should_panic_info}\n");
    if let Some(reason) = effective_success_reason(status, should_panic, failed_properties)
        && env::var_os(EFFECTIVE_SUCCESS_MARKER_ENV).is_some()
    {
        let _ = writeln!(result_str, "[AY:EFFECTIVE_SUCCESS:{reason}]");
    }

    if has_check_failure(properties, UNSUPPORTED_CONSTRUCT_DESC) {
        result_str.push_str(
            "** WARNING: A Rust construct that is not currently supported \
        by trust-mc was found to be reachable. Check the results for \
        more details.\n",
        );
    }
    if has_unwinding_assertion_failures(properties) {
        result_str.push_str("[trust_mc] info: Verification output shows one or more unwinding failures.\n\
        [trust_mc] tip: Consider increasing the unwinding value or disabling `--unwinding-assertions`.\n");
    }

    result_str
}

pub(crate) fn effective_success_reason(
    status: VerificationStatus,
    should_panic: bool,
    failed_properties: FailedProperties,
) -> Option<&'static str> {
    if status != VerificationStatus::Success
        && should_panic
        && matches!(failed_properties, FailedProperties::PanicsOnly)
    {
        Some(SHOULD_PANIC_PANICS_ONLY_EFFECTIVE_SUCCESS)
    } else {
        None
    }
}

/// Separate checks into coverage and non-coverage based on property class and
/// format them separately for `--coverage`.
pub(crate) fn format_coverage(
    properties: &[Property],
    cov_results: &CoverageResults,
    status: VerificationStatus,
    should_panic: bool,
    failed_properties: FailedProperties,
    show_checks: bool,
    validation_status: ValidationStatus,
) -> String {
    let (_coverage_checks, non_coverage_checks): (Vec<Property>, Vec<Property>) =
        properties.iter().cloned().partition(|x| x.property_class() == "code_coverage");

    let verification_output = format_result(
        &non_coverage_checks,
        status,
        should_panic,
        failed_properties,
        show_checks,
        validation_status,
    );
    let cov_results_intro = "Source-based code coverage results:";
    format!("{verification_output}\n{cov_results_intro}\n\n{cov_results}")
}
#[cfg(test)]
#[path = "verification_result_tests.rs"]
mod tests;

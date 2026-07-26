// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for verification_result verdict rendering (#3709).

use super::*;
use crate::property_model::{PropertyId, RawSourceLocation};
use std::borrow::Cow;

fn make_property(status: CheckStatus) -> Property {
    Property {
        description: Cow::Borrowed("test assertion"),
        property_id: PropertyId {
            fn_name: Some("test_fn".to_string()),
            class: Cow::Borrowed("assertion"),
            id: 1,
        },
        source_location: RawSourceLocation { column: None, file: None, function: None, line: None },
        status,
        trace: None,
    }
}

#[test]
fn test_render_nia_success_shows_unvalidated() {
    let output = format_result(
        &[make_property(CheckStatus::Success)],
        VerificationStatus::Success,
        false,
        FailedProperties::None,
        true,
        ValidationStatus::Unvalidated,
    );
    assert!(
        output.contains("SUCCESSFUL (UNVALIDATED)"),
        "NIA PROOF should show SUCCESSFUL (UNVALIDATED), got: {output}"
    );
    assert!(
        !output.contains("VERIFICATION:- SUCCESSFUL\n"),
        "NIA PROOF must not show bare SUCCESSFUL without qualification"
    );
}

#[test]
fn test_render_validated_success_shows_successful() {
    let output = format_result(
        &[make_property(CheckStatus::Success)],
        VerificationStatus::Success,
        false,
        FailedProperties::None,
        true,
        ValidationStatus::Validated,
    );
    assert!(output.contains("SUCCESSFUL"), "Validated PROOF should show SUCCESSFUL, got: {output}");
    assert!(!output.contains("UNVALIDATED"), "Validated PROOF must not show UNVALIDATED");
}

#[test]
fn test_render_nia_failure_shows_failed_not_unvalidated() {
    let output = format_result(
        &[make_property(CheckStatus::Failure)],
        VerificationStatus::Failure,
        false,
        FailedProperties::Other,
        true,
        ValidationStatus::Unvalidated,
    );
    assert!(
        output.contains("UNVALIDATED (DT+BV)"),
        "NIA failure should show UNVALIDATED (DT+BV), got: {output}"
    );
}

#[test]
fn test_render_validated_failure_shows_failed() {
    let output = format_result(
        &[make_property(CheckStatus::Failure)],
        VerificationStatus::Failure,
        false,
        FailedProperties::Other,
        true,
        ValidationStatus::Validated,
    );
    assert!(output.contains("FAILED"), "Validated failure should show FAILED, got: {output}");
    assert!(!output.contains("UNVALIDATED"), "Validated failure must not show UNVALIDATED");
}

#[test]
fn test_render_should_panic_panics_only_shows_successful() {
    let output = format_result(
        &[make_property(CheckStatus::Failure)],
        VerificationStatus::Failure,
        true,
        FailedProperties::PanicsOnly,
        true,
        ValidationStatus::Validated,
    );
    assert!(
        output.contains("VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)"),
        "should_panic panics-only result should render as effective success, got: {output}"
    );
    assert!(
        !output.contains("VERIFICATION:- FAILED"),
        "effective success must not render as FAILED"
    );
}

#[test]
fn test_effective_success_reason_is_stable_for_should_panic_panics_only() {
    assert_eq!(
        effective_success_reason(VerificationStatus::Failure, true, FailedProperties::PanicsOnly,),
        Some("should_panic_panics_only")
    );
    assert_eq!(
        effective_success_reason(VerificationStatus::Success, true, FailedProperties::None),
        None
    );
}

#[test]
fn test_logic_tier_validation_status_helper() {
    assert_eq!(LogicTier::TierA.validation_status(), ValidationStatus::Validated);
    assert_eq!(LogicTier::TierB.validation_status(), ValidationStatus::Unvalidated);
}

#[test]
fn test_solver_unknown_reason_labels_are_stable() {
    assert_eq!(SolverUnknownReason::Timeout.label(), "Timeout");
    assert_eq!(SolverUnknownReason::SolverError.label(), "SolverError");
}

#[test]
fn test_proof_crosscheck_labels_are_stable() {
    assert_eq!(ProofCrosscheck::NotRun.label(), None);
}

#[test]
fn test_render_zero_checks_shows_inconclusive() {
    // #4216: 0-of-0 checks should be INCONCLUSIVE, not FAILED.
    let output = format_result(
        &[],
        VerificationStatus::Failure,
        false,
        FailedProperties::Other,
        true,
        ValidationStatus::Validated,
    );
    assert!(
        output.contains("INCONCLUSIVE (no checks)"),
        "0-of-0 checks should show INCONCLUSIVE, got: {output}"
    );
    assert!(!output.contains("VERIFICATION:- FAILED"), "0-of-0 checks must not show FAILED");
    assert!(output.contains("0 of 0 failed"), "summary should show 0 of 0 failed, got: {output}");
}

#[test]
fn test_render_zero_checks_success_still_shows_successful() {
    // When status is Success with 0 properties, it should remain SUCCESSFUL.
    let output = format_result(
        &[],
        VerificationStatus::Success,
        false,
        FailedProperties::None,
        true,
        ValidationStatus::Validated,
    );
    assert!(
        output.contains("SUCCESSFUL"),
        "0 checks with Success status should still show SUCCESSFUL, got: {output}"
    );
    assert!(!output.contains("INCONCLUSIVE"), "Success status should not show INCONCLUSIVE");
}

#[test]
fn test_render_success_omits_kani_mem_overapprox_proof_note() {
    let mut result =
        crate::test_support::test_result(VerificationStatus::Success, FailedProperties::None);
    result.results.push(make_property(CheckStatus::Success));
    result.kani_mem_overapprox_count = 1;

    let output = result.render(&crate::args::OutputFormat::Regular, false);

    assert!(output.contains("SUCCESSFUL"), "success status should still render, got: {output}");
    assert!(
        !output.contains("memory safety check(s) over-approximated as true"),
        "kani_mem_overapprox is a demoting category, not a success proof note: {output}"
    );
}

// --- Vacuity gate (V4 unsat-assumption / V5 unsatisfiable-cover) ----------------

/// A `cover`-class property, with the given status (Satisfied / Unsatisfiable / ...).
fn make_cover(status: CheckStatus) -> Property {
    Property {
        description: Cow::Borrowed("test cover"),
        property_id: PropertyId {
            fn_name: Some("test_fn".to_string()),
            class: Cow::Borrowed("cover"),
            id: 1,
        },
        source_location: RawSourceLocation { column: None, file: None, function: None, line: None },
        status,
        trace: None,
    }
}

#[test]
fn v4_all_checks_unreachable_is_vacuous() {
    let props = [make_property(CheckStatus::Unreachable), make_property(CheckStatus::Unreachable)];
    assert!(
        is_unsat_assumption_vacuous(&props),
        "every non-cover check unreachable ⇒ unsatisfiable-assumption vacuity"
    );
}

#[test]
fn v4_one_reachable_success_is_not_vacuous() {
    // A single genuinely-verified (reachable) check breaks the all-unreachable signature.
    let props = [make_property(CheckStatus::Unreachable), make_property(CheckStatus::Success)];
    assert!(!is_unsat_assumption_vacuous(&props), "a reachable Success check ⇒ not vacuous");
}

#[test]
fn v4_undetermined_is_not_vacuous() {
    // A solver timeout (Undetermined) is inconclusive, NOT a proof of unreachability —
    // it must not be misread as vacuous (no false positives on flaky/slow runs).
    let props = [make_property(CheckStatus::Unreachable), make_property(CheckStatus::Undetermined)];
    assert!(!is_unsat_assumption_vacuous(&props), "an Undetermined check ⇒ not vacuous");
}

#[test]
fn v4_failure_is_not_vacuous() {
    // A genuine counterexample (Failure-status check) is a real defect, never vacuity.
    let props = [make_property(CheckStatus::Unreachable), make_property(CheckStatus::Failure)];
    assert!(!is_unsat_assumption_vacuous(&props), "a Failure check ⇒ real failure, not vacuous");
}

#[test]
fn v4_no_checks_is_not_vacuous() {
    // 0 non-cover checks is the INCONCLUSIVE(no checks) case, handled separately.
    assert!(!is_unsat_assumption_vacuous(&[]), "no checks ⇒ not the vacuity case");
    assert!(
        !is_unsat_assumption_vacuous(&[make_cover(CheckStatus::Satisfied)]),
        "cover-only harness ⇒ not the unsat-assumption vacuity case"
    );
}

#[test]
fn v4_renders_vacuous_not_failed() {
    // status==Failure (flipped by the gate) + all-unreachable + !should_panic ⇒ VACUOUS.
    let output = format_result(
        &[make_property(CheckStatus::Unreachable)],
        VerificationStatus::Failure,
        false,
        FailedProperties::Other,
        true,
        ValidationStatus::Validated,
    );
    assert!(output.contains("VACUOUS"), "all-unreachable Failure should render VACUOUS: {output}");
    assert!(!output.contains("FAILED"), "vacuous should not render as a plain FAILED: {output}");
}

#[test]
fn v4_should_panic_is_exempt_from_vacuous_label() {
    // should_panic harnesses are exempt — they must not be relabeled VACUOUS.
    let output = format_result(
        &[make_property(CheckStatus::Unreachable)],
        VerificationStatus::Failure,
        true, // should_panic
        FailedProperties::None,
        true,
        ValidationStatus::Validated,
    );
    assert!(!output.contains("VACUOUS"), "should_panic is exempt from the V4 label: {output}");
}

#[test]
fn v5_unsatisfiable_cover_detected_satisfied_is_not() {
    assert!(
        has_unsatisfiable_cover(&[make_cover(CheckStatus::Unsatisfiable)]),
        "a provably-unsatisfiable cover is a vacuous witness"
    );
    assert!(
        has_unsatisfiable_cover(&[make_cover(CheckStatus::Unreachable)]),
        "a provably-unreachable cover is a vacuous witness"
    );
    assert!(
        !has_unsatisfiable_cover(&[make_cover(CheckStatus::Satisfied)]),
        "a satisfied cover is a real witness, not vacuous"
    );
    assert!(
        !has_unsatisfiable_cover(&[make_cover(CheckStatus::Undetermined)]),
        "an undetermined cover is a timeout, not a definitive vacuous witness"
    );
}

#[test]
fn v5_conformance_requires_a_satisfied_cover() {
    // The conformance tier (V5 manifest): a conformance harness must reach ≥1 SATISFIED
    // cover, else its claim is vacuous. `has_satisfied_cover` is the witness predicate.
    assert!(
        has_satisfied_cover(&[make_cover(CheckStatus::Satisfied)]),
        "a satisfied cover IS the conformance witness"
    );
    assert!(
        !has_satisfied_cover(&[make_cover(CheckStatus::Unsatisfiable)]),
        "an unsatisfiable cover is not a witness ⇒ conformance claim vacuous"
    );
    assert!(
        !has_satisfied_cover(&[make_cover(CheckStatus::Undetermined)]),
        "an undetermined cover is not a definitive witness"
    );
    assert!(
        !has_satisfied_cover(&[make_property(CheckStatus::Success)]),
        "a passing non-cover check is not a cover witness ⇒ conformance claim vacuous"
    );
    assert!(!has_satisfied_cover(&[]), "no covers at all ⇒ conformance claim vacuous");
}

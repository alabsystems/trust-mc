// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for direct AY solver integration (Phase 1: SMT-LIB text path).

use super::*;

#[test]
fn test_parse_simple_smt2() {
    let content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let commands = parse_smt2_content(content).unwrap();
    assert_eq!(commands.len(), 4);
}

#[test]
fn test_direct_solver_sat() {
    let content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let (status, _, _) = run_ay_direct(content, false).unwrap();
    assert_eq!(status, VerificationStatus::Failure); // SAT = counterexample exists
}

#[test]
fn test_direct_solver_unsat() {
    let content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
"#;
    let (status, _, _) = run_ay_direct(content, false).unwrap();
    assert_eq!(status, VerificationStatus::Success); // UNSAT = no counterexample
}

#[test]
fn test_violation_name_to_description() {
    assert_eq!(violation_name_to_description("ay_violation_kani_assert_0"), "kani assert 0");
    assert_eq!(
        violation_name_to_description("ay_violation_overflow_check_add_1"),
        "overflow check add 1"
    );
}

#[test]
fn test_violation_tracking() {
    // Verify that violation variables are properly tracked
    let content = r#"
(set-logic QF_LIA)
(declare-const ay_violation_test_0 Bool)
(declare-const ay_violation_test_1 Bool)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let (_, _, properties) = run_ay_direct(content, false).unwrap();
    assert_eq!(properties.len(), 2);
    assert_eq!(properties[0].description, "test 0");
    assert_eq!(properties[1].description, "test 1");
}

#[test]
fn test_no_violations() {
    // Verify behavior when no violation variables are declared
    let content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(check-sat)
"#;
    let (_, _, properties) = run_ay_direct(content, false).unwrap();
    assert_eq!(properties.len(), 0);
}

/// DISCRIMINATING: #2660 — dropped SMT assert commands must demote Success to Failure.
/// Reverting the demotion fix would turn this into a false positive.
///
/// Without the fix, a dropped assert weakens the constraint set, making UNSAT
/// easier to achieve — a direct false-positive vector. The fix tracks failed
/// assert commands and demotes any Success result to Failure.
///
/// The test is designed so that when the failing assert is dropped, the remaining
/// constraints are contradictory (UNSAT → Success). Without the demotion fix,
/// this would be a false positive. The fix demotes to Failure.
#[test]
fn test_failed_assert_demotes_result() {
    // Construct a problem where:
    //   1. One assert uses an undeclared function → will error (be dropped)
    //   2. The remaining asserts are contradictory (x > 0 AND x < 0) → UNSAT
    //
    // Without fix: dropped assert + remaining UNSAT → Success (FALSE POSITIVE)
    // With fix: failed assert count > 0 → demote Success to Failure
    let content = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (undeclared_function x))
(assert (> x 0))
(assert (< x 0))
(check-sat)
"#;
    let (status, _, _) = run_ay_direct(content, false).unwrap();
    // Without the demotion fix, check-sat returns UNSAT (remaining asserts
    // contradict) → Success. The fix detects the failed assert and demotes.
    assert_eq!(
        status,
        VerificationStatus::Failure,
        "Result must be Failure when an assert command failed — \
         dropped asserts weaken the problem and can cause false proofs"
    );
}

#[test]
fn test_summarize_command_indices_empty() {
    assert_eq!(summarize_command_indices(&[], 8), "none");
}

#[test]
fn test_summarize_command_indices_truncated() {
    let indices = [1, 3, 5, 7, 9];
    assert_eq!(summarize_command_indices(&indices, 3), "1, 3, 5, ... (+2 more)");
}

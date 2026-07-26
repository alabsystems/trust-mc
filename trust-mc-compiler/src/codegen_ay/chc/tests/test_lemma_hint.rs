// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR-backed production-path tests for `lemma_hint.rs`.
//!
//! Covers the two observable side effects of `emit_loop_invariant_lemmas()`:
//! 1. Auxiliary `... -> error` rule emission (loop invariant hints)
//! 2. Registry publication via `register_loop_invariants()` for PDR pipeline
//!
//! Part of #3644: MIR-backed coverage for loop guidance postpasses.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::ExprValue;

// =============================================================================
// Source code fixtures (unique names per D5 to avoid registry bleed-through)
// =============================================================================

/// Forward accumulator: `sum += counter; counter += 1; while counter < n`.
const FORWARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_lemma_forward(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut counter: u32 = 0;
        while counter < n {
            sum += counter;
            counter += 1;
        }
        sum
    }
"#;

/// Countdown accumulator: `sum += n; counter -= 1; while counter > 0`.
/// The detector requires `sum` to be incremented by a loop-INVARIANT variable
/// (`n`, which is not modified in the loop body), and `counter` to be
/// decremented by a constant.
const COUNTDOWN_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_lemma_countdown(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut counter: u32 = n;
        while counter > 0 {
            sum += n;
            counter -= 1;
        }
        sum
    }
"#;

/// No loop — lemma hint should be a no-op.
const NO_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_lemma_noop(x: u32) -> u32 {
        x + 1
    }
"#;

// =============================================================================
// Helper functions
// =============================================================================

/// Generate a VC with int_lift enabled, stopping before TIC.
///
/// Reuses the same pipeline boundary as `test_lemma_linearize.rs`:
/// runs `emit_loop_invariant_lemmas` + `apply_linearization` but NOT TIC.
fn vc_with_int_lift(source: &str, fn_name: &str) -> trust_mc_core::chc::ChcVc {
    let mut result = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_skip_tic(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
        result = Some(vc);
    });
    result.expect("vc should be produced")
}

/// Count error-headed rules that have a body relation (non-init error rules).
fn count_error_rules_with_body(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules.iter().filter(|r| r.head.name == "error" && r.body.relation.is_some()).count()
}

/// Count error-headed rules whose body constraints contain IntMul.
/// IntMul is the unique signature of lemma hint error rules — they inject
/// nonlinear terms (counter*counter, counter*n, n*n) that normal overflow
/// checks and assertion error rules do not produce.
fn count_lemma_error_rules(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules
        .iter()
        .filter(|r| {
            r.head.name == "error"
                && r.body.relation.is_some()
                && r.body.constraints.iter().any(|c| {
                    constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::IntMul(_, _)))
                })
        })
        .count()
}

// =============================================================================
// Tests: Forward accumulator
// =============================================================================

#[test]
fn test_lemma_hint_forward_emits_error_rules() {
    let vc = vc_with_int_lift(FORWARD_SOURCE, "probe_lemma_forward");

    // Forward accumulator should emit at least one auxiliary error rule
    // containing Int comparisons (invariant violation checks).
    let lemma_errors = count_lemma_error_rules(&vc);
    assert!(
        lemma_errors > 0,
        "forward accumulator should emit at least one lemma hint error rule, got 0. \
         Total error rules with body: {}",
        count_error_rules_with_body(&vc)
    );
}

#[test]
fn test_lemma_hint_forward_registers_invariants() {
    let vc = vc_with_int_lift(FORWARD_SOURCE, "probe_lemma_forward");

    // Verify the VC was produced (sanity)
    assert!(!vc.rules.is_empty(), "VC should have rules");

    // The registry should contain invariants for this function.
    let invariants =
        crate::kani_middle::transform::loop_contracts::get_loop_invariants("probe_lemma_forward");
    assert!(
        invariants.is_some(),
        "get_loop_invariants('probe_lemma_forward') should return Some(...) after \
         emit_loop_invariant_lemmas ran on a forward accumulator"
    );
    let invariants = invariants.unwrap();
    assert!(
        !invariants.is_empty(),
        "forward accumulator should register at least one extracted loop invariant"
    );
}

#[test]
fn test_lemma_hint_forward_invariant_contains_int_mul() {
    let vc = vc_with_int_lift(FORWARD_SOURCE, "probe_lemma_forward");
    assert!(!vc.rules.is_empty());

    // The forward accumulator invariant includes `counter*counter` (triangular sum).
    // Check that at least one lemma error rule contains IntMul.
    let has_int_mul = vc.rules.iter().any(|r| {
        r.head.name == "error"
            && r.body.relation.is_some()
            && r.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::IntMul(_, _)))
            })
    });
    assert!(
        has_int_mul,
        "forward accumulator lemma error rules should contain IntMul for the \
         triangular invariant (2*sum + counter = counter*counter)"
    );
}

// =============================================================================
// Tests: Countdown accumulator
// =============================================================================

#[test]
fn test_lemma_hint_countdown_emits_error_rules() {
    let vc = vc_with_int_lift(COUNTDOWN_SOURCE, "probe_lemma_countdown");

    let lemma_errors = count_lemma_error_rules(&vc);
    assert!(
        lemma_errors > 0,
        "countdown accumulator should emit at least one lemma hint error rule, got 0. \
         Total error rules with body: {}",
        count_error_rules_with_body(&vc)
    );
}

#[test]
fn test_lemma_hint_countdown_registers_invariants() {
    let vc = vc_with_int_lift(COUNTDOWN_SOURCE, "probe_lemma_countdown");
    assert!(!vc.rules.is_empty());

    let invariants =
        crate::kani_middle::transform::loop_contracts::get_loop_invariants("probe_lemma_countdown");
    assert!(
        invariants.is_some(),
        "get_loop_invariants('probe_lemma_countdown') should return Some(...) after \
         emit_loop_invariant_lemmas ran on a countdown accumulator"
    );
    let invariants = invariants.unwrap();
    assert!(
        !invariants.is_empty(),
        "countdown accumulator should register at least one extracted loop invariant"
    );
}

// =============================================================================
// Tests: Negative case (no-op)
// =============================================================================

#[test]
fn test_lemma_hint_noop_no_extra_error_rules() {
    let vc = vc_with_int_lift(NO_LOOP_SOURCE, "probe_lemma_noop");

    // No loop → no lemma error rules
    let lemma_errors = count_lemma_error_rules(&vc);
    assert_eq!(lemma_errors, 0, "function without a loop should not emit lemma hint error rules");
}

#[test]
fn test_lemma_hint_noop_no_registry() {
    let _ = vc_with_int_lift(NO_LOOP_SOURCE, "probe_lemma_noop");

    let invariants =
        crate::kani_middle::transform::loop_contracts::get_loop_invariants("probe_lemma_noop");
    assert!(
        invariants.is_none(),
        "get_loop_invariants('probe_lemma_noop') should return None for a non-loop function"
    );
}

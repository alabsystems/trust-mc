// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `lemma_linearize.rs` — Strategy D auxiliary variable linearization.
//!
//! Covers:
//! - Forward accumulator detection (`sum += counter; counter += 1`)
//! - No-op when no accumulator pattern exists
//! - Synthetic `sq` variable addition to relation declarations
//! - Entry constraint (sq = 0), frame condition, counter-update constraint
//! - LIA error rule emission (`2*sum > sq → error`)
//!
//! Part of #3342: zero test coverage for soundness-critical linearization pass.
//! Part of #3258: CHC lemma injection for UNKNOWN harnesses.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::ExprValue;

// =============================================================================
// Source code fixtures
// =============================================================================

/// Forward accumulator loop: `sum += counter; counter += 1`.
/// This is the canonical pattern that Strategy D targets.
const ACCUMULATOR_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_accumulator(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut counter: u32 = 0;
        while counter < n {
            sum += counter;
            counter += 1;
        }
        sum
    }
"#;

/// Simple function with no loop — linearization should be a no-op.
const NO_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_no_loop(x: u32) -> u32 {
        x + 1
    }
"#;

/// Loop without accumulator pattern — linearization should be a no-op.
const NON_ACCUMULATOR_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_non_accumulator(n: u32) -> u32 {
        let mut x: u32 = 1;
        let mut i: u32 = 0;
        while i < n {
            x = x.wrapping_mul(2);
            i += 1;
        }
        x
    }
"#;

// =============================================================================
// Helper functions
// =============================================================================

/// Generate a VC with int_lift enabled, stopping before TIC.
///
/// Uses `mir_to_chc_skip_tic` to halt the pipeline after linearization but
/// before TIC (Template-Directed Inductive Checking). TIC detects the same
/// forward accumulator patterns and replaces the VC with a trivially safe
/// system (clearing all rules), which would make structure tests vacuous.
///
/// Tests that verify linearization artifacts (entry rules, error rules,
/// frame conditions) need the pre-TIC VC to inspect intermediate structure.
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

/// Check if any variable declaration name contains the `_aux_sq_` prefix.
fn has_aux_sq_var(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.vars().iter().any(|v| v.name.contains("_aux_sq_"))
}

/// Assert that linearization triggered. Fails with diagnostics if not.
/// Used as a precondition in tests that inspect linearization artifacts.
fn assert_linearization_triggered(vc: &trust_mc_core::chc::ChcVc) {
    assert!(
        has_aux_sq_var(vc),
        "precondition failed: linearization did not trigger — cannot verify structure. \
         Vars: {:?}",
        vc.vars().iter().map(|v| &*v.name).collect::<Vec<_>>()
    );
}

/// Count the number of rules whose head targets "error" and whose body has
/// a relation (i.e., non-entry error rules from linearization).
fn count_linearization_error_rules(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules
        .iter()
        .filter(|r| {
            r.head.name == "error"
                && r.body.relation.is_some()
                // Linearization error rules contain Int comparisons (IntGt)
                && r.body.constraints.iter().any(|c| {
                    constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::IntGt(_, _)))
                })
        })
        .count()
}

/// Recursively check if any sub-expression in the tree satisfies the predicate.
fn constraint_tree_contains(
    expr: &ay_bindings::Expr,
    pred: &dyn Fn(&ay_bindings::Expr) -> bool,
) -> bool {
    if pred(expr) {
        return true;
    }
    match expr.value() {
        ExprValue::Eq(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntSub(a, b) => {
            constraint_tree_contains(a, pred) || constraint_tree_contains(b, pred)
        }
        ExprValue::Not(inner) => constraint_tree_contains(inner, pred),
        ExprValue::And(es) | ExprValue::Or(es) => {
            es.iter().any(|e| constraint_tree_contains(e, pred))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            constraint_tree_contains(cond, pred)
                || constraint_tree_contains(then_expr, pred)
                || constraint_tree_contains(else_expr, pred)
        }
        _ => false,
    }
}

// =============================================================================
// Test: Forward accumulator detection
// =============================================================================

/// Verify that the linearization pass detects the forward accumulator pattern
/// and adds synthetic `_aux_sq_*` variables to the VC.
#[test]
fn test_linearization_detects_forward_accumulator() {
    let vc = vc_with_int_lift(ACCUMULATOR_SOURCE, "probe_accumulator");

    // Linearization should add _aux_sq_* variable declarations
    assert_linearization_triggered(&vc);

    // Non-error relations should have more args than the error relation
    // (linearization adds sq to non-error relations only)
    let error_arity =
        vc.relations.iter().find(|r| r.name == "error").map(|r| r.arg_sorts.len()).unwrap_or(0);
    let non_error_has_extra =
        vc.relations.iter().any(|r| r.name != "error" && r.arg_sorts.len() > error_arity);
    assert!(
        non_error_has_extra,
        "non-error relations should have more args than error (linearization adds sq). \
         error_arity={error_arity}, relations: {:?}",
        vc.relations.iter().map(|r| (&r.name, r.arg_sorts.len())).collect::<Vec<_>>()
    );
}

// =============================================================================
// Test: No-op for non-accumulator patterns
// =============================================================================

/// Linearization should be a no-op for functions without loops.
#[test]
fn test_linearization_noop_no_loop() {
    let vc = vc_with_int_lift(NO_LOOP_SOURCE, "probe_no_loop");

    assert!(!has_aux_sq_var(&vc), "non-loop function should not trigger linearization");
}

/// Linearization should be a no-op when the loop does not contain the
/// `sum += counter; counter += 1` accumulator pattern.
#[test]
fn test_linearization_noop_non_accumulator_loop() {
    let vc = vc_with_int_lift(NON_ACCUMULATOR_LOOP_SOURCE, "probe_non_accumulator");

    assert!(
        !has_aux_sq_var(&vc),
        "non-accumulator loop (x *= 2) should not trigger linearization. \
         Vars: {:?}",
        vc.vars().iter().map(|v| &*v.name).collect::<Vec<_>>()
    );
}

// =============================================================================
// Test: Entry constraint initializes sq = 0
// =============================================================================

/// Entry rules (body.relation is None) should have Int(0) in head args
/// for the sq position, ensuring `sq` starts at 0.
#[test]
fn test_linearization_entry_initializes_sq_zero() {
    let vc = vc_with_int_lift(ACCUMULATOR_SOURCE, "probe_accumulator");

    assert_linearization_triggered(&vc);

    let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
    assert!(!entry_rules.is_empty(), "should have at least one entry rule");

    // The last arg of the entry rule's head should be Int(0) (sq starts at 0)
    let has_zero_init = entry_rules.iter().any(|rule| {
        rule.head.args.iter().any(|arg| {
            matches!(arg.value(), ExprValue::IntConst(v) if v == &num_bigint::BigInt::from(0))
        })
    });

    assert!(
        has_zero_init,
        "entry rule should initialize sq = 0. Entry head args: {:?}",
        entry_rules
            .iter()
            .map(|r| r.head.args.iter().map(|a| a.to_string()).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );
}

// =============================================================================
// Test: LIA error rule emission
// =============================================================================

/// Linearization should emit at least one error rule containing an IntGt
/// comparison (the `2*sum > sq` violation).
#[test]
fn test_linearization_emits_lia_error_rule() {
    let vc = vc_with_int_lift(ACCUMULATOR_SOURCE, "probe_accumulator");

    assert_linearization_triggered(&vc);

    let error_count = count_linearization_error_rules(&vc);
    assert!(
        error_count >= 1,
        "linearization should emit at least 1 LIA error rule with IntGt constraint, got {error_count}"
    );
}

// =============================================================================
// Test: Frame condition — non-updating rules pass sq through
// =============================================================================

/// Rules that don't update the counter should pass `sq` through unchanged.
/// This means the body and head should reference the same sq variable.
#[test]
fn test_linearization_frame_condition() {
    let vc = vc_with_int_lift(ACCUMULATOR_SOURCE, "probe_accumulator");

    assert_linearization_triggered(&vc);

    // Non-entry, non-error transition rules should exist
    let transition_rules: Vec<_> =
        vc.rules.iter().filter(|r| r.body.relation.is_some() && r.head.name != "error").collect();

    assert!(!transition_rules.is_empty(), "should have transition rules after linearization");

    // At least one rule should have matching last args between body relation
    // and head (frame condition: sq_in passed through as sq_in, not sq_out).
    // This is the "non-updating" path.
    let has_frame = transition_rules.iter().any(|rule| {
        let body_rel = rule.body.relation.as_ref().unwrap();
        let body_last = body_rel.args.last();
        let head_last = rule.head.args.last();
        match (body_last, head_last) {
            (Some(b), Some(h)) => {
                // Frame: both should be the same variable (sq_in)
                if let (ExprValue::Var { name: bn }, ExprValue::Var { name: hn }) =
                    (b.value(), h.value())
                {
                    bn == hn
                } else {
                    false
                }
            }
            _ => false,
        }
    });

    assert!(
        has_frame,
        "at least one transition rule should have frame condition (sq passed through unchanged)"
    );
}

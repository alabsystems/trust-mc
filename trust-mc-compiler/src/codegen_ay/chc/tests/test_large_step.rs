// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `ChcStepMode::Large` — fragment-based CHC encoding (#112 Step 6).
//!
//! Validates that Large-mode produces fewer predicates than Small-mode while
//! maintaining VC structural integrity (entry rule, error relation, rule heads
//! reference declared relations).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// Assert basic VC integrity for Large mode.
///
/// Large mode may have fewer relations than Small mode, but must still have:
/// - An error relation
/// - A bb0 relation (entry point)
/// - An entry rule (body.relation is None, head targets bb0)
/// - All rule heads reference declared relations
fn assert_large_vc_integrity(vc: &trust_mc_core::chc::ChcVc, fn_name: &str) {
    let has_error = vc.relations.iter().any(|r| r.name == "error");
    assert!(has_error, "{fn_name} Large: missing 'error' relation");

    let has_bb0 = vc.relations.iter().any(|r| r.name.contains("__bb0"));
    assert!(has_bb0, "{fn_name} Large: missing bb0 relation");

    let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
    assert!(!entry_rules.is_empty(), "{fn_name} Large: no entry (init) rule found");
    assert!(
        entry_rules[0].head.name.contains("__bb0"),
        "{fn_name} Large: entry rule head should target bb0, got: {}",
        entry_rules[0].head.name
    );

    let declared: std::collections::HashSet<_> =
        vc.relations.iter().map(|r| r.name.as_str()).collect();
    for rule in &vc.rules {
        assert!(
            declared.contains(rule.head.name.as_str()),
            "{fn_name} Large: rule head '{}' references undeclared relation",
            rule.head.name
        );
    }

    assert!(
        vc.rules.len() >= 2,
        "{fn_name} Large: expected >= 2 rules (entry + at least one transition), got {}",
        vc.rules.len()
    );
}

// =============================================================================
// Test: Linear function — Large mode composes straight-line blocks
// =============================================================================

#[test]
fn test_large_step_linear_function_fewer_predicates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_linear(a: u32, b: u32) -> u32 {
            let c = a.wrapping_add(b);
            let d = c.wrapping_mul(2);
            let e = d.wrapping_add(1);
            e
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_linear");
        let body = instance.body().expect("function body");

        let vc_small = mir_to_chc(ctx.tcx, &body, "probe_linear", ChcConfig::default());
        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_linear",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_linear");

        assert!(
            vc_large.relations.len() <= vc_small.relations.len(),
            "Large mode should have <= predicates: Large={}, Small={}",
            vc_large.relations.len(),
            vc_small.relations.len()
        );
    });
}

// =============================================================================
// Test: Function with branching — Large mode handles non-composable fragments
// =============================================================================

#[test]
fn test_large_step_branching_function_integrity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_branch(x: u32) -> u32 {
            if x > 10 {
                x.wrapping_mul(2)
            } else {
                x.wrapping_add(1)
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_branch");
        let body = instance.body().expect("function body");

        let vc_small = mir_to_chc(ctx.tcx, &body, "probe_branch", ChcConfig::default());
        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_branch",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_branch");

        assert!(
            vc_large.relations.len() <= vc_small.relations.len(),
            "Large mode should not produce more predicates: Large={}, Small={}",
            vc_large.relations.len(),
            vc_small.relations.len()
        );
    });
}

// =============================================================================
// Test: Simple assert — Large mode preserves error rule emission
// =============================================================================

#[test]
fn test_large_step_assert_preserves_error_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_assert(x: u32) -> u32 {
            let y = x.wrapping_add(1);
            assert!(y > 0);
            y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert");
        let body = instance.body().expect("function body");

        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_assert",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_assert");

        let error_rules: Vec<_> =
            vc_large.rules.iter().filter(|r| r.head.name == "error").collect();
        assert!(!error_rules.is_empty(), "Large mode must emit error rules for assertions");
    });
}

// =============================================================================
// Test: Predicate count comparison across modes (quantitative)
// =============================================================================

#[test]
fn test_large_step_predicate_count_reduction() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_chain(a: u32) -> u32 {
            let b = a.wrapping_add(1);
            let c = b.wrapping_add(2);
            let d = c.wrapping_add(3);
            let e = d.wrapping_add(4);
            e
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_chain");
        let body = instance.body().expect("function body");

        let vc_small = mir_to_chc(ctx.tcx, &body, "probe_chain", ChcConfig::default());
        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_chain",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_chain");

        assert!(
            vc_large.relations.len() <= vc_small.relations.len(),
            "Large mode predicate count ({}) must be <= Small mode ({})",
            vc_large.relations.len(),
            vc_small.relations.len()
        );

        assert!(
            vc_large.rules.len() <= vc_small.rules.len(),
            "Large mode rule count ({}) must be <= Small mode ({})",
            vc_large.rules.len(),
            vc_small.rules.len()
        );
    });
}

// =============================================================================
// Regression test: R1:2614 Finding 2 — composed fragment terminator dispatch
// =============================================================================

/// Regression test for R1:2614 Finding 2 (completeness bug).
///
/// When a composed fragment has blocks [B0, ..., BN] where a variable is
/// modified in B0 but read in BN's terminator, the terminator dispatch must
/// resolve the variable to its intermediate name (`__mid_bb{B0}`), not the
/// free `__out` variable. The fix moves `dispatch_block_terminator` before
/// `restore_names` and uses the last block's modified set.
///
/// This test uses a function with multiple wrapping operations followed by a
/// conditional branch, creating a pattern likely to produce composable linear
/// chains. Even when MIR collapses blocks, the test validates VC integrity.
#[test]
fn test_large_step_composed_terminator_no_free_out_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_assign_then_branch(a: u32, b: u32) -> u32 {
            let x = a.wrapping_add(b);
            let y = x.wrapping_mul(3);
            let z = y.wrapping_sub(1);
            if z > 100 {
                x.wrapping_add(z)
            } else {
                y
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assign_then_branch");
        let body = instance.body().expect("function body");

        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_assign_then_branch",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_assign_then_branch");

        // If composition occurred, intermediate variables should be declared.
        // If MIR collapsed everything into one block, this check is vacuously
        // true but the VC integrity check above still validates the output.
        let mid_vars: Vec<_> =
            vc_large.vars().iter().filter(|v| v.name.contains("__mid_bb")).collect();

        if !mid_vars.is_empty() {
            // When composition happens: every __mid_bb variable must also
            // appear in at least one rule's constraints or head arguments,
            // confirming it is actually constrained (not free).
            for mid_var in &mid_vars {
                let var_name = &mid_var.name;
                let referenced = vc_large.rules.iter().any(|rule| {
                    let in_body = rule.body.constraints.iter().any(|c| {
                        constraint_tree_contains(c, &|e| {
                            matches!(e.value(), ExprValue::Var { name } if **name == **var_name)
                        })
                    });
                    let in_head = rule.head.args.iter().any(|a| {
                        constraint_tree_contains(a, &|e| {
                            matches!(e.value(), ExprValue::Var { name } if **name == **var_name)
                        })
                    });
                    in_body || in_head
                });
                assert!(
                    referenced,
                    "Intermediate variable '{var_name}' is declared but never referenced \
                     in any rule — indicates a free variable bug in composition"
                );
            }
        }

        // VC must have non-trivial transition constraints regardless.
        assert_has_nontrivial_transition_constraints(&vc_large, "probe_assign_then_branch");
    });
}

// =============================================================================
// Test: Range for-loop in Large mode — compose_range_next_constraints (#3146)
// =============================================================================

/// Range for-loop composition in Large mode must produce both destination
/// (Option<T>) and iterator state (start' = start + 1) constraints.
///
/// This exercises `compose_range_next_constraints` in fragment_gen.rs.
/// The #3146 guard ensures that if destination constraints fail, iterator
/// state constraints are also skipped (preventing unsound partial rules).
/// This test verifies the happy path: both sections emit constraints.
///
/// Part of #3146: compose_range_next_constraints soundness guard.
#[test]
fn test_large_step_range_for_loop_composition_both_sections() {
    use ay_bindings::ExprValue;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_compose(n: u32) -> u32 {
            let mut sum = 0u32;
            for i in 0u32..n {
                sum = sum.wrapping_add(i);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_compose");
        let body = instance.body().expect("function body");

        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_range_compose",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        assert_large_vc_integrity(&vc_large, "probe_range_compose");
        assert_has_nontrivial_transition_constraints(&vc_large, "probe_range_compose");

        // Range iteration should emit BvAdd for `start + 1` advancement
        // (iterator state section of compose_range_next_constraints).
        assert_rule_contains_expr_kind(
            &vc_large,
            "probe_range_compose (Large)",
            |e| matches!(e.value(), ExprValue::BvAdd(..)),
            "BvAdd (range start + 1 in composed fragment)",
        );

        // Range iteration should emit BvULt for `start < end` guard
        // (used in both destination Ite and iterator Ite).
        assert_rule_contains_expr_kind(
            &vc_large,
            "probe_range_compose (Large)",
            |e| matches!(e.value(), ExprValue::BvULt(..)),
            "BvULt (range start < end in composed fragment)",
        );
    });
}

// =============================================================================
// Test: ChcStepMode::Auto resolves to Large for looping functions (#112)
// =============================================================================

/// Auto mode should resolve to Large for a function with a loop, producing
/// the same VC structure as explicit Large mode. For acyclic functions, Auto
/// should resolve to Small, matching explicit Small mode.
///
/// Part of #112: ChcStepMode::Auto per-function loop detection.
#[test]
fn test_auto_step_mode_resolves_per_function() {
    // Looping function: Auto should resolve to Large.
    const LOOP_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_auto_loop(n: u32) -> u32 {
            let mut acc = 0u32;
            for i in 0u32..n {
                acc = acc.wrapping_add(i);
            }
            acc
        }
    "#;

    // Acyclic function: Auto should resolve to Small.
    const ACYCLIC_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_auto_acyclic(a: u32, b: u32) -> u32 {
            let c = a.wrapping_add(b);
            let d = c.wrapping_mul(2);
            d
        }
    "#;

    // Test 1: Looping function — Auto should match Large.
    with_test_ay_ctx_for_source(LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_auto_loop");
        let body = instance.body().expect("function body");

        let vc_auto = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_auto_loop",
            ChcConfig { step_mode: crate::args::ChcStepMode::Auto, ..ChcConfig::default() },
        );
        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_auto_loop",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        // Auto on a looping fn should produce identical relation/rule counts to Large.
        assert_eq!(
            vc_auto.relations.len(),
            vc_large.relations.len(),
            "Auto (loop fn) should match Large relation count"
        );
        assert_eq!(
            vc_auto.rules.len(),
            vc_large.rules.len(),
            "Auto (loop fn) should match Large rule count"
        );
    });

    // Test 2: Acyclic function — Auto should match Small.
    with_test_ay_ctx_for_source(ACYCLIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_auto_acyclic");
        let body = instance.body().expect("function body");

        let vc_auto = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_auto_acyclic",
            ChcConfig { step_mode: crate::args::ChcStepMode::Auto, ..ChcConfig::default() },
        );
        let vc_small = mir_to_chc(ctx.tcx, &body, "probe_auto_acyclic", ChcConfig::default());

        // Auto on an acyclic fn should produce identical relation/rule counts to Small.
        assert_eq!(
            vc_auto.relations.len(),
            vc_small.relations.len(),
            "Auto (acyclic fn) should match Small relation count"
        );
        assert_eq!(
            vc_auto.rules.len(),
            vc_small.rules.len(),
            "Auto (acyclic fn) should match Small rule count"
        );
    });
}

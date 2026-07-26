// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// Part of #2314: emit_error_rule_for_condition conservative fallback
// ============================================================================

/// Per-ctx heap_check_untranslatable counter defaults to 0 (Part of #2906).
#[test]
fn test_heap_check_untranslatable_count_accessible() {
    use crate::codegen_ay::chc::codegen_ctx::ChcDiagnostics;

    let diag = ChcDiagnostics::default();
    assert_eq!(diag.heap_check_untranslatable.get(), 0, "default should be 0");
}

/// Per-ctx heap_check_untranslatable counter increments via CellCounter (Part of #2906).
#[test]
fn test_heap_check_untranslatable_count_increment() {
    use crate::codegen_ay::chc::codegen_ctx::ChcDiagnostics;
    use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

    let diag = ChcDiagnostics::default();
    diag.heap_check_untranslatable.inc();
    assert_eq!(diag.heap_check_untranslatable.get(), 1, "after inc, should be 1");
}

/// Test that emit_error_rule_for_condition with an unsupported sort (array)
/// emits a conservative unconditional error rule instead of silently dropping
/// the safety check. This prevents false proofs when heap safety conditions
/// have non-bool/non-bitvec/non-int sorts.
///
/// Part of #2314: covers codegen_expr_heap.rs emit_error_rule_for_condition fallback.
#[test]
fn test_emit_error_rule_for_condition_unsupported_sort_emits_conservative_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn heap_probe(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "heap_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "heap_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args);

        // Seed reachability so error is solver-visible.
        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        let rules_before = chc_ctx.vc.rules.len();
        let count_before = chc_ctx.diagnostics.heap_check_untranslatable.get();

        // Create a condition with an array sort — to_bool_expr returns None for this.
        let array_cond =
            Expr::var("unsupported_cond", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
        let stmt_constraints = vec![Expr::bool_const(true)];

        chc_ctx.emit_error_rule_for_condition(&from_app, array_cond, &stmt_constraints, 0);

        let rules_after = chc_ctx.vc.rules.len();
        let count_after = chc_ctx.diagnostics.heap_check_untranslatable.get();

        // A conservative error rule must have been emitted (not silently dropped).
        assert!(
            rules_after > rules_before,
            "emit_error_rule_for_condition must emit a conservative error rule \
             when to_bool_expr fails (got {} rules before, {} after)",
            rules_before,
            rules_after,
        );

        // The per-ctx counter must have been incremented (Part of #2906).
        assert!(
            count_after > count_before,
            "heap_check_untranslatable must increment when to_bool_expr fails \
             (was {count_before}, now {count_after})",
        );

        // The emitted rule should target the error relation.
        let last_rule = chc_ctx.vc.rules.last().expect("at least one rule");
        assert_eq!(last_rule.head.name, "error", "Conservative rule must target error relation");
    });
}

/// Test that emit_error_rule_for_condition still works correctly for
/// supported sorts (bool, bitvec) — regression guard for #2314 fix.
#[test]
fn test_emit_error_rule_for_condition_bool_sort_emits_negated_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn heap_probe_bool(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "heap_probe_bool");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "heap_probe_bool", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args);

        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        let rules_before = chc_ctx.vc.rules.len();

        // Bool condition — should work normally (not trigger fallback).
        let bool_cond = Expr::var("validity_check", Sort::bool());
        let stmt_constraints = vec![Expr::bool_const(true)];

        chc_ctx.emit_error_rule_for_condition(&from_app, bool_cond, &stmt_constraints, 0);

        let rules_after = chc_ctx.vc.rules.len();
        assert!(rules_after > rules_before, "Bool condition must emit an error rule");

        // The rule should contain a negation (violation = !cond), not be unconditional.
        let last_rule = chc_ctx.vc.rules.last().expect("at least one rule");
        assert_eq!(last_rule.head.name, "error", "Rule must target error");
        // The body should have more constraints than just stmt_constraints
        // (the violation constraint is appended).
        let body_constraints = &last_rule.body.constraints;
        assert!(
            body_constraints.len() > stmt_constraints.len(),
            "Normal error rule must include negated condition constraint \
             (got {} constraints, expected > {})",
            body_constraints.len(),
            stmt_constraints.len(),
        );
    });
}

#[test]
fn test_emit_error_rule_for_condition_shared_reuses_constraint_base() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn heap_probe_shared(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "heap_probe_shared");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "heap_probe_shared", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args);
        let shared_constraints: std::sync::Arc<[Expr]> = vec![Expr::bool_const(true)].into();

        chc_ctx.emit_error_rule_for_condition_shared(
            &from_app,
            Expr::var("validity_check", Sort::bool()),
            &shared_constraints,
            0,
        );

        let last_rule = chc_ctx.vc.rules.last().expect("at least one rule");
        match &last_rule.body.constraints {
            trust_mc_core::constraints::Constraints::Shared { base, extra } => {
                assert!(
                    std::sync::Arc::ptr_eq(base, &shared_constraints),
                    "shared emitter must reuse the Arc base constraints"
                );
                assert_eq!(extra.len(), 1, "shared emitter must append the violation");
            }
            other => unreachable!("expected shared constraints in error rule, got {other:?}"),
        }
    });
}

// ============================================================================
// Part of #2501: heap_access_checks fail-closed for unknown layout
// ============================================================================

/// Per-ctx heap_check_unknown_layout counter defaults to 0, increments, and reads back.
/// Replaces Mutex-guarded global atomic drain test (Part of #2906).
#[test]
fn test_heap_check_unknown_layout_count_drain() {
    use crate::codegen_ay::chc::codegen_ctx::ChcDiagnostics;
    use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

    let diag = ChcDiagnostics::default();
    assert_eq!(diag.heap_check_unknown_layout.get(), 0, "default should be 0");

    diag.heap_check_unknown_layout.inc();
    assert_eq!(diag.heap_check_unknown_layout.get(), 1, "after inc, should be 1");

    diag.heap_check_unknown_layout.inc();
    assert_eq!(diag.heap_check_unknown_layout.get(), 2, "after second inc, should be 2");
}

/// Regression test (#2501): When heap_access_checks receives a `false` check
/// (emitted when get_type_size/get_type_align returns None), the error rule
/// must be unconditional — ensuring fail-closed behavior for unknown-layout types.
#[test]
fn test_false_check_produces_unconditional_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn heap_probe_failclosed(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "heap_probe_failclosed");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "heap_probe_failclosed", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args);

        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        let rules_before = chc_ctx.vc.rules.len();

        // Simulate the fail-closed pattern: Expr::bool_const(false) as a check.
        // This is what heap_access_checks now emits when get_type_size/get_type_align
        // returns None (#2501).
        let fail_closed_check = Expr::bool_const(false);
        let stmt_constraints = vec![Expr::bool_const(true)];

        chc_ctx.emit_error_rule_for_condition(&from_app, fail_closed_check, &stmt_constraints, 0);

        let rules_after = chc_ctx.vc.rules.len();
        assert!(
            rules_after > rules_before,
            "bool_const(false) check must emit an error rule (fail-closed)"
        );

        // The rule body should contain `not(false)` = `true`, making it unconditional.
        let last_rule = chc_ctx.vc.rules.last().expect("at least one rule");
        assert_eq!(last_rule.head.name, "error", "Rule must target error");

        // The body constraints should include the negated false (= true).
        let body_constraints = &last_rule.body.constraints;
        assert!(
            body_constraints.len() > stmt_constraints.len(),
            "Error rule must include negated condition (got {} constraints, expected > {})",
            body_constraints.len(),
            stmt_constraints.len(),
        );

        // The negated condition (last constraint) should contain `not` or simplify to `true`.
        let violation = body_constraints.last().expect("violation constraint");
        let smt = violation.to_string();
        assert!(
            smt.contains("not") || smt.contains("true"),
            "Violation for bool_const(false) should be negated to true: {smt}"
        );
    });
}

// ============================================================================
// HeapState region sort conflict: non-bv8 vs non-bv8 (Part of #2529)
// Exercises heap_state.rs:309 — two different typed sorts for same obj_id
// ============================================================================

/// When a region array is first assigned a typed sort (bv32), then a different
/// typed sort (bv64) is requested for the same obj_id, the function should
/// warn and return the existing region (no upgrade, no crash).
#[test]
fn test_region_array_sort_conflict_non_bv8_returns_existing() {
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();

    // First assignment: typed sort bv32
    let (typed_name, typed_out) = heap.assign_region_array(obj_id, Sort::bitvec(32), "fn_test");
    assert!(typed_name.contains("bv32"), "Initial region should be bv32");

    // Second assignment: different typed sort bv64 — should warn and return existing
    let (conflict_name, conflict_out) =
        heap.assign_region_array(obj_id, Sort::bitvec(64), "fn_test");
    assert_eq!(
        typed_name, conflict_name,
        "Sort conflict should return existing region name, not create new. existing: {typed_name}, got: {conflict_name}"
    );
    assert_eq!(typed_out, conflict_out, "Sort conflict should return existing output name");
}

/// When a region array has a Bool sort and a bv32 is requested, the function
/// should return the existing Bool region (Bool is not bv8, so no upgrade).
#[test]
fn test_region_array_sort_conflict_bool_vs_bv32_returns_existing() {
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();

    // First assignment: Bool sort
    let (bool_name, _) = heap.assign_region_array(obj_id, Sort::bool(), "fn_test");

    // Second assignment: bv32 — Bool is not bv8, so no upgrade path; returns existing
    let (conflict_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(32), "fn_test");
    assert_eq!(
        bool_name, conflict_name,
        "Bool vs bv32 conflict should return existing Bool region"
    );
}

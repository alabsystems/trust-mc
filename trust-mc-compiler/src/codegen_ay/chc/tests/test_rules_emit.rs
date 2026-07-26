// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct unit tests for `emit_goto_rule_extra` and `emit_guarded_goto_rule`
//! in codegen_rules/mod.rs.
//!
//! These are the core CHC transition rule emitters. Prior to this file,
//! they had no direct coverage — only indirect exercising through
//! full-pipeline translate() tests.
//!
//! Covers:
//! - `emit_goto_rule_extra`: extra constraints appended to base slice
//! - `emit_guarded_goto_rule`: guard=true optimization, guard=false skip, normal guard
//! - Missing target block → warn + no rule emitted
//! - `project_full_output_to_block` arity invariant (debug assertion)
//!
//! Part of #2875: proof_coverage gap for codegen_rules.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// emit_goto_rule_extra — direct tests
// ═══════════════════════════════════════════════════════════════════════

/// `emit_goto_rule_extra` with no extra constraints should produce a rule
/// whose body constraints match the base `stmt_constraints`.
#[test]
fn test_emit_goto_rule_extra_no_extra_matches_base_constraints() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_extra(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_extra");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_goto_extra", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let base_constraint = Expr::bool_const(true);
            let stmt_constraints = [base_constraint];

            let before_len = chc_ctx.vc.rules.len();

            // Call emit_goto_rule_extra with empty extra
            chc_ctx.emit_goto_rule_extra(
                &from_app,
                target,
                &output_args,
                &stmt_constraints,
                std::iter::empty::<Expr>(),
            );

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "should emit exactly one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                1,
                "no-extra rule should have only the base constraint"
            );
        },
    );
}

/// `emit_goto_rule_extra` with extra constraints appends them after base.
#[test]
fn test_emit_goto_rule_extra_appends_extra_constraints() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_extra_append(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_extra_append");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_goto_extra_append", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let base = [Expr::bool_const(true)];
            let extra_1 = Expr::var("extra_a", ay_bindings::Sort::bool());
            let extra_2 = Expr::var("extra_b", ay_bindings::Sort::bool());

            let before_len = chc_ctx.vc.rules.len();

            chc_ctx.emit_goto_rule_extra(
                &from_app,
                target,
                &output_args,
                &base,
                [extra_1, extra_2],
            );

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "should emit exactly one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                3,
                "rule should have base(1) + extra(2) = 3 constraints, got {}",
                new_rules[0].body.constraints.len()
            );
        },
    );
}

#[test]
fn test_emit_goto_rule_extra_appends_constructor_guard_for_selector_extra() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_extra_selector(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_extra_selector");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_goto_extra_selector", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let option_sort = enum_sort(
                "Option_bv32",
                vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])],
            );
            let selector = Expr::var("opt", option_sort).field_select(
                "Option_bv32",
                "value",
                Sort::bitvec(32),
            );
            let extra_constraint = selector.eq(Expr::bitvec_const(1u64, 32));

            let before_len = chc_ctx.vc.rules.len();
            chc_ctx.emit_goto_rule_extra(&from_app, target, &output_args, &[], [extra_constraint]);

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "should emit exactly one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                2,
                "selector extra should append its constructor guard"
            );
            assert!(new_rules[0].body.constraints.iter().any(|expr| {
                matches!(
                    expr.value(),
                    ExprValue::DatatypeTester { constructor_name, .. } if constructor_name == "Some"
                )
            }));
        },
    );
}

/// A stale source relation app should pick up late-created block state vars
/// instead of relying on translate-time `__pad_*` placeholders.
#[test]
fn test_emit_goto_rule_extra_refreshes_late_source_relation_args() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_late_source(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_late_source");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_goto_late_source", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));

            let late_sort = ay_bindings::Sort::array(
                ay_bindings::Sort::bitvec(64),
                ay_bindings::Sort::bitvec(32),
            );
            chc_ctx.push_late_state_var_pair(
                std::sync::Arc::from("late_region_i32"),
                "late_region_i32__out",
                late_sort.clone(),
            );

            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .output_state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            chc_ctx.emit_goto_rule_extra(
                &from_app,
                target,
                &output_args,
                &[],
                std::iter::empty::<Expr>(),
            );

            let emitted = chc_ctx.vc.rules.last().expect("emitted goto rule");
            let body_rel = emitted.body.relation.as_ref().expect("body relation");
            let late_input = Expr::var("late_region_i32", late_sort);
            assert_eq!(
                body_rel.args.last(),
                Some(&late_input),
                "emit_goto_rule_extra should thread the real late input var into the body relation",
            );
            let rendered = format!("{}", body_rel.args.last().expect("late arg"));
            assert!(
                !rendered.contains("__pad_"),
                "late source arg should not be a translate-time pad variable: {rendered}"
            );
        },
    );
}

/// A stale output_args vector (shorter than current state_vars because a late
/// state var was added after output_args was built) should be repaired by
/// `refresh_full_output_args()` inside `project_full_output_to_block()`.
/// Part of #3815: D3 regression — output-side mirror of stale-source test above.
#[test]
fn test_emit_goto_rule_extra_refreshes_late_output_args() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_late_output(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_late_output");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_goto_late_output", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();

            // Snapshot output_args BEFORE late state var addition (stale).
            let stale_output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .output_state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let stale_len = stale_output_args.len();

            // Late-declare a new state var pair (simulates slice/vec memory model).
            let late_sort = ay_bindings::Sort::array(
                ay_bindings::Sort::bitvec(64),
                ay_bindings::Sort::bitvec(32),
            );
            chc_ctx.push_late_state_var_pair(
                std::sync::Arc::from("late_region_i32"),
                "late_region_i32__out",
                late_sort,
            );

            // Mark the late index as modified so refresh picks __out, not input var.
            let late_idx = chc_ctx.state_var_mgr.state_vars.len() - 1;
            chc_ctx.encode.modified_state_indices.insert(late_idx);

            // Build a fresh from_app that includes the late var (source side is fresh).
            let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let before_len = chc_ctx.vc.rules.len();

            // This must NOT panic despite stale_output_args being shorter than state_vars.
            chc_ctx.emit_goto_rule_extra(
                &from_app,
                target,
                &stale_output_args,
                &[],
                std::iter::empty::<Expr>(),
            );

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "should emit exactly one rule");

            // The emitted head should have arity matching the target block's live state,
            // which includes the late-added var.
            let head = &new_rules[0].head;
            assert!(
                head.args.len() > stale_len,
                "emitted head arity ({}) should exceed stale output_args length ({})",
                head.args.len(),
                stale_len,
            );

            // The late output slot should reference the __out var (modified), not input.
            let head_strs: Vec<String> = head.args.iter().map(ToString::to_string).collect();
            assert!(
                head_strs
                    .iter()
                    .any(|s| s.contains("late_region_i32__out") || s.contains("late_region_i32")),
                "emitted head should reference the late state var: {head_strs:?}"
            );
        },
    );
}

/// `emit_goto_rule_extra` with invalid target emits no rule.
#[test]
fn test_emit_goto_rule_extra_missing_target_emits_nothing() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_goto_missing(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_goto_missing");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_goto_missing", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let before_len = chc_ctx.vc.rules.len();

            // Target 9999 does not exist in block_relations
            chc_ctx.emit_goto_rule_extra(
                &from_app,
                9999,
                &output_args,
                &[],
                std::iter::empty::<Expr>(),
            );

            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_len,
                "missing target should not emit any rule"
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// emit_guarded_goto_rule — direct tests
// ═══════════════════════════════════════════════════════════════════════

/// Guard `true` optimization: delegates to `emit_goto_rule` (unguarded).
/// The resulting rule should have no guard constraint.
#[test]
fn test_emit_guarded_goto_rule_true_guard_optimization() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_guard_true(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_guard_true");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_guard_true", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let before_len = chc_ctx.vc.rules.len();

            // Guard = true → should delegate to unguarded emit_goto_rule
            chc_ctx.emit_guarded_goto_rule(
                &from_app,
                target,
                &output_args,
                &[],
                Expr::bool_const(true),
            );

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "guard=true should emit exactly one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                0,
                "guard=true optimization should produce rule with no constraints (unguarded)"
            );
        },
    );
}

/// Guard `false` optimization: no rule emitted (dead branch).
#[test]
fn test_emit_guarded_goto_rule_false_guard_skips() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_guard_false(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_guard_false");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_guard_false", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let before_len = chc_ctx.vc.rules.len();

            // Guard = false → should skip (dead branch), no rule emitted
            chc_ctx.emit_guarded_goto_rule(
                &from_app,
                target,
                &output_args,
                &[],
                Expr::bool_const(false),
            );

            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_len,
                "guard=false should not emit any rule (dead branch)"
            );
        },
    );
}

/// Normal guard (non-constant) appends guard as extra constraint.
#[test]
fn test_emit_guarded_goto_rule_normal_guard_appends_constraint() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_guard_normal(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_guard_normal");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_guard_normal", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let base = [Expr::bool_const(true)];
            let guard = Expr::var("my_guard", ay_bindings::Sort::bool());

            let before_len = chc_ctx.vc.rules.len();

            chc_ctx.emit_guarded_goto_rule(&from_app, target, &output_args, &base, guard);

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "normal guard should emit one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                2,
                "normal guard rule should have base(1) + guard(1) = 2 constraints"
            );

            // Verify the guard is in the constraints
            let constraint_strs: Vec<String> = new_rules[0]
                .body
                .constraints
                .iter()
                .map(std::string::ToString::to_string)
                .collect();
            assert!(
                constraint_strs.iter().any(|s| s.contains("my_guard")),
                "guard expression 'my_guard' should appear in rule constraints, got: {:?}",
                constraint_strs
            );
        },
    );
}

#[test]
fn test_emit_guarded_goto_rule_appends_constructor_guard_for_selector_guard() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_guard_selector(x: u32) -> u32 {
            if x > 0 { x } else { 0 }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_guard_selector");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_guard_selector", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            let option_sort = enum_sort(
                "Option_bv32",
                vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])],
            );
            let guard = Expr::var("opt", option_sort)
                .field_select("Option_bv32", "value", Sort::bitvec(32))
                .eq(Expr::bitvec_const(1u64, 32));

            let before_len = chc_ctx.vc.rules.len();
            chc_ctx.emit_guarded_goto_rule(&from_app, target, &output_args, &[], guard);

            let new_rules = &chc_ctx.vc.rules[before_len..];
            assert_eq!(new_rules.len(), 1, "normal guard should emit one rule");
            assert_eq!(
                new_rules[0].body.constraints.len(),
                2,
                "selector guard should append its constructor guard"
            );
            assert!(new_rules[0].body.constraints.iter().any(|expr| {
                matches!(
                    expr.value(),
                    ExprValue::DatatypeTester { constructor_name, .. } if constructor_name == "Some"
                )
            }));
        },
    );
}

/// Missing target block in emit_guarded_goto_rule emits nothing.
#[test]
fn test_emit_guarded_goto_rule_missing_target_emits_nothing() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_guard_missing(x: u32) -> u32 { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_guard_missing");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_guard_missing", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());
            let guard = Expr::var("g", ay_bindings::Sort::bool());

            let before_len = chc_ctx.vc.rules.len();

            // Target 9999 does not exist
            chc_ctx.emit_guarded_goto_rule(&from_app, 9999, &output_args, &[], guard);

            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_len,
                "missing target should not emit any rule"
            );
        },
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Arity consistency between emit_goto_rule_extra and emit_guarded_goto_rule
// ═══════════════════════════════════════════════════════════════════════

/// Both emit paths should produce rules with the same head arity
/// for the same target block. This verifies they use the same
/// projection logic (project_full_output_to_block).
#[test]
fn test_emit_goto_and_guarded_goto_produce_same_head_arity() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn probe_arity_match(x: u32, y: u32) -> u32 {
            if x > y { x } else { y }
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_arity_match");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_arity_match", ChcConfig::default());

            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();

            let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args.clone());

            let target = *chc_ctx
                .block_relations
                .keys()
                .find(|&&idx| idx != 0)
                .expect("at least one non-entry block");

            // Emit one rule via emit_goto_rule_extra
            chc_ctx.emit_goto_rule_extra(
                &from_app,
                target,
                &output_args,
                &[],
                std::iter::empty::<Expr>(),
            );

            // Emit another via emit_guarded_goto_rule
            let guard = Expr::var("g", ay_bindings::Sort::bool());
            chc_ctx.emit_guarded_goto_rule(&from_app, target, &output_args, &[], guard);

            let rules = &chc_ctx.vc.rules;
            assert!(rules.len() >= 2, "should have at least 2 emitted rules");

            let last_two = &rules[rules.len() - 2..];
            assert_eq!(
                last_two[0].head.args.len(),
                last_two[1].head.args.len(),
                "emit_goto_rule_extra and emit_guarded_goto_rule should produce same head arity \
                 for same target (goto={}, guarded={})",
                last_two[0].head.args.len(),
                last_two[1].head.args.len()
            );
            assert_eq!(
                last_two[0].head.name, last_two[1].head.name,
                "both rules should target the same relation"
            );
        },
    );
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_expr_assert.rs fallback and soundness paths.
//!
//! Split from test_assert_encoding.rs (#2584 file-size gate).
//!
//! Covers:
//! - emit_kani_assert_error_rule: empty-args and untranslatable fallback
//! - emit_kani_assume_rule: empty-args/untranslatable fail-closed fallback and missing-target drop
//! - Real-condition paths: negated violation guard, BV-to-Bool coercion, guarded transition
//! - ASSUME_DROPPED_TRANSITION_COUNT and ASSERT_UNTRANSLATABLE_COUNT counter verification (as side effects)

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_expr_assert::KaniAssumeContext;
use crate::codegen_ay::emit_chc;
use trust_mc_core::{ChcQuery, RelationApp, Rule};

/// Simple probe function for fallback-path unit tests.
const FALLBACK_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn fallback_probe(x: u32) -> u32 { x + 1 }
"#;

/// Probe with a bool parameter for testing real-condition assert/assume paths.
const BOOL_COND_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn bool_cond_probe(cond: bool, x: u32) -> u32 { if cond { x } else { 0 } }
"#;

// ═══════════════════════════════════════════════════════════════════════
// Untranslatable kani::assert / kani::assume fallback behavior
// ═══════════════════════════════════════════════════════════════════════

/// Tests that `emit_kani_assert_error_rule` with empty args emits a
/// conservative error rule (via `emit_untranslatable_assert_rule`)
/// instead of silently dropping the assertion. This prevents false PROOF.
///
/// Part of #2233: CHC must never silently drop kani::assert.
#[test]
fn test_kani_assert_empty_args_emits_conservative_error_rule() {
    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

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
        let modified = HashSet::new();

        // Seed reachability so an unconditional error rule is solver-visible.
        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        let before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        // Pass empty args with non-empty stmt_constraints — exercises the
        // production-realistic path where block constraints are propagated
        // into the conservative error rule.
        let stmt_constraints = [Expr::bool_const(true)];
        chc_ctx.emit_kani_assert_error_rule(&from_app, &[], &stmt_constraints, &modified, 0);

        let after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(
            after,
            before + 1,
            "empty-args fallback must emit an error rule, not silently drop the assert"
        );

        // The fallback error rule should carry stmt_constraints (block context)
        let fallback_rule = chc_ctx
            .vc
            .rules
            .iter()
            .rfind(|r| r.head.name == "error")
            .expect("expected fallback error rule");
        assert_eq!(
            fallback_rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule should propagate stmt_constraints from the enclosing block"
        );

        // End-to-end: Z3 should find error() reachable (sat)
        chc_ctx.vc.query = ChcQuery::new().with_target("error");
        let smt = emit_chc(&chc_ctx.vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}

/// Tests that `emit_kani_assume_rule` with empty args emits a conservative
/// error rule instead of silently dropping the assume.
///
/// Part of #2233: CHC must warn and fall back, not silently drop kani::assume.
#[test]
fn test_kani_assume_empty_args_emits_conservative_error_rule() {
    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args.clone());
        let modified = HashSet::new();

        // Use a non-zero block as the target (must exist in block_relations)
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&k| k != 0)
            .expect("need at least 2 blocks for assume target");

        let stmt_constraints = vec![Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.len();

        // Pass empty args — triggers conservative error fallback.
        let assume_cx = KaniAssumeContext {
            from_app: &from_app,
            args: &[],
            target,
            output_args: &state_args,
            extra_constraints: &[],
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified,
            bb_idx: 0,
        };
        chc_ctx.emit_kani_assume_rule(&assume_cx);

        // Should emit exactly one fallback rule.
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before + 1,
            "empty-args fallback must emit a conservative error rule, not silently drop the assume"
        );

        // The fallback rule should target error and preserve stmt_constraints.
        let assume_rule = chc_ctx
            .vc
            .rules
            .iter()
            .find(|r| r.head.name == "error")
            .expect("expected fallback error rule for assume");
        assert_eq!(
            assume_rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule must contain only stmt_constraints (no assume guard)"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Real-condition kani::assert / kani::assume paths (Part of #2272 Step 1)
// ═══════════════════════════════════════════════════════════════════════

/// Tests that `emit_kani_assert_error_rule` with a translatable bool operand
/// emits an error rule whose constraints include a negation of the condition
/// variable — not just the stmt_constraints passthrough seen in fallback paths.
///
/// Part of #2272: covers `codegen_expr_assert.rs:247-302` (happy path).
#[test]
fn test_kani_assert_nonempty_args_emits_negated_violation_guard() {
    with_test_ay_ctx_for_source(BOOL_COND_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bool_cond_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bool_cond_probe", ChcConfig::default());

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
        let modified = HashSet::new();

        // Seed reachability so error is solver-visible.
        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        // Construct Operand::Copy for local 1 (the `cond: bool` parameter).
        let cond_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });

        let stmt_constraints = [Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        // Call with real args — exercises the successful translation path.
        chc_ctx.emit_kani_assert_error_rule(
            &from_app,
            &[cond_operand],
            &stmt_constraints,
            &modified,
            0,
        );

        let after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(after, before + 1, "real-condition assert must emit exactly one error rule");

        // The real-condition error rule should have MORE constraints than just
        // stmt_constraints: specifically stmt_constraints + the negated condition.
        let error_rule = chc_ctx
            .vc
            .rules
            .iter()
            .rfind(|r| r.head.name == "error")
            .expect("expected error rule from real-condition assert");
        assert!(
            error_rule.body.constraints.len() > stmt_constraints.len(),
            "real-condition error rule must include the negated violation guard \
             (got {} constraints, expected > {})",
            error_rule.body.constraints.len(),
            stmt_constraints.len()
        );

        // The violation constraint (last added) should be a Not() expression
        // wrapping the bool condition variable — not a BoolConst.
        let violation = error_rule.body.constraints.last().expect("expected violation constraint");
        assert!(
            matches!(violation.value(), ExprValue::Not(_)),
            "violation guard should be Not(cond), got: {:?}",
            violation.value()
        );

        // End-to-end: Z3 should find the error reachable (sat) because
        // there exist inputs where the condition is false.
        chc_ctx.vc.query = ChcQuery::new().with_target("error");
        let smt = emit_chc(&chc_ctx.vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}

/// Tests that `emit_kani_assert_error_rule` with a bitvec (u32) operand
/// correctly converts it to a bool via to_bool_expr (non-zero check)
/// before emitting the negated violation guard.
///
/// Part of #2272: covers the BV-to-Bool coercion in `to_bool_expr`.
#[test]
fn test_kani_assert_bitvec_condition_coerced_to_bool() {
    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

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
        let modified = HashSet::new();

        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        // Local 1 is `x: u32` — a bitvec sort, not bool.
        let bv_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });

        let stmt_constraints = [Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        chc_ctx.emit_kani_assert_error_rule(
            &from_app,
            &[bv_operand],
            &stmt_constraints,
            &modified,
            0,
        );

        let after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(after, before + 1, "bitvec-condition assert must emit exactly one error rule");

        // The violation guard should be a negation of the BV-to-Bool conversion:
        // to_bool_expr returns Not(Eq(x, 0)), then assert negates → Not(Not(Eq(x, 0))).
        let error_rule = chc_ctx
            .vc
            .rules
            .iter()
            .rfind(|r| r.head.name == "error")
            .expect("expected error rule from bitvec-condition assert");
        assert!(
            error_rule.body.constraints.len() > stmt_constraints.len(),
            "bitvec-condition error rule must include coerced violation guard \
             (got {} constraints, expected > {})",
            error_rule.body.constraints.len(),
            stmt_constraints.len()
        );

        // Verify the violation guard is a Not() wrapping the BV-to-Bool conversion,
        // mirroring the structure check in the bool-condition test.
        let violation = error_rule.body.constraints.last().expect("expected violation constraint");
        assert!(
            matches!(violation.value(), ExprValue::Not(_)),
            "bitvec violation guard should be Not(Not(Eq(x, 0))), got: {:?}",
            violation.value()
        );

        // End-to-end: Z3 should find error reachable (x=0 satisfies violation).
        chc_ctx.vc.query = ChcQuery::new().with_target("error");
        let smt = emit_chc(&chc_ctx.vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}

/// Tests that `emit_kani_assume_rule` with a translatable bool operand
/// emits a guarded transition with the assume condition as an extra constraint.
///
/// Part of #2272: covers `codegen_expr_assert.rs:363-430` (happy path).
#[test]
fn test_kani_assume_nonempty_args_emits_guarded_transition() {
    with_test_ay_ctx_for_source(BOOL_COND_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bool_cond_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bool_cond_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args.clone());
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&k| k != 0)
            .expect("need at least 2 blocks for assume target");
        let cond_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let stmt_constraints = vec![Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.len();

        let modified = HashSet::new();
        let assume_cx = KaniAssumeContext {
            from_app: &from_app,
            args: &[cond_operand],
            target,
            output_args: &state_args,
            extra_constraints: &[],
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified,
            bb_idx: 0,
        };
        chc_ctx.emit_kani_assume_rule(&assume_cx);

        assert_eq!(chc_ctx.vc.rules.len(), before + 1, "must emit exactly one transition rule");

        let target_rel = chc_ctx.block_relations.get(&target).expect("target relation").clone();
        let assume_rule = chc_ctx
            .vc
            .rules
            .iter()
            .rfind(|r| r.head.name == target_rel)
            .expect("expected guarded transition rule");

        assert!(assume_rule.body.relation.is_some(), "must be a transition, not an init rule");
        assert_eq!(
            assume_rule.body.constraints.len(),
            stmt_constraints.len() + 1,
            "guarded transition must include stmt_constraints + assume condition"
        );

        let guard = assume_rule.body.constraints.last().expect("assume guard");
        assert!(
            matches!(guard.value(), ExprValue::Var { .. }),
            "guard should be Var, got: {:?}",
            guard.value()
        );
        assert!(guard.sort().is_bool(), "guard must be Bool sort, got: {:?}", guard.sort());
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Fallback paths: untranslatable operands (Part of #2272 Step 2)
// ═══════════════════════════════════════════════════════════════════════

/// Tests that `emit_kani_assert_error_rule` with an untranslatable operand
/// (local index out of bounds) emits a conservative error rule via
/// `emit_untranslatable_assert_rule`, preventing false PROOF.
///
/// Part of #2272: covers `codegen_expr_assert.rs:248-261` (translate failure).
#[test]
fn test_kani_assert_untranslatable_operand_emits_conservative_error() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

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
        let modified = HashSet::new();

        // Seed reachability so error is solver-visible.
        chc_ctx.vc.add_rule(Rule::init(Expr::bool_const(true), from_app.clone()));

        // Use an out-of-bounds local index — translate_operand_with_modified returns None.
        let bogus_operand = Operand::Copy(Place { local: 999usize, projection: vec![] });

        let stmt_constraints = [Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        let before_count = GLOBAL_COUNTERS.assert_untranslatable.load(Ordering::Relaxed);

        chc_ctx.emit_kani_assert_error_rule(
            &from_app,
            &[bogus_operand],
            &stmt_constraints,
            &modified,
            0,
        );

        let after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(
            after,
            before + 1,
            "untranslatable operand must emit conservative error rule (fail-closed), not drop the assert"
        );

        // Verify the untranslatable counter incremented (production path side effect).
        let after_count = GLOBAL_COUNTERS.assert_untranslatable.load(Ordering::Relaxed);
        assert!(
            after_count > before_count,
            "ASSERT_UNTRANSLATABLE_COUNT must increment for untranslatable operand \
             (before={before_count}, after={after_count})"
        );

        // End-to-end: Z3 should find error reachable (conservative rule is unconstrained).
        chc_ctx.vc.query = ChcQuery::new().with_target("error");
        let smt = emit_chc(&chc_ctx.vc).to_string();
        assert_z3_result(&smt, "sat");
    });
}

/// Tests that `emit_kani_assume_rule` with an untranslatable operand
/// (local index out of bounds) emits a conservative error rule.
///
/// Part of #2272: covers `codegen_expr_assert.rs:364-373` (translate failure).
#[test]
fn test_kani_assume_untranslatable_operand_emits_conservative_error() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args.clone());
        let modified = HashSet::new();

        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&k| k != 0)
            .expect("need at least 2 blocks for assume target");

        // Use an out-of-bounds local index — translate_operand_with_modified returns None.
        let bogus_operand = Operand::Copy(Place { local: 999usize, projection: vec![] });

        let stmt_constraints = vec![Expr::bool_const(true)];
        let before = chc_ctx.vc.rules.len();
        let before_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);

        let assume_cx = KaniAssumeContext {
            from_app: &from_app,
            args: &[bogus_operand],
            target,
            output_args: &state_args,
            extra_constraints: &[],
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified,
            bb_idx: 0,
        };
        chc_ctx.emit_kani_assume_rule(&assume_cx);

        // Should emit one rule: the conservative error fallback.
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before + 1,
            "untranslatable operand must emit conservative error rule, not silently drop the assume"
        );

        // The fallback rule should target error and preserve stmt_constraints.
        let assume_rule = chc_ctx
            .vc
            .rules
            .iter()
            .find(|r| r.head.name == "error")
            .expect("expected fallback error rule");
        assert_eq!(
            assume_rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule must contain only stmt_constraints (no assume guard)"
        );

        let after_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);
        assert!(
            after_count > before_count,
            "ASSUME_DROPPED_TRANSITION_COUNT must increment for untranslatable assume \
             fallback (before={}, after={})",
            before_count,
            after_count
        );
    });
}

/// Tests that `emit_kani_assume_rule` with no args emits a conservative
/// error rule and increments the dropped-assume counter.
#[test]
fn test_kani_assume_empty_args_falls_back_and_counts_drop() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "fallback_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "fallback_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args.clone());
        let modified = HashSet::new();

        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&k| k != 0)
            .expect("need at least 2 blocks for assume target");

        let stmt_constraints = vec![Expr::bool_const(true)];
        let before_rules = chc_ctx.vc.rules.len();
        let before_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);

        let assume_cx = KaniAssumeContext {
            from_app: &from_app,
            args: &[],
            target,
            output_args: &state_args,
            extra_constraints: &[],
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified,
            bb_idx: 0,
        };
        chc_ctx.emit_kani_assume_rule(&assume_cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "empty-args assume must emit conservative error fallback rule"
        );

        let last_rule = chc_ctx.vc.rules.last().expect("expected fallback rule");
        assert_eq!(last_rule.head.name, "error", "fallback rule must target error relation");

        let after_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);
        assert!(
            after_count > before_count,
            "ASSUME_DROPPED_TRANSITION_COUNT must increment for empty-args assume \
             fallback (before={}, after={})",
            before_count,
            after_count
        );
    });
}

/// Tests that `emit_kani_assume_rule` with a valid condition but missing target
/// block relation drops the transition and increments the dropped counter.
///
/// This exercises the production path at codegen_expr_assert.rs:408-422 where
/// `block_relations.get(&target)` returns None — a soundness-relevant path because
/// dropped transitions make the target block unreachable from the assume path,
/// which may cause downstream assertions to be vacuously true.
///
/// Part of #2272: covers the ASSUME_DROPPED_TRANSITION_COUNT production path.
#[test]
fn test_kani_assume_missing_target_block_drops_transition() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    with_test_ay_ctx_for_source(BOOL_COND_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "bool_cond_probe");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "bool_cond_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args.clone());
        let modified = HashSet::new();

        // Use local 1 (cond: bool) — a valid translatable operand.
        let cond_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });

        // Use a target block index that does NOT exist in block_relations.
        let nonexistent_target = 9999usize;
        assert!(
            !chc_ctx.block_relations.contains_key(&nonexistent_target),
            "target {} must not exist in block_relations for this test",
            nonexistent_target
        );

        let stmt_constraints = vec![Expr::bool_const(true)];
        let before_rules = chc_ctx.vc.rules.len();
        let before_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);

        let assume_cx = KaniAssumeContext {
            from_app: &from_app,
            args: &[cond_operand],
            target: nonexistent_target,
            output_args: &state_args,
            extra_constraints: &[],
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified,
            bb_idx: 0,
        };
        chc_ctx.emit_kani_assume_rule(&assume_cx);

        // A conservative error rule should be added (Part of #3099):
        // from(state) -> error(). This is fail-closed: if the path is reachable
        // the solver reports FAILURE, preventing unsound vacuous truth.
        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "missing target block must emit conservative error rule"
        );

        // The dropped transition counter must have incremented.
        let after_count = GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed);
        assert!(
            after_count > before_count,
            "ASSUME_DROPPED_TRANSITION_COUNT must increment when target block is missing \
             (before={}, after={})",
            before_count,
            after_count
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused tests for `expr/codegen_expr_assert.rs` helpers.
//!
//! Part of #2921 (untested CHC production file remediation).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use std::sync::Arc;
use trust_mc_core::chc::RelationApp;

const ASSERT_BOOL_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_assert_bool(cond: bool) {
    assert!(cond);
}
"#;

const INT_COND_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_int_cond(x: i32) -> i32 {
    x
}
"#;

#[test]
fn test_translate_assert_condition_bool_operand_returns_bool_expr() {
    with_test_ay_ctx_for_source(ASSERT_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_bool");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assert_bool", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let cond_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let bool_expr = chc_ctx
            .translate_assert_condition(&cond_operand, &HashSet::new(), 0)
            .expect("bool operand should translate");

        assert!(bool_expr.sort().is_bool(), "translated condition must be bool sort");
    });
}

#[test]
fn test_translate_assert_condition_numeric_operand_coerces_to_nonzero_bool() {
    with_test_ay_ctx_for_source(INT_COND_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_int_cond");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_int_cond", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let numeric_operand = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let coerced_bool = chc_ctx
            .translate_assert_condition(&numeric_operand, &HashSet::new(), 0)
            .expect("numeric operand should coerce to bool");

        assert!(coerced_bool.sort().is_bool(), "coerced condition must be bool sort");
        assert!(
            matches!(coerced_bool.value(), ExprValue::Not(_)),
            "numeric coercion should emit `expr != 0` as a negated equality guard"
        );
    });
}

#[test]
fn test_emit_assert_error_rule_shared_appends_violation_to_shared_base() {
    with_test_ay_ctx_for_source(ASSERT_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_bool");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assert_bool", ChcConfig::default());

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

        let shared_constraints: Arc<[Expr]> = vec![Expr::bool_const(true)].into();
        let before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        chc_ctx.emit_assert_error_rule_shared(
            &from_app,
            Expr::bool_const(true),
            true,
            &shared_constraints,
            0,
            None,
        );

        let after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert_eq!(after, before + 1, "shared assert helper must emit one error rule");

        let error_rule = chc_ctx
            .vc
            .rules
            .iter()
            .rfind(|r| r.head.name == "error")
            .expect("expected emitted error rule");
        assert_eq!(
            error_rule.body.constraints.len(),
            shared_constraints.len() + 1,
            "error rule should include shared constraints plus one violation guard"
        );
    });
}

#[test]
fn test_fn_ptr_constant_true_assert_keeps_error_obligation_after_cleanup() {
    with_test_ay_ctx_for_source(ASSERT_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_bool");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assert_bool", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();
        chc_ctx.fn_ptr_ids.insert(
            "probe_fn_ptr".to_string(),
            Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH),
        );

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let state_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, state_args);
        let shared_constraints: Arc<[Expr]> = vec![Expr::bool_const(true)].into();

        chc_ctx.emit_assert_error_rule_shared(
            &from_app,
            Expr::bool_const(true),
            true,
            &shared_constraints,
            0,
            None,
        );

        assert_eq!(
            chc_ctx.vc.rules.iter().filter(|rule| rule.head.name == "error").count(),
            1,
            "setup must emit one error rule before cleanup"
        );
        assert!(
            chc_ctx
                .vc
                .rules
                .iter()
                .find(|rule| rule.head.name == "error")
                .expect("error rule")
                .body
                .constraints
                .iter()
                .all(|constraint| !matches!(constraint.value(), ExprValue::BoolConst(false))),
            "function-pointer obligation should replace literal false before cleanup"
        );
        chc_ctx.vc.propagate_constants();
        assert_eq!(
            chc_ctx.vc.rules.iter().filter(|rule| rule.head.name == "error").count(),
            1,
            "constant propagation must keep the function-pointer obligation"
        );
        chc_ctx.vc.prune_dead_vars_and_constraints();

        let error_rules: Vec<_> =
            chc_ctx.vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
        assert_eq!(
            error_rules.len(),
            1,
            "function-pointer constant-true assertions must keep a solver-visible error rule"
        );
        assert!(
            error_rules[0]
                .body
                .constraints
                .iter()
                .all(|constraint| !matches!(constraint.value(), ExprValue::BoolConst(false))),
            "the retained obligation must not be a literal false rule that cleanup will erase"
        );
    });
}

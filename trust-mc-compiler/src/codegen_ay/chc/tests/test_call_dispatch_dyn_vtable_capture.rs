// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for `capture_known_vtable_constraint` in `codegen_call_dispatch_dyn`.
//!
//! Part of #4138: this function manages vtable state-variable creation and
//! constraint emission on the critical dyn-dispatch path. A wrong constraint
//! here silently breaks Rc/Arc/Box dyn trait dispatch.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, ExprValue};

const SIMPLE_FN_SOURCE: &str = r#"
    #![allow(dead_code)]
    fn identity(x: u32) -> u32 { x }
"#;

/// Verify that `capture_known_vtable_constraint` returns an Eq constraint
/// binding the vtable output state-var to the provided vtable expression,
/// and that internal tracking state (dyn_vtable_ids, vtable_state_vars) is
/// correctly updated.
#[test]
fn test_capture_known_vtable_constraint_returns_eq_constraint() {
    with_test_ay_ctx_for_source(SIMPLE_FN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 5;
        let vtable_id: u128 = 42;
        let vtable_expr = Expr::bitvec_const(vtable_id, crate::codegen_ay::types::POINTER_WIDTH);

        let constraint = chc_ctx
            .capture_known_vtable_constraint(local_idx, vtable_expr.clone())
            .expect("should return a constraint");

        // The constraint should be an Eq between the output var and vtable_expr.
        match constraint.value() {
            ExprValue::Eq(lhs, rhs) => {
                // One side should be the vtable out var, the other the vtable const.
                let is_var_eq_const = matches!(lhs.value(), ExprValue::Var { name } if name.contains("__vtable_sv_5"))
                    || matches!(rhs.value(), ExprValue::Var { name } if name.contains("__vtable_sv_5"));
                assert!(
                    is_var_eq_const,
                    "Eq constraint should reference __vtable_sv_5; got lhs={:?}, rhs={:?}",
                    lhs.value(),
                    rhs.value()
                );
            }
            other => panic!(
                "Expected Eq constraint from capture_known_vtable_constraint, got {:?}",
                other
            ),
        }
    });
}

/// Verify that `capture_known_vtable_constraint` stores the vtable expression
/// in `dyn_vtable_ids` for later propagation (e.g., Rc clone, deref).
#[test]
fn test_capture_known_vtable_constraint_stores_in_dyn_vtable_ids() {
    with_test_ay_ctx_for_source(SIMPLE_FN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 3;
        let vtable_expr = Expr::bitvec_const(99u128, crate::codegen_ay::types::POINTER_WIDTH);

        assert!(
            chc_ctx.dyn_vtable_ids.get(&local_idx).is_none(),
            "dyn_vtable_ids should be empty before capture"
        );

        chc_ctx.capture_known_vtable_constraint(local_idx, vtable_expr.clone());

        let stored = chc_ctx
            .dyn_vtable_ids
            .get(&local_idx)
            .expect("vtable_expr should be stored in dyn_vtable_ids after capture");
        assert_eq!(
            stored.to_string(),
            vtable_expr.to_string(),
            "stored vtable expr should match the provided one"
        );
    });
}

/// Verify that `capture_known_vtable_constraint` creates a vtable state-var
/// pair (__vtable_sv_N / __vtable_sv_N__out) on first call for a local_idx.
#[test]
fn test_capture_known_vtable_constraint_creates_vtable_state_var() {
    with_test_ay_ctx_for_source(SIMPLE_FN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 7;
        assert!(
            chc_ctx.vtable_state_vars.get(&local_idx).is_none(),
            "vtable_state_vars should be empty before capture"
        );

        let vtable_expr = Expr::bitvec_const(1u128, crate::codegen_ay::types::POINTER_WIDTH);
        chc_ctx.capture_known_vtable_constraint(local_idx, vtable_expr);

        let (in_name, out_name) = chc_ctx
            .vtable_state_vars
            .get(&local_idx)
            .expect("vtable_state_vars should contain entry after capture");
        assert_eq!(&**in_name, "__vtable_sv_7", "input state var name");
        assert_eq!(&**out_name, "__vtable_sv_7__out", "output state var name");
    });
}

/// Verify that calling `capture_known_vtable_constraint` twice for the same
/// local_idx reuses the existing state-var pair (idempotent creation).
#[test]
fn test_capture_known_vtable_constraint_reuses_state_var_on_second_call() {
    with_test_ay_ctx_for_source(SIMPLE_FN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let local_idx = 2;
        let vtable_a = Expr::bitvec_const(10u128, crate::codegen_ay::types::POINTER_WIDTH);
        let vtable_b = Expr::bitvec_const(20u128, crate::codegen_ay::types::POINTER_WIDTH);

        let c1 =
            chc_ctx.capture_known_vtable_constraint(local_idx, vtable_a).expect("first capture");
        let c2 =
            chc_ctx.capture_known_vtable_constraint(local_idx, vtable_b).expect("second capture");

        // Both should produce Eq constraints with the same output var name.
        let extract_var_name = |expr: &Expr| -> Option<String> {
            match expr.value() {
                ExprValue::Eq(lhs, rhs) => {
                    if let ExprValue::Var { name } = lhs.value() {
                        Some(name.to_string())
                    } else if let ExprValue::Var { name } = rhs.value() {
                        Some(name.to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };
        let name1 = extract_var_name(&c1).expect("c1 should have a var");
        let name2 = extract_var_name(&c2).expect("c2 should have a var");
        assert_eq!(name1, name2, "both captures should reference the same output state var");
    });
}

/// Verify that `capture_known_vtable_constraint` for different local indices
/// creates distinct state-var pairs.
#[test]
fn test_capture_known_vtable_constraint_distinct_locals_get_distinct_vars() {
    with_test_ay_ctx_for_source(SIMPLE_FN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let vtable_expr = Expr::bitvec_const(1u128, crate::codegen_ay::types::POINTER_WIDTH);
        chc_ctx.capture_known_vtable_constraint(3, vtable_expr.clone());
        chc_ctx.capture_known_vtable_constraint(8, vtable_expr);

        let (in_3, out_3) = chc_ctx.vtable_state_vars.get(&3).expect("local 3 entry");
        let (in_8, out_8) = chc_ctx.vtable_state_vars.get(&8).expect("local 8 entry");
        assert_ne!(&**in_3, &**in_8, "distinct locals should have distinct input vars");
        assert_ne!(&**out_3, &**out_8, "distinct locals should have distinct output vars");
        assert!(in_3.contains("3") && in_8.contains("8"), "var names should encode local index");
    });
}

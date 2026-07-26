// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for call-result memory bridge helpers.
//!
//! Part of #4138: dedicated MIR-backed coverage for
//! `build_call_result_memory_bridge_constraints` and
//! `try_decompose_flattened_enum_field_stores`.

#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashSet;

use num_bigint::BigInt;

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_result_mem::{
    build_call_result_memory_bridge_constraints, try_decompose_flattened_enum_field_stores,
};
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::TerminatorKind;

const CALL_RESULT_MEM_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn make_result(flag: bool) -> Result<u8, u8> {
        if flag {
            Ok(7)
        } else {
            Err(9)
        }
    }

    pub fn probe_result_bridge(flag: bool) -> u8 {
        match make_result(flag) {
            Ok(value) | Err(value) => value,
        }
    }
"#;

fn find_make_result_dest_local(chc_ctx: &ChcCtx<'_, '_>, body: &rustc_public::mir::Body) -> usize {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind else {
                return None;
            };
            let callee_path = chc_ctx.resolve_callee_path(func)?;
            callee_path.ends_with("make_result").then_some(destination.local)
        })
        .expect("expected make_result() call destination local")
}

fn build_err_result_expr(local_ty: rustc_public::ty::Ty) -> Expr {
    let result_sort = ChcCtx::translate_ty(local_ty).expect("Result<u8, u8> should translate");
    let result_dt = result_sort.datatype_sort().expect("Result<u8, u8> should be a datatype");
    let err_ctor = result_dt
        .constructors
        .iter()
        .find(|ctor| ctor.name.contains("Err"))
        .or_else(|| result_dt.constructors.get(1))
        .expect("Result datatype should expose an Err constructor");
    let payload_sort = err_ctor
        .fields
        .first()
        .map(|field| field.sort.clone())
        .expect("Err constructor should carry one payload");
    Expr::datatype_constructor(
        result_dt.name.clone(),
        err_ctor.name.clone(),
        vec![Expr::bitvec_const(9u64, payload_sort.bitvec_width().expect("u8 payload"))],
        result_sort,
    )
}

fn seed_flattened_result_env(chc_ctx: &mut ChcCtx<'_, '_>, dest_local: usize, result_expr: Expr) {
    let constraints = chc_ctx
        .build_flattened_destination_constraints(dest_local, result_expr)
        .expect("flattened Result destination should decompose into tag + payload");
    assert!(
        !constraints.is_empty(),
        "flattened destination setup should emit at least one field constraint"
    );
    assert!(
        chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 0)),
        "flattened destination setup should cache the Result discriminant"
    );
    assert!(
        chc_ctx.encode.flattened_field_env.contains_key(&(dest_local, 1)),
        "flattened destination setup should cache the Result payload"
    );
}

fn find_output_store_chain_suffix<'a>(constraints: &'a [Expr], suffix: &str) -> &'a Expr {
    constraints
        .iter()
        .find_map(|constraint| match constraint.value() {
            ExprValue::Eq(lhs, rhs) => match lhs.value() {
                ExprValue::Var { name } if name.ends_with(suffix) => Some(rhs),
                _ => None,
            },
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected *{suffix} store chain in constraints: {constraints:?}"))
}

fn collect_nested_stores<'a>(expr: &'a Expr, stores: &mut Vec<(&'a Expr, &'a Expr)>) {
    if let ExprValue::Store { array, index, value } = expr.value() {
        stores.push((index, value));
        collect_nested_stores(array, stores);
    }
}

fn expr_is_bv_const(expr: &Expr, width: u32, value: u128) -> bool {
    match expr.value() {
        ExprValue::BitVecConst { value: actual, width: actual_width } => {
            *actual_width == width && *actual == BigInt::from(value)
        }
        // Bool→BV8 discriminant pattern: ite(cond, BV8(then_val), BV8(else_val))
        // Production code emits this for boolean discriminants (codegen_call_result_mem.rs:182).
        ExprValue::Ite { then_expr, else_expr, .. } => {
            expr_is_bv_const(then_expr, width, value) || expr_is_bv_const(else_expr, width, value)
        }
        _ => false,
    }
}

fn with_result_bridge_ctx(
    body_fn: impl FnOnce(&mut ChcCtx<'_, '_>, rustc_public::ty::Ty, usize) + Send,
) {
    with_test_ay_ctx_for_source(CALL_RESULT_MEM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_bridge");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_result_bridge",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let dest_local = find_make_result_dest_local(&chc_ctx, &body);
        let local_ty = body.locals().get(dest_local).expect("Result local").ty;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local)
                || chc_ctx.flatten.enum_bv_layouts.contains_key(&dest_local),
            "make_result destination local _{dest_local} should be flattened for Result<u8, u8>"
        );

        body_fn(&mut chc_ctx, local_ty, dest_local);
    });
}

#[test]
fn test_build_call_result_memory_bridge_constraints_mirrors_flattened_result_to_mem_u8() {
    with_result_bridge_ctx(|chc_ctx, local_ty, dest_local| {
        seed_flattened_result_env(chc_ctx, dest_local, build_err_result_expr(local_ty));

        let modified_locals = [dest_local].into_iter().collect::<HashSet<_>>();
        let constraints = build_call_result_memory_bridge_constraints(
            chc_ctx,
            dest_local,
            &Expr::bool_const(true),
            &modified_locals,
        );

        // Memory stores are accumulated in heap_state and drained by
        // build_call_result_memory_bridge_constraints (lines 88-89). The
        // output variable names are prefixed with the function name.
        let mem_u8_out = find_output_store_chain_suffix(&constraints, "mem_u8__out");
        let mut stores = Vec::new();
        collect_nested_stores(mem_u8_out, &mut stores);

        assert!(
            stores.len() >= 2,
            "flattened Result bridge should emit at least two mem_u8 stores (tag + payload), got {mem_u8_out}"
        );
        assert!(
            stores.iter().any(|(_, value)| expr_is_bv_const(value, 8, 1)),
            "flattened Result bridge should store the Err discriminant byte, got {mem_u8_out}"
        );
        assert!(
            stores.iter().any(|(_, value)| expr_is_bv_const(value, 8, 9)),
            "flattened Result bridge should store the Err payload byte, got {mem_u8_out}"
        );
    });
}

#[test]
fn test_try_decompose_flattened_enum_field_stores_uses_flattened_env_values() {
    with_result_bridge_ctx(|chc_ctx, local_ty, dest_local| {
        seed_flattened_result_env(chc_ctx, dest_local, build_err_result_expr(local_ty));

        let modified_locals = [dest_local].into_iter().collect::<HashSet<_>>();
        let addr_expr =
            Expr::var("result_addr", Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        let mut constraints = Vec::new();
        chc_ctx.suppress_heap_store_checks = true;
        try_decompose_flattened_enum_field_stores(
            chc_ctx,
            dest_local,
            &addr_expr,
            local_ty,
            &modified_locals,
            &mut constraints,
        );
        // Stores are accumulated in heap_state; drain them like the
        // production caller does (codegen_call_result_mem.rs:88-89).
        constraints.append(&mut chc_ctx.heap_state.pending_updates);
        constraints.append(&mut chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics));

        let mem_u8_out = find_output_store_chain_suffix(&constraints, "mem_u8__out");
        let mut stores = Vec::new();
        collect_nested_stores(mem_u8_out, &mut stores);

        assert!(
            stores.len() >= 2,
            "flattened enum decomposition should emit at least tag + payload stores, got {mem_u8_out}"
        );
        assert!(
            stores.iter().any(|(_, value)| expr_is_bv_const(value, 8, 1)),
            "flattened enum decomposition should store the Err discriminant byte, got {mem_u8_out}"
        );
        assert!(
            stores.iter().any(|(_, value)| expr_is_bv_const(value, 8, 9)),
            "flattened enum decomposition should store the Err payload byte, got {mem_u8_out}"
        );
    });
}

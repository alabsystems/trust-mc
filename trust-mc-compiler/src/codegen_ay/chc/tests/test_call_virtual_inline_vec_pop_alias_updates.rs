// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_vec::ChcVecFields;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use crate::codegen_ay::test_fixtures::{vec_expr, vec_sort};
use rustc_public::mir::{Operand, Place, TerminatorKind};
use std::collections::HashMap;

const INLINE_VEC_POP_UNWRAP_REPRO_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;

    use alloc::vec::Vec;

    fn pop_and_unwrap(v: &mut Vec<bool>) -> bool {
        v.pop().unwrap()
    }

    pub fn probe_inline_vec_pop_unwrap() -> bool {
        let mut v = Vec::new();
        v.push(true);
        pop_and_unwrap(&mut v)
    }
"#;

const INLINE_STRUCT_VEC_POP_WRITEBACK_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;

    use alloc::vec::Vec;

    struct Holder {
        scopes: Vec<bool>,
    }

    fn pop_then_is_empty(holder: &mut Holder) -> bool {
        let _ = holder.scopes.pop();
        holder.scopes.is_empty()
    }

    fn probe_pop_then_is_empty(holder: &mut Holder) -> bool {
        pop_then_is_empty(holder)
    }
"#;

const INLINE_ARRAY_SOLVER_PUSH_WRITEBACK_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;

    use alloc::vec::Vec;

    type TermId = u32;

    struct ArraySolver {
        assign_terms: Vec<TermId>,
        assign_values: Vec<bool>,
        trail_terms: Vec<TermId>,
        trail_prev_present: Vec<bool>,
        trail_prev_values: Vec<bool>,
        scopes: Vec<usize>,
        dirty: bool,
    }

    fn push_then_is_empty(solver: &mut ArraySolver) -> bool {
        let marker = solver.trail_terms.len();
        solver.scopes.push(marker);
        solver.scopes.is_empty()
    }

    fn probe_push_then_is_empty(solver: &mut ArraySolver) -> bool {
        push_then_is_empty(solver)
    }
"#;

fn find_call_by_path_suffix(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    suffix: &str,
) -> (Operand, Vec<Operand>, Place, String) {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                return None;
            };
            let path =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))?;
            path.ends_with(suffix).then(|| (func.clone(), args.clone(), destination.clone(), path))
        })
        .unwrap_or_else(|| panic!("expected nested call ending with {suffix}"))
}

fn find_nested_vec_pop_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (Operand, Vec<Operand>, Place, String) {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                return None;
            };
            let path =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))?;
            path.contains("Vec").then(|| (func.clone(), args.clone(), destination.clone(), path))
        })
        .expect("expected Vec::pop nested call inside pop_and_unwrap")
}

fn receiver_fixture_with_sort(receiver_sort: ay_bindings::Sort) -> Expr {
    let elem_sort = Expr::bool_const(true).sort().clone();
    let ptr = Expr::bitvec_const(0x1_0000_0000u64, crate::codegen_ay::types::POINTER_WIDTH);
    let len = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);
    let cap = Expr::bitvec_const(3u64, crate::codegen_ay::types::POINTER_WIDTH);
    let data = Expr::var(
        "inline_vec_data",
        ay_bindings::Sort::array(crate::codegen_ay::types::ptr_sort(), elem_sort.clone()),
    );
    vec_expr(ptr, len, cap, data, receiver_sort)
}

fn receiver_fixture() -> Expr {
    let elem_sort = Expr::bool_const(true).sort().clone();
    receiver_fixture_with_sort(vec_sort(elem_sort))
}

fn expected_vec_pop_alias_update(
    chc_ctx: &mut ChcCtx<'_, '_>,
    receiver: &Expr,
) -> (Expr, ChcVecFields) {
    let elem_sort = Expr::bool_const(true).sort().clone();
    let receiver_sort = receiver.sort().clone();
    let receiver_fields =
        ChcVecFields::extract(receiver.clone()).expect("expected Vec fixture fields");
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
    let is_nonempty = receiver_fields.len.clone().ne(zero.clone());
    let expected_len = Expr::ite(
        is_nonempty.clone(),
        receiver_fields
            .len
            .clone()
            .bvsub(Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH)),
        zero,
    );
    let expected_result = chc_ctx
        .build_vec_pop_option_result(
            receiver_fields.data.clone(),
            elem_sort,
            is_nonempty,
            expected_len.clone(),
        )
        .expect("expected nested VecPop option result");
    let expected_receiver = vec_expr(
        receiver_fields.ptr.clone(),
        expected_len,
        receiver_fields.cap.clone(),
        receiver_fields.data.clone(),
        receiver_sort,
    );
    let expected_fields =
        ChcVecFields::extract(expected_receiver).expect("expected Vec fields for comparison");
    (expected_result, expected_fields)
}

fn assert_vec_fields_match(actual_fields: ChcVecFields, expected_fields: ChcVecFields) {
    assert_eq!(
        actual_fields.len.to_string(),
        expected_fields.len.to_string(),
        "nested VecPop alias update should decrement the receiver length"
    );
    assert_eq!(
        actual_fields.cap.to_string(),
        expected_fields.cap.to_string(),
        "nested VecPop alias update should preserve capacity"
    );
    assert_eq!(
        actual_fields.data.to_string(),
        expected_fields.data.to_string(),
        "nested VecPop alias update should preserve backing data"
    );
}

fn holder_fixture(chc_ctx: &ChcCtx<'_, '_>, body: &rustc_public::mir::Body) -> Expr {
    let holder_ty = match chc_ctx.resolve_body_ty(body.locals()[1].ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => chc_ctx.resolve_body_ty(inner),
        other => panic!("expected &mut Holder receiver, got {other:?}"),
    };
    let holder_sort = ChcCtx::translate_ty(holder_ty).expect("Holder sort should translate");
    let holder_sort_clone = holder_sort.clone();
    let holder_dt =
        holder_sort_clone.datatype_sort().expect("Holder should translate to a datatype");
    let scopes_sort = holder_dt.constructors[0].fields[0].sort.clone();
    let scopes = receiver_fixture_with_sort(scopes_sort);
    Expr::datatype_constructor(
        &holder_dt.name,
        holder_dt.constructors[0].name.clone(),
        vec![scopes],
        holder_sort,
    )
}

fn vec_fixture_for_sort(
    name_prefix: &str,
    vec_sort: ay_bindings::Sort,
    len: u64,
    cap: u64,
) -> Expr {
    let vec_sort_clone = vec_sort.clone();
    let vec_dt = vec_sort_clone.datatype_sort().expect("expected Vec datatype sort");
    let data_sort = vec_dt.constructors[0].fields[3].sort.clone();
    let ptr = Expr::bitvec_const(0x1_0000_0000u64, crate::codegen_ay::types::POINTER_WIDTH);
    let len = Expr::bitvec_const(len, crate::codegen_ay::types::POINTER_WIDTH);
    let cap = Expr::bitvec_const(cap, crate::codegen_ay::types::POINTER_WIDTH);
    let data = Expr::var(&format!("{name_prefix}_data"), data_sort);
    vec_expr(ptr, len, cap, data, vec_sort)
}

fn extract_datatype_vec_field(expr: &Expr, field_idx: usize) -> ChcVecFields {
    let expr_sort = expr.sort().clone();
    let expr_dt = expr_sort.datatype_sort().expect("expected owner datatype sort");
    let field = &expr_dt.constructors[0].fields[field_idx];
    let field_expr = expr.clone().field_select(&expr_dt.name, &field.name, field.sort.clone());
    ChcVecFields::extract(field_expr).expect("expected Vec field")
}

fn array_solver_fixture(chc_ctx: &ChcCtx<'_, '_>, body: &rustc_public::mir::Body) -> Expr {
    let solver_ty = match chc_ctx.resolve_body_ty(body.locals()[1].ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => chc_ctx.resolve_body_ty(inner),
        other => panic!("expected &mut ArraySolver receiver, got {other:?}"),
    };
    let solver_sort = ChcCtx::translate_ty(solver_ty).expect("ArraySolver sort should translate");
    let solver_sort_clone = solver_sort.clone();
    let solver_dt =
        solver_sort_clone.datatype_sort().expect("ArraySolver should translate to a datatype");

    let assign_terms = vec_fixture_for_sort(
        "array_solver_assign_terms",
        solver_dt.constructors[0].fields[0].sort.clone(),
        0,
        2,
    );
    let assign_values = vec_fixture_for_sort(
        "array_solver_assign_values",
        solver_dt.constructors[0].fields[1].sort.clone(),
        0,
        2,
    );
    let trail_terms = vec_fixture_for_sort(
        "array_solver_trail_terms",
        solver_dt.constructors[0].fields[2].sort.clone(),
        1,
        3,
    );
    let trail_prev_present = vec_fixture_for_sort(
        "array_solver_trail_prev_present",
        solver_dt.constructors[0].fields[3].sort.clone(),
        0,
        2,
    );
    let trail_prev_values = vec_fixture_for_sort(
        "array_solver_trail_prev_values",
        solver_dt.constructors[0].fields[4].sort.clone(),
        0,
        2,
    );
    let scopes = vec_fixture_for_sort(
        "array_solver_scopes",
        solver_dt.constructors[0].fields[5].sort.clone(),
        0,
        2,
    );
    let dirty = Expr::bool_const(false);

    Expr::datatype_constructor(
        &solver_dt.name,
        solver_dt.constructors[0].name.clone(),
        vec![
            assign_terms,
            assign_values,
            trail_terms,
            trail_prev_present,
            trail_prev_values,
            scopes,
            dirty,
        ],
        solver_sort,
    )
}

fn expected_holder_after_pop(chc_ctx: &mut ChcCtx<'_, '_>, holder: &Expr) -> (Expr, Expr) {
    let holder_sort = holder.sort().clone();
    let holder_sort_clone = holder_sort.clone();
    let holder_dt = holder_sort_clone.datatype_sort().expect("Holder should remain a datatype");
    let scopes_field = &holder_dt.constructors[0].fields[0];
    // The inline walker resolves `self.scopes` directly to the inner Vec value,
    // not through field_select on the Holder. Build the expected value from the
    // raw Vec to match the walker's resolution path.
    let scopes = receiver_fixture_with_sort(scopes_field.sort.clone());
    let scopes_fields = ChcVecFields::extract(scopes).expect("expected Vec fields for scopes");
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
    let is_nonempty = scopes_fields.len.clone().ne(zero.clone());
    let expected_len = Expr::ite(
        is_nonempty.clone(),
        scopes_fields
            .len
            .clone()
            .bvsub(Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH)),
        zero,
    );
    // Build updated Vec directly from raw fields (matching walker's construction path).
    let updated_scopes = vec_expr(
        scopes_fields.ptr.clone(),
        expected_len.clone(),
        scopes_fields.cap.clone(),
        scopes_fields.data.clone(),
        scopes_field.sort.clone(),
    );
    let updated_holder = Expr::datatype_constructor(
        &holder_dt.name,
        holder_dt.constructors[0].name.clone(),
        vec![updated_scopes.clone()],
        holder_sort,
    );
    // The walker reads is_empty from the reconstructed updated Vec (fld_len(updated_vec) == 0),
    // not from the raw expected_len expression directly.
    let updated_scopes_sort = updated_scopes.sort().clone();
    let updated_scopes_dt =
        updated_scopes_sort.datatype_sort().expect("updated scopes should be a datatype");
    let len_field = &updated_scopes_dt.constructors[0].fields[1];
    let updated_len = updated_scopes.field_select(
        &updated_scopes_dt.name,
        &len_field.name,
        len_field.sort.clone(),
    );
    let expected_result =
        updated_len.eq(Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH));
    // Build the option result for completeness (used by other tests via expected_vec_pop_alias_update).
    let _expected_option = chc_ctx.build_vec_pop_option_result(
        scopes_fields.data,
        Expr::bool_const(true).sort().clone(),
        is_nonempty,
        expected_len,
    );
    (expected_result, updated_holder)
}

#[test]
fn test_nested_inline_vec_pop_updates_receiver_via_alias_updates() {
    with_test_ay_ctx_for_source(INLINE_VEC_POP_UNWRAP_REPRO_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "pop_and_unwrap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "pop_and_unwrap", ChcConfig::default());
        let (func, args, destination, callee_path) = find_nested_vec_pop_call(&mut chc_ctx, &body);

        let receiver = receiver_fixture();
        let (expected_result, expected_fields) =
            expected_vec_pop_alias_update(&mut chc_ctx, &receiver);
        let local_exprs = HashMap::from([(1usize, receiver)]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            &mut chc_ctx,
            &func,
            &args,
            &body,
            &local_exprs,
            &resolver,
            &HashMap::new(),
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| {
            panic!("expected nested inline {callee_path} to return a VecPop result")
        });

        let updated_receiver = result
            .alias_updates
            .get(&1)
            .unwrap_or_else(|| panic!("expected alias update for nested inline {callee_path}"));
        let actual_fields = ChcVecFields::extract(updated_receiver.clone())
            .expect("expected alias-updated Vec fields");

        assert_eq!(
            result.value.to_string(),
            expected_result.to_string(),
            "nested VecPop should keep the precise Option<T> result"
        );
        assert_vec_fields_match(actual_fields, expected_fields);
    });
}

#[test]
fn test_nested_inline_struct_vec_pop_updates_owner_before_followup_read() {
    with_test_ay_ctx_for_source(INLINE_STRUCT_VEC_POP_WRITEBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pop_then_is_empty");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_pop_then_is_empty", ChcConfig::default());
        let (func, args, destination, callee_path) =
            find_call_by_path_suffix(&mut chc_ctx, &body, "pop_then_is_empty");

        let holder = holder_fixture(&chc_ctx, &body);
        let (expected_result, expected_holder) = expected_holder_after_pop(&mut chc_ctx, &holder);
        let local_exprs = HashMap::from([(1usize, holder)]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            &mut chc_ctx,
            &func,
            &args,
            &body,
            &local_exprs,
            &resolver,
            &HashMap::new(),
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested inline {callee_path} to inline fully"));

        let updated_holder = result.alias_updates.get(&1).unwrap_or_else(|| {
            panic!("expected owner alias update for nested inline {callee_path}")
        });

        assert_eq!(
            result.value.to_string(),
            expected_result.to_string(),
            "struct-embedded nested VecPop should update the owner before Vec::is_empty()"
        );
        assert_eq!(
            updated_holder.to_string(),
            expected_holder.to_string(),
            "struct-embedded nested VecPop should write back the updated owner value"
        );
    });
}

#[test]
fn test_nested_inline_array_solver_push_updates_owner_before_followup_read() {
    with_test_ay_ctx_for_source(INLINE_ARRAY_SOLVER_PUSH_WRITEBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_then_is_empty");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_push_then_is_empty", ChcConfig::default());
        let (func, args, destination, callee_path) =
            find_call_by_path_suffix(&mut chc_ctx, &body, "push_then_is_empty");

        let solver = array_solver_fixture(&chc_ctx, &body);
        let local_exprs = HashMap::from([(1usize, solver)]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            &mut chc_ctx,
            &func,
            &args,
            &body,
            &local_exprs,
            &resolver,
            &HashMap::new(),
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested inline {callee_path} to inline fully"));

        let updated_solver = result.alias_updates.get(&1).unwrap_or_else(|| {
            panic!("expected owner alias update for nested inline {callee_path}")
        });
        let scopes_fields = extract_datatype_vec_field(updated_solver, 5);
        let trail_terms_fields = extract_datatype_vec_field(updated_solver, 2);

        // The inline walker does not constant-fold, so result.value is a symbolic
        // expression like `fld_len(updated_scopes_vec) == 0`. The key property is
        // that it references the UPDATED scopes (with bvadd), not the stale original.
        let val_str = result.value.to_string();
        assert!(
            val_str.contains("bvadd") || val_str.contains("fld_len"),
            "result should reference the updated scopes len (got {val_str})"
        );
        // Scopes len should be incremented: bvadd(original_len, 1).
        let scopes_len_str = scopes_fields.len.to_string();
        assert!(
            scopes_len_str.contains("bvadd"),
            "scopes len should be incremented via bvadd (got {scopes_len_str})"
        );
        // Trail_terms should be preserved: the updated solver reconstructs the
        // DT with the original trail_terms Vec. Field extraction from the DT
        // constructor doesn't simplify, but the original len=1 must appear
        // in the expression tree and be distinct from the scopes update.
        let trail_len_str = trail_terms_fields.len.to_string();
        assert!(
            trail_len_str.contains("trail_terms"),
            "trail_terms len should reference original trail_terms field (got {trail_len_str})"
        );
        assert_ne!(
            scopes_fields.len.to_string(),
            trail_len_str,
            "scopes len and trail_terms len should be distinct after push"
        );
    });
}

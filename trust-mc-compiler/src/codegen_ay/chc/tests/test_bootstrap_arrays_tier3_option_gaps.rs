// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use super::test_bootstrap_arrays_tier3::{
    BOOTSTRAP_ARRAYS_TIER3_SOURCE, reset_bootstrap_arrays_tier3_counters,
};
use crate::codegen_ay::chc::call::codegen_call_vec::ChcVecFields;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use crate::codegen_ay::chc::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::test_fixtures::{vec_expr, vec_sort};
use ay_bindings::Sort;
use rustc_public::mir::{Body, Operand, Place, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap};

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

struct InlineVecPopFixture {
    receiver: Expr,
    receiver_fields: ChcVecFields,
    receiver_sort: Sort,
    elem_sort: Sort,
}

fn with_pop_and_unwrap_ctx<T: Send>(f: impl FnOnce(&mut ChcCtx<'_, '_>, &Body) -> T + Send) -> T {
    let mut result = None;
    with_test_ay_ctx_for_source(INLINE_VEC_POP_UNWRAP_REPRO_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "pop_and_unwrap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "pop_and_unwrap", ChcConfig::default());
        result = Some(f(&mut chc_ctx, &body));
    });
    result.expect("pop_and_unwrap test context should produce a value")
}

fn find_nested_vec_pop_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &Body,
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

fn pop_and_unwrap_receiver_sort(chc_ctx: &ChcCtx<'_, '_>, body: &Body) -> Sort {
    let receiver_ty = match chc_ctx.resolve_body_ty(body.locals()[1].ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => chc_ctx.resolve_body_ty(inner),
        other => panic!("expected &mut Vec receiver for pop_and_unwrap, got {other:?}"),
    };
    ChcCtx::translate_ty(receiver_ty).expect("Vec<bool> receiver sort should translate")
}

fn inline_vec_pop_fixture() -> InlineVecPopFixture {
    let elem_sort = Expr::bool_const(true).sort().clone();
    let receiver_sort = vec_sort(elem_sort.clone());
    let ptr = Expr::bitvec_const(0x1_0000_0000u64, crate::codegen_ay::types::POINTER_WIDTH);
    let len = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);
    let cap = Expr::bitvec_const(3u64, crate::codegen_ay::types::POINTER_WIDTH);
    let data = Expr::var(
        "inline_vec_data",
        ay_bindings::Sort::array(crate::codegen_ay::types::ptr_sort(), elem_sort.clone()),
    );
    let receiver =
        vec_expr(ptr.clone(), len.clone(), cap.clone(), data.clone(), receiver_sort.clone());
    let receiver_fields =
        ChcVecFields::extract(receiver.clone()).expect("expected Vec fixture fields");
    InlineVecPopFixture { receiver, receiver_fields, receiver_sort, elem_sort }
}

fn gap_reasons_for_source_fn(source: &str, fn_name: &str) -> BTreeMap<String, usize> {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
    });

    let aggregate_gaps = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    eprintln!(
        "[arrays_method_gap_reasons {fn_name}] aggregate_gap_count={}, gap_reasons={gap_reasons:?}",
        aggregate_gaps.get(fn_name).copied().unwrap_or(0),
    );
    reset_bootstrap_arrays_tier3_counters();
    gap_reasons
}

fn arrays_method_gap_reasons(fn_name: &str) -> BTreeMap<String, usize> {
    gap_reasons_for_source_fn(BOOTSTRAP_ARRAYS_TIER3_SOURCE, fn_name)
}

#[test]
fn test_array_solver_pop_has_no_option_unwrap_symbolic_gap_reasons() {
    let gap_reasons = arrays_method_gap_reasons("ArraySolver::pop");
    assert_eq!(
        gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
        0,
        "ArraySolver::pop should not overapproximate internal VecPop unwrap payloads: {gap_reasons:?}"
    );
}

#[test]
fn test_array_solver_record_assignment_has_no_option_unwrap_symbolic_gap_reasons() {
    let gap_reasons = arrays_method_gap_reasons("ArraySolver::record_assignment");
    assert_eq!(
        gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
        0,
        "ArraySolver::record_assignment should not overapproximate previous.unwrap_or(false): {gap_reasons:?}"
    );
}

#[test]
fn test_inline_vec_pop_unwrap_has_no_option_unwrap_symbolic_gap_reasons() {
    let gap_reasons = gap_reasons_for_source_fn(
        INLINE_VEC_POP_UNWRAP_REPRO_SOURCE,
        "probe_inline_vec_pop_unwrap",
    );
    assert_eq!(
        gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
        0,
        "nested inline Vec::pop().unwrap() should preserve exact payload extraction: {gap_reasons:?}"
    );
}

#[test]
fn test_nested_inline_vec_pop_result_unwraps_without_symbolic_fallback() {
    with_pop_and_unwrap_ctx(|chc_ctx, body| {
        let (func, args, destination, callee_path) = find_nested_vec_pop_call(chc_ctx, body);
        let receiver_sort = pop_and_unwrap_receiver_sort(chc_ctx, body);
        let local_exprs =
            HashMap::from([(1usize, Expr::var("inline_vec_receiver", receiver_sort))]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            body,
            &local_exprs,
            &resolver,
            &HashMap::new(),
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested inline {callee_path} to return an Option"));

        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();
        let unwrapped = chc_ctx
            .option_unwrap_value(result.value.clone())
            .expect("nested Vec::pop result should unwrap");
        eprintln!(
            "[nested inline VecPop] callee_path={callee_path}, option_result={}, unwrapped={}",
            result.value, unwrapped
        );
        assert_eq!(
            chc_ctx.diagnostics.stub_approximation.get(),
            before_stub_approx,
            "nested Vec::pop result should unwrap without allocating a symbolic fallback payload"
        );
    });
}

#[test]
fn test_nested_inline_vec_pop_updates_receiver_via_alias_updates() {
    with_pop_and_unwrap_ctx(|chc_ctx, body| {
        let (func, args, destination, callee_path) = find_nested_vec_pop_call(chc_ctx, body);
        let fixture = inline_vec_pop_fixture();
        let local_exprs = HashMap::from([(1usize, fixture.receiver.clone())]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            body,
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
        let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
        let is_nonempty = fixture.receiver_fields.len.clone().ne(zero.clone());
        let expected_len = Expr::ite(
            is_nonempty.clone(),
            fixture
                .receiver_fields
                .len
                .bvsub(Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH)),
            zero,
        );
        let expected_result = chc_ctx
            .build_vec_pop_option_result(
                fixture.receiver_fields.data.clone(),
                fixture.elem_sort,
                is_nonempty,
                expected_len.clone(),
            )
            .expect("expected nested VecPop option result");
        let expected_receiver = vec_expr(
            fixture.receiver_fields.ptr.clone(),
            expected_len.clone(),
            fixture.receiver_fields.cap.clone(),
            fixture.receiver_fields.data.clone(),
            fixture.receiver_sort,
        );
        let expected_fields =
            ChcVecFields::extract(expected_receiver).expect("expected Vec fields for comparison");
        let actual_fields = ChcVecFields::extract(updated_receiver.clone())
            .expect("expected alias-updated Vec fields");

        assert_eq!(
            result.value.to_string(),
            expected_result.to_string(),
            "nested VecPop should keep the precise Option<T> result"
        );
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
    });
}

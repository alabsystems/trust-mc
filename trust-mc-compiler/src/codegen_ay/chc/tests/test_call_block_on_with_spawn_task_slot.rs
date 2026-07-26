// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Task-slot regression coverage for `block_on_with_spawn`.
//!
//! Part of #4075.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::{
    InlineReturn, nested_option_state::try_inline_option_state_call,
};
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::{
    OptionHelpers, option_value_sort,
};
use crate::codegen_ay::names::enum_sort;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue, Sort};
use num_bigint::BigInt;
use rustc_public::mir::TerminatorKind;
use std::collections::{BTreeMap, HashMap};

const SPAWN_TASK_SLOT_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::{
        future::Future,
        pin::Pin,
        task::{Context, Poll},
    };

    type BoxFuture = Pin<Box<dyn Future<Output = ()> + Sync + 'static>>;

    pub fn probe_spawn_task_slot(task: &mut Option<BoxFuture>, cx: &mut Context<'_>) {
        if let Some(fut) = task.as_mut() {
            match fut.as_mut().poll(cx) {
                Poll::Ready(()) => {
                    let _prev = task.take();
                }
                Poll::Pending => {}
            }
        }
    }
"#;

fn reset_spawn_task_slot_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    reset_spawn_task_slot_aggregate_gap_metadata();
}

fn expr_is_bv_const(expr: &Expr, width: u32, value: u128) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value: actual, width: actual_width }
            if *actual_width == width && *actual == BigInt::from(value)
    )
}

fn expr_is_option_none_constructor(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::DatatypeConstructor { constructor_name, args, .. }
            if crate::codegen_ay::names::is_none_constructor(constructor_name) =>
        {
            args.is_empty()
        }
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 2 => {
            matches!(args[0].value(), ExprValue::BoolConst(false))
        }
        _ => false,
    }
}

fn option_constructor_payload(expr: &Expr) -> Option<&Expr> {
    match expr.value() {
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => args.first(),
        ExprValue::DatatypeConstructor { args, .. } if args.len() == 2 => args.get(1),
        _ => None,
    }
}

fn expr_var_name_starts_with(expr: &Expr, prefix: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name.starts_with(prefix))
}

fn reset_spawn_task_slot_aggregate_gap_metadata() {
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
}

fn assert_single_spawn_task_slot_aggregate_gap(reason: &str) {
    let gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let gap_by_fn = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let gap_reasons_by_fn = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
    let fn_gap_reasons =
        gap_reasons_by_fn.get("probe_spawn_task_slot").cloned().unwrap_or_default();
    assert_eq!(gap_count, 1, "fallback path should record one aggregate gap");
    if !gap_by_fn.is_empty() {
        assert_eq!(
            gap_by_fn.get("probe_spawn_task_slot").copied().unwrap_or(0),
            1,
            "fallback path should attribute one aggregate gap to probe_spawn_task_slot: {gap_by_fn:?}"
        );
    }
    assert_eq!(
        fn_gap_reasons.get(reason).copied().unwrap_or(0),
        1,
        "fallback path should record the named aggregate-gap reason: {gap_reasons_by_fn:?}"
    );
}

fn translate_spawn_task_slot_probe() -> BTreeMap<String, BTreeMap<String, usize>> {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_spawn_task_slot_metadata();

    with_test_ay_ctx_for_source(SPAWN_TASK_SLOT_SOURCE, |ctx| {
        let fn_name = "probe_spawn_task_slot";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        // After #4071 DST string backing fix, the expanded resolve chain
        // may add 1 additional translation drop for ptr_metadata fallthrough.
        assert!(
            diagnostics.place_translation_drop.get() <= 2,
            "{fn_name} should stay narrow on the task-slot probe; \
             got {} drops",
            diagnostics.place_translation_drop.get()
        );
    });

    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
}

fn with_spawn_task_slot_ctx<T: Send>(
    f: impl FnOnce(&mut ChcCtx<'_, '_>, &rustc_public::mir::Body) -> T + Send,
) -> T {
    let mut result = None;
    with_test_ay_ctx_for_source(SPAWN_TASK_SLOT_SOURCE, |ctx| {
        let fn_name = "probe_spawn_task_slot";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        result = Some(f(&mut chc_ctx, &body));
    });
    result.expect("spawn task-slot test closure should produce a result")
}

fn find_spawn_task_slot_as_mut_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (rustc_public::mir::Operand, Vec<rustc_public::mir::Operand>, rustc_public::mir::Place, String)
{
    find_spawn_task_slot_call(chc_ctx, body, "as_mut")
}

fn find_spawn_task_slot_take_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (rustc_public::mir::Operand, Vec<rustc_public::mir::Operand>, rustc_public::mir::Place, String)
{
    find_spawn_task_slot_call(chc_ctx, body, "take")
}

fn find_spawn_task_slot_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    method_name: &str,
) -> (rustc_public::mir::Operand, Vec<rustc_public::mir::Operand>, rustc_public::mir::Place, String)
{
    let call_sites: Vec<_> = body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => chc_ctx
                .resolve_callee_path(func)
                .map(|path| (func.clone(), args.clone(), destination.clone(), path)),
            _ => None,
        })
        .collect();
    let available_paths: Vec<_> = call_sites.iter().map(|(_, _, _, path)| path.clone()).collect();
    call_sites
        .into_iter()
        .find(|(_, _, _, path)| {
            path.ends_with(&format!("::{method_name}")) && path.contains("Option")
        })
        .unwrap_or_else(|| {
            panic!("expected Option::{method_name} call in probe, saw {available_paths:?}")
        })
}

#[test]
fn test_spawn_task_slot_probe_stays_narrow_in_single_unit() {
    let translation_sites = translate_spawn_task_slot_probe();
    let fn_sites = translation_sites.get("probe_spawn_task_slot").cloned().unwrap_or_default();

    // Worker vtable_prop expansion may introduce virtual_missing_vtable for
    // intermediate trait-object projections. Accept up to 1 (over-approximation, sound).
    let vtable_missing = fn_sites.get("virtual_missing_vtable").copied().unwrap_or(0);
    assert!(
        vtable_missing <= 1,
        "single-unit task-slot probe virtual_missing_vtable should be <=1; \
         got {vtable_missing}; the remaining #4075 gap is in the real library scheduler lane: {fn_sites:?}"
    );
}

#[test]
fn test_spawn_task_slot_option_as_mut_has_no_vtable_without_model() {
    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (func, args, destination, callee_path) =
            find_spawn_task_slot_as_mut_call(chc_ctx, body);
        let local_exprs =
            HashMap::from([(1usize, Expr::var("task_slot_ptr", Sort::bitvec(POINTER_WIDTH)))]);
        let inline_vtable_ids = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested helper call {callee_path} to inline"));

        assert!(
            result.vtable.is_none(),
            "{callee_path} should not synthesize a vtable without the spawn scheduler model"
        );
        assert!(
            result.alias_updates.is_empty(),
            "{callee_path} should not mutate the receiver in the nested-call fast path"
        );
    });
}

#[test]
fn test_spawn_task_slot_option_as_mut_seeds_modeled_vtable() {
    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (func, args, destination, callee_path) =
            find_spawn_task_slot_as_mut_call(chc_ctx, body);
        chc_ctx.spawn_scheduler_vtable_model =
            Some(crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
                poll_vtable_ids: vec![11],
                next_poll_idx: 0,
                poll_task_indices: vec![0],
                next_task_idx: 0,
                current_task_vtable_id: None,
                scheduler_loop_replay_fuel: None,
            });

        let local_exprs =
            HashMap::from([(1usize, Expr::var("task_slot_ptr", Sort::bitvec(POINTER_WIDTH)))]);
        let inline_vtable_ids = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested helper call {callee_path} to inline"));

        let vtable = result
            .vtable
            .expect("spawn task-slot bridge should seed the Option::as_mut result vtable");
        assert!(
            expr_is_bv_const(&vtable, POINTER_WIDTH, 11),
            "spawn task-slot bridge should use the first modeled poll vtable, got {vtable}"
        );
        assert_eq!(
            chc_ctx.spawn_scheduler_vtable_model.as_ref().expect("spawn model").next_poll_idx,
            1,
            "seeding the task-slot Option::as_mut result should consume exactly one modeled poll vtable"
        );
        assert_eq!(
            chc_ctx
                .spawn_scheduler_vtable_model
                .as_ref()
                .expect("spawn model")
                .current_task_vtable_id,
            Some(11),
            "seeding the task-slot Option::as_mut result should remember the active task vtable"
        );
    });
}

fn run_inline_step(
    chc_ctx: &mut ChcCtx<'_, '_>,
    func: &rustc_public::mir::Operand,
    args: &[rustc_public::mir::Operand],
    body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    destination: &rustc_public::mir::Place,
    callee_label: &str,
) -> crate::codegen_ay::chc::call::codegen_call_virtual_inline::InlineReturn {
    let inline_vtable_ids = HashMap::new();
    try_inline_nested_call_step(
        chc_ctx,
        func,
        args,
        body,
        local_exprs,
        resolver,
        &inline_vtable_ids,
        &HashMap::new(),
        destination,
        0,
    )
    .unwrap_or_else(|| panic!("expected nested helper call {callee_label} to inline"))
}

fn option_as_mut_destination_sort(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Sort {
    destination
        .ty(body.locals())
        .ok()
        .map(|ty| chc_ctx.resolve_body_ty(ty))
        .and_then(ChcCtx::translate_ty)
        .expect("Option::as_mut destination should translate to an Option-like sort")
}

fn assert_fallback_as_mut_result(
    chc_ctx: &ChcCtx<'_, '_>,
    result: &InlineReturn,
    receiver: &Expr,
    dest_sort: &Sort,
    dest_payload_sort: &Sort,
) {
    assert_eq!(result.value.sort(), dest_sort, "as_mut result should use destination sort");
    match result.value.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            assert_eq!(
                cond,
                &chc_ctx.option_is_some(receiver.clone()),
                "fallback must still be guarded by the receiver discriminator"
            );
            assert!(
                expr_is_option_none_constructor(else_expr),
                "fallback None branch should remain destination-shaped None"
            );
            let fallback_payload = option_constructor_payload(then_expr)
                .expect("fallback Some branch should carry a payload");
            assert_eq!(
                fallback_payload.sort(),
                dest_payload_sort,
                "fallback payload should use the destination payload sort"
            );
            assert!(
                expr_var_name_starts_with(fallback_payload, "option_as_mut_ref"),
                "fallback payload should be an explicit fresh as_mut referent"
            );
        }
        other => panic!("expected destination-shaped guarded Option ITE, got {other:?}"),
    }
}

#[test]
fn test_spawn_task_slot_option_take_reuses_active_vtable() {
    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (as_mut_func, as_mut_args, as_mut_dest, _) =
            find_spawn_task_slot_as_mut_call(chc_ctx, body);
        let (take_func, take_args, take_dest, _) = find_spawn_task_slot_take_call(chc_ctx, body);
        chc_ctx.spawn_scheduler_vtable_model =
            Some(crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
                poll_vtable_ids: vec![11, 22],
                next_poll_idx: 0,
                poll_task_indices: vec![0, 1],
                next_task_idx: 0,
                current_task_vtable_id: None,
                scheduler_loop_replay_fuel: None,
            });

        let local_exprs =
            HashMap::from([(1usize, Expr::var("task_slot_ptr", Sort::bitvec(POINTER_WIDTH)))]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let as_mut_result = run_inline_step(
            chc_ctx,
            &as_mut_func,
            &as_mut_args,
            body,
            &local_exprs,
            &resolver,
            &as_mut_dest,
            "as_mut",
        );
        let as_mut_vtable = as_mut_result.vtable.expect("as_mut should seed vtable");
        assert!(expr_is_bv_const(&as_mut_vtable, POINTER_WIDTH, 11), "as_mut got {as_mut_vtable}");

        let take_result = run_inline_step(
            chc_ctx,
            &take_func,
            &take_args,
            body,
            &local_exprs,
            &resolver,
            &take_dest,
            "take",
        );
        let take_vtable = take_result.vtable.expect("take should seed vtable");
        assert!(expr_is_bv_const(&take_vtable, POINTER_WIDTH, 11), "take got {take_vtable}");

        let take_sort = take_dest
            .ty(body.locals())
            .ok()
            .map(|ty| chc_ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)
            .expect("take destination should translate");
        let expected_none =
            chc_ctx.make_none_expr_for_option(&take_sort).expect("take should build None");
        assert_eq!(
            take_result.alias_updates.get(&1),
            Some(&expected_none),
            "take should clear slot"
        );

        let model = chc_ctx.spawn_scheduler_vtable_model.as_ref().expect("spawn model");
        assert_eq!(model.next_poll_idx, 1, "take should not advance poll schedule");
        assert_eq!(model.current_task_vtable_id, None, "take should clear active slot");
    });
}

#[test]
fn test_option_as_mut_fast_path_reconstructs_same_sort_with_fresh_payload_without_provenance() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_spawn_task_slot_aggregate_gap_metadata();

    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (_, _, destination, _) = find_spawn_task_slot_as_mut_call(chc_ctx, body);
        let option_sort = destination
            .ty(body.locals())
            .ok()
            .map(|ty| chc_ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)
            .expect("Option::as_mut destination should translate to an Option-like sort");
        let payload_sort = option_value_sort(&option_sort)
            .expect("Option::as_mut destination should expose a payload sort");
        let receiver = chc_ctx
            .make_some_expr_for_option(
                Expr::var("option_as_mut_payload", payload_sort.clone()),
                &option_sort,
            )
            .expect("Option::as_mut fast path should build a Some receiver");
        let local_exprs = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();

        let result = try_inline_option_state_call(
            chc_ctx,
            "core::option::Option::<u64>::as_mut",
            &[],
            std::slice::from_ref(&receiver),
            body,
            &destination,
            &local_exprs,
            &resolver,
        )
        .expect("Option::as_mut fast path should trigger on Option-like receivers");

        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap + 1,
            "as_mut should record the guarded reconstruction payload only after it is emitted"
        );
        assert_fallback_as_mut_result(chc_ctx, &result, &receiver, &option_sort, &payload_sort);
    });

    assert_single_spawn_task_slot_aggregate_gap("option_as_mut_payload_unconstrained");
}

#[test]
fn test_option_as_mut_fast_path_does_not_reuse_sort_only_receiver_payload() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_spawn_task_slot_aggregate_gap_metadata();

    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (_, _, destination, _) = find_spawn_task_slot_as_mut_call(chc_ctx, body);
        let dest_sort = option_as_mut_destination_sort(chc_ctx, body, &destination);
        let payload_sort = option_value_sort(&dest_sort)
            .expect("Option::as_mut destination should expose a payload sort");
        let receiver_sort = enum_sort(
            "LaneCGOptionAsMutReceiver",
            vec![("Missing", vec![]), ("Present", vec![("payload", payload_sort.clone())])],
        );
        assert_ne!(
            &receiver_sort, &dest_sort,
            "test precondition: receiver and destination option sorts should differ"
        );
        let payload = Expr::var("option_as_mut_receiver_payload", payload_sort.clone());
        let receiver = chc_ctx
            .make_some_expr_for_option(payload.clone(), &receiver_sort)
            .expect("Option::as_mut fast path should build a Some receiver");
        let local_exprs = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();

        let result = try_inline_option_state_call(
            chc_ctx,
            "core::option::Option::<u64>::as_mut",
            &[],
            std::slice::from_ref(&receiver),
            body,
            &destination,
            &local_exprs,
            &resolver,
        )
        .expect("Option::as_mut fast path should shape mismatched Option sorts");

        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap + 1,
            "as_mut should not reuse receiver payload solely because the payload sorts match"
        );
        assert_fallback_as_mut_result(chc_ctx, &result, &receiver, &dest_sort, &payload_sort);
    });

    assert_single_spawn_task_slot_aggregate_gap("option_as_mut_payload_unconstrained");
}

#[test]
fn test_option_as_mut_fast_path_guards_fresh_payload_when_receiver_payload_unusable() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_spawn_task_slot_aggregate_gap_metadata();

    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (_, _, destination, _) = find_spawn_task_slot_as_mut_call(chc_ctx, body);
        let dest_sort = option_as_mut_destination_sort(chc_ctx, body, &destination);
        let dest_payload_sort = option_value_sort(&dest_sort)
            .expect("Option::as_mut destination should expose a payload sort");
        let source_payload_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
        let receiver_sort = enum_sort(
            "LaneCGOptionAsMutFallbackReceiver",
            vec![("Missing", vec![]), ("Present", vec![("payload", source_payload_sort.clone())])],
        );
        let source_payload = Expr::var("option_as_mut_unusable_payload", source_payload_sort);
        let receiver = chc_ctx
            .make_some_expr_for_option(source_payload, &receiver_sort)
            .expect("Option::as_mut fast path should build a Some receiver");
        let local_exprs = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();

        let result = try_inline_option_state_call(
            chc_ctx,
            "core::option::Option::<u64>::as_mut",
            &[],
            std::slice::from_ref(&receiver),
            body,
            &destination,
            &local_exprs,
            &resolver,
        )
        .expect("Option::as_mut fast path should use a guarded fallback payload");

        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap + 1,
            "as_mut should record the explicit guarded unconstrained-payload fallback"
        );
        assert_fallback_as_mut_result(chc_ctx, &result, &receiver, &dest_sort, &dest_payload_sort);
    });

    assert_single_spawn_task_slot_aggregate_gap("option_as_mut_payload_unconstrained");
}

#[test]
fn test_option_take_fast_path_returns_receiver_and_clears_alias() {
    with_spawn_task_slot_ctx(|chc_ctx, body| {
        let (_, _, destination, _) = find_spawn_task_slot_take_call(chc_ctx, body);
        let option_sort = destination
            .ty(body.locals())
            .ok()
            .map(|ty| chc_ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)
            .expect("Option::take destination should translate to an Option-like sort");
        let payload_sort = option_value_sort(&option_sort)
            .expect("Option::take destination should expose a payload sort");
        let receiver = chc_ctx
            .make_some_expr_for_option(Expr::var("option_take_payload", payload_sort), &option_sort)
            .expect("Option::take fast path should build a Some receiver");
        let expected_none = chc_ctx
            .make_none_expr_for_option(&option_sort)
            .expect("Option::take fast path should build the cleared receiver state");
        let local_exprs = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        let result = try_inline_option_state_call(
            chc_ctx,
            "core::option::Option::<u64>::take",
            &[],
            std::slice::from_ref(&receiver),
            body,
            &destination,
            &local_exprs,
            &resolver,
        )
        .expect("Option::take fast path should trigger on Option-like receivers");

        assert_eq!(result.value, receiver, "Option::take should return the pre-take receiver");
        assert_eq!(
            result.alias_updates.get(&1),
            Some(&expected_none),
            "Option::take should clear the aliased receiver to None"
        );
    });
}

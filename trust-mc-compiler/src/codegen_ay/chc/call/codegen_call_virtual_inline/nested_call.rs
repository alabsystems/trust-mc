// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Nested call inlining (fn-def, fn-ptr, closure, virtual). Part of #3159, #3335, #3639.
use super::super::ChcCtx;
use super::super::codegen_call_cmp_string::misc_intrinsics::{
    MiscIntrinsicKind, detect_misc_intrinsic,
};
use super::super::codegen_call_cmp_string::misc_intrinsics_write_bytes::zero_expr_for_ty;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::{
    build_inline_subslice_maps_from_args, translate_inline_body_with_metadata,
};
use super::super::inline_bool_return::try_inline_simple_bool_return_helper;
use super::super::inline_field_map::populate_inline_self_field_hints_for_arg;
use super::super::inline_known_calls::inline_known_call_expr_for_callee_path;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use super::dispatch::build_dispatch_ite_chain_impl;
use super::drop_placeholders::{
    inline_trivial_drop_placeholder, inline_trivial_hashbrown_drop_elements_placeholder,
    try_inline_dyn_drop_call, try_inline_shared_pointer_drop_call,
};
use super::fn_trait_dispatch::{is_fn_trait_call, try_fn_trait_direct_dispatch};
use super::inline_alloc_helpers::{emit_inline_alloc_metadata, inline_alloc_size_expr};
use super::inline_call_classify::{
    is_inline_alloc_call, is_inline_noop_call, is_inline_pointer_identity_call,
    is_inline_ub_precondition_noop, is_inline_vec_internal_noop,
};
use super::pointer_wrapper::{
    try_inline_box_new, try_inline_pointer_wrapper_deref, try_inline_rc_arc_new,
};
use super::register_contract::{nested_fn_trait_closure_captures, try_inline_register_contract};
use super::result_copied::try_inline_result_copied_call;
use super::{InlineReturn, receiver_base_local};
use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::attributes;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::BTreeMap;
use std::collections::HashMap;
use tracing::debug;

use super::nested_option_state::try_inline_option_state_call;
use super::nested_option_unwrap::{
    inline_formatting_call_placeholder, try_inline_option_unwrap_call,
};
use super::nested_spawn_schedule::try_inline_round_robin_pick_task_call;
use super::nested_string_leaf::{try_inline_str_nth_call, try_inline_str_nth_const_fold};
use super::nested_vec_pop::try_inline_vec_pop_call;
use super::nested_vec_push::try_inline_vec_push_call;
fn nested_caller_vtable_ids(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
    inline_vtable_ids: &HashMap<usize, Expr>,
) -> HashMap<usize, Expr> {
    let mut caller_vtable_ids = HashMap::new();
    for (i, arg) in args.iter().enumerate() {
        if let Some(local_idx) = receiver_base_local(arg)
            && let Some(vtable) = inline_vtable_ids
                .get(&local_idx)
                .cloned()
                .or_else(|| ctx.known_vtable_expr_for_local(local_idx))
        {
            caller_vtable_ids.insert(i + 1, vtable);
        }
    }
    caller_vtable_ids
}
/// Fully-resolved inline callee metadata. Part of #3768.
struct ResolvedInlineCallee {
    canonical_path: String,
    instance: Option<Instance>,
}

/// Resolve call operand against outer_body with full generic normalization.
fn resolve_inline_callee(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    outer_body: &rustc_public::mir::Body,
) -> Option<ResolvedInlineCallee> {
    let raw_func_ty = func.ty(outer_body.locals()).ok()?;
    let func_ty = ctx.resolve_body_ty(raw_func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        // Part of #4161: a few std/core nested calls keep a raw FnDef shape
        // but lose it under body-ty normalization. The terminator fallback can
        // still recover these paths, so keep the same visibility here and let
        // precise pre-translation handlers run before the symbolic fallback.
        _ => match raw_func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None,
        },
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok();
    let def_id = instance.as_ref().map_or_else(|| fn_def.def_id(), |inst| inst.def.def_id());
    let internal_def_id = rustc_internal::internal(ctx.tcx, def_id);
    let canonical_path = ctx.tcx.def_path_str(internal_def_id);
    Some(ResolvedInlineCallee { canonical_path, instance })
}

/// Inline `TypeId::of::<T>()` as a constant bv128 expression.
///
/// `TypeId::of::<T>()` is a nullary const fn that returns a 128-bit type
/// identity value. In MIR, the compiler may or may not const-evaluate it.
/// When it remains as a call (e.g., inside provided trait method bodies),
/// the inline walker has no handler for the `type_id` intrinsic and falls
/// through to symbolic fallback, producing unconstrained TypeId values.
/// This breaks `<dyn Error>::is::<T>()` which compares two TypeIds.
///
/// Part of #1739.
fn try_inline_type_id_of(
    ctx: &ChcCtx<'_, '_>,
    callee_path: &str,
    func: &Operand,
    outer_body: &rustc_public::mir::Body,
) -> Option<InlineReturn> {
    // Detect `TypeId::of`, `any::TypeId::of`, or the underlying intrinsic.
    let is_type_id_of = callee_path.ends_with("::of")
        && (callee_path.contains("TypeId") || callee_path.contains("any::"));
    let is_type_id_intrinsic =
        callee_path.contains("intrinsics") && callee_path.contains("type_id");
    if !is_type_id_of && !is_type_id_intrinsic {
        return None;
    }
    // Extract the type parameter T from the generic args.
    let func_ty = func.ty(outer_body.locals()).ok()?;
    let func_ty = ctx.resolve_body_ty(func_ty);
    let fn_substs = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
        _ => return None,
    };
    let target_ty = fn_substs
        .0
        .iter()
        .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(*ty) } else { None })?;
    // Only handle concrete (monomorphized) types.
    if matches!(target_ty.kind(), TyKind::Param(_)) {
        return None;
    }
    let type_id_expr = type_id_expr_for_ty(ctx, target_ty)?;
    debug!(
        %callee_path,
        ?target_ty,
        "nested call: inline TypeId::of as constant bv128"
    );
    Some(InlineReturn::value_only(type_id_expr))
}

fn type_id_expr_for_ty(ctx: &ChcCtx<'_, '_>, ty: rustc_public::ty::Ty) -> Option<Expr> {
    if matches!(ty.kind(), TyKind::Param(_)) {
        return None;
    }
    let internal_ty = rustc_internal::internal(ctx.tcx, ty);
    let type_id_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ctx.tcx.type_id_hash(internal_ty).as_u128()
    }));
    Some(Expr::bitvec_const(type_id_result.ok()?, 128))
}

fn is_error_type_id_virtual_path(callee_path: &str) -> bool {
    callee_path.ends_with("::Error::type_id") && callee_path.contains("::error::")
}

fn try_inline_virtual_error_type_id(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    candidates: &[super::super::dyn_coercion::DynCandidate],
    vtable_disc: Expr,
) -> Option<InlineReturn> {
    if !is_error_type_id_virtual_path(callee_path) {
        return None;
    }

    let mut type_ids = Vec::new();
    for candidate in candidates {
        if let Some(type_id) = type_id_expr_for_ty(ctx, candidate.concrete_ty) {
            type_ids.push((candidate.vtable_id, type_id));
        }
    }
    if type_ids.is_empty() {
        return None;
    }

    if let ay_bindings::ExprValue::BitVecConst { value, .. } = vtable_disc.value() {
        let disc_u64 = value.to_u64_digits().1.first().copied().unwrap_or(0);
        if let Some((_, type_id)) = type_ids.iter().find(|(id, _)| *id == disc_u64) {
            debug!(
                vtable_id = disc_u64,
                %callee_path,
                "nested call: inline virtual Error::type_id from constant vtable"
            );
            return Some(InlineReturn::value_only(type_id.clone()));
        }
    }

    let mut result = super::super::declare_pending_var(
        super::super::chc_fresh_name("__virtual_error_type_id"),
        Sort::bitvec(128),
    );
    for (vtable_id, type_id) in type_ids.into_iter().rev() {
        let cond = vtable_disc.clone().eq(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
        result = Expr::ite(cond, type_id, result);
    }
    debug!(%callee_path, "nested call: inline virtual Error::type_id by vtable");
    Some(InlineReturn::value_only(result))
}

fn try_inline_misc_intrinsic_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    let destination_ty =
        || destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty));

    match detect_misc_intrinsic(callee_path)? {
        MiscIntrinsicKind::MemZeroed => {
            let zero_expr = zero_expr_for_ty(destination_ty()?)?;
            Some(InlineReturn::value_only(zero_expr))
        }
        MiscIntrinsicKind::AssertZeroValid
        | MiscIntrinsicKind::AssertMemUninitializedValid
        | MiscIntrinsicKind::Forget => Some(InlineReturn::value_only(Expr::bool_const(true))),
        MiscIntrinsicKind::MaybeUninitUninit | MiscIntrinsicKind::MemUninitialized => {
            let dest_sort = ChcCtx::translate_ty(destination_ty()?)?;
            let fresh = super::super::declare_pending_var(
                super::super::chc_fresh_name("__inline_misc_intrinsic"),
                dest_sort,
            );
            Some(InlineReturn::value_only(fresh))
        }
        _ => None,
    }
}

fn try_inline_kani_any_modifies_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !(callee_path.contains("kani::") && callee_path.rsplit("::").next() == Some("any_modifies"))
    {
        return None;
    }
    let destination_ty =
        destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty))?;
    let dest_sort = ChcCtx::translate_ty(destination_ty)?;
    let fresh = super::super::declare_pending_var(
        super::super::chc_fresh_name("__kani_any_modifies_inline"),
        dest_sort,
    );
    debug!(%callee_path, "nested call: inline kani::any_modifies as fresh value");
    Some(InlineReturn::value_only(fresh))
}

fn try_inline_slice_as_ptr_call(
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<InlineReturn> {
    let is_slice_as_ptr = callee_path.contains("slice::<impl")
        && matches!(callee_path.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr"));
    if !is_slice_as_ptr || translated_args.len() != 1 {
        return None;
    }
    let receiver = translated_args[0].clone();
    let ptr = super::super::dyn_coercion::extract_pointer_expr(&receiver).unwrap_or(receiver);
    if ptr.sort().bitvec_width() == Some(POINTER_WIDTH) {
        debug!(%callee_path, "nested call: inline slice::as_ptr/as_mut_ptr as data pointer");
        Some(InlineReturn::value_only(ptr))
    } else {
        None
    }
}

pub(in crate::codegen_ay::chc) fn try_inline_nested_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    inline_alloc_ids: &HashMap<usize, u32>,
    destination: &rustc_public::mir::Place,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let caller_vtable_ids = nested_caller_vtable_ids(ctx, args, inline_vtable_ids);
    let (caller_subslice_lens, caller_subslice_offsets) =
        build_inline_subslice_maps_from_args(ctx, args);

    // Resolve the callee once, body-relative, with full generic normalization.
    // All downstream paths reuse this instead of re-resolving from raw FnDef.
    let resolved = resolve_inline_callee(ctx, func, outer_body);
    let (callee_path_owned, resolved_instance) = match resolved {
        Some(r) => (Some(r.canonical_path), r.instance),
        None => (None, None),
    };
    let callee_path = callee_path_owned.as_deref();

    if let Some(callee_path) = callee_path
        && let Some(result) =
            try_inline_kani_any_modifies_call(ctx, callee_path, outer_body, destination)
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) =
            try_inline_misc_intrinsic_call(ctx, callee_path, outer_body, destination)
    {
        return Some(result);
    }

    // Part of #1739: Inline TypeId::of::<T>() as a constant bv128.
    // Must run before arg translation — TypeId::of takes no value args.
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_type_id_of(ctx, callee_path, func, outer_body)
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_pointer_wrapper_deref(
            ctx,
            callee_path,
            args,
            outer_body,
            local_exprs,
            resolver,
            inline_vtable_ids,
            destination,
        )
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) =
            inline_formatting_call_placeholder(ctx, callee_path, outer_body, destination)
    {
        return Some(result);
    }
    // Part of #4050: UB-precondition helpers like
    // std::hint::assert_unchecked::precondition_check return `()` and may fail
    // argument translation inside nested inline bodies. Short-circuit them
    // before translated-arg collection so they cannot fall through to
    // `inline_nested_call_fallback_symbolic`.
    if let Some(callee_path) = callee_path
        && is_inline_ub_precondition_noop(callee_path)
    {
        return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_shared_pointer_drop_call(
            ctx,
            callee_path,
            args,
            outer_body,
            local_exprs,
            resolver,
            inline_alloc_ids,
            inline_depth,
        )
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_dyn_drop_call(
            ctx,
            callee_path,
            args,
            outer_body,
            local_exprs,
            resolver,
            inline_vtable_ids,
            inline_alloc_ids,
            inline_depth,
        )
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) =
            inline_trivial_drop_placeholder(ctx, callee_path, args, outer_body, destination)
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_option_state_call(
            ctx,
            callee_path,
            args,
            &[],
            outer_body,
            destination,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = super::nested_iter_next::try_inline_iter_next_call(
            ctx,
            callee_path,
            args,
            &[],
            outer_body,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }

    let func_ty = func.ty(outer_body.locals()).ok()?;
    let func_ty = ctx.resolve_body_ty(func_ty);
    let (fn_def, fn_substs) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
        TyKind::RigidTy(RigidTy::FnPtr(..)) => {
            let translated_args: Vec<Expr> = args
                .iter()
                .filter_map(|arg| {
                    inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
                })
                .collect();
            if translated_args.len() != args.len() {
                return None;
            }
            // Reuse the body-relative callee path from `resolve_inline_callee`
            // instead of falling back to `ctx.resolve_callee_path(func)`, which
            // resolves against `ctx.body.locals()` and can panic for inline bodies.
            if let Some(callee_path) = callee_path
                && let Some(result) = try_inline_option_state_call(
                    ctx,
                    callee_path,
                    args,
                    &translated_args,
                    outer_body,
                    destination,
                    local_exprs,
                    resolver,
                )
            {
                return Some(result);
            }
            if let Some(callee_path) = callee_path
                && let Some(expr) =
                    try_inline_option_unwrap_call(ctx, callee_path, &translated_args)
            {
                return Some(InlineReturn::value_only(expr));
            }
            if let Some(callee_path) = callee_path
                && let Some(expr) = inline_known_call_expr_for_callee_path(
                    ctx,
                    func,
                    callee_path,
                    &translated_args,
                    None,
                    outer_body.locals(),
                )
            {
                // Part of #4053: declare DT sorts for known-call arg/result accessors.
                for arg in &translated_args {
                    ctx.declare_datatype_sort_if_needed(arg.sort());
                }
                return Some(InlineReturn::value_only(expr));
            }
            let (fn_body, is_closure) = ctx.resolve_any_fn_ptr_body()?;
            let effective = count_effective_blocks(&fn_body);
            if effective > inline_effective_block_limit(&fn_body, effective) {
                return None;
            }
            return if is_closure {
                let no_captures: Vec<Expr> = Vec::new();
                let (address_hints, _address_constraints) =
                    ctx.build_inline_zst_param_address_hints(&fn_body, 0);
                let saved_inline_hints = ctx.inline_local_address_hints.take();
                if !address_hints.is_empty() {
                    let body_key = &raw const fn_body as usize;
                    ctx.inline_local_address_hints = Some((body_key, address_hints));
                }
                // Value-only semantics for vtable/alias_updates (unchanged),
                // but PRESERVE the assert-guard side-channel: dropping it here
                // would silently lose checks recorded inside the closure body.
                let result = super::super::inline_body::translate_closure_inline_result(
                    ctx,
                    &fn_body,
                    &translated_args,
                    &no_captures,
                    0,
                    inline_depth + 1,
                )
                .map(|full| {
                    let mut value_only = InlineReturn::value_only(full.value);
                    value_only.deferred_checks = full.deferred_checks;
                    value_only
                });
                ctx.inline_local_address_hints = saved_inline_hints;
                result
            } else {
                ctx.mark_inline_field_reads(&fn_body, &translated_args, 0);
                translate_inline_body_with_metadata(
                    ctx,
                    &fn_body,
                    &translated_args,
                    0,
                    &caller_vtable_ids,
                    &caller_subslice_lens,
                    &caller_subslice_offsets,
                    None,
                    inline_depth + 1,
                )
            };
        }
        _ => return None,
    };
    if attributes::fn_marker(fn_def).as_deref() == Some("kani_register_contract") {
        return try_inline_register_contract(
            ctx,
            args,
            outer_body,
            local_exprs,
            resolver,
            inline_depth,
        );
    }
    // Part of #4075: the real `RoundRobin::pick_task` call shape goes through
    // a `&mut` reborrow temp. Generic nested-arg translation bails on that
    // ref local before the spawn-specific fast path gets a chance to resolve
    // the receiver referent, so claim this scheduler packet first.
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_round_robin_pick_task_call(
            ctx,
            callee_path,
            args,
            outer_body,
            destination,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }
    let translated_args: Vec<Expr> = args
        .iter()
        .filter_map(|arg| {
            inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
        })
        .collect();
    if translated_args.len() != args.len() {
        return None;
    }

    if let Some(callee_path) = callee_path {
        let vec_result = try_inline_vec_pop_call(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body,
            local_exprs,
            resolver,
        )
        .or_else(|| {
            try_inline_vec_push_call(
                ctx,
                callee_path,
                args,
                &translated_args,
                outer_body,
                local_exprs,
                resolver,
            )
        });
        if let Some(result) = vec_result {
            return Some(result);
        }
    }

    // Part of #1739: Intercept IntoIterNext (slice/Vec iterator next()) inside
    // inline walker bodies. Without this, the fallback recursive inline of
    // next()'s MIR produces a partial result (element without is_some),
    // causing SwitchInt on the Option discriminant to read unconstrained Bool.
    if let Some(callee_path) = callee_path
        && let Some(result) = super::nested_iter_next::try_inline_iter_next_call(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }

    // Part of #4161: Intercept kani_str_bytes_nth / kani_str_chars_nth inside
    // inline walker bodies. Reuses the shared str_nth result builder from the
    // main encoder instead of duplicating heap_select + Option<T> semantics.
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_str_nth_call(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body,
            local_exprs,
            resolver,
            destination,
        )
    {
        return Some(result);
    }

    // Part of #4161: const-fold fallback when symbolic backing resolution fails.
    // When String::from("literal").chars().nth(i) traces through passthrough
    // callees the inline walker cannot resolve to an Array expression, fall back
    // to MIR-level const-fold which extracts concrete string bytes directly.
    if let Some(callee_path) = callee_path
        && let Some(result) =
            try_inline_str_nth_const_fold(ctx, callee_path, args, destination, outer_body)
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_option_state_call(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body,
            destination,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_round_robin_pick_task_call(
            ctx,
            callee_path,
            args,
            outer_body,
            destination,
            local_exprs,
            resolver,
        )
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(expr) = try_inline_option_unwrap_call(ctx, callee_path, &translated_args)
    {
        return Some(InlineReturn::value_only(expr));
    }

    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_slice_as_ptr_call(callee_path, &translated_args)
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_box_new(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body,
            inline_vtable_ids,
            destination,
        )
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) =
            try_inline_rc_arc_new(ctx, callee_path, args, &translated_args, outer_body, destination)
    {
        return Some(result);
    }

    if let Some(callee_path) = callee_path
        && let Some(result) = try_inline_result_copied_call(
            ctx,
            callee_path,
            &translated_args,
            outer_body,
            destination,
        )
    {
        return Some(result);
    }
    // Use the body-relative callee path exclusively — do NOT fall back to
    // `inline_known_call_expr` which reaches into `ctx.resolve_callee_path(func)`
    // and resolves against the wrong body (ctx.body vs outer_body). Part of #3768.
    if let Some(callee_path) = callee_path
        && let Some(expr) = inline_known_call_expr_for_callee_path(
            ctx,
            func,
            callee_path,
            &translated_args,
            args.first(),
            outer_body.locals(),
        )
    {
        // Part of #4053: declare DT sorts for known-call arg/result accessors.
        for arg in &translated_args {
            ctx.declare_datatype_sort_if_needed(arg.sort());
        }
        return Some(InlineReturn::value_only(expr));
    }
    // Part of #4057: When the known-call fast-path failed because the receiver
    // is a BV64 pointer (e.g., closure-captured &Vec), load the Vec from typed
    // memory and retry.  This handles Vec::len/is_empty inside closure bodies
    // where the capture is a reference, not the DT value.
    if let Some(callee_path) = callee_path
        && let Some(expr) =
            try_inline_vec_accessor_via_memory(ctx, callee_path, &translated_args, args, outer_body)
    {
        return Some(InlineReturn::value_only(expr));
    }
    // Part of #3768: Handle allocation calls inside the inline walker.
    // exchange_malloc / __rust_alloc produce nondeterministic addresses when the
    // inline walker can't resolve them (body is intrinsic-like), breaking
    // store-to-load chains for Rc::new/Box::new inside inlined functions.
    // Produce a concrete heap address so downstream field stores connect to
    // loads (e.g., Rc<dyn Trait>::deref → virtual dispatch → field read).
    if let Some(callee_path) = callee_path
        && is_inline_alloc_call(callee_path)
    {
        if let Some(obj_id) = ctx.heap_state.next_heap_alloc_id() {
            let size_expr =
                inline_alloc_size_expr(ctx, callee_path, args, outer_body, &translated_args);
            emit_inline_alloc_metadata(
                ctx,
                obj_id,
                size_expr,
                callee_path.ends_with("__rust_alloc_zeroed"),
            );
            let addr = Expr::bitvec_const((obj_id as u128) << 32, POINTER_WIDTH);
            return Some(InlineReturn {
                value: addr,
                vtable: None,
                alloc_id: Some(obj_id),
                alias_updates: BTreeMap::new(),
                deferred_checks: Vec::new(),
            });
        }
    }
    // Part of #3768: Handle pointer identity calls inside the inline walker.
    // NonNull::new_unchecked, NonNull::as_ptr, NonNull::cast, Unique::new_unchecked,
    // ptr::cast, Box::into_raw are all identity at the BV level. The stub registry
    // may not find these paths when resolved from the inline walker context, so
    // detect them by path pattern directly.
    if let Some(callee_path) = callee_path
        && is_inline_pointer_identity_call(callee_path)
        && translated_args.len() == 1
    {
        return Some(InlineReturn::value_only(translated_args[0].clone()));
    }
    // No-op calls: mem::forget (#3768), UB precondition checks (#4050),
    // Vec/RawVec allocation infrastructure (#4050). All return () or have
    // side effects already modeled by the outer encoding. Complex bodies
    // exhaust the inline walker budget, producing symbolic fallback variables.
    if let Some(callee_path) = callee_path
        && (is_inline_noop_call(callee_path)
            || is_inline_ub_precondition_noop(callee_path)
            || is_inline_vec_internal_noop(callee_path))
    {
        return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
    }
    if let Some(callee_path) = callee_path
        && let Some(result) = inline_trivial_hashbrown_drop_elements_placeholder(
            ctx,
            callee_path,
            &fn_substs,
            outer_body,
            destination,
        )
    {
        return Some(result);
    }

    // Reuse the already-resolved Instance from resolve_inline_callee instead of
    // re-resolving from raw FnDef metadata (which may carry unresolved params).
    let instance = resolved_instance.or_else(|| Instance::resolve(fn_def, &fn_substs).ok())?;
    if let InstanceKind::Virtual { idx: _ } = instance.kind {
        let trait_def_id = ctx.resolve_parent_trait_def_id(fn_def)?;
        let candidates =
            super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);

        let receiver_local = args.first().and_then(receiver_base_local);
        let vtable_disc =
            if let Some(vtable) = receiver_local.and_then(|l| inline_vtable_ids.get(&l)) {
                vtable.clone()
            } else {
                // Part of #4075: trait-scope the spawn vtable model to Future::poll only.
                ctx.try_extract_vtable_discriminant_for_trait(
                    &translated_args,
                    receiver_local,
                    Some(trait_def_id),
                )
            };

        if let Some(callee_path) = callee_path
            && let Some(result) =
                try_inline_virtual_error_type_id(ctx, callee_path, &candidates, vtable_disc.clone())
        {
            return Some(result);
        }

        let (concrete_bodies, dropped_candidate) =
            super::super::dyn_coercion::resolve_dispatch_bodies(
                ctx,
                &candidates,
                fn_def,
                &fn_substs,
            );
        if concrete_bodies.is_empty() {
            if dropped_candidate {
                ctx.record_sound_fallback_reason("dyn_dispatch_candidate_body_dropped");
            }
            return None;
        }
        // A dropped candidate is safe here — every path below goes through the
        // guarded dispatch ITE (disc == id per arm, fresh unconstrained
        // default), so the dropped type falls to the sound default arm. Record
        // the narrowing for attribution only.
        if dropped_candidate {
            ctx.record_aggregate_gap("dyn_dispatch_candidate_body_dropped");
        }

        // Part of #3980: Short-circuit Fn-trait shim to direct fn-item body.
        if callee_path.is_some_and(is_fn_trait_call) {
            let candidate_types: Vec<_> = candidates.iter().map(|c| c.concrete_ty).collect();
            let closure_captures =
                nested_fn_trait_closure_captures(ctx, args, outer_body, local_exprs, resolver);
            if let Some(r) = try_fn_trait_direct_dispatch(
                ctx,
                &candidate_types,
                &translated_args,
                &closure_captures,
                &caller_vtable_ids,
                inline_depth,
            ) {
                return Some(r);
            }
        }

        for dispatch_body in &concrete_bodies {
            ctx.mark_inline_field_reads(&dispatch_body.body, &translated_args, 0);
        }
        if let Some(first_arg) = args.first() {
            populate_inline_self_field_hints_for_arg(ctx, first_arg, None);
        }
        return build_dispatch_ite_chain_impl(
            ctx,
            &concrete_bodies,
            &translated_args,
            vtable_disc,
            0,
            &caller_vtable_ids,
            inline_depth + 1,
        );
    }

    // TRANSFORMED body fetch: raw `instance.body()` bypasses the kani_middle
    // transform pipeline, leaving `kani_contract_mode()` at the macro dummy
    // ORIGINAL=0 inside walked contract chains (vacuous ensures/requires).
    let fn_body = crate::kani_middle::transform::walker_transformed_body(ctx.tcx, instance)?;
    // Kani parity fail-close: contracted recursive callee without
    // #[kani::recursion] — Kani fails via the reentry tracker; the walk's
    // replace-style inner-call semantics erase that failure. Demote.
    if crate::codegen_ay::chc::call::codegen_call_fn_inline::contract_recursion_unannotated(
        ctx.tcx, instance, &fn_body,
    ) {
        ctx.record_fallback();
    }
    if let Some(expr) =
        try_inline_simple_bool_return_helper(ctx, &fn_body, &translated_args, callee_path)
    {
        return Some(InlineReturn::value_only(expr));
    }
    ctx.mark_inline_field_reads(&fn_body, &translated_args, 0);
    translate_inline_body_with_metadata(
        ctx,
        &fn_body,
        &translated_args,
        0,
        &caller_vtable_ids,
        &caller_subslice_lens,
        &caller_subslice_offsets,
        Some(instance),
        inline_depth + 1,
    )
}

/// Part of #4057: When Vec::len or Vec::is_empty is called with a BV64 receiver
/// (e.g., closure-captured `&Vec<T>`), load the Vec from typed memory and
/// extract the len/is_empty result.  The known-call fast-path
/// (`inline_known_call_expr_for_callee_path`) only handles Vec DT receivers;
/// this fallback resolves the pointer→DT indirection.
fn try_inline_vec_accessor_via_memory(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    translated_args: &[Expr],
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
) -> Option<Expr> {
    use super::super::codegen_call_vec::ChcVecFields;
    use trust_mc_codegen_stubs::StubKind;

    let stub = ctx.stub_registry.lookup(callee_path);
    let stub = stub?;
    if !matches!(stub, StubKind::VecLen | StubKind::VecIsEmpty) {
        return None;
    }
    if translated_args.len() != 1 {
        return None;
    }
    let receiver = &translated_args[0];
    debug!(receiver_sort = ?receiver.sort(), "try_inline_vec_accessor_via_memory: receiver sort (#4057)");
    // Only trigger when receiver is BV64 (pointer), not an already-resolved Vec DT.
    if receiver.sort().bitvec_width() != Some(POINTER_WIDTH) {
        return None;
    }

    // Resolve the pointee type: &Vec<T> → Vec<T>.
    let arg_ty = args.first()?.ty(outer_body.locals()).ok()?;
    let arg_ty = ctx.resolve_body_ty(arg_ty);
    debug!(?arg_ty, "try_inline_vec_accessor_via_memory: arg type (#4057)");
    let pointee_ty = match arg_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            ctx.resolve_body_ty(inner)
        }
        _ => arg_ty,
    };
    debug!(?pointee_ty, "try_inline_vec_accessor_via_memory: pointee type (#4057)");

    let loaded = ctx.load_from_memory(receiver.clone(), pointee_ty);
    debug!(loaded_sort = ?loaded.as_ref().map(|e| e.sort()), "try_inline_vec_accessor_via_memory: memory load result (#4057)");
    let loaded = loaded?;
    let loaded = ctx.try_unflatten_bv_to_datatype(loaded, pointee_ty);
    debug!(
        reconstructed_sort = ?loaded.sort(),
        "try_inline_vec_accessor_via_memory: reconstructed Vec load (#4057)"
    );
    let extract_result = ChcVecFields::extract_without_name(loaded);
    debug!(
        extract_ok = extract_result.is_some(),
        "try_inline_vec_accessor_via_memory: Vec field extract (#4057)"
    );
    let (_, len, _, _) = extract_result?;

    match stub {
        StubKind::VecLen => {
            debug!(callee_path, "inline Vec::len via memory load (#4057)");
            Some(len)
        }
        StubKind::VecIsEmpty => {
            debug!(callee_path, "inline Vec::is_empty via memory load (#4057)");
            Some(len.eq(Expr::bitvec_const(0u64, POINTER_WIDTH)))
        }
        _ => None,
    }
}

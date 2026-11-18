// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Nested call inlining (fn-def, fn-ptr, closure, virtual). Part of #3159, #3335, #3639.
use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc, sound_havoc};
use crate::codegen_ay::provenance::{Loc, Val};

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
use super::assert_validity_inline::{push_validity_obligation, validity_definitely_violated};
use super::dispatch::build_dispatch_ite_chain_impl;
use super::drop_placeholders::{
    inline_trivial_drop_placeholder, inline_trivial_hashbrown_drop_elements_placeholder,
    try_inline_dyn_drop_call, try_inline_shared_pointer_drop_call,
};
use super::fn_trait_dispatch::{is_fn_trait_call, try_fn_trait_direct_dispatch};
use super::inline_alloc_helpers::{emit_inline_alloc_metadata, inline_alloc_size_expr};
use super::inline_call_classify::{
    is_inline_alloc_call, is_inline_noop_call, is_inline_pointer_identity_call,
    is_inline_ub_precondition_noop, is_inline_vec_internal_noop, is_std_family_crate,
};
use super::pointer_wrapper::{
    try_inline_box_new, try_inline_pointer_wrapper_deref, try_inline_rc_arc_new,
};
use super::register_contract::{nested_fn_trait_closure_captures, try_inline_register_contract};
use super::result_copied::try_inline_result_copied_call;
use super::{InlineReturn, receiver_base_local};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::attributes;
use ay_bindings::{Expr, Sort};
use rustc_middle::ty::layout::ValidityRequirement;
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
    spec_array_operation: Option<bool>,
    spec_array_default_body: bool,
    /// The callee is DEFINED in `std`, `core` or `alloc`. The path-text
    /// classifiers in `inline_call_classify.rs` describe standard-library
    /// functions only; see `std_callee_path` in `try_inline_nested_call`.
    std_family: bool,
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
    let canonical_path = crate::intrinsics::callee_path_model_spelling(
        ctx.tcx.def_path_str(internal_def_id),
        fn_def,
        &fn_args,
    );
    let std_family = is_std_family_crate(ctx.tcx.crate_name(internal_def_id.krate).as_str());
    let spec_array_operation = ctx.authenticated_spec_array_comparison_is_ne(def_id);
    let spec_array_default_body =
        instance.as_ref().is_some_and(|instance| ctx.spec_array_has_default_body(instance));
    Some(ResolvedInlineCallee {
        canonical_path,
        instance,
        std_family,
        spec_array_operation,
        spec_array_default_body,
    })
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

    let mut result = Havoc::mint(
        ctx,
        sound_havoc::UNTRACKED_VTABLE_METADATA,
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

    // `mem::zeroed::<T>()` and `mem::uninitialized::<T>()` are claimed WHOLE,
    // so the `assert_zero_valid::<T>` / `assert_mem_uninitialized_valid::<T>`
    // at the top of their bodies is never walked: the claim must state that
    // requirement itself, or `mem::zeroed::<&u8>()` is silently a null
    // reference (Kani: "attempted to zero-initialize type `&u8`").
    let kind = detect_misc_intrinsic(callee_path)?;
    match kind {
        MiscIntrinsicKind::MemZeroed => {
            let ty = destination_ty()?;
            let zero_expr = zero_expr_for_ty(ty)?;
            let mut result = InlineReturn::value_only(zero_expr);
            if validity_definitely_violated(ctx, ty, ValidityRequirement::Zero) {
                push_validity_obligation(&mut result, callee_path, ctx.heap_state.write_mark());
            }
            Some(result)
        }
        // `assert_zero_valid` / `assert_mem_uninitialized_valid` are NOT claimed
        // here: they are decided by the `assert_*` validity arm further down,
        // which states a definitely violated requirement. Claiming them here as
        // `true` made that arm dead for both.
        MiscIntrinsicKind::Forget => Some(InlineReturn::value_only(Expr::bool_const(true))),
        MiscIntrinsicKind::MaybeUninitUninit | MiscIntrinsicKind::MemUninitialized => {
            let ty = destination_ty()?;
            let dest_sort = ChcCtx::translate_ty(ty)?;
            let fresh = ExactVar::nondet(
                super::super::chc_fresh_name("__inline_misc_intrinsic"),
                dest_sort,
            );
            let mut result = InlineReturn::value_only(fresh);
            if matches!(kind, MiscIntrinsicKind::MemUninitialized)
                && validity_definitely_violated(
                    ctx,
                    ty,
                    ValidityRequirement::UninitMitigated0x01Fill,
                )
            {
                push_validity_obligation(&mut result, callee_path, ctx.heap_state.write_mark());
            }
            Some(result)
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
    let fresh =
        ExactVar::nondet(super::super::chc_fresh_name("__kani_any_modifies_inline"), dest_sort);
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
    let ptr = super::super::dyn_coercion::extract_pointer_expr(&receiver)
        .map(Loc::into_expr)
        .unwrap_or(receiver);
    // `<[T]>::as_ptr` returns the slice's data pointer, so the CALLEE supplies
    // the provenance — this function does not infer it from the width. The only
    // open question is the shape, which is what the decoder answers; it accepts
    // exactly `width == POINTER_WIDTH`, so nothing new is admitted.
    let data_ptr = PtrRepr::thin_address(&ptr)?;
    debug!(%callee_path, "nested call: inline slice::as_ptr/as_mut_ptr as data pointer");
    Some(InlineReturn::value_only(data_ptr.into_expr()))
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
    if crate::codegen_ay::native_string_unmodeled_operation(
        ctx.tcx,
        func,
        outer_body.locals(),
        true,
    ) {
        ctx.record_sound_fallback_reason("native_string_unmodeled_operation");
        return None;
    }
    let caller_vtable_ids = nested_caller_vtable_ids(ctx, args, inline_vtable_ids);
    let (caller_subslice_lens, caller_subslice_offsets) =
        build_inline_subslice_maps_from_args(ctx, args);
    // F2 (inline_walk_guard.rs): a nested walk's parameter is address-bound
    // exactly when its operand copies an address-bound local of this walk (the
    // nested binders hand the walker the operand's own term).
    let mut nested_address_seeds: Vec<usize> = args
        .iter()
        .enumerate()
        .filter(|(_, arg)| ctx.inline_walk_operand_is_address(arg))
        .map(|(i, _)| i + 1)
        .collect();
    let nested_referent_seeds: Vec<usize> = args
        .iter()
        .enumerate()
        .filter(|(_, arg)| ctx.inline_walk_operand_is_referent(arg))
        .map(|(i, _)| i + 1)
        .collect();

    let nested_mut_owner_seeds: Vec<_> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| ctx.inline_operand_mut_ref_owner(arg).map(|owner| (i + 1, owner)))
        .collect();

    let nested_rustcall_mut_owner_seeds: Vec<_> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| {
            let owners = ctx.inline_rustcall_mut_ref_args(arg);
            (!owners.is_empty()).then_some((i + 1, owners))
        })
        .collect();

    let native_dyn_seeds: Vec<_> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| {
            ctx.inline_native_dyn_origin(arg, outer_body.locals()).map(|origin| (i + 1, origin))
        })
        .collect();
    let native_drop_seeds: Vec<_> = args
        .iter()
        .enumerate()
        .filter_map(|(i, arg)| {
            ctx.inline_native_drop_address(arg, outer_body.locals()).map(|address| (i + 1, address))
        })
        .collect();

    // Resolve the callee once, body-relative, with full generic normalization.
    // All downstream paths reuse this instead of re-resolving from raw FnDef.
    let resolved = resolve_inline_callee(ctx, func, outer_body);
    let (
        callee_path_owned,
        resolved_instance,
        callee_std_family,
        spec_array_operation,
        spec_array_default_body,
    ) = match resolved {
        Some(r) => (
            Some(r.canonical_path),
            r.instance,
            r.std_family,
            r.spec_array_operation,
            r.spec_array_default_body,
        ),
        None => (None, None, false, None, false),
    };
    let callee_path = callee_path_owned.as_deref();
    if matches!(
        callee_path.and_then(crate::codegen_ay::shared::compare_loops::comparison_call),
        Some(crate::codegen_ay::shared::compare_loops::ComparisonCall::Eq { .. })
    ) && ctx.has_heterogeneous_sequence_elements(func, outer_body.locals())
    {
        ctx.record_sound_fallback_reason("heterogeneous_sequence_comparison");
        return None;
    }
    // The path-text classifiers of `inline_call_classify.rs` (allocation,
    // pointer identity, no-op, UB-precondition, Vec internals) replace the
    // callee's BODY with a model, so they may only ever claim the standard
    // library function they describe. They match substrings of the printed
    // path (`ends_with("::forget") && contains("mem")`,
    // `contains("Vec") && ends_with("::new")`), which a USER function matches
    // just as well: `mod mem { fn forget(..) { assert!(..) } }` or
    // `Vec3::new` lost its assertion and its writes and the harness PROVED
    // (tools/soundness-duals/walker_noop_table_user_fn_dual.rs). They see only
    // this crate-anchored path; a user callee falls through to the walk or the
    // fail-closed fallback like any other function.
    let std_callee_path = callee_path.filter(|_| callee_std_family);
    // The stub-registry fast paths below match the printed path of std's
    // methods (`Chain<` and `next`), which a callee of the LOCAL crate can
    // match as well: a user `Chain<T>` iterator was read as std's chain
    // adapter (walker fail-closed repair round 5,
    // `user_type_named_like_std_dual.rs`; `shared::callee_is_local_item`).
    // A user callee keeps no path for them and is walked as its code; a
    // `Fn*` trait call of a local closure keeps it for its own dispatch.
    let callee_is_local = resolved_instance
        .as_ref()
        .is_some_and(|instance| rustc_public::CrateDef::krate(&instance.def).is_local);
    let callee_path = callee_path.filter(|path| !callee_is_local || is_fn_trait_call(path));
    // Under a declared unwind bound with unwinding assertions on, a callee
    // that may run a loop is not answered by a path-text model: the models
    // state nothing about the loop, so Kani's unwinding assertion on it was
    // lost. `Iterator::ne` walked over a `Filter` answered its nested
    // `Iterator::eq` with the iterator-state model, and `[1u32].iter().ne(
    // [1, 2, 3, 4, 5].iter().filter(..))` under `unwind(3)` verified clean
    // where Kani fails (walker fail-closed repair round 5,
    // `model_call_unwind_iter_eq_dual.rs` `z3`). Such a callee is walked (the
    // declared-unwind replay is exact) or havocked, which books the lost
    // effect (`terminator_exec.rs`, Rule D's nested-call site). `Fn*` trait
    // calls keep their dispatch.
    let loops_under_declared_unwind = ctx.recursive_unwind_depth > 0
        && ctx.unwinding_assertions
        && resolved_instance.is_some_and(|instance| {
            let stubs = crate::kani_middle::transform::walker_stub_map();
            super::uncertified_check::instance_may_loop_cached(ctx, instance, &stubs)
        });
    let callee_path =
        callee_path.filter(|path| !loops_under_declared_unwind || is_fn_trait_call(path));
    let std_callee_path = std_callee_path.filter(|_| !loops_under_declared_unwind);

    // `<&() as PartialEq<&()>>::eq` is `() == ()`: true whatever addresses the
    // references hold (`inline_ref_arg_binding::comparison_referent_is_unit_like`).
    // It is the `Some(a) == Some(b)` arm of an inlined `Option<&()>::eq`; the
    // referent guard below would leave it unconstrained.
    if let Some(callee_path) = callee_path
        && super::super::inline_ref_arg_binding::is_comparison_callee_path(callee_path)
        && let Some(answer) = match callee_path.rsplit("::").next() {
            Some("eq") => Some(true),
            Some("ne") => Some(false),
            _ => None,
        }
        && args.first().is_some_and(|arg| {
            super::super::inline_ref_arg_binding::comparison_referent_is_unit_like(
                ctx,
                arg,
                outer_body.locals(),
            )
        })
    {
        debug!(%callee_path, answer, "nested call: comparison through references to unit");
        return Some(InlineReturn::value_only(Expr::bool_const(answer)));
    }

    // A comparison of a type holding references compares referents; the terms
    // the walker holds for its reference arguments are addresses here
    // (`inline_ref_arg_binding::comparison_referent_holds_reference`). The
    // nested fallback leaves the result unconstrained instead.
    if let Some(callee_path) = callee_path
        && super::super::inline_ref_arg_binding::is_comparison_callee_path(callee_path)
        && args.first().is_some_and(|arg| {
            super::super::inline_ref_arg_binding::comparison_referent_holds_reference(
                ctx,
                arg,
                outer_body.locals(),
            )
        })
    {
        debug!(%callee_path, "nested call: comparison of a type holding references not inlined");
        return None;
    }

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
    if let Some(callee_path) = std_callee_path
        && is_inline_ub_precondition_noop(callee_path)
    {
        return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
    }
    // M3 (measured 2026-09-18, docs/chc-nested-call-overapprox-2026-09-18/):
    // `assert_inhabited` and its two siblings are RECOGNIZED by
    // `detect_misc_intrinsic` and DECIDED by
    // `assert_requirement_definitely_violated`, both of which the STATEMENT
    // path already uses — the walker consulted neither, so the call became a
    // fresh `__nested_call_overapprox` variable and the solver could pick the
    // result. Probe on `expected/any_vec/exact_length.rs`: 68 of that unit's
    // 168 havocs were `std::intrinsics::assert_inhabited`, with zero
    // interception lines logged. 13 corpus units carry it, 5 with a
    // counterexample resting on the approximation.
    //
    // Placed HERE, ahead of translated-arg collection, because `assert_*` takes
    // no arguments: the bail below cannot defeat it, and that is also why this
    // family is not the argument-translation case (M1).
    if let Some(callee_path) = callee_path
        && let Some(result) = super::assert_validity_inline::try_inline_assert_validity_intrinsic(
            ctx,
            callee_path,
            func,
            outer_body,
        )
    {
        return Some(result);
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
            func,
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
            func,
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
    if callee_path.is_some()
        && let Some(result) = super::nested_iter_query::try_inline_native_iterator_query(
            ctx,
            func,
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
                    &[],
                    outer_body.locals(),
                )
            {
                // Part of #4053: declare DT sorts for known-call arg/result accessors.
                for arg in &translated_args {
                    ctx.declare_datatype_sort_if_needed(arg.sort());
                }
                return Some(InlineReturn::value_only(expr));
            }
            // The known path identified an array comparison, but its model
            // could not establish the array data. Do not walk fn-pointer
            // candidates into a raw_eq fallback over untyped pointer bits.
            if spec_array_operation.is_some() {
                ctx.record_sound_fallback_reason("nested_spec_array_referent_unresolved");
                return None;
            }
            // Which function is called? Design 3 (call/fn_ptr_targets.rs): the
            // candidate set is COMPLETE when every value the pointer can hold
            // is known (one minted id, an if-then-else of minted ids, or the
            // term of a closed host fn-pointer local), and is then dispatched
            // under `pointer == id` with the checked obligation `pointer ∈ ids`
            // as its default arm. Otherwise the targets the host reifies are
            // walked for the counterexamples they can show and the call fails
            // closed. (Before 2026-09-23 the FIRST reification in the host body
            // was walked unconditionally; until design 3, ids were keyed by
            // trimmed name, so `m1::op2` stood in for `m2::op2`, a pointer read
            // from a static walked a decoy the host happened to reify, and a
            // lone target too large to walk was havocked as a blessed
            // `nested_call_overapprox`.)
            let pointer =
                inline_operand_to_expr(ctx, func, local_exprs, resolver, outer_body.locals());
            let candidates = ctx.fn_ptr_call_candidates(pointer.as_ref(), Some(func_ty));
            use super::super::fn_ptr_targets::{
                FN_PTR_CANDIDATES_INCOMPLETE, FN_PTR_TARGET_UNWALKABLE,
            };
            if candidates.targets.is_empty() {
                debug!("nested fn-ptr call: no candidate target; failing closed");
                ctx.record_sound_fallback_reason(FN_PTR_CANDIDATES_INCOMPLETE);
                return None;
            }
            let contains_spec_array_target =
                candidates.targets.iter().any(|(_, target)| match &target.kind {
                    crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Item {
                        instance, ..
                    } => ctx
                        .authenticated_spec_array_comparison_is_ne(instance.def.def_id())
                        .is_some(),
                    crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Closure { .. } => false,
                });
            if contains_spec_array_target {
                ctx.record_sound_fallback_reason("nested_spec_array_referent_unresolved");
                return None;
            }
            if ctx.has_heterogeneous_sequence_elements(func, outer_body.locals())
                && candidates.targets.iter().any(|(_, target)| match &target.kind {
                    crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Item {
                        instance, ..
                    } => {
                        let path = ctx
                            .tcx
                            .def_path_str(rustc_internal::internal(ctx.tcx, instance.def.def_id()));
                        matches!(
                            crate::codegen_ay::shared::compare_loops::comparison_call(&path),
                            Some(
                                crate::codegen_ay::shared::compare_loops::ComparisonCall::Eq { .. }
                            )
                        )
                    }
                    crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Closure { .. } => false,
                })
            {
                ctx.record_sound_fallback_reason("heterogeneous_sequence_comparison");
                return None;
            }
            if candidates.targets.iter().any(|(_, target)| {
                matches!(&target.kind, crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Item { instance, .. }
                    if crate::codegen_ay::native_string_unmodeled_operation_instance(ctx.tcx, *instance, true))
            }) {
                ctx.record_sound_fallback_reason("native_string_unmodeled_operation");
                return None;
            }
            if candidates.exact {
                let (_, target) = candidates.targets.into_iter().next()?;
                let walked = target.target_body().and_then(|fn_body| {
                    walk_nested_fn_ptr_target(
                        ctx,
                        fn_body,
                        target.is_closure(),
                        &translated_args,
                        &caller_vtable_ids,
                        &caller_subslice_lens,
                        &caller_subslice_offsets,
                        &nested_address_seeds,
                        inline_depth,
                    )
                });
                if walked.is_none() {
                    debug!(target = %target.label(), "nested fn-ptr call: exact target not walked");
                    ctx.record_sound_fallback_reason(FN_PTR_TARGET_UNWALKABLE);
                }
                return walked;
            }
            let guardable =
                pointer.as_ref().is_some_and(|p| p.sort().bitvec_width() == Some(POINTER_WIDTH));
            if !guardable {
                // A pointer value the merge cannot compare against the ids.
                ctx.record_sound_fallback_reason(FN_PTR_CANDIDATES_INCOMPLETE);
                return None;
            }
            let pointer = pointer?;
            let multi = candidates.targets.len() > 1;
            let mut complete = candidates.complete;
            let mut walked: Vec<(u64, InlineReturn)> = Vec::new();
            let dispatch_heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
            let dispatch_modified_snapshot = ctx.encode.modified_state_indices.clone();
            let mut arm_effect = false;
            // Phase 0 (inline_walk_guard.rs): one write mark over every
            // candidate, so a candidate that reads what an earlier one wrote
            // (its stores are kept) fails closed; a candidate's memory effect
            // is applied unguarded and fails closed too.
            ctx.with_inline_walk_write_mark(|ctx| {
                for (id, target) in candidates.targets.iter().cloned() {
                    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
                    let modified_snapshot = ctx.encode.modified_state_indices.clone();
                    let effects_before = ctx.heap_state.effect_mark();
                    let checks_before = ctx.heap_state.pending_checks.len();
                    let result = target.target_body().and_then(|fn_body| {
                        walk_nested_fn_ptr_target(
                            ctx,
                            fn_body,
                            target.is_closure(),
                            &translated_args,
                            &caller_vtable_ids,
                            &caller_subslice_lens,
                            &caller_subslice_offsets,
                            &nested_address_seeds,
                            inline_depth,
                        )
                    });
                    match result {
                        Some(result) => {
                            if multi && ctx.heap_state.effect_mark() > effects_before {
                                ctx.note_inline_branch_arm_effects(effects_before);
                                arm_effect = true;
                            }
                            super::dispatch::guard_dispatch_arm_pending_checks(
                                ctx,
                                checks_before,
                                &pointer,
                                id,
                            );
                            walked.push((id, result));
                        }
                        None => {
                            ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                            ctx.encode.modified_state_indices = modified_snapshot;
                            // Its obligations would be dropped with it.
                            debug!(target = %target.label(), "nested fn-ptr call: candidate not walked");
                            ctx.record_sound_fallback_reason(FN_PTR_TARGET_UNWALKABLE);
                            complete = false;
                        }
                    }
                }
            });
            if arm_effect {
                // An arm's memory effect would reach the host unguarded (two
                // arms storing different values to one `static mut` made the
                // walk's constraints unsatisfiable). It fails closed anyway:
                // decline the dispatch, leaving the call to the recorded havoc.
                ctx.heap_state.restore_transient_rule_state(&dispatch_heap_snapshot);
                ctx.encode.modified_state_indices = dispatch_modified_snapshot;
                return None;
            }
            if walked.is_empty() {
                return None;
            }
            let default = if complete {
                ctx.fn_ptr_obligation_default(&candidates)
            } else {
                super::dispatch::DispatchDefault::FailClosed(FN_PTR_CANDIDATES_INCOMPLETE)
            };
            return Some(super::dispatch::merge_guarded_dispatch_results(
                ctx, walked, &pointer, default,
            ));
        }
        _ => return None,
    };
    // `kani_force_fn_once(f) -> f` is the IDENTITY — resolve it here instead of
    // spending an inline-depth level on its body.
    //
    // `const fn kani_force_fn_once<T, F: FnOnce() -> T>(f: F) -> F { f }`
    // (library/kani_macros/src/sysroot/contracts). The non-nested lane already
    // relies on that exactness (codegen_call_closure/mod.rs, "This is EXACT, not
    // a guess"), but the NESTED walker had no case for it, so it fell through to
    // a generic body inline costing one depth level — and
    // `try_inline_register_contract` costs another.
    //
    // That matters because `#[kani::recursion]` lowering stacks
    // recursion-closure -> force_fn_once -> register_contract -> check-closure ->
    // force_fn_once -> body per USER frame. Two wasted levels per frame reaches
    // MAX_INLINE_DEPTH sooner, and depth exhaustion is precisely the branch that
    // havocs the callee result AND books a demoting fallback
    // (terminator_exec.rs, `inline_depth >= MAX_INLINE_DEPTH`).
    //
    // EXACT, not an approximation: destination and argument denote the SAME
    // closure value, so returning the argument's expression removes a level of
    // indirection and nothing else. Anything without one of the two markers, or
    // with no first argument, falls through unchanged.
    if matches!(
        attributes::fn_marker(fn_def).as_deref(),
        Some("kani_force_fn_once" | "kani_force_fn_once_with_args")
    ) && let Some(arg) = args.first()
        && let Some(expr) =
            inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
    {
        debug!("nested call: kani_force_fn_once identity -> argument expression");
        return Some(InlineReturn::value_only(expr));
    }

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
        // M1: an untranslatable ARGUMENT must not defeat an interception that
        // never reads the arguments. Both families here are decided by the
        // callee path alone and return `()` (or an effect the outer encoding
        // already models) — exactly the argument for which #4050 hoisted
        // `is_inline_ub_precondition_noop` above this bail. Only the case that
        // would otherwise have bailed is rescued, so the relative order of
        // every other callee is unchanged. The rescue bypasses the fallback's
        // fail-closed guards (a visible callee obligation, a write through a
        // pointer argument), which is sound only for the standard-library
        // functions the tables describe: hence `std_callee_path`. A user
        // `mem::forget` or `Vec3::new` whose argument failed to translate falls
        // through to that fallback below.
        if let Some(callee_path) = std_callee_path
            && (is_inline_noop_call(callee_path) || is_inline_vec_internal_noop(callee_path))
        {
            debug!(
                %callee_path,
                args = args.len(),
                translated = translated_args.len(),
                "nested call: argument translation incomplete, but the callee is an \
                 argument-independent no-op — intercepting instead of falling through"
            );
            return Some(InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH)));
        }
        // This bail was SILENT, and that silence is the whole reason M1 had to
        // be established by ELIMINATION: a corpus-scale triage and then a
        // targeted debug probe (whole call module at debug, ZERO `nested call:`
        // lines) could only infer that an argument failure here is what stops
        // the identity/no-op tables ~200 lines below from ever being consulted.
        // It logs now so the next reader READS the cause instead of deducing
        // it: a callee named on this line that has a matching entry in
        // `inline_call_classify.rs` is being over-approximated because of its
        // ARGUMENTS, not because it is unrecognized. A one-argument identity
        // such as `<*const T>::cast` cannot be rescued above — the argument IS
        // the value it would return — so the cause to chase for those rows is
        // the unpopulated local, not this ordering.
        debug!(
            ?callee_path,
            args = args.len(),
            translated = translated_args.len(),
            "nested call: argument translation incomplete — declining before the \
             identity/no-op interception tables"
        );
        return None;
    }

    // Core's `unchecked_*` wrappers: the BinOp's value and UB checks, no walk
    // (and so no inline depth spent; see `inline_unchecked_arith_wrapper_call`).
    if let Some(callee_path) = callee_path
        && let Some(result) = super::super::inline_shared::inline_unchecked_arith_wrapper_call(
            ctx,
            callee_path,
            args,
            &translated_args,
            outer_body.locals(),
        )
    {
        return Some(result);
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
            func,
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
    if callee_path.is_some()
        && let Some(result) = super::nested_iter_query::try_inline_native_iterator_query(
            ctx,
            func,
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
    // A comparison's reference arguments must carry their referents' values.
    // The fast path below compares its arguments as values, and an argument
    // translated to an ADDRESS (`&(*other).0` through an address-bound
    // parameter) made a joined `(Ordering, u8)` compare unequal to the promoted
    // constant it equals. The nested fallback leaves the result unconstrained.
    //
    // Do not read an address argument's referent back from the place it
    // borrows. A 2026-09-24 repair did (`comparison_arg_referent_value`, for
    // `(a..b).rev().next()`'s lost `self.start < self.end` guard) and it was
    // unsound: the walker's place resolver answered `(*_2).a` for a non-first
    // reference parameter with bits of the pointer, and `(*_1).a` after `_1`
    // was reassigned with the entry snapshot of the first parameter, proving
    // programs that Kani and main both FAIL (walker_referent_read_dual.rs).
    if let Some(callee_path) = callee_path
        && super::super::inline_ref_arg_binding::is_comparison_callee_path(callee_path)
        && !comparison_ref_args_carry_referent_values(
            ctx,
            args,
            &translated_args,
            outer_body.locals(),
        )
    {
        debug!(
            %callee_path,
            arg_sorts = ?translated_args.iter().map(|a| a.sort().clone()).collect::<Vec<_>>(),
            "nested call: comparison argument is not its referent's value; not inlined"
        );
        return None;
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
            args,
            outer_body.locals(),
        )
    {
        debug!(
            %callee_path,
            arg_sorts = ?translated_args.iter().map(|a| a.sort().clone()).collect::<Vec<_>>(),
            result = %expr,
            "nested call: known-call fast path"
        );
        // Part of #4053: declare DT sorts for known-call arg/result accessors.
        for arg in &translated_args {
            ctx.declare_datatype_sort_if_needed(arg.sort());
        }
        return Some(InlineReturn::value_only(expr));
    }
    // A declined specialization must not walk raw_eq on address bits. The
    // default implementation may compare established array values through a
    // checked value-only element body; otherwise preserve the refusal.
    if spec_array_operation.is_some() {
        if spec_array_default_body
            && let Some(instance) = resolved_instance.as_ref()
            && let Some(result) =
                super::super::inline_array_semantic_eq::try_inline_array_semantic_eq(
                    ctx,
                    instance,
                    args,
                    &translated_args,
                    outer_body.locals(),
                    inline_depth,
                )
        {
            return Some(result);
        }
        ctx.record_sound_fallback_reason("nested_spec_array_referent_unresolved");
        return None;
    }
    // Part of #4057: When the known-call fast-path failed because the receiver
    // is a BV64 pointer (e.g., closure-captured &Vec), load the Vec from typed
    // memory and retry.  This handles Vec::len/is_empty inside closure bodies
    // where the capture is a reference, not the DT value.
    if let Some(callee_path) = callee_path
        && let Some(expr) = try_inline_vec_accessor_via_memory(
            ctx,
            func,
            callee_path,
            &translated_args,
            args,
            outer_body,
        )
    {
        return Some(InlineReturn::value_only(expr));
    }
    // Part of #3768: Handle allocation calls inside the inline walker.
    // exchange_malloc / __rust_alloc produce nondeterministic addresses when the
    // inline walker can't resolve them (body is intrinsic-like), breaking
    // store-to-load chains for Rc::new/Box::new inside inlined functions.
    // Produce a concrete heap address so downstream field stores connect to
    // loads (e.g., Rc<dyn Trait>::deref → virtual dispatch → field read).
    if let Some(callee_path) = std_callee_path
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
    if let Some(callee_path) = std_callee_path
        && is_inline_pointer_identity_call(callee_path)
        && translated_args.len() == 1
    {
        return Some(InlineReturn::value_only(translated_args[0].clone()));
    }
    // No-op calls: mem::forget (#3768), UB precondition checks (#4050),
    // Vec/RawVec allocation infrastructure (#4050). All return () or have
    // side effects already modeled by the outer encoding. Complex bodies
    // exhaust the inline walker budget, producing symbolic fallback variables.
    if let Some(callee_path) = std_callee_path
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
        // Design 3 (dyn_dispatch_scope.rs): dispatch over the receiver's
        // principal, whose list the stored vtable ids index.
        let Some(dispatch_trait) = super::super::dyn_dispatch_scope::dispatch_trait_for_call(
            ctx,
            trait_def_id,
            &fn_substs,
        ) else {
            ctx.record_sound_fallback_reason(
                super::super::dyn_dispatch_scope::DYN_PRINCIPAL_MISMATCH,
            );
            return None;
        };
        let candidates =
            super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, dispatch_trait.def_id);
        let scope = super::super::dyn_dispatch_scope::DynDispatchScope::new(
            ctx,
            &dispatch_trait,
            &candidates,
        );

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
        // A dropped candidate falls to the merge's default arm, whose policy
        // (design 3: `DynDispatchScope::default_arm`) fails closed when the
        // dropped type is a runtime type of the receiver. It used to be
        // called safe here: the default arm drops its obligations.
        if dropped_candidate {
            ctx.record_aggregate_gap("dyn_dispatch_candidate_body_dropped");
        }

        // Part of #3980: Short-circuit Fn-trait shim to direct fn-item body.
        if callee_path.is_some_and(is_fn_trait_call) {
            // Only candidates whose `Fn*::call` resolved for this signature.
            let candidate_types: Vec<_> = candidates
                .iter()
                .filter(|c| concrete_bodies.iter().any(|b| b.vtable_id == c.vtable_id))
                .map(|c| (c.concrete_ty, c.vtable_id))
                .collect();
            let closure_captures =
                nested_fn_trait_closure_captures(ctx, args, outer_body, local_exprs, resolver);
            let mut_ref_args =
                args.get(1).map(|arg| ctx.inline_rustcall_mut_ref_args(arg)).unwrap_or_default();
            let receiver_origin =
                args.first().and_then(|arg| ctx.inline_native_dyn_origin(arg, outer_body.locals()));
            if let Some(r) = try_fn_trait_direct_dispatch(
                ctx,
                &candidate_types,
                &scope,
                Some(&vtable_disc),
                &translated_args,
                receiver_origin.as_ref(),
                &mut_ref_args,
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
            Some(&scope),
        );
    }

    // A renamed float intrinsic reaches its model, never Trust's fallback body: no body to
    // walk, as on the nightly (`intrinsics::is_modelled_renamed_intrinsic`).
    if crate::intrinsics::is_modelled_renamed_intrinsic(&instance) {
        return None;
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
    ctx.inline_walk_param_address_seeds = Some(nested_address_seeds.clone());
    ctx.inline_walk_param_referent_seeds = Some(nested_referent_seeds.clone());
    ctx.inline_walk_param_mut_owner_seeds = Some(nested_mut_owner_seeds.clone());
    ctx.inline_walk_param_rustcall_mut_owner_seeds = Some(nested_rustcall_mut_owner_seeds.clone());
    let readonly_ref_seeds = ctx.readonly_ref_call_seeds(args, &fn_body);
    // RustCall's native body may spread a singleton into a reference
    // parameter even though the caller operand is a tuple. A current typed
    // read transports its value; every other such view must retain refusal
    // authority rather than silently losing the tuple's address carrier.
    for (i, argument) in args.iter().enumerate() {
        let Some(parameter) = fn_body.locals().get(i + 1).map(|decl| ctx.resolve_body_ty(decl.ty))
        else {
            continue;
        };
        let Ok(actual) = argument.ty(outer_body.locals()) else { continue };
        if matches!(
            parameter.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Not))
        ) && matches!(ctx.resolve_body_ty(actual).kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.as_slice() == [parameter])
            && !readonly_ref_seeds.iter().any(|(local, _)| *local == i + 1)
            && !nested_mut_owner_seeds.iter().any(|(local, _)| *local == i + 1)
            && !nested_address_seeds.contains(&(i + 1))
        {
            nested_address_seeds.push(i + 1);
        }
    }
    ctx.inline_walk_param_address_seeds = Some(nested_address_seeds.clone());
    ctx.inline_walk_param_readonly_ref_seeds = Some(readonly_ref_seeds.clone());
    ctx.inline_walk_param_native_dyn_seeds = Some(native_dyn_seeds.clone());
    ctx.inline_walk_param_native_drop_seeds = Some(native_drop_seeds.clone());
    let bool_helper =
        try_inline_simple_bool_return_helper(ctx, &fn_body, &translated_args, callee_path);
    ctx.inline_walk_param_address_seeds = None;
    ctx.inline_walk_param_referent_seeds = None;
    ctx.inline_walk_param_mut_owner_seeds = None;
    ctx.inline_walk_param_rustcall_mut_owner_seeds = None;
    ctx.inline_walk_param_readonly_ref_seeds = None;
    ctx.inline_walk_param_native_dyn_seeds = None;
    ctx.inline_walk_param_native_drop_seeds = None;
    if let Some(expr) = bool_helper {
        return Some(InlineReturn::value_only(expr));
    }
    ctx.mark_inline_field_reads(&fn_body, &translated_args, 0);
    ctx.inline_walk_param_address_seeds = Some(nested_address_seeds);
    ctx.inline_walk_param_referent_seeds = Some(nested_referent_seeds);
    ctx.inline_walk_param_mut_owner_seeds = Some(nested_mut_owner_seeds);
    ctx.inline_walk_param_rustcall_mut_owner_seeds = Some(nested_rustcall_mut_owner_seeds);
    ctx.inline_walk_param_readonly_ref_seeds = Some(readonly_ref_seeds);
    ctx.inline_walk_param_native_dyn_seeds = Some(native_dyn_seeds);
    ctx.inline_walk_param_native_drop_seeds = Some(native_drop_seeds);
    let result = translate_inline_body_with_metadata(
        ctx,
        &fn_body,
        &translated_args,
        0,
        &caller_vtable_ids,
        &caller_subslice_lens,
        &caller_subslice_offsets,
        Some(instance),
        inline_depth + 1,
    );
    ctx.inline_walk_param_address_seeds = None;
    ctx.inline_walk_param_referent_seeds = None;
    ctx.inline_walk_param_mut_owner_seeds = None;
    ctx.inline_walk_param_rustcall_mut_owner_seeds = None;
    ctx.inline_walk_param_readonly_ref_seeds = None;
    ctx.inline_walk_param_native_dyn_seeds = None;
    ctx.inline_walk_param_native_drop_seeds = None;
    result
}

/// Part of #4057: When Vec::len or Vec::is_empty is called with a BV64 receiver
/// (e.g., closure-captured `&Vec<T>`), load the Vec from typed memory and
/// extract the len/is_empty result.  The known-call fast-path
/// (`inline_known_call_expr_for_callee_path`) only handles Vec DT receivers;
/// this fallback resolves the pointer→DT indirection.
fn try_inline_vec_accessor_via_memory(
    ctx: &mut ChcCtx<'_, '_>,
    func: &Operand,
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
    if !crate::codegen_ay::shared::vec_query_identity::vec_query_stub_is_authorized(
        ctx.tcx,
        func,
        outer_body.locals(),
        stub,
    ) {
        return None;
    }
    if translated_args.len() != 1 {
        return None;
    }
    let receiver = &translated_args[0];
    debug!(receiver_sort = ?receiver.sort(), "try_inline_vec_accessor_via_memory: receiver sort (#4057)");

    // Only a thin address can be loaded through here; an already-resolved Vec
    // datatype receiver is not pointer-shaped at all and declines. This decodes
    // the SHAPE — what makes the receiver an address is the `Ref`/`RawPtr`
    // argument type matched out of the MIR just below, not this test. (Kept in
    // the width test's original position on purpose: `Operand::ty` panics on an
    // out-of-bounds local, so it must stay behind the cheap shape filter.)
    let receiver_addr = PtrRepr::thin_address(receiver)?;

    // Resolve the pointee type: `&Vec<T>` -> `Vec<T>`.
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

    let loaded = ctx.load_from_memory(receiver_addr, pointee_ty).map(Val::into_expr);
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

/// Do a comparison call's reference arguments carry their REFERENTS' values?
///
/// The walker translates `&place` to the place's value where it resolves the
/// place (a field hint, a value-bound parameter) and to an address otherwise
/// (`&(*other).0` through an address-bound parameter). A comparison fast path
/// compares its arguments as values: a term whose sort is not its referent's
/// is an address, and a joined `(Ordering, u8)` compared against the promoted
/// constant it equals came back unequal, proving `!(o == (Ordering::Greater, 1))`
/// (tools/soundness-duals/negative/joined_enum_constant_payloads.rs). Unsized
/// referents keep their own lanes' representation and are not checked; a
/// referent type that does not translate counts as not carried.
fn comparison_ref_args_carry_referent_values(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
    translated_args: &[Expr],
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    args.iter().zip(translated_args).all(|(arg, term)| {
        let Ok(arg_ty) = arg.ty(locals) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ctx.resolve_body_ty(arg_ty).kind()
        else {
            return true;
        };
        let pointee = ctx.resolve_body_ty(pointee);
        if matches!(
            pointee.kind(),
            TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_) | RigidTy::Dynamic(..))
        ) {
            return true;
        }
        ChcCtx::translate_ty(pointee).is_some_and(|sort| *term.sort() == sort)
    })
}

/// Walk the body a fn pointer inside a walked body resolved to (closure bodies
/// use the RustCall local layout, plain functions the direct one). The closure
/// lane keeps the assert-guard side-channel: dropping it would silently lose
/// checks recorded inside the closure body.
#[allow(clippy::too_many_arguments)]
fn walk_nested_fn_ptr_target(
    ctx: &mut ChcCtx<'_, '_>,
    fn_body: rustc_public::mir::Body,
    is_closure: bool,
    translated_args: &[Expr],
    caller_vtable_ids: &HashMap<usize, Expr>,
    caller_subslice_lens: &HashMap<usize, Expr>,
    caller_subslice_offsets: &HashMap<usize, Expr>,
    address_seeds: &[usize],
    inline_depth: usize,
) -> Option<InlineReturn> {
    let effective = count_effective_blocks(&fn_body);
    if effective > inline_effective_block_limit(&fn_body, effective) {
        return None;
    }
    if is_closure {
        // RustCall layout: argument `i` is local `i + 2` (local 1 is the env).
        ctx.inline_walk_param_address_seeds =
            Some(address_seeds.iter().map(|local| local + 1).collect());
        let no_captures: Vec<Expr> = Vec::new();
        let (address_hints, _address_constraints) =
            ctx.build_inline_zst_param_address_hints(&fn_body, 0);
        let saved_inline_hints = ctx.inline_local_address_hints.take();
        if !address_hints.is_empty() {
            let body_key = &raw const fn_body as usize;
            ctx.inline_local_address_hints = Some((body_key, address_hints));
        }
        let result = super::super::inline_body::translate_closure_inline_result(
            ctx,
            &fn_body,
            translated_args,
            &no_captures,
            0,
            inline_depth + 1,
        )
        .map(|full| {
            let mut value_only = InlineReturn::value_only(full.value);
            value_only.deferred_checks = full.deferred_checks;
            // Lost-write record (docs/chc-hole-fix-designs-2026-09-24.md
            // section 2): keep the closure's alias updates, re-keyed from the
            // RustCall layout to the caller's argument numbering.
            value_only.alias_updates =
                super::super::inline_walk_guard::rekey_closure_alias_updates_for_caller(
                    ctx,
                    full.alias_updates,
                );
            value_only
        });
        ctx.inline_walk_param_address_seeds = None;
        ctx.inline_local_address_hints = saved_inline_hints;
        result
    } else {
        ctx.mark_inline_field_reads(&fn_body, translated_args, 0);
        ctx.inline_walk_param_address_seeds = Some(address_seeds.to_vec());
        let result = translate_inline_body_with_metadata(
            ctx,
            &fn_body,
            translated_args,
            0,
            caller_vtable_ids,
            caller_subslice_lens,
            caller_subslice_offsets,
            None,
            inline_depth + 1,
        );
        ctx.inline_walk_param_address_seeds = None;
        result
    }
}

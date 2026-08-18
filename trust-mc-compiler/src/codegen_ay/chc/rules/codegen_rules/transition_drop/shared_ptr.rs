// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared pointer (Arc/Rc) drop helpers for CHC encoding.
//!
//! Contains:
//! - `SharedPointerDeallocEffects`: deallocation effect accumulator
//! - `shared_pointer_inner_ty`: Arc<T>/Rc<T> inner type extraction
//! - `shared_pointer_drop_local_from_drop_arg`: operand→local resolution
//! - `shared_pointer_value_ptr_*`: heap pointer computation for drop
//! - `collect_shared_pointer_dealloc_effects`: RustDealloc-style heap metadata invalidation
//! - `try_translate_shared_pointer_inner_drop`: inline inner drop body
//! - `is_mutex_rwlock_drop`: Mutex/RwLock type detection
//!
//! Split from `codegen_drop.rs` — Part of #3927.

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::inline_body::InlineReturn;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::{
    rust_dealloc_base_pointer_guard, rust_dealloc_base_ptr_for_known_alloc_id,
    rust_dealloc_obj_id_expr, rust_dealloc_validity_guard,
};
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;

pub(in crate::codegen_ay::chc) struct SharedPointerDeallocEffects {
    pub pending_checks: Vec<ay_bindings::Expr>,
    pub pending_updates: Vec<ay_bindings::Expr>,
}

pub(super) fn shared_pointer_value_ptr_from_alloc_id(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    pointee_ty: rustc_public::ty::Ty,
) -> Option<ay_bindings::Expr> {
    let obj_id = ctx.known_alloc_ids.get(&local_idx).copied()?;
    shared_pointer_value_ptr_from_obj_id(ctx, obj_id, pointee_ty)
}

pub(in crate::codegen_ay::chc) fn shared_pointer_value_ptr_from_obj_id(
    ctx: &ChcCtx<'_, '_>,
    obj_id: u32,
    pointee_ty: rustc_public::ty::Ty,
) -> Option<ay_bindings::Expr> {
    let base_ptr = ay_bindings::Expr::bitvec_const(obj_id as u128, 32)
        .concat(ay_bindings::Expr::bitvec_const(0u128, 32));
    let effective_pointee_ty = ctx.normalize_unique_dyn_tail_ty(pointee_ty);
    let header_size = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
    let align = ctx.get_type_align(effective_pointee_ty).unwrap_or(1);
    let value_offset = if align <= 1 { header_size } else { header_size.div_ceil(align) * align };

    Some(if value_offset == 0 {
        base_ptr
    } else {
        base_ptr.bvadd(ay_bindings::Expr::bitvec_const(
            value_offset as u128,
            crate::codegen_ay::types::POINTER_WIDTH,
        ))
    })
}

pub(in crate::codegen_ay::chc) fn shared_pointer_inner_ty(
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    use rustc_public::CrateDef;
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if {
                let name = def.trimmed_name();
                name == "Arc" || name == "Rc"
            } =>
        {
            args.0.first().and_then(|arg| match arg {
                GenericArgKind::Type(inner_ty) => Some(*inner_ty),
                _ => None,
            })
        }
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn shared_pointer_drop_local_from_drop_arg(
    ctx: &ChcCtx<'_, '_>,
    arg: &rustc_public::mir::Operand,
) -> Option<usize> {
    let (rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)) = arg
    else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    match ctx.ref_resolution.ref_targets.get(&place.local) {
        Some(target) if target.projections.is_empty() => Some(target.local),
        Some(_) => None,
        None => Some(place.local),
    }
}

fn shared_pointer_value_offset(ctx: &ChcCtx<'_, '_>, pointee_ty: rustc_public::ty::Ty) -> u64 {
    let effective_pointee_ty = ctx.normalize_unique_dyn_tail_ty(pointee_ty);
    let header_size = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
    let align = ctx.get_type_align(effective_pointee_ty).unwrap_or(1);
    if align <= 1 { header_size } else { header_size.div_ceil(align) * align }
}

/// The Rc/Arc header ADDRESS held in the wrapper.
///
/// Wave 4: the `width == 2 * POINTER_WIDTH` test this replaces chose which half
/// of a wide pointer names the allocation that the drop path then FREES, on a
/// coincidence that a widened thin pointer satisfies just as well as a real fat
/// one. `PtrRepr` decides it structurally and `into_data` is total, so all three
/// shapes yield their address half and nothing else changes.
///
/// `extract_pointer_expr` is one of the encoder's address producers. Its
/// `unwrap_or_else` fallback, however, is the RAW wrapper term — nothing
/// produced it as an address — so when `PtrRepr` cannot decode that term this
/// function returns `None` instead of tagging it. It used to spell the failure
/// `map_or_else(|| Loc::of_address(storage), ..)`, which asserted address-ness
/// of precisely the terms the decoder had just declined to recognize, on a path
/// that goes on to FREE whatever the tag names. Both callers already fail closed
/// through `split_pointer`, so `None` costs nothing they were not already
/// handling.
fn shared_pointer_storage_expr(wrapper_expr: &ay_bindings::Expr) -> Option<Loc> {
    let storage = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(wrapper_expr)
        .map(Loc::into_expr)
        .unwrap_or_else(|| wrapper_expr.clone());
    PtrRepr::classify(&storage).map(PtrRepr::into_data)
}

pub(in crate::codegen_ay::chc) fn shared_pointer_value_ptr_for_drop(
    ctx: &ChcCtx<'_, '_>,
    local_idx: Option<usize>,
    pointee_ty: rustc_public::ty::Ty,
    wrapper_expr: &ay_bindings::Expr,
) -> Option<ay_bindings::Expr> {
    if let Some(local_idx) = local_idx
        && let Some(ptr) = shared_pointer_value_ptr_from_alloc_id(ctx, local_idx, pointee_ty)
    {
        return Some(ptr);
    }

    let storage = shared_pointer_storage_expr(wrapper_expr)?.into_expr();
    let value_offset = shared_pointer_value_offset(ctx, pointee_ty);
    Some(if value_offset == 0 {
        storage
    } else {
        storage.bvadd(ay_bindings::Expr::bitvec_const(
            value_offset as u128,
            crate::codegen_ay::types::POINTER_WIDTH,
        ))
    })
}

pub(in crate::codegen_ay::chc) fn collect_shared_pointer_dealloc_effects(
    ctx: &mut ChcCtx<'_, '_>,
    wrapper_expr: &ay_bindings::Expr,
    known_alloc_id: Option<u32>,
) -> Option<SharedPointerDeallocEffects> {
    use crate::codegen_ay::chc::codegen_expr_heap::{
        obj_size_in, obj_size_out, obj_valid_in, obj_valid_out,
    };
    use ay_bindings::Expr;

    let storage = match known_alloc_id {
        Some(alloc_id) => rust_dealloc_base_ptr_for_known_alloc_id(alloc_id),
        None => shared_pointer_storage_expr(wrapper_expr)?.into_expr(),
    };
    let (raw_obj_id_expr, offset_expr) = ctx.split_pointer(&storage)?;
    let obj_id_expr = rust_dealloc_obj_id_expr(raw_obj_id_expr, known_alloc_id);

    let obj_valid_in = obj_valid_in();
    let obj_size_in = obj_size_in();
    let is_valid = rust_dealloc_validity_guard(&obj_valid_in, &obj_size_in, &obj_id_expr);
    let offset_zero = rust_dealloc_base_pointer_guard(&obj_size_in, &obj_id_expr, offset_expr);

    let mut pending_updates = Vec::new();
    for stack_obj_id in ctx.heap_state.stack_local_obj_ids() {
        let stack_id_expr = Expr::bitvec_const(stack_obj_id as i128, 32);
        pending_updates.push(obj_id_expr.clone().eq(stack_id_expr).not());
    }
    let freed = obj_valid_out().eq(obj_valid_in.store(obj_id_expr, Expr::bool_const(false)));
    let size_preserved = obj_size_out().eq(obj_size_in);
    pending_updates.push(freed);
    pending_updates.push(size_preserved);
    ctx.mark_heap_metadata_modified();

    Some(SharedPointerDeallocEffects {
        pending_checks: vec![is_valid, offset_zero],
        pending_updates,
    })
}

pub(in crate::codegen_ay::chc) fn try_translate_shared_pointer_inner_drop(
    ctx: &mut ChcCtx<'_, '_>,
    pointee_ty: rustc_public::ty::Ty,
    wrapper_local_idx: Option<usize>,
    wrapper_alloc_id: Option<u32>,
    wrapper_expr: &ay_bindings::Expr,
    bb_idx: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    use rustc_public::mir::mono::Instance;

    if super::no_drop::ty_trivially_no_drop(pointee_ty) || is_mutex_rwlock_drop(pointee_ty) {
        return None;
    }
    let drop_instance = Instance::resolve_drop_in_place(pointee_ty);
    if drop_instance.is_empty_shim() {
        return None;
    }
    let Some(body) = drop_instance.body() else {
        return None;
    };
    let Some(self_expr) = wrapper_alloc_id
        .and_then(|obj_id| shared_pointer_value_ptr_from_obj_id(ctx, obj_id, pointee_ty))
        .or_else(|| {
            shared_pointer_value_ptr_for_drop(ctx, wrapper_local_idx, pointee_ty, wrapper_expr)
        })
    else {
        return None;
    };
    let params = [self_expr];
    ctx.register_callee_body_statics(&body);
    ctx.mark_inline_field_reads(&body, &params, bb_idx);
    let mut caller_vtable_ids = std::collections::HashMap::new();
    // Seed vtable IDs for dyn members inside the pointee type so that
    // drop_in_place::<dyn Trait> calls inside the drop body can resolve
    // vtable dispatch instead of falling back to virtual_missing_vtable.
    seed_shared_pointer_inner_drop_vtable(
        ctx,
        pointee_ty,
        wrapper_local_idx,
        wrapper_expr,
        &body,
        &mut caller_vtable_ids,
    );
    let result = crate::codegen_ay::chc::call::inline_body::translate_inline_body(
        ctx,
        &body,
        &params,
        bb_idx,
        &caller_vtable_ids,
        Some(drop_instance),
        inline_depth,
    );
    result
}

/// Seed vtable discriminant IDs for dyn trait members within an Rc/Arc inner
/// drop body. Without this, `drop_in_place::<dyn Trait>` calls inside the drop
/// shim for `Wrapper<dyn Trait>` produce `virtual_missing_vtable` translation
/// drops, leading to spurious CTREX.
///
/// Drop shims for `Wrapper<dyn Trait>` contain Drop terminators on fields like
/// `(*_1).inner` where `inner: dyn Trait`. The inline walker processes these
/// via `try_handle_inline_dyn_drop`, which looks up vtable from:
/// 1. `inline_vtable_ids[place.local]` — seeded here for the self param (local 1)
/// 2. `dyn_projection_locals` — locals assigned via dyn-producing casts
///
/// Strategy:
/// 1. Try the wrapper local's known vtable from the outer context.
/// 2. Fall back to collect_dyn_trait_candidates — if exactly one candidate,
///    use its vtable ID directly.
fn seed_shared_pointer_inner_drop_vtable(
    ctx: &ChcCtx<'_, '_>,
    pointee_ty: rustc_public::ty::Ty,
    wrapper_local_idx: Option<usize>,
    wrapper_expr: &ay_bindings::Expr,
    drop_body: &rustc_public::mir::Body,
    caller_vtable_ids: &mut std::collections::HashMap<usize, ay_bindings::Expr>,
) {
    // Only needed when pointee_ty contains a dyn trait tail.
    let Some(dyn_tail) =
        crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, pointee_ty)
    else {
        return;
    };

    // Collect target locals: dyn-cast locals, the self parameter (local 1),
    // locals referenced by Drop terminators with dyn types, and locals
    // whose declared type is dyn or &mut dyn.
    let mut target_locals = super::dyn_dispatch::dyn_projection_locals(ctx, drop_body);
    target_locals.push(1);
    for (idx, local_decl) in drop_body.locals().iter().enumerate() {
        let local_ty = ctx.resolve_body_ty(local_decl.ty);
        let is_dyn = matches!(
            local_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Dynamic(..))
        );
        let is_ref_dyn = matches!(local_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, pointee, _))
            | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(pointee, _))
            if matches!(ctx.resolve_body_ty(pointee).kind(),
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Dynamic(..))));
        if is_dyn || is_ref_dyn {
            target_locals.push(idx);
        }
    }
    for block in &drop_body.blocks {
        if let rustc_public::mir::TerminatorKind::Drop { place, .. } = &block.terminator.kind {
            let drop_place_ty = place.ty(drop_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty));
            if drop_place_ty.is_some_and(|ty| {
                crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, ty).is_some()
            }) {
                target_locals.push(place.local);
            }
        }
    }
    target_locals.sort_unstable();
    target_locals.dedup();

    if target_locals.is_empty() {
        return;
    }

    // Strategy 1: Use the wrapper local's tracked vtable from the outer context.
    if let Some(local_idx) = wrapper_local_idx {
        if let Some(vtable_expr) = ctx.known_vtable_expr_for_local(local_idx) {
            for &target_local in &target_locals {
                caller_vtable_ids.entry(target_local).or_insert_with(|| vtable_expr.clone());
            }
            return;
        }
    }

    // Strategy 1b: Extract vtable from the wrapper expression itself.
    if let Some(vtable_expr) = ctx.extract_embedded_vtable_expr(wrapper_expr).map(Val::into_expr) {
        for &target_local in &target_locals {
            caller_vtable_ids.entry(target_local).or_insert_with(|| vtable_expr.clone());
        }
        return;
    }

    // Strategy 2: If there's exactly one concrete candidate for this trait,
    // use its vtable ID directly. This handles the common case where the
    // harness creates one concrete type implementing the trait.
    let Some(trait_def_id) =
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, dyn_tail)
    else {
        return;
    };
    let candidates =
        crate::codegen_ay::chc::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.len() == 1 {
        let vtable_expr = ay_bindings::Expr::bitvec_const(
            candidates[0].vtable_id as u128,
            crate::codegen_ay::types::POINTER_WIDTH,
        );
        for &target_local in &target_locals {
            caller_vtable_ids.entry(target_local).or_insert_with(|| vtable_expr.clone());
        }
    }
}

/// Part of #4067: Check if a type is Mutex<T> or RwLock<T> (or a reference to one).
pub(super) fn is_mutex_rwlock_drop(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let name = def.trimmed_name();
            matches!(
                name.as_str(),
                "Mutex" | "RwLock" | "MutexGuard" | "RwLockReadGuard" | "RwLockWriteGuard"
            )
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => is_mutex_rwlock_drop(inner),
        _ => false,
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vtable propagation through inlined virtual method bodies.
//!
//! Part of #3159: DynTrait vtable tracking.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{
    AggregateKind, CastKind, LocalDecl, Operand, Place, PointerCoercion, Rvalue,
};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashMap;

use rustc_public::CrateDef;

use super::super::ChcCtx;
use crate::codegen_ay::chc::call::inline_shared::{
    PlaceResolver, inline_operand_to_expr, resolve_place,
};
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};

/// Part of #3159: Propagate vtable discriminant through inline body assignments.
pub(in crate::codegen_ay::chc) fn propagate_inline_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    dst_local: usize,
    dst_expr: &Expr,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    inline_vtable_ids: &mut HashMap<usize, Expr>,
) {
    // Capture vtable from Dyn_Trait Datatype expressions.
    if let ay_bindings::SortInner::Datatype(dt) = dst_expr.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            if cons.has_field("fld_vtable") {
                let vtable_expr = dst_expr.clone().field_select(
                    &dt.name,
                    "fld_vtable",
                    Sort::bitvec(POINTER_WIDTH),
                );
                inline_vtable_ids.insert(dst_local, vtable_expr);
                return;
            }
        }
    }

    if let Some(vtable_expr) = inline_unsize_dyn_vtable(ctx, rvalue, locals) {
        inline_vtable_ids.insert(dst_local, vtable_expr);
        return;
    }

    if let Some(vtable_expr) =
        inline_raw_ptr_dyn_metadata_vtable(ctx, rvalue, dst_local, local_exprs, resolver, locals)
    {
        inline_vtable_ids.insert(dst_local, vtable_expr);
        return;
    }

    if let Some(vtable_expr) = projected_source_vtable(ctx, rvalue, local_exprs, resolver, locals) {
        inline_vtable_ids.insert(dst_local, vtable_expr);
        return;
    }

    if let Some(vtable_expr) = projected_heap_forward_vtable(ctx, rvalue, local_exprs) {
        inline_vtable_ids.insert(dst_local, vtable_expr);
        return;
    }

    let preserve_seeded_projected_dyn = match rvalue {
        Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) => {
            !src.projection.is_empty()
                && super::super::dyn_coercion::find_dyn_trait_tail_ty(
                    ctx,
                    ctx.resolve_body_ty(*target_ty),
                )
                .is_some()
        }
        _ => false,
    };
    if preserve_seeded_projected_dyn && inline_vtable_ids.contains_key(&dst_local) {
        return;
    }

    // Propagate from source local for identity-like rvalues.
    let src_local = match rvalue {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p.local),
        Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place) => Some(place.local),
        Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => Some(p.local),
        _ => None,
    };
    if let Some(src) = src_local {
        if let Some(vtable) = inline_vtable_ids.get(&src).cloned() {
            inline_vtable_ids.insert(dst_local, vtable);
        }
    }
}

fn inline_raw_ptr_dyn_metadata_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    dst_local: usize,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let Rvalue::Aggregate(AggregateKind::RawPtr(_, _), operands) = rvalue else {
        return None;
    };
    let metadata = operands.get(1)?;
    let dest_ty = ctx.resolve_body_ty(locals.get(dst_local)?.ty);
    let pointee = match dest_ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
        _ => return None,
    };
    super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, ctx.resolve_body_ty(pointee))?;
    inline_operand_to_expr(ctx, metadata, local_exprs, resolver, locals)
}

fn projected_source_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let (src, target_ty) = match rvalue {
        Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty)
            if !src.projection.is_empty() =>
        {
            (src, *target_ty)
        }
        _ => return None,
    };
    if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, ctx.resolve_body_ty(target_ty))
        .is_none()
    {
        return None;
    }

    let src_expr = resolve_place(ctx, local_exprs, src, resolver, locals)?;
    let embedded = ctx.extract_embedded_vtable_expr(&src_expr);
    let heap = heap_forward_vtable_for_expr(ctx, &src_expr).or_else(|| {
        ctx.extract_pointer_storage_expr(&src_expr)
            .and_then(|ptr| heap_forward_vtable_for_expr(ctx, &ptr))
    });
    embedded.or(heap)
}

fn projected_heap_forward_vtable(
    ctx: &ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
) -> Option<Expr> {
    let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), target_ty) = rvalue else {
        return None;
    };
    if src.projection.is_empty()
        || !matches!(src.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
    {
        return None;
    }
    let target_ty = ctx.resolve_body_ty(*target_ty);
    if super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, target_ty).is_none() {
        return None;
    }

    let root_expr = local_exprs.get(&src.local)?;
    let addr = super::super::dyn_coercion::extract_pointer_expr(root_expr)
        .unwrap_or_else(|| root_expr.clone());
    heap_forward_vtable_for_expr(ctx, &addr)
}

fn heap_forward_vtable_for_expr(ctx: &ChcCtx<'_, '_>, expr: &Expr) -> Option<Expr> {
    if let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(expr) {
        let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
        if let Some(vtable) = ctx.heap_state.region_vtable_forwards.get(&fwd_key) {
            return Some(vtable.clone());
        }
    }
    ctx.heap_state.region_vtable_forward_exprs.get(&format!("{expr}")).cloned()
}

fn inline_unsize_dyn_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    locals: &[LocalDecl],
) -> Option<Expr> {
    use crate::kani_middle::abi::LayoutOf;
    use rustc_public::rustc_internal;
    use rustc_public::ty::ExistentialPredicate;

    let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, target_ty) =
        rvalue
    else {
        return None;
    };

    let target_inner = super::super::dyn_coercion::peel_pointer_like_wrapper_ty(*target_ty);
    let dyn_tail = super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, target_inner)?;
    let TyKind::RigidTy(RigidTy::Dynamic(ref predicates, _)) = dyn_tail.kind() else {
        return None;
    };

    let principal = predicates.first()?;
    let trait_def_id = match &principal.value {
        ExistentialPredicate::Trait(trait_ref) => {
            rustc_internal::internal(ctx.tcx, trait_ref.def_id.def_id())
        }
        // Part of #4097 D2: Handle auto-trait-only dyn types (dyn Send/Sync).
        ExistentialPredicate::AutoTrait(trait_def) => {
            use rustc_public::CrateDef;
            rustc_internal::internal(ctx.tcx, trait_def.def_id())
        }
        _ => return None,
    };

    let src_ty = operand.ty(locals).ok()?;
    let src_inner = super::super::dyn_coercion::peel_pointer_like_wrapper_ty(src_ty);
    let concrete_for_vtable =
        super::super::dyn_coercion::extract_concrete_tail_for_dyn(src_inner, target_inner);
    let vtable_src = rustc_internal::stable(rustc_internal::internal(ctx.tcx, concrete_for_vtable));

    let candidates = super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    let vtable_id = super::super::dyn_coercion::resolve_vtable_id(&candidates, vtable_src)?;

    let layout = LayoutOf::new(vtable_src);
    if let (Some(size), Some(align)) = (layout.size_of(), layout.align_of()) {
        ctx.vtable_type_metadata.entry(vtable_id).or_insert((size as u64, align as u64));
    }

    Some(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH))
}

/// Propagate vtable from call arguments to the call result.
///
/// Part of #3589: Fixes UNKNOWN verdict for Box/Rc/custom dyn coercions.
pub(in crate::codegen_ay::chc) fn propagate_vtable_through_call(
    args: &[Operand],
    dst_local: usize,
    dst_expr: &Expr,
    inline_vtable_ids: &mut HashMap<usize, Expr>,
) {
    // If the result already has Dyn_Trait sort, extract vtable directly.
    if let ay_bindings::SortInner::Datatype(dt) = dst_expr.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            if cons.has_field("fld_vtable") {
                let vtable_expr = dst_expr.clone().field_select(
                    &dt.name,
                    "fld_vtable",
                    Sort::bitvec(POINTER_WIDTH),
                );
                inline_vtable_ids.insert(dst_local, vtable_expr);
                return;
            }
        }
    }

    // Propagate from the receiver (first argument) if it has a known vtable.
    if let Some(receiver) = args.first() {
        let receiver_local = match receiver {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        };
        if let Some(local) = receiver_local {
            if let Some(vtable) = inline_vtable_ids.get(&local).cloned() {
                inline_vtable_ids.insert(dst_local, vtable);
            }
        }
    }
}

pub(in crate::codegen_ay::chc) fn attach_spawn_task_slot_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: Option<&str>,
    destination: &Place,
    body: &rustc_public::mir::Body,
    result: &mut super::InlineReturn,
) {
    if result.vtable.is_some() {
        return;
    }
    let Some(callee_path) = callee_path else {
        return;
    };
    if !callee_path.contains("Option")
        || (!callee_path.ends_with("::as_mut") && !callee_path.ends_with("::take"))
    {
        return;
    }
    if !destination_is_spawn_task_slot_option(ctx, destination, body) {
        return;
    }
    let take_none_expr = callee_path.ends_with("::take").then(|| {
        destination
            .ty(body.locals())
            .ok()
            .map(|ty| ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)
            .and_then(|sort| ctx.make_none_expr_for_option(&sort))
    });
    let Some(model) = ctx.spawn_scheduler_vtable_model.as_mut() else {
        return;
    };
    let vtable = if callee_path.ends_with("::as_mut") {
        model.next_vtable_expr()
    } else {
        let current = model.current_vtable_expr();
        model.clear_current_vtable();
        current
    };
    if let Some(vtable) = vtable {
        result.vtable = Some(vtable);
    }
    if let Some(Some(none_expr)) = take_none_expr
        && !result.alias_updates.contains_key(&1)
    {
        result.alias_updates.insert(1, none_expr);
    }
}

fn destination_is_spawn_task_slot_option(
    ctx: &ChcCtx<'_, '_>,
    destination: &Place,
    body: &rustc_public::mir::Body,
) -> bool {
    let Ok(dest_ty) = destination.ty(body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    let payload_ty = match dest_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
            args.0.iter().find_map(|arg| match arg {
                GenericArgKind::Type(ty) => Some(ctx.resolve_body_ty(*ty)),
                _ => None,
            })
        }
        _ => None,
    };
    let Some(payload_ty) = payload_ty else {
        return false;
    };
    let Some(dyn_tail) = super::super::dyn_coercion::find_dyn_trait_tail_ty(ctx, payload_ty) else {
        return false;
    };
    let Some(trait_def_id) = super::super::dyn_coercion::extract_dyn_trait_def_id(ctx, dyn_tail)
    else {
        return false;
    };
    let trait_path = ctx.tcx.def_path_str(trait_def_id);
    trait_path == "core::future::future::Future" || trait_path.ends_with("::Future")
}

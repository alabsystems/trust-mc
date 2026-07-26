// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer-wrapper helpers for virtual-inline nested call handling.

use std::collections::{BTreeMap, HashMap};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr, resolve_place};
use super::inline_alloc_helpers::{emit_inline_alloc_metadata, inline_alloc_size_expr};
use super::inline_call_classify::is_nested_pointer_wrapper_deref_call;
use super::loop_replay::InlineWalkCtx;
use super::{InlineReturn, receiver_base_local};
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

fn path_mentions_pointer_wrapper(path: &str, wrapper: &str) -> bool {
    path.contains(wrapper) || path.contains(&format!("{wrapper}::"))
}

fn inline_box_new_payload_vtable(
    ctx: &ChcCtx<'_, '_>,
    arg: &Operand,
    value_expr: &Expr,
    inline_vtable_ids: &HashMap<usize, Expr>,
) -> Option<Expr> {
    receiver_base_local(arg)
        .and_then(|local_idx| {
            inline_vtable_ids
                .get(&local_idx)
                .cloned()
                .or_else(|| ctx.known_vtable_expr_for_local(local_idx))
        })
        .or_else(|| ctx.extract_embedded_vtable_expr(value_expr))
}

fn record_inline_heap_vtable_forward(ctx: &mut ChcCtx<'_, '_>, addr: &Expr, vtable: Option<Expr>) {
    let Some(vtable_expr) = vtable else {
        return;
    };
    if let Some((obj_id, offset)) = ChcCtx::try_extract_constant_addr(addr) {
        let fwd_key = ((obj_id as u64) << 32) | (offset as u64);
        ctx.heap_state.region_vtable_forwards.insert(fwd_key, vtable_expr.clone());
    }
    ctx.heap_state.region_vtable_forward_exprs.insert(format!("{addr}"), vtable_expr);
}

fn record_inline_loaded_value_vtable_forward(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    store_ty: rustc_public::ty::Ty,
    vtable: Option<Expr>,
) {
    let Some(vtable_expr) = vtable else {
        return;
    };
    let Some(loaded) = ctx.load_from_memory(addr.clone(), store_ty) else {
        return;
    };
    record_inline_heap_vtable_forward(ctx, &loaded, Some(vtable_expr.clone()));
    if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
        store_ty.kind()
        && let Some(variant) = def.variants().first()
        && variant.fields().len() == 1
    {
        let field_ty = ctx.resolve_body_ty(variant.fields()[0].ty_with_args(&args));
        if let Some(field_loaded) = ctx.load_from_memory(addr.clone(), field_ty) {
            record_inline_heap_vtable_forward(ctx, &field_loaded, Some(vtable_expr.clone()));
        }
    }
    if let Some(ptr_expr) = ctx.extract_pointer_storage_expr(&loaded) {
        record_inline_heap_vtable_forward(ctx, &ptr_expr, Some(vtable_expr));
    }
}

fn record_inline_loaded_wrapper_payload_vtable_forward(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    store_ty: rustc_public::ty::Ty,
    vtable: Option<Expr>,
) {
    let Some(vtable_expr) = vtable else {
        return;
    };
    let Some(loaded) = ctx.load_from_memory(addr.clone(), store_ty) else {
        return;
    };
    record_inline_heap_vtable_forward(ctx, &loaded, Some(vtable_expr.clone()));
    if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
        store_ty.kind()
        && let Some(variant) = def.variants().first()
        && variant.fields().len() == 1
    {
        let field_ty = ctx.resolve_body_ty(variant.fields()[0].ty_with_args(&args));
        if let Some(field_loaded) = ctx.load_from_memory(addr.clone(), field_ty) {
            record_inline_heap_vtable_forward(ctx, &field_loaded, Some(vtable_expr));
        }
    }
}

pub(super) fn inline_pointer_wrapper_deref_result_ptr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    destination: &rustc_public::mir::Place,
    outer_body: &rustc_public::mir::Body,
    ptr_expr: Expr,
) -> Option<Expr> {
    if path_mentions_pointer_wrapper(callee_path, "boxed::Box") {
        return Some(ptr_expr);
    }

    if path_mentions_pointer_wrapper(callee_path, "rc::Rc")
        || path_mentions_pointer_wrapper(callee_path, "sync::Arc")
    {
        let dest_ty = ctx.resolve_body_ty(destination.ty(outer_body.locals()).ok()?);
        let pointee_ty = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };
        let effective_pointee_ty = ctx.normalize_unique_dyn_tail_ty(pointee_ty);

        let header_size = 2u64 * (POINTER_WIDTH as u64 / 8);
        // Part of #4014: default to align=1 when pointee is unsized dyn Trait.
        let align = ctx.get_type_align(effective_pointee_ty).unwrap_or(1);
        let value_offset =
            if align <= 1 { header_size } else { header_size.div_ceil(align) * align };

        return Some(if value_offset == 0 {
            ptr_expr
        } else {
            ptr_expr.bvadd(Expr::bitvec_const(value_offset as u128, POINTER_WIDTH))
        });
    }

    Some(ptr_expr)
}

pub(super) fn resolve_inline_ref_local_target_place(
    body: &rustc_public::mir::Body,
    local: usize,
    depth_remaining: usize,
) -> Option<rustc_public::mir::Place> {
    if depth_remaining == 0 {
        return None;
    }

    let mut target_place = None;
    for block in &body.blocks {
        for stmt in &block.statements {
            let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != local || !lhs.projection.is_empty() {
                continue;
            }

            let candidate = match rhs {
                rustc_public::mir::Rvalue::Ref(_, _, place)
                | rustc_public::mir::Rvalue::AddressOf(_, place) => {
                    // Part of #4193: AddressOf(Mut, (*_N)) produces a place
                    // with a Deref projection. Resolve through the intermediate
                    // reference to find the underlying local.
                    if place.projection.len() == 1
                        && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
                    {
                        resolve_inline_ref_local_target_place(
                            body,
                            place.local,
                            depth_remaining - 1,
                        )
                    } else {
                        Some(place.clone())
                    }
                }
                rustc_public::mir::Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | rustc_public::mir::Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() =>
                {
                    resolve_inline_ref_local_target_place(body, src.local, depth_remaining - 1)
                }
                _ => None,
            };

            if let Some(candidate) = candidate {
                if target_place.as_ref().is_some_and(|existing| existing != &candidate) {
                    return None;
                }
                target_place = Some(candidate);
            }
        }
    }

    target_place
}

pub(super) fn resolve_inline_writeback_target_place<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    place: &rustc_public::mir::Place,
    value: &Expr,
) -> Option<rustc_public::mir::Place> {
    if !place.projection.is_empty() {
        return None;
    }
    let local_ty = ctx.resolve_body_ty(walk_ctx.locals.get(place.local)?.ty);
    if !matches!(local_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
        return None;
    }
    let local_sort = ChcCtx::translate_ty(local_ty)?;
    if local_sort == *value.sort() {
        return None;
    }
    resolve_inline_ref_local_target_place(walk_ctx.body, place.local, 8)
}

pub(super) fn resolve_nested_ref_arg_referent<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    arg: &Operand,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }

    let arg_ty = ctx.resolve_body_ty(arg.ty(outer_body.locals()).ok()?);
    if !matches!(arg_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
        return None;
    }

    let target_place = resolve_inline_ref_local_target_place(outer_body, place.local, 8)?;
    resolve_place(ctx, local_exprs, &target_place, resolver, outer_body.locals())
}

pub(super) fn try_inline_pointer_wrapper_deref<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !is_nested_pointer_wrapper_deref_call(callee_path, args, outer_body) {
        return None;
    }

    let wrapper_expr = args.first().and_then(|arg| {
        resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver).or_else(|| {
            inline_operand_to_expr(ctx, arg, local_exprs, resolver, outer_body.locals())
        })
    })?;
    let ptr_expr = ctx.extract_pointer_storage_expr(&wrapper_expr)?;
    let ptr_expr = inline_pointer_wrapper_deref_result_ptr(
        ctx,
        callee_path,
        destination,
        outer_body,
        ptr_expr,
    )?;
    let dest_ty = destination.ty(outer_body.locals()).ok()?;

    let vtable = args
        .first()
        .and_then(receiver_base_local)
        .and_then(|local_idx| inline_vtable_ids.get(&local_idx).cloned())
        .or_else(|| {
            let width = wrapper_expr.sort().bitvec_width()?;
            (width == 2 * POINTER_WIDTH)
                .then(|| wrapper_expr.clone().extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH))
        })
        .or_else(|| {
            ctx.resolve_unique_wrapped_dyn_vtable_id(dest_ty)
                .map(|id| Expr::bitvec_const(id as u128, POINTER_WIDTH))
        });

    Some(InlineReturn {
        value: ptr_expr,
        vtable,
        alloc_id: None,
        alias_updates: BTreeMap::new(),
        deferred_checks: Vec::new(),
    })
}

pub(super) fn try_inline_rc_arc_new<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !ChcCtx::is_rc_arc_new_path(callee_path) || translated_args.len() != 1 {
        return None;
    }

    let obj_id = ctx.heap_state.next_heap_alloc_id()?;
    let arg_ty = args.first().and_then(|arg| arg.ty(outer_body.locals()).ok())?;
    let store_ty = ctx.resolve_body_ty(arg_ty);
    let size_expr = ctx
        .get_type_size(store_ty)
        .map(|size| Expr::bitvec_const(size as u128, 32))
        .unwrap_or_else(|| {
            ctx.record_sound_fallback_reason("inline_rc_arc_new_size_unknown");
            inline_alloc_size_expr(ctx, callee_path, args, outer_body, translated_args)
        });
    emit_inline_alloc_metadata(ctx, obj_id, size_expr, false);

    let alloc_ptr = Expr::bitvec_const((obj_id as u128) << 32, POINTER_WIDTH);
    let header_size = 2u64 * (POINTER_WIDTH as u64 / 8);
    let value_ptr = alloc_ptr.bvadd(Expr::bitvec_const(header_size as u128, POINTER_WIDTH));
    let value_expr = translated_args[0].clone();
    let mut extra = Vec::new();

    let prev_suppress = ctx.suppress_heap_store_checks;
    ctx.suppress_heap_store_checks = true;
    ctx.mirror_array_elements_to_flat_memory(&value_expr, store_ty, &value_ptr, &mut extra);
    // Part of #4014: Always emit the whole-struct store so that
    // `load_from_memory(addr, StructTy)` finds the value in `mem_StructTy`.
    // Additionally decompose into per-field stores so virtual dispatch that
    // reads individual fields (e.g., `mem_bool` for a bool field) also works.
    // Previously, decomposition success skipped the whole-struct store,
    // causing a store/load type-key mismatch: stores went to `mem_bool` but
    // loads read from `mem_Table` → unconstrained → false CTREX.
    ctx.try_decompose_struct_store(&value_ptr, &value_expr, store_ty, &mut extra);
    if let Some(store_constraint) = ctx.build_memory_store(value_ptr.clone(), value_expr, store_ty)
    {
        extra.push(store_constraint);
    }
    ctx.suppress_heap_store_checks = prev_suppress;
    ctx.heap_state.pending_updates.extend(extra);

    let dest_ty = destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty));
    let vtable = dest_ty
        .and_then(|ty| ctx.resolve_unique_wrapped_dyn_vtable_id(ty))
        .map(|id| Expr::bitvec_const(id as u128, POINTER_WIDTH));

    // Part of #4014: Return `value_ptr` (alloc + header offset) instead of
    // `alloc_ptr`. The inline walker context does not propagate
    // `known_alloc_ids`, so downstream `codegen_pointer_wrapper_deref_call`
    // falls to its extract-only path (no header addition). Baking the header
    // offset into the returned pointer matches the `from_inner_in` pattern
    // where the Rc local already points to the value field. Without this,
    // stores go to `alloc+0x10` but loads read from `alloc+0x00` → 16-byte
    // address mismatch → false CTREX.
    Some(InlineReturn {
        value: value_ptr,
        vtable,
        alloc_id: Some(obj_id),
        alias_updates: BTreeMap::new(),
        deferred_checks: Vec::new(),
    })
}

pub(super) fn try_inline_box_new<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    inline_vtable_ids: &HashMap<usize, Expr>,
    destination: &rustc_public::mir::Place,
) -> Option<InlineReturn> {
    if !path_mentions_pointer_wrapper(callee_path, "boxed::Box") || !callee_path.ends_with("::new")
    {
        return None;
    }
    if translated_args.len() != 1 {
        return None;
    }

    let obj_id = ctx.heap_state.next_heap_alloc_id()?;
    let arg_ty = args.first().and_then(|arg| arg.ty(outer_body.locals()).ok())?;
    let store_ty = ctx.resolve_body_ty(arg_ty);
    let size_expr = ctx
        .get_type_size(store_ty)
        .map(|size| Expr::bitvec_const(size as u128, 32))
        .unwrap_or_else(|| {
            ctx.record_sound_fallback_reason("inline_box_new_size_unknown");
            inline_alloc_size_expr(ctx, callee_path, args, outer_body, translated_args)
        });
    emit_inline_alloc_metadata(ctx, obj_id, size_expr, false);

    let alloc_ptr = Expr::bitvec_const((obj_id as u128) << 32, POINTER_WIDTH);
    let value_expr = translated_args[0].clone();
    let payload_vtable = args
        .first()
        .and_then(|arg| inline_box_new_payload_vtable(ctx, arg, &value_expr, inline_vtable_ids));
    let embedded_payload_vtable = ctx.extract_embedded_vtable_expr(&value_expr);
    let mut extra = Vec::new();

    let prev_suppress = ctx.suppress_heap_store_checks;
    ctx.suppress_heap_store_checks = true;
    ctx.mirror_array_elements_to_flat_memory(&value_expr, store_ty, &alloc_ptr, &mut extra);
    ctx.try_decompose_struct_store(&alloc_ptr, &value_expr, store_ty, &mut extra);
    if let Some(store_constraint) = ctx.build_memory_store(alloc_ptr.clone(), value_expr, store_ty)
    {
        extra.push(store_constraint);
    }
    ctx.suppress_heap_store_checks = prev_suppress;
    record_inline_heap_vtable_forward(ctx, &alloc_ptr, payload_vtable.clone());
    record_inline_loaded_value_vtable_forward(ctx, &alloc_ptr, store_ty, payload_vtable);
    record_inline_loaded_wrapper_payload_vtable_forward(
        ctx,
        &alloc_ptr,
        store_ty,
        embedded_payload_vtable,
    );
    ctx.heap_state.pending_updates.extend(extra);

    let dest_ty = destination.ty(outer_body.locals()).ok().map(|ty| ctx.resolve_body_ty(ty));
    let vtable = dest_ty
        .and_then(|ty| ctx.resolve_unique_wrapped_dyn_vtable_id(ty))
        .map(|id| Expr::bitvec_const(id as u128, POINTER_WIDTH));

    Some(InlineReturn {
        value: alloc_ptr,
        vtable,
        alloc_id: Some(obj_id),
        alias_updates: BTreeMap::new(),
        deferred_checks: Vec::new(),
    })
}

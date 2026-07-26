// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise inline `SliceIndex` handling for virtual-inline nested calls.
//! Part of #4050: pointer-backed slice/index fallback for raw-slice receivers.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;

use super::super::inline_shared::inline_operand_to_expr;
use super::super::inline_shared::place::inline_ref_place_to_expr;
use super::execution_state::InlineExecutionState;
use super::loop_replay::InlineWalkCtx;
use super::slice_index_metadata::propagate_inline_range_full_metadata;
use super::slice_index_trace::{
    MAX_INLINE_REF_SOURCE_TRACE_DEPTH, describe_inline_local_source, rawptr_aggregate_data_operand,
    trace_inline_source_place,
};
use super::terminator_exec::{TerminatorStep, apply_inline_writeback, resolve_inline_callee_path};
use crate::codegen_ay::chc::codegen_ctx::ChcCtx;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;

fn inline_slice_index_receiver_arg<'a>(
    ctx: &ChcCtx<'_, '_>,
    args: &'a [Operand],
    locals: &[LocalDecl],
) -> Option<(&'a Operand, &'a Operand)> {
    let is_slice_like = |op: &Operand| -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        let ty = ctx.resolve_body_ty(ty);
        let inner = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ctx.resolve_body_ty(inner),
            _ => return false,
        };
        let inner = match inner.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ctx.resolve_body_ty(inner),
            _ => inner,
        };
        matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Array(..)))
            || matches!(inner.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Vec")
    };

    let lhs = args.first()?;
    let rhs = args.get(1)?;
    if is_slice_like(lhs) {
        return Some((lhs, rhs));
    }
    if is_slice_like(rhs) {
        return Some((rhs, lhs));
    }
    Some((lhs, rhs))
}

fn coerce_inline_index_expr(expr: Expr) -> Option<Expr> {
    match expr.sort().bitvec_width() {
        Some(w) if w == crate::codegen_ay::types::POINTER_WIDTH => Some(expr),
        Some(w) if w < crate::codegen_ay::types::POINTER_WIDTH => {
            Some(expr.zero_extend(crate::codegen_ay::types::POINTER_WIDTH - w))
        }
        Some(_) => Some(expr.extract(crate::codegen_ay::types::POINTER_WIDTH - 1, 0)),
        None => None,
    }
}

fn materialize_inline_collection_receiver(
    ctx: &mut ChcCtx<'_, '_>,
    mut expr: Expr,
    mut ty: Ty,
) -> Option<(Expr, Ty, Option<Expr>)> {
    let mut collection_addr = None;
    loop {
        ty = ctx.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _))
                if expr.sort().bitvec_width() == Some(crate::codegen_ay::types::POINTER_WIDTH) =>
            {
                let addr = expr.clone();
                let inner = ctx.resolve_body_ty(inner);
                expr = ctx.load_from_memory(addr.clone(), inner)?;
                ty = inner;
                collection_addr = Some(addr);
            }
            _ => return Some((expr, ty, collection_addr)),
        }
    }
}

fn inline_collection_select_expr(collection_expr: Expr, index_expr: Expr) -> Option<Expr> {
    if collection_expr.sort().is_array() {
        return Some(collection_expr.select(index_expr));
    }
    let dt_name = collection_expr.sort().datatype_name()?.to_owned();
    let data_sort = ChcCtx::get_dt_field_sort(&collection_expr, "fld_data")?;
    if !data_sort.is_array() {
        return None;
    }
    let data = collection_expr.field_select(&dt_name, "fld_data", data_sort);
    Some(data.select(index_expr))
}

fn inline_collection_select_via_memory_model(
    ctx: &mut ChcCtx<'_, '_>,
    data_ptr: Expr,
    collection_ty: Ty,
    index_expr: Expr,
) -> Option<Expr> {
    let (elem_addr, elem_ty) =
        inline_collection_element_addr(ctx, data_ptr, collection_ty, index_expr)?;
    ctx.load_from_memory(elem_addr, elem_ty)
}

fn indexed_collection_elem_ty(ctx: &ChcCtx<'_, '_>, ty: Ty) -> Option<Ty> {
    let ty = ctx.resolve_body_ty(ty);
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            indexed_collection_elem_ty(ctx, inner)
        }
        TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => {
            Some(ctx.resolve_body_ty(elem))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
            args.0.first().and_then(|arg| match arg {
                GenericArgKind::Type(elem_ty) => Some(ctx.resolve_body_ty(*elem_ty)),
                _ => None,
            })
        }
        _ => None,
    }
}

fn inline_collection_element_addr(
    ctx: &ChcCtx<'_, '_>,
    data_ptr: Expr,
    collection_ty: Ty,
    index_expr: Expr,
) -> Option<(Expr, Ty)> {
    let elem_ty = indexed_collection_elem_ty(ctx, collection_ty)?;
    let elem_size = ctx.get_type_size(elem_ty).unwrap_or(1) as u64;
    let elem_addr =
        if elem_size <= 1 {
            data_ptr.bvadd(index_expr)
        } else {
            data_ptr.bvadd(index_expr.bvmul(Expr::bitvec_const(
                elem_size as i128,
                crate::codegen_ay::types::POINTER_WIDTH,
            )))
        };
    Some((elem_addr, elem_ty))
}

fn inline_slice_receiver_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &InlineExecutionState,
    receiver_arg: &Operand,
) -> Option<Expr> {
    inline_operand_to_expr(
        ctx,
        receiver_arg,
        &state.local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    )
    .or_else(|| match receiver_arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            let source_place = trace_inline_source_place(
                ctx,
                walk_ctx.body,
                place.local,
                MAX_INLINE_REF_SOURCE_TRACE_DEPTH,
            );
            debug!(
                ?receiver_arg,
                traced_source = ?source_place,
                "inline slice-index: traced receiver source"
            );
            let source_place = source_place?;
            let translated = if let Some(expr) = inline_ref_place_to_expr(
                ctx,
                &state.local_exprs,
                &source_place,
                &walk_ctx.resolver,
                walk_ctx.locals,
            ) {
                Some(expr)
            } else if matches!(
                source_place.projection.as_slice(),
                [rustc_public::mir::ProjectionElem::Deref]
            ) {
                let bare_place =
                    rustc_public::mir::Place { local: source_place.local, projection: Vec::new() };
                inline_operand_to_expr(
                    ctx,
                    &Operand::Copy(bare_place),
                    &state.local_exprs,
                    &walk_ctx.resolver,
                    walk_ctx.locals,
                )
                .or_else(|| {
                    let data_operand =
                        rawptr_aggregate_data_operand(walk_ctx.body, source_place.local)?;
                    inline_operand_to_expr(
                        ctx,
                        &data_operand,
                        &state.local_exprs,
                        &walk_ctx.resolver,
                        walk_ctx.locals,
                    )
                })
            } else {
                None
            };
            debug!(
                ?receiver_arg,
                translated = translated.is_some(),
                "inline slice-index: traced receiver source translation"
            );
            if translated.is_none() {
                debug!(
                    ?receiver_arg,
                    ?source_place,
                    base_local = source_place.local,
                    base_local_present = state.local_exprs.contains_key(&source_place.local),
                    base_local_source = ?describe_inline_local_source(walk_ctx.body, source_place.local),
                    "inline slice-index: traced receiver source still untranslatable"
                );
            }
            translated
        }
        _ => None,
    })
}

/// Part of #4163: RangeFull identity for inline walker.
///
/// `<RangeFull as SliceIndex<T>>::get_mut(..)` and friends return the input
/// unchanged (identity operation). For `get`/`get_mut`, the return type is
/// `Option<&T>` / `Option<&mut T>` — niche-optimized to the same BV128 fat
/// pointer as the input. For `index`/`index_mut`, the return is `&T` / `&mut T`
/// directly.
///
/// Without this, nested `string.get_mut(..)` + Option extraction calls produce
/// unconstrained fallback expressions, breaking metadata propagation for custom-DST
/// constructors.
fn try_inline_range_full_identity<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    target_bb: usize,
    callee_name: &str,
    callee_path: &str,
) -> Option<TerminatorStep> {
    // Identify the RangeFull argument. RangeFull is a ZST struct — check arg types.
    let range_full_idx = args.iter().position(|arg| {
        let Ok(ty) = arg.ty(walk_ctx.locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeFull"
        )
    })?;
    // The other arg is the receiver (the slice/str being indexed).
    let receiver_idx = if range_full_idx == 0 { 1 } else { 0 };
    let receiver_arg = args.get(receiver_idx)?;

    // Translate the receiver expression.
    let receiver_expr = inline_operand_to_expr(
        ctx,
        receiver_arg,
        &state.local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    )?;

    // For niche-optimized Option<&T> / Option<&mut T>, Some(ptr) has the same
    // bit representation as ptr itself (BV128 for fat pointers). Write the
    // receiver expression directly as the result.
    if !apply_inline_writeback(ctx, walk_ctx, state, destination, receiver_expr) {
        debug!(
            %callee_path,
            callee_name,
            "inline RangeFull identity: write-back failed"
        );
        return Some(TerminatorStep::Return(None));
    }

    // Propagate the full ref metadata bundle from receiver to destination so
    // downstream unwrap, `size_of_val`, and `str_{chars,bytes}_nth` recovery
    // see the same backing information on the identity result local.
    if let Operand::Copy(place) | Operand::Move(place) = receiver_arg {
        if place.projection.is_empty() {
            propagate_inline_range_full_metadata(ctx, place.local, destination.local);
        }
    }

    debug!(
        %callee_path,
        callee_name,
        dest_local = destination.local,
        "inline RangeFull identity: handled as identity propagation"
    );
    Some(TerminatorStep::ContinueAt(target_bb))
}

pub(super) fn try_execute_inline_slice_index_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    func: &Operand,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    target_bb: usize,
    current_bb: usize,
) -> Option<TerminatorStep> {
    let callee_path = resolve_inline_callee_path(ctx, func, walk_ctx.locals)?;
    let callee_name = callee_path.rsplit("::").next()?;
    if !callee_path.contains("SliceIndex")
        || !matches!(
            callee_name,
            "index" | "index_mut" | "get" | "get_mut" | "get_unchecked" | "get_unchecked_mut"
        )
    {
        return None;
    }

    // Part of #4163: RangeFull identity — `get_mut(..)` / `index(..)` with RangeFull
    // returns the input unchanged. Detect RangeFull index arg and short-circuit to
    // identity propagation. This avoids unconstrained fallback for patterns like
    // `string.get_mut(..)` + Option extraction inside custom-DST constructors.
    if let Some(step) = try_inline_range_full_identity(
        ctx,
        walk_ctx,
        state,
        args,
        destination,
        target_bb,
        callee_name,
        &callee_path,
    ) {
        return Some(step);
    }

    // Below: scalar element indexing (index/index_mut only).
    if !matches!(callee_name, "index" | "index_mut") {
        return None;
    }

    let Some((receiver_arg, index_arg)) =
        inline_slice_index_receiver_arg(ctx, args, walk_ctx.locals)
    else {
        debug!(%callee_path, "inline slice-index: could not classify receiver/index args");
        return None;
    };
    let receiver_ty = match receiver_arg.ty(walk_ctx.locals).ok()?.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            ctx.resolve_body_ty(inner)
        }
        other => {
            debug!(%callee_path, ?other, "inline slice-index: receiver arg not ref/rawptr");
            return None;
        }
    };
    let Some(receiver_expr) = inline_slice_receiver_expr(ctx, walk_ctx, state, receiver_arg) else {
        debug!(
            %callee_path,
            ?receiver_arg,
            "inline slice-index: receiver operand translation failed"
        );
        return None;
    };
    let Some(index_expr) = inline_operand_to_expr(
        ctx,
        index_arg,
        &state.local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    ) else {
        debug!(%callee_path, "inline slice-index: index operand translation failed");
        return None;
    };
    let Some(index_expr) = coerce_inline_index_expr(index_expr) else {
        debug!(%callee_path, "inline slice-index: index coercion failed");
        return None;
    };
    let Some((collection_expr, collection_ty, _collection_addr)) =
        materialize_inline_collection_receiver(ctx, receiver_expr, receiver_ty)
    else {
        debug!(%callee_path, "inline slice-index: receiver materialization failed");
        return None;
    };
    let collection_data_ptr = collection_expr
        .sort()
        .bitvec_width()
        .filter(|&w| w == crate::codegen_ay::types::POINTER_WIDTH)
        .map(|_| collection_expr.clone());
    let Some(element_expr) =
        inline_collection_select_expr(collection_expr.clone(), index_expr.clone()).or_else(|| {
            collection_data_ptr.clone().and_then(|data_ptr| {
                inline_collection_select_via_memory_model(
                    ctx,
                    data_ptr,
                    collection_ty,
                    index_expr.clone(),
                )
            })
        })
    else {
        debug!(
            %callee_path,
            collection_sort = ?collection_expr.sort(),
            "inline slice-index: backing array extraction failed"
        );
        return None;
    };

    let writeback_value = if callee_name == "index_mut" && destination.projection.is_empty() {
        match collection_data_ptr.and_then(|data_ptr| {
            inline_collection_element_addr(ctx, data_ptr, collection_ty, index_expr)
                .map(|(elem_addr, _)| elem_addr)
        }) {
            Some(elem_addr) => elem_addr,
            None => {
                debug!(
                    %callee_path,
                    collection_sort = ?collection_expr.sort(),
                    "inline slice-index: index_mut address recovery failed"
                );
                element_expr
            }
        }
    } else {
        element_expr
    };

    if !apply_inline_writeback(ctx, walk_ctx, state, destination, writeback_value) {
        debug!(
            bb_idx = walk_ctx.bb_idx,
            current_bb,
            local = destination.local,
            callee = %callee_path,
            "virtual body: inline slice-index destination write-back cannot be tracked"
        );
        return Some(TerminatorStep::Return(None));
    }
    debug!(
        %callee_path,
        dest_local = destination.local,
        collection_sort = ?collection_expr.sort(),
        "inline slice-index: handled precisely"
    );
    Some(TerminatorStep::ContinueAt(target_bb))
}

pub(super) fn nested_call_fallback_sort(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    destination: &rustc_public::mir::Place,
    callee_path: Option<&str>,
    dest_sort: ay_bindings::Sort,
) -> ay_bindings::Sort {
    let default_sort =
        crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::option_value_sort(&dest_sort)
            .unwrap_or(dest_sort);
    let Some(callee_path) = callee_path else {
        return default_sort;
    };
    let is_slice_index_ref = callee_path.contains("SliceIndex")
        && matches!(callee_path.rsplit("::").next(), Some("index" | "index_mut"));
    if !is_slice_index_ref {
        return default_sort;
    }
    let Some(dest_ty) = ctx
        .resolve_inline_local_ty(walk_ctx.body, destination.local)
        .or_else(|| destination.ty(walk_ctx.locals).ok().map(|ty| ctx.resolve_body_ty(ty)))
    else {
        return default_sort;
    };
    let Some(pointee_ty) = ChcCtx::deref_pointee_ty(dest_ty).map(|ty| ctx.resolve_body_ty(ty))
    else {
        return default_sort;
    };
    ChcCtx::translate_ty(pointee_ty)
        .and_then(|sort| {
            crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::option_value_sort(&sort)
                .or(Some(sort))
        })
        .unwrap_or(default_sort)
}

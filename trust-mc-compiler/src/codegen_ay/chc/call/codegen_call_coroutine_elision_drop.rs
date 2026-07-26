// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};

use super::ChcCtx;
use super::mentions::{
    operand_mentions_local, place_index_mentions_local, rvalue_mentions_local,
    statement_allows_elided_pin_box_local, terminator_allows_ref_local_unmentioned,
};
use super::ty::{
    drop_derived_local_ty_elidable, drop_ref_pointee_elidable, is_dealloc_like_path,
    ref_or_raw_ptr_pointee_ty,
};

pub(super) fn drop_chain_derived_local_reaches(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    target_local: usize,
    visited: &mut std::collections::HashSet<usize>,
) -> bool {
    if local_idx == target_local {
        return true;
    }
    if !visited.insert(local_idx) {
        return false;
    }

    for block in &ctx.body.blocks {
        for stmt in &block.statements {
            let alias_local = local_move_alias_from_stmt(&stmt.kind, local_idx)
                .or_else(|| elidable_drop_derived_alias_from_stmt(ctx, &stmt.kind, local_idx));
            if let Some(alias_local) = alias_local
                && drop_chain_derived_local_reaches(ctx, alias_local, target_local, visited)
            {
                return true;
            }
        }
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            && let Some(alias_local) =
                elidable_drop_derived_alias_from_call(ctx, func, args, destination, local_idx)
            && drop_chain_derived_local_reaches(ctx, alias_local, target_local, visited)
        {
            return true;
        }
    }
    false
}

pub(super) fn pin_box_ref_local_used_only_for_drop(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    defining_assign: Option<(usize, usize)>,
    visited: &mut std::collections::HashSet<usize>,
) -> bool {
    if !visited.insert(local_idx) {
        return false;
    }

    let mut saw_drop = false;
    for (bb_idx, block) in ctx.body.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if defining_assign == Some((bb_idx, stmt_idx)) {
                continue;
            }
            if let Some(alias_local) = local_move_alias_from_stmt(&stmt.kind, local_idx) {
                if pin_box_ref_local_used_only_for_drop(
                    ctx,
                    alias_local,
                    Some((bb_idx, stmt_idx)),
                    visited,
                ) {
                    saw_drop = true;
                    continue;
                }
                return false;
            }
            if let Some(alias_local) =
                elidable_drop_derived_alias_from_stmt(ctx, &stmt.kind, local_idx)
            {
                if pin_box_ref_local_used_only_for_drop(
                    ctx,
                    alias_local,
                    Some((bb_idx, stmt_idx)),
                    visited,
                ) {
                    saw_drop = true;
                    continue;
                }
                return false;
            }
            if !statement_allows_elided_pin_box_local(&stmt.kind, local_idx) {
                return false;
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                if is_drop_call_on_elidable_ref(ctx, func, args, local_idx) {
                    saw_drop = true;
                    if operand_mentions_local(func, local_idx)
                        || place_index_mentions_local(destination, local_idx)
                    {
                        return false;
                    }
                    continue;
                }
                if is_dealloc_call_on_drop_derived_local(ctx, func, args, local_idx) {
                    saw_drop = true;
                    continue;
                }
                if let Some(alias_local) =
                    elidable_drop_derived_alias_from_call(ctx, func, args, destination, local_idx)
                {
                    if pin_box_ref_local_used_only_for_drop(ctx, alias_local, None, visited) {
                        saw_drop = true;
                        continue;
                    }
                    return false;
                }
                if !terminator_allows_ref_local_unmentioned(&block.terminator.kind, local_idx) {
                    return false;
                }
            }
            TerminatorKind::Drop { place, .. }
                if is_drop_terminator_on_elidable_deref(ctx, place, local_idx) =>
            {
                saw_drop = true;
            }
            TerminatorKind::SwitchInt { discr, .. } if operand_mentions_local(discr, local_idx) => {
                saw_drop = true;
            }
            kind if terminator_allows_ref_local_unmentioned(kind, local_idx) => {}
            _ => return false,
        }
    }
    saw_drop
}

fn local_move_alias_from_stmt(kind: &StatementKind, source_local: usize) -> Option<usize> {
    let StatementKind::Assign(lhs, Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))) = kind
    else {
        return None;
    };
    (rhs.local == source_local
        && rhs.projection.is_empty()
        && lhs.local != source_local
        && lhs.projection.is_empty())
    .then_some(lhs.local)
}

fn elidable_drop_derived_alias_from_stmt(
    ctx: &ChcCtx<'_, '_>,
    kind: &StatementKind,
    source_local: usize,
) -> Option<usize> {
    let StatementKind::Assign(lhs, rvalue) = kind else {
        return None;
    };
    if !lhs.projection.is_empty() || lhs.local == source_local {
        return None;
    }
    if !rvalue_mentions_local(rvalue, source_local) {
        return None;
    }
    let lhs_ty = ctx.resolve_body_ty(lhs.ty(ctx.body.locals()).ok()?);
    drop_derived_local_ty_elidable(ctx, lhs_ty).then_some(lhs.local)
}

fn is_drop_call_on_elidable_ref(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    args: &[Operand],
    local_idx: usize,
) -> bool {
    let Some(path) = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func)) else {
        return false;
    };
    if !path.contains("Drop>::drop") && !path.contains("drop_in_place") {
        return false;
    }
    let Some(arg) = args.first() else {
        return false;
    };
    if !operand_mentions_local(arg, local_idx) {
        return false;
    }
    let Ok(arg_ty) = arg.ty(ctx.body.locals()) else {
        return false;
    };
    let Some(pointee_ty) = ref_or_raw_ptr_pointee_ty(ctx, ctx.resolve_body_ty(arg_ty)) else {
        return false;
    };
    drop_ref_pointee_elidable(ctx, pointee_ty)
}

fn elidable_drop_derived_alias_from_call(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    args: &[Operand],
    destination: &rustc_public::mir::Place,
    source_local: usize,
) -> Option<usize> {
    if destination.local == source_local || !destination.projection.is_empty() {
        return None;
    }
    if operand_mentions_local(func, source_local)
        || !args.iter().any(|arg| operand_mentions_local(arg, source_local))
    {
        return None;
    }
    let path = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func))?;
    if !is_drop_derived_pointer_identity_path(&path) && !is_drop_derived_layout_path(&path) {
        return None;
    }
    let dest_ty = ctx.resolve_body_ty(destination.ty(ctx.body.locals()).ok()?);
    drop_derived_local_ty_elidable(ctx, dest_ty).then_some(destination.local)
}

fn is_drop_derived_pointer_identity_path(path: &str) -> bool {
    matches!(path.rsplit("::").next(), Some("as_ptr" | "as_non_null_ptr" | "cast"))
        && (path.contains("ptr::NonNull") || path.contains("ptr::Unique"))
}

fn is_drop_derived_layout_path(path: &str) -> bool {
    path.contains("alloc::Layout")
        && (path.ends_with("::for_value_raw")
            || path.ends_with("::size")
            || path.ends_with("::align"))
}

fn is_dealloc_call_on_drop_derived_local(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    args: &[Operand],
    local_idx: usize,
) -> bool {
    let Some(path) = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func)) else {
        return false;
    };
    is_dealloc_like_path(&path) && args.iter().any(|arg| operand_mentions_local(arg, local_idx))
}

fn is_drop_terminator_on_elidable_deref(
    ctx: &ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
    local_idx: usize,
) -> bool {
    if place.local != local_idx || !matches!(place.projection.first(), Some(ProjectionElem::Deref))
    {
        return false;
    }
    let Ok(drop_ty) = place.ty(ctx.body.locals()) else {
        return false;
    };
    drop_ref_pointee_elidable(ctx, ctx.resolve_body_ty(drop_ty))
}

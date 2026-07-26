// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};

use super::ChcCtx;
use super::drop_flow::{drop_chain_derived_local_reaches, pin_box_ref_local_used_only_for_drop};
use super::mentions::{
    assert_msg_mentions_local, operand_mentions_local, place_index_mentions_local,
    place_mentions_local, statement_allows_elided_pin_box_local,
};
use super::ty::{box_coroutine_inner_ty, is_box_into_pin_path, is_box_pin_path};
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    coroutine_drop_fields_trivially_no_drop, pin_box_coroutine_inner_ty,
};

pub(super) fn has_box_pin_coroutine_definition(ctx: &ChcCtx<'_, '_>, local_idx: usize) -> bool {
    ctx.body
        .blocks
        .iter()
        .any(|block| terminator_is_box_pin_coroutine_def(ctx, &block.terminator.kind, local_idx))
}

pub(super) fn has_pin_new_unchecked_box_coroutine_definition(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
) -> bool {
    ctx.body.blocks.iter().any(|block| {
        terminator_is_pin_new_unchecked_box_coroutine_def(ctx, &block.terminator.kind, local_idx)
    })
}

pub(super) fn has_box_into_pin_coroutine_definition(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
) -> bool {
    ctx.body.blocks.iter().any(|block| {
        terminator_is_box_into_pin_coroutine_def(ctx, &block.terminator.kind, local_idx)
    })
}

fn terminator_is_box_pin_coroutine_def(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    local_idx: usize,
) -> bool {
    let TerminatorKind::Call { func, destination, .. } = kind else {
        return false;
    };
    if destination.local != local_idx || !destination.projection.is_empty() {
        return false;
    }
    let Ok(dest_ty) = destination.ty(ctx.body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    if pin_box_coroutine_inner_ty(dest_ty).is_none() {
        return false;
    }
    ctx.resolve_callee_path(func)
        .or_else(|| ctx.resolve_fn_def_name(func))
        .is_some_and(|path| is_box_pin_path(&path))
}

fn terminator_is_pin_new_unchecked_box_coroutine_def(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    local_idx: usize,
) -> bool {
    let TerminatorKind::Call { func, args, destination, .. } = kind else {
        return false;
    };
    if destination.local != local_idx || !destination.projection.is_empty() {
        return false;
    }
    let Ok(dest_ty) = destination.ty(ctx.body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    if pin_box_coroutine_inner_ty(dest_ty).is_none() {
        return false;
    }
    if !ctx.detect_pin_new_unchecked_call(func) {
        return false;
    }
    args.first()
        .and_then(|arg| arg.ty(ctx.body.locals()).ok())
        .and_then(|ty| box_coroutine_inner_ty(ctx, ctx.resolve_body_ty(ty)))
        .is_some()
}

fn terminator_is_box_into_pin_coroutine_def(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    local_idx: usize,
) -> bool {
    let TerminatorKind::Call { func, args, destination, .. } = kind else {
        return false;
    };
    if destination.local != local_idx || !destination.projection.is_empty() {
        return false;
    }
    let Ok(dest_ty) = destination.ty(ctx.body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    if pin_box_coroutine_inner_ty(dest_ty).is_none() {
        return false;
    }
    if !ctx
        .resolve_callee_path(func)
        .or_else(|| ctx.resolve_fn_def_name(func))
        .is_some_and(|path| is_box_into_pin_path(&path))
    {
        return false;
    }
    args.first()
        .and_then(|arg| arg.ty(ctx.body.locals()).ok())
        .and_then(|ty| box_coroutine_inner_ty(ctx, ctx.resolve_body_ty(ty)))
        .is_some()
}

pub(super) fn pin_box_local_used_only_by_drop(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    defining_call_bb: Option<usize>,
) -> bool {
    let mut visited = std::collections::HashSet::new();
    pin_box_local_used_only_by_drop_inner(ctx, local_idx, defining_call_bb, None, &mut visited)
}

pub(super) fn local_is_in_elidable_pin_box_drop_chain(
    ctx: &ChcCtx<'_, '_>,
    target_local: usize,
) -> bool {
    ctx.body.locals().iter().enumerate().any(|(root_local, local_decl)| {
        let root_ty = ctx.resolve_body_ty(local_decl.ty);
        let Some(coroutine_ty) = pin_box_coroutine_inner_ty(root_ty) else {
            return false;
        };
        coroutine_drop_fields_trivially_no_drop(ctx, coroutine_ty)
            && pin_box_drop_chain_reaches_local(
                ctx,
                root_local,
                target_local,
                &mut std::collections::HashSet::new(),
            )
    })
}

fn pin_box_drop_chain_reaches_local(
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
            if let Some(alias_local) = pin_box_address_alias_from_stmt(&stmt.kind, local_idx)
                && drop_chain_derived_local_reaches(ctx, alias_local, target_local, visited)
            {
                return true;
            }
        }
    }
    false
}

fn pin_box_local_used_only_by_drop_inner(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    defining_call_bb: Option<usize>,
    defining_addr_assign: Option<(usize, usize)>,
    visited: &mut std::collections::HashSet<usize>,
) -> bool {
    if !visited.insert(local_idx) {
        return false;
    }

    let mut saw_drop = false;
    for (bb_idx, block) in ctx.body.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if defining_addr_assign == Some((bb_idx, stmt_idx)) {
                continue;
            }
            if let Some(ref_local) = pin_box_address_alias_from_stmt(&stmt.kind, local_idx) {
                let mut visited_refs = std::collections::HashSet::new();
                if pin_box_ref_local_used_only_for_drop(
                    ctx,
                    ref_local,
                    Some((bb_idx, stmt_idx)),
                    &mut visited_refs,
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
        let is_allowed_defining_call = defining_call_bb == Some(bb_idx)
            || (defining_call_bb.is_none()
                && (terminator_is_box_pin_coroutine_def(ctx, &block.terminator.kind, local_idx)
                    || terminator_is_pin_new_unchecked_box_coroutine_def(
                        ctx,
                        &block.terminator.kind,
                        local_idx,
                    )));
        if !terminator_allows_elided_pin_box_local(
            &block.terminator.kind,
            local_idx,
            is_allowed_defining_call,
            &mut saw_drop,
        ) {
            return false;
        }
    }
    saw_drop
}

fn pin_box_address_alias_from_stmt(kind: &StatementKind, source_local: usize) -> Option<usize> {
    let StatementKind::Assign(lhs, rvalue) = kind else {
        return None;
    };
    if !lhs.projection.is_empty() || lhs.local == source_local {
        return None;
    }
    let place = match rvalue {
        Rvalue::AddressOf(_, place) | Rvalue::Ref(_, _, place)
            if place.local == source_local && place.projection.is_empty() =>
        {
            place
        }
        _ => return None,
    };
    (place.local == source_local).then_some(lhs.local)
}

fn terminator_allows_elided_pin_box_local(
    kind: &TerminatorKind,
    local_idx: usize,
    is_defining_call: bool,
    saw_drop: &mut bool,
) -> bool {
    match kind {
        TerminatorKind::Call { func, args, destination, .. } => {
            let writes_elided_local = destination.local == local_idx;
            if writes_elided_local && (!is_defining_call || !destination.projection.is_empty()) {
                return false;
            }
            !operand_mentions_local(func, local_idx)
                && args.iter().all(|arg| !operand_mentions_local(arg, local_idx))
                && !place_index_mentions_local(destination, local_idx)
        }
        TerminatorKind::Drop { place, .. }
            if place.local == local_idx && place.projection.is_empty() =>
        {
            *saw_drop = true;
            true
        }
        TerminatorKind::Drop { place, .. } => !place_mentions_local(place, local_idx),
        TerminatorKind::SwitchInt { discr, .. } => !operand_mentions_local(discr, local_idx),
        TerminatorKind::Assert { cond, msg, .. } => {
            !operand_mentions_local(cond, local_idx) && !assert_msg_mentions_local(msg, local_idx)
        }
        TerminatorKind::Return => local_idx != 0,
        TerminatorKind::Goto { .. }
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => true,
        TerminatorKind::InlineAsm { .. } => false,
    }
}

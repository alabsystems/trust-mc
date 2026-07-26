// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

use super::ChcCtx;
use super::mentions::{
    assert_msg_mentions_local, operand_mentions_local, place_index_mentions_local,
    place_mentions_local, statement_allows_elided_pin_box_local,
};
use super::pin_flow::pin_box_local_used_only_by_drop;
use super::ty::{box_coroutine_inner_ty, is_box_into_pin_path};
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::pin_box_coroutine_inner_ty;

pub(super) fn box_coroutine_local_flows_only_to_elided_pin_drop(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    defining_call_bb: Option<usize>,
) -> bool {
    let mut visited = std::collections::HashSet::new();
    box_coroutine_local_flows_only_to_elided_pin_drop_inner(
        ctx,
        local_idx,
        defining_call_bb,
        None,
        &mut visited,
    )
}

fn box_coroutine_local_flows_only_to_elided_pin_drop_inner(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    defining_call_bb: Option<usize>,
    defining_assign: Option<(usize, usize)>,
    visited: &mut std::collections::HashSet<usize>,
) -> bool {
    if !visited.insert(local_idx) {
        return false;
    }

    let mut saw_pin = false;
    for (bb_idx, block) in ctx.body.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if defining_assign == Some((bb_idx, stmt_idx)) {
                continue;
            }
            if let Some(alias_local) =
                box_coroutine_move_alias_from_stmt(ctx, &stmt.kind, local_idx)
            {
                if box_coroutine_local_flows_only_to_elided_pin_drop_inner(
                    ctx,
                    alias_local,
                    None,
                    Some((bb_idx, stmt_idx)),
                    visited,
                ) {
                    saw_pin = true;
                    continue;
                }
                return false;
            }
            if !statement_allows_elided_pin_box_local(&stmt.kind, local_idx) {
                return false;
            }
        }
        if !terminator_allows_elided_box_coroutine_local(
            ctx,
            &block.terminator.kind,
            local_idx,
            defining_call_bb == Some(bb_idx),
            bb_idx,
            &mut saw_pin,
        ) {
            return false;
        }
    }
    saw_pin
}

fn box_coroutine_move_alias_from_stmt(
    ctx: &ChcCtx<'_, '_>,
    kind: &StatementKind,
    source_local: usize,
) -> Option<usize> {
    let StatementKind::Assign(lhs, Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))) = kind
    else {
        return None;
    };
    if rhs.local != source_local
        || !rhs.projection.is_empty()
        || lhs.local == source_local
        || !lhs.projection.is_empty()
    {
        return None;
    }
    let lhs_ty = lhs.ty(ctx.body.locals()).ok()?;
    box_coroutine_inner_ty(ctx, ctx.resolve_body_ty(lhs_ty)).map(|_| lhs.local)
}

fn terminator_allows_elided_box_coroutine_local(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    local_idx: usize,
    is_defining_call: bool,
    bb_idx: usize,
    saw_pin: &mut bool,
) -> bool {
    match kind {
        TerminatorKind::Call { func, args, destination, .. } => {
            if destination.local == local_idx {
                return is_defining_call
                    && destination.projection.is_empty()
                    && !operand_mentions_local(func, local_idx)
                    && args.iter().all(|arg| !operand_mentions_local(arg, local_idx));
            }

            if is_pin_new_unchecked_from_box_local(ctx, kind, local_idx)
                && pin_box_local_used_only_by_drop(ctx, destination.local, Some(bb_idx))
            {
                *saw_pin = true;
                return !operand_mentions_local(func, local_idx)
                    && !place_index_mentions_local(destination, local_idx);
            }

            if is_box_into_pin_from_box_local(ctx, kind, local_idx)
                && pin_box_local_used_only_by_drop(ctx, destination.local, Some(bb_idx))
            {
                *saw_pin = true;
                return !operand_mentions_local(func, local_idx)
                    && !place_index_mentions_local(destination, local_idx);
            }

            !operand_mentions_local(func, local_idx)
                && args.iter().all(|arg| !operand_mentions_local(arg, local_idx))
                && !place_index_mentions_local(destination, local_idx)
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

fn is_pin_new_unchecked_from_box_local(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    box_local: usize,
) -> bool {
    let TerminatorKind::Call { func, args, destination, .. } = kind else {
        return false;
    };
    if !ctx.detect_pin_new_unchecked_call(func) {
        return false;
    }
    let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() else {
        return false;
    };
    if place.local != box_local || !place.projection.is_empty() {
        return false;
    }
    let Ok(dest_ty) = destination.ty(ctx.body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    pin_box_coroutine_inner_ty(dest_ty).is_some()
}

fn is_box_into_pin_from_box_local(
    ctx: &ChcCtx<'_, '_>,
    kind: &TerminatorKind,
    box_local: usize,
) -> bool {
    let TerminatorKind::Call { func, args, destination, .. } = kind else {
        return false;
    };
    if !ctx
        .resolve_callee_path(func)
        .or_else(|| ctx.resolve_fn_def_name(func))
        .is_some_and(|path| is_box_into_pin_path(&path))
    {
        return false;
    }
    let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() else {
        return false;
    };
    if place.local != box_local || !place.projection.is_empty() {
        return false;
    }
    let Ok(dest_ty) = destination.ty(ctx.body.locals()) else {
        return false;
    };
    let dest_ty = ctx.resolve_body_ty(dest_ty);
    pin_box_coroutine_inner_ty(dest_ty).is_some()
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared-pointer Drop handling for inline body walking.

use std::collections::HashMap;

use ay_bindings::Expr;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_body::extract_inline_assert_guard;
use super::super::inline_shared::resolve_place;
use super::walker::InlineWalkCtx;
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    collect_shared_pointer_dealloc_effects, shared_pointer_inner_ty,
    try_translate_shared_pointer_inner_drop,
};
use crate::codegen_ay::chc::rules::codegen_rules_helpers::rust_dealloc_base_ptr_for_known_alloc_id;

pub(super) fn try_handle_inline_shared_pointer_drop<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    inline_alloc_ids: &HashMap<usize, u32>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    inline_depth: usize,
) -> Option<Expr> {
    let inner_ty = shared_pointer_inner_ty(drop_ty)?;
    let wrapper_expr = resolve_place(ctx, local_exprs, place, &walk_ctx.resolver, walk_ctx.locals)?;
    let wrapper_local_idx = place.projection.is_empty().then_some(place.local);
    let known_alloc_id = inline_alloc_id_for_unprojected_drop_place(inline_alloc_ids, place);
    let dealloc_wrapper_expr = known_alloc_id
        .map(rust_dealloc_base_ptr_for_known_alloc_id)
        .unwrap_or_else(|| wrapper_expr.clone());

    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
    let modified_snapshot = ctx.encode.modified_state_indices.clone();
    if let Some(inline_result) = try_translate_shared_pointer_inner_drop(
        ctx,
        inner_ty,
        wrapper_local_idx,
        known_alloc_id,
        &wrapper_expr,
        walk_ctx.bb_idx,
        inline_depth + 1,
    ) {
        append_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id);
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: shared pointer inner inlined");
        return Some(
            extract_inline_assert_guard(&inline_result.value)
                .unwrap_or_else(|| Expr::bool_const(true)),
        );
    }
    ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
    ctx.encode.modified_state_indices = modified_snapshot;

    if crate::codegen_ay::chc::dyn_coercion::find_dyn_trait_tail_ty(ctx, inner_ty).is_none() {
        return None;
    }

    if append_shared_pointer_dealloc_effects(ctx, &dealloc_wrapper_expr, known_alloc_id) {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: shared pointer dyn-tail dealloc-only");
        return Some(Expr::bool_const(true));
    }

    None
}

fn append_shared_pointer_dealloc_effects<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dealloc_wrapper_expr: &Expr,
    known_alloc_id: Option<u32>,
) -> bool {
    let Some(dealloc_effects) =
        collect_shared_pointer_dealloc_effects(ctx, dealloc_wrapper_expr, known_alloc_id)
    else {
        return false;
    };
    ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
    ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
    true
}

fn inline_alloc_id_for_unprojected_drop_place(
    inline_alloc_ids: &HashMap<usize, u32>,
    place: &rustc_public::mir::Place,
) -> Option<u32> {
    if place.projection.is_empty() { inline_alloc_ids.get(&place.local).copied() } else { None }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline Drop terminator handling for the body walker.
//!
//! Part of #3848: Handle `TerminatorKind::Drop` inside inline bodies.

use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
use crate::codegen_ay::shared::mono_ty;
use ay_bindings::{Expr, Sort};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_body::{extract_inline_assert_guard, walk_drop_body};
use super::super::inline_shared::resolve_place;
use super::inline_drop_helpers::{
    is_coroutine_drop, is_transparent_platform_drop, resolve_inline_drop_self_expr,
};
use super::inline_shared_drop::try_handle_inline_shared_pointer_drop;
use super::walker::{InlineWalkCtx, translate_virtual_body_inline};
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::{
    translate_native_dyn_box_drop, translate_native_thin_box_free,
};
use crate::codegen_ay::chc::rules::codegen_rules_helpers::CodegenRulesHelpers;
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::shared::{
    native_box_drop::native_global_box_pointee, native_box_raw::native_thin_global_box_pointee,
};
use crate::codegen_ay::types::POINTER_WIDTH;

/// Handle a Drop terminator encountered during inline body walking.
///
/// Returns `Some(success_guard)` unconditionally -- drops that can't be
/// inlined are treated as sound over-approximation (skip with `true`).
/// Part of #3872: never bails the parent inline for unresolvable drops.
///
/// Part of #3848: Without this, drop glue for captured values in closures
/// (e.g., `Box<dyn FnOnce()>` with move-captured Drop types) bails the
/// entire inline translation.
pub(in crate::codegen_ay::chc) fn try_handle_inline_drop<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    inline_alloc_ids: &HashMap<usize, u32>,
    place: &rustc_public::mir::Place,
    inline_depth: usize,
) -> Option<Expr> {
    let Some(drop_ty) = place.ty(walk_ctx.locals).ok().map(|ty| ctx.resolve_body_ty(ty)) else {
        // Can't resolve type -- skip (conservative: may under-approximate
        // for unknown types, but unresolvable types are typically ZSTs
        // or compiler-generated temporaries with no real Drop impl).
        ctx.record_sound_fallback_reason("walked_drop_type_unresolved");
        return Some(Expr::bool_const(true));
    };

    // Native Box transport is typed in this walk's namespace. Missing or
    // invalidated origin never falls back to a host-local or first producer.
    if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)) =
        drop_ty.kind()
        && def.is_box()
    {
        let Some(inner) = native_global_box_pointee(ctx.tcx, drop_ty) else {
            ctx.record_sound_fallback_reason("walked_native_box_allocator_or_carrier_unmodeled");
            return Some(Expr::bool_const(true));
        };
        use rustc_public::ty::{RigidTy, TyKind};
        let handled = if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            let origin = ctx.inline_native_dyn_origin(
                &rustc_public::mir::Operand::Copy(place.clone()),
                walk_ctx.locals,
            );
            origin
                .and_then(|origin| {
                    translate_native_dyn_box_drop(
                        ctx,
                        drop_ty,
                        &origin,
                        walk_ctx.bb_idx,
                        inline_depth,
                    )
                })
                .map(|result| park_drop_checks_and_guard(ctx, result))
        } else if native_thin_global_box_pointee(ctx.tcx, drop_ty).is_some()
            && mono_ty::drop_in_place(inner).is_some_and(|instance| instance.is_empty_shim())
        {
            let value = resolve_place(ctx, local_exprs, place, &walk_ctx.resolver, walk_ctx.locals);
            value
                .and_then(|value| translate_native_thin_box_free(ctx, drop_ty, value))
                .map(|_| Expr::bool_const(true))
        } else {
            None
        };
        if let Some(guard) = handled {
            return Some(guard);
        }
        ctx.record_sound_fallback_reason("walked_native_box_drop_exact_effects_unavailable");
        return Some(Expr::bool_const(true));
    }

    // Part of #4067: Skip drops for types that contain only platform sync
    // types modeled as transparent scalars (BV32). Their drop glue involves
    // Box deallocation of pthread_mutex_t which is not heap-allocated in our
    // model -- walking the body fails at depth 4+ and produces spurious CTREX.
    if is_transparent_platform_drop(drop_ty) {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: transparent platform type, skip (#4067)");
        return Some(Expr::bool_const(true));
    }

    // Part of #4150: Coroutine drop glue uses discriminant-based switching
    // across all possible coroutine states. The inline body walker cannot
    // handle this complexity -- it always returns None, recording
    // `inline_drop_walk_failed`. Since coroutine drop glue only drops
    // captured values (no user assertions in the drop path), skipping the
    // body walk is sound for assertion checking.
    if is_coroutine_drop(drop_ty) {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: coroutine type, skip (#4150)");
        return Some(Expr::bool_const(true));
    }

    if let Some(shared_guard) = try_handle_inline_shared_pointer_drop(
        ctx,
        walk_ctx,
        local_exprs,
        inline_alloc_ids,
        place,
        drop_ty,
        inline_depth,
    ) {
        return Some(shared_guard);
    }

    if let Some(dyn_guard) = try_handle_inline_dyn_drop(
        ctx,
        walk_ctx,
        local_exprs,
        inline_vtable_ids,
        place,
        drop_ty,
        inline_depth,
    ) {
        return Some(dyn_guard);
    }

    let Some(drop_instance) = mono_ty::drop_in_place(drop_ty) else {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: glue refused (unresolved params), skip");
        ctx.record_sound_fallback_reason(mono_ty::DROP_GLUE_UNRESOLVED);
        return Some(Expr::bool_const(true));
    };
    if drop_instance.is_empty_shim() {
        return Some(Expr::bool_const(true));
    }

    let Some(drop_body) = drop_instance.callee_body() else {
        // Part of #3872: Sound over-approximation -- skip the drop instead of
        // bailing the entire parent inline. The top-level drop handler does the
        // same (transition_drop.rs: "drop_shim_no_body" fallback).
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: no body available, skip (#3872)");
        ctx.record_sound_fallback_reason("inline_drop_no_body");
        return Some(Expr::bool_const(true));
    };

    // Build self_expr: drop body expects &mut Self (a pointer).
    // Try address resolution; fall back to fresh symbolic BV64
    // (sound over-approximation -- works for ZSTs and types
    // where the drop body only accesses statics).
    let self_expr = resolve_inline_drop_self_expr(ctx, walk_ctx, local_exprs, place)
        .unwrap_or_else(|| {
            Havoc::mint(
                ctx,
                sound_havoc::UNTRACKED_POINTER_VALUE,
                super::super::chc_fresh_name("__drop_self"),
                Sort::bitvec(POINTER_WIDTH),
            )
        });

    let params = [self_expr];
    let caller_vtable_ids_drop = inline_vtable_ids
        .get(&place.local)
        .cloned()
        .into_iter()
        .map(|vtable| (1, vtable))
        .collect();
    ctx.mark_inline_field_reads(&drop_body, &params, walk_ctx.bb_idx);
    let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
    let modified_snapshot = ctx.encode.modified_state_indices.clone();

    if let Some(inline_result) = walk_drop_body(ctx, |ctx| {
        translate_virtual_body_inline(
            ctx,
            &drop_body,
            &params,
            walk_ctx.bb_idx,
            &caller_vtable_ids_drop,
            Some(drop_instance),
            inline_depth + 1,
        )
    }) {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: inlined drop body (#3848)");
        Some(park_drop_checks_and_guard(ctx, inline_result))
    } else {
        // Part of #3872: Sound over-approximation -- skip the drop instead of
        // bailing the entire parent inline. The drop may have side effects we
        // don't model, but skipping it only allows more behaviors (sound for
        // assertion checking). Same semantics as transition_drop.rs fallback.
        ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
        ctx.encode.modified_state_indices = modified_snapshot;
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: drop body walk failed, skip (#3872)");
        ctx.record_sound_fallback_reason("inline_drop_walk_failed");
        Some(Expr::bool_const(true))
    }
}

fn try_handle_inline_dyn_drop(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    depth: usize,
) -> Option<Expr> {
    use rustc_public::ty::{RigidTy, TyKind};
    if !matches!(drop_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return None;
    }
    let pointer = resolve_inline_drop_self_expr(ctx, walk_ctx, local_exprs, place);
    let metadata = inline_vtable_ids.get(&place.local).cloned().or_else(|| {
        local_exprs
            .get(&place.local)
            .and_then(|value| ctx.extract_embedded_vtable_expr(value))
            .map(Val::into_expr)
    });
    let result = pointer.and_then(|pointer| {
        super::super::native_dyn_drop::translate_bound_dyn_drop(
            ctx,
            drop_ty,
            pointer,
            metadata,
            walk_ctx.bb_idx,
            depth,
        )
    });
    if let Some(result) = result {
        return Some(park_drop_checks_and_guard(ctx, result));
    }
    ctx.record_sound_fallback_reason("walked_dyn_drop_exact_effects_unavailable");
    Some(Expr::bool_const(true))
}

/// The success guard of a drop body the walker inlined, parking the walk's
/// side-channel checks in `ctx.inline_drop_deferred_checks` for the walker's
/// `Drop` arm to absorb (these helpers answer only a guard). The walk went
/// through `walk_drop_body`, which accounted for checks after a store.
pub(super) fn park_drop_checks_and_guard(
    ctx: &mut ChcCtx<'_, '_>,
    inline_result: super::InlineReturn,
) -> Expr {
    let guard =
        extract_inline_assert_guard(&inline_result.value).unwrap_or_else(|| Expr::bool_const(true));
    ctx.inline_drop_deferred_checks.extend(inline_result.deferred_checks);
    guard
}

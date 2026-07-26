// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline Drop terminator handling for the body walker.
//!
//! Part of #3848: Handle `TerminatorKind::Drop` inside inline bodies.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::dyn_coercion::ResolvedDispatchBody;
use super::super::inline_body::extract_inline_assert_guard;
use super::super::inline_shared::resolve_place;
use super::dispatch::build_dispatch_ite_chain_impl;
use super::inline_drop_helpers::{
    find_inline_concrete_source_for_dyn_local, forwarded_heap_vtable_for_dyn_local,
    forwarded_heap_vtable_for_expr, is_coroutine_drop, is_transparent_platform_drop,
    resolve_inline_drop_self_expr, seed_box_new_payload_vtable_inline,
};
use super::inline_shared_drop::try_handle_inline_shared_pointer_drop;
use super::walker::{InlineWalkCtx, translate_virtual_body_inline};
use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::collect_box_dyn_dealloc_effects;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::CodegenRulesHelpers;
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
        return Some(Expr::bool_const(true));
    };

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

    if let Some(box_guard) = try_handle_inline_box_dyn_drop(
        ctx,
        walk_ctx,
        local_exprs,
        inline_vtable_ids,
        inline_alloc_ids,
        place,
        drop_ty,
        inline_depth,
    ) {
        return Some(box_guard);
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

    let drop_instance = Instance::resolve_drop_in_place(drop_ty);
    if drop_instance.is_empty_shim() {
        return Some(Expr::bool_const(true));
    }

    let Some(drop_body) = drop_instance.body() else {
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
            super::super::declare_pending_var(
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

    if let Some(inline_result) = translate_virtual_body_inline(
        ctx,
        &drop_body,
        &params,
        walk_ctx.bb_idx,
        &caller_vtable_ids_drop,
        Some(drop_instance),
        inline_depth + 1,
    ) {
        debug!(bb_idx = walk_ctx.bb_idx, "inline drop: inlined drop body (#3848)");
        Some(
            extract_inline_assert_guard(&inline_result.value)
                .unwrap_or_else(|| Expr::bool_const(true)),
        )
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

fn try_handle_inline_box_dyn_drop<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    inline_alloc_ids: &HashMap<usize, u32>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    inline_depth: usize,
) -> Option<Expr> {
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    let TyKind::RigidTy(RigidTy::Adt(_, args)) = drop_ty.kind() else {
        return None;
    };
    if !<ChcCtx<'_, '_> as CodegenRulesHelpers>::is_box_ty(drop_ty) {
        return None;
    }
    let inner_dyn_ty = match args.0.first() {
        Some(GenericArgKind::Type(inner))
            if matches!(
                ctx.resolve_body_ty(*inner).kind(),
                TyKind::RigidTy(RigidTy::Dynamic(..))
            ) =>
        {
            ctx.resolve_body_ty(*inner)
        }
        _ => return None,
    };

    // Part of #4231: When the dyn trait inside the Box is non-assertion-relevant
    // (e.g., `core::error::Error`), skip vtable dispatch entirely and emit
    // dealloc-only effects. The drop side-effects of error/formatting types
    // don't affect assertion-relevant state, and attempting vtable extraction
    // for these traits introduces unconstrained BV64 variables that cause
    // solver timeouts (PROOF → UNKNOWN regression).
    if let Some(trait_def_id) =
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, inner_dyn_ty)
    {
        let trait_path = ctx.tcx.def_path_str(trait_def_id);
        if ChcCtx::is_formatting_path(&trait_path) {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                %trait_path,
                "inline box dyn drop: non-assertion-relevant trait, dealloc-only (#4231)"
            );
            let box_expr =
                resolve_place(ctx, local_exprs, place, &walk_ctx.resolver, walk_ctx.locals)?;
            let bv_ptr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&box_expr)?;
            let known_alloc_id =
                inline_alloc_id_for_unprojected_drop_place(inline_alloc_ids, place);
            let dealloc_effects = collect_box_dyn_dealloc_effects(ctx, bv_ptr, known_alloc_id)?;
            ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
            ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
            return Some(Expr::bool_const(true));
        }
    }

    let box_expr = resolve_place(ctx, local_exprs, place, &walk_ctx.resolver, walk_ctx.locals)?;
    let ptr_expr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&box_expr)?;
    let known_alloc_id = inline_alloc_id_for_unprojected_drop_place(inline_alloc_ids, place);
    let dealloc_effects = collect_box_dyn_dealloc_effects(ctx, ptr_expr, known_alloc_id)?;

    let vtable_expr = if place.projection.is_empty() {
        inline_vtable_ids.get(&place.local).cloned()
    } else {
        None
    }
    .or_else(|| {
        place.projection.is_empty().then(|| ctx.known_vtable_expr_for_local(place.local)).flatten()
    })
    .or_else(|| ctx.extract_embedded_vtable_expr(&box_expr))
    .or_else(|| {
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, inner_dyn_ty).map(
            |trait_def_id| {
                ctx.try_extract_vtable_discriminant_for_trait(
                    std::slice::from_ref(&box_expr),
                    place.projection.is_empty().then_some(place.local),
                    Some(trait_def_id),
                )
            },
        )
    });

    let guard = try_inline_dyn_drop_dispatch(
        ctx,
        walk_ctx,
        inner_dyn_ty,
        dealloc_effects.bv_ptr,
        vtable_expr,
        inline_depth,
    )
    .unwrap_or_else(|| Expr::bool_const(true));

    ctx.heap_state.pending_checks.extend(dealloc_effects.pending_checks);
    ctx.heap_state.pending_updates.extend(dealloc_effects.pending_updates);
    Some(guard)
}

fn inline_alloc_id_for_unprojected_drop_place(
    inline_alloc_ids: &HashMap<usize, u32>,
    place: &rustc_public::mir::Place,
) -> Option<u32> {
    if place.projection.is_empty() { inline_alloc_ids.get(&place.local).copied() } else { None }
}

fn try_handle_inline_dyn_drop<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    inline_vtable_ids: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    drop_ty: rustc_public::ty::Ty,
    inline_depth: usize,
) -> Option<Expr> {
    use rustc_public::mir::ProjectionElem;
    use rustc_public::ty::{RigidTy, TyKind};

    if !matches!(drop_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return None;
    }

    // Part of #4231: When the dyn trait being dropped is non-assertion-relevant
    // (e.g., `core::error::Error`), skip vtable dispatch entirely.
    // The drop of boxed dyn Error inner payload goes through here as a bare
    // dyn Error after the Box pointer is dereferenced. Without this,
    // `try_extract_vtable_discriminant_for_trait` creates an unconstrained BV64
    // that causes solver timeouts.
    if let Some(trait_def_id) =
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty)
    {
        let trait_path = ctx.tcx.def_path_str(trait_def_id);
        if ChcCtx::is_formatting_path(&trait_path) {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                %trait_path,
                "inline dyn drop: non-assertion-relevant trait, skip (#4231)"
            );
            return Some(Expr::bool_const(true));
        }
    }

    let Some(self_expr) = resolve_inline_drop_self_expr(ctx, walk_ctx, local_exprs, place) else {
        return None;
    };
    let place_root_expr = local_exprs.get(&place.local).cloned();
    let place_expr = resolve_place(ctx, local_exprs, place, &walk_ctx.resolver, walk_ctx.locals);
    let receiver_local = if place.projection.is_empty()
        || matches!(place.projection.as_slice(), [ProjectionElem::Deref])
    {
        Some(place.local)
    } else {
        None
    };
    let vtable_disc =
        forwarded_heap_vtable_for_dyn_local(ctx, walk_ctx.body, local_exprs, place.local, 8)
            .or_else(|| {
                // Always check inline_vtable_ids for the place's base local,
                // even when the place has field projections (e.g., (*_1).inner).
                // Drop shims for Wrapper<dyn Trait> have Drop terminators on
                // field projections of local 1 (self), and the vtable is seeded
                // on local 1 by seed_shared_pointer_inner_drop_vtable.
                inline_vtable_ids.get(&place.local).cloned()
            })
            .or_else(|| {
                receiver_local.and_then(|local_idx| ctx.known_vtable_expr_for_local(local_idx))
            })
            .or_else(|| {
                // Also check ctx vtable for the base local even with projections.
                ctx.known_vtable_expr_for_local(place.local)
            })
            .or_else(|| {
                place_root_expr.as_ref().and_then(|expr| forwarded_heap_vtable_for_expr(ctx, expr))
            })
            .or_else(|| {
                place_root_expr.as_ref().and_then(|expr| ctx.extract_embedded_vtable_expr(expr))
            })
            .or_else(|| {
                place_expr.as_ref().and_then(|expr| forwarded_heap_vtable_for_expr(ctx, expr))
            })
            .or_else(|| place_expr.as_ref().and_then(|expr| ctx.extract_embedded_vtable_expr(expr)))
            .or_else(|| {
                crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty).map(
                    |trait_def_id| {
                        let receiver_expr = place_root_expr
                            .clone()
                            .or(place_expr.clone())
                            .into_iter()
                            .collect::<Vec<_>>();
                        ctx.try_extract_vtable_discriminant_for_trait(
                            &receiver_expr,
                            receiver_local,
                            Some(trait_def_id),
                        )
                    },
                )
            });

    if let Some(concrete_ty) =
        find_inline_concrete_source_for_dyn_local(ctx, walk_ctx.body, place.local, 8)
    {
        let drop_instance = Instance::resolve_drop_in_place(concrete_ty);
        if !drop_instance.is_empty_shim()
            && let Some(drop_body) = drop_instance.body()
        {
            let mut caller_vtable_ids = HashMap::new();
            seed_box_new_payload_vtable_inline(
                ctx,
                walk_ctx.body,
                local_exprs,
                inline_vtable_ids,
                place.local,
                &drop_body,
                &mut caller_vtable_ids,
            );
            ctx.mark_inline_field_reads(
                &drop_body,
                std::slice::from_ref(&self_expr),
                walk_ctx.bb_idx,
            );
            if let Some(inline_result) = translate_virtual_body_inline(
                ctx,
                &drop_body,
                std::slice::from_ref(&self_expr),
                walk_ctx.bb_idx,
                &caller_vtable_ids,
                Some(drop_instance),
                inline_depth + 1,
            ) {
                return Some(
                    extract_inline_assert_guard(&inline_result.value)
                        .unwrap_or_else(|| Expr::bool_const(true)),
                );
            }
        }
    }

    Some(try_inline_dyn_drop_dispatch(
        ctx,
        walk_ctx,
        drop_ty,
        self_expr,
        vtable_disc,
        inline_depth,
    )?)
}

fn try_inline_dyn_drop_dispatch<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    drop_ty: rustc_public::ty::Ty,
    self_expr: Expr,
    vtable_disc: Option<Expr>,
    inline_depth: usize,
) -> Option<Expr> {
    let trait_def_id =
        crate::codegen_ay::chc::dyn_coercion::extract_dyn_trait_def_id(ctx, drop_ty)?;
    let candidates =
        crate::codegen_ay::chc::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return Some(Expr::bool_const(true));
    }

    let params = [self_expr];
    let mut drop_bodies: Vec<(u64, rustc_public::mir::Body, Instance)> = Vec::new();
    for candidate in &candidates {
        let drop_instance = Instance::resolve_drop_in_place(candidate.concrete_ty);
        if drop_instance.is_empty_shim() {
            continue;
        }
        if let Some(body) = drop_instance.body() {
            drop_bodies.push((candidate.vtable_id, body, drop_instance));
        }
    }
    if drop_bodies.is_empty() {
        return Some(Expr::bool_const(true));
    }

    if drop_bodies.len() == 1 {
        let (_, ref body, ref drop_instance) = drop_bodies[0];
        ctx.mark_inline_field_reads(body, &params, walk_ctx.bb_idx);
        let mut caller_vtable_ids = HashMap::new();
        if let Some(vtable_disc) = &vtable_disc {
            caller_vtable_ids.insert(1, vtable_disc.clone());
        }
        let inline_result = translate_virtual_body_inline(
            ctx,
            body,
            &params,
            walk_ctx.bb_idx,
            &caller_vtable_ids,
            Some(*drop_instance),
            inline_depth + 1,
        )?;
        return Some(
            extract_inline_assert_guard(&inline_result.value)
                .unwrap_or_else(|| Expr::bool_const(true)),
        );
    }

    let concrete_bodies: Vec<ResolvedDispatchBody> = drop_bodies
        .into_iter()
        .map(|(vtable_id, body, _)| ResolvedDispatchBody { vtable_id, body })
        .collect();
    let dispatch_vtable = vtable_disc.unwrap_or_else(|| {
        super::super::declare_pending_var(
            super::super::chc_fresh_name("__dyn_drop_vtable"),
            Sort::bitvec(POINTER_WIDTH),
        )
    });
    let mut caller_vtable_ids = HashMap::new();
    caller_vtable_ids.insert(1, dispatch_vtable.clone());
    let inline_result = build_dispatch_ite_chain_impl(
        ctx,
        &concrete_bodies,
        &params,
        dispatch_vtable,
        walk_ctx.bb_idx,
        &caller_vtable_ids,
        inline_depth + 1,
    )?;
    Some(
        extract_inline_assert_guard(&inline_result.value).unwrap_or_else(|| Expr::bool_const(true)),
    )
}

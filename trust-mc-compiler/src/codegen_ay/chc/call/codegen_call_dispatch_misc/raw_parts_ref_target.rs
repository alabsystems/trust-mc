// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ref-target propagation helpers for `NonNull::from_raw_parts`.

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use super::super::ChcCtx;
use super::super::codegen_ctx::types::RefTarget;

fn is_nonnull_raw_parts_ref_target_identity_call(path: &str) -> bool {
    (path.contains("NonNull")
        && (path.ends_with("::new")
            || path.ends_with("::new_unchecked")
            || path.ends_with("::as_ptr")
            || path.ends_with("::cast")))
        || (path.contains("Option") && (path.ends_with("::unwrap") || path.ends_with("::expect")))
}

fn nonnull_from_raw_parts_source_local(
    ctx: &ChcCtx<'_, '_>,
    src_local: Option<usize>,
    ptr_expr: &Expr,
) -> Option<usize> {
    src_local.map(|local| ctx.resolve_provenance_local(local)).or_else(|| {
        ChcCtx::try_extract_obj_id(ptr_expr)
            .and_then(|obj_id| ctx.heap_state.local_idx_for_obj_id(obj_id))
    })
}

pub(super) fn propagate_nonnull_from_raw_parts_identity(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    src_local: Option<usize>,
    ptr_expr: &Expr,
) {
    let source_local = nonnull_from_raw_parts_source_local(ctx, src_local, ptr_expr);
    let ptr_obj_id = ChcCtx::try_extract_obj_id(ptr_expr);

    if let Some(obj_id) = source_local
        .and_then(|sl| ctx.known_alloc_ids.get(&sl).copied())
        .or_else(|| source_local.and_then(|sl| ctx.trace_deref_store_alloc_id(sl)))
        .or_else(|| src_local.and_then(|sl| ctx.known_alloc_ids.get(&sl).copied()))
        .or_else(|| src_local.and_then(|sl| ctx.trace_deref_store_alloc_id(sl)))
        .or(ptr_obj_id)
    {
        ctx.known_alloc_ids.insert(dest_local, obj_id);
    } else {
        ctx.known_alloc_ids.remove(&dest_local);
    }

    let ref_target = source_local
        .and_then(|sl| ctx.ref_resolution.ref_targets.get(&sl).cloned())
        .or_else(|| src_local.and_then(|sl| ctx.ref_resolution.ref_targets.get(&sl).cloned()))
        .or_else(|| src_local.and_then(|sl| trace_nonnull_raw_parts_ref_target(ctx, sl)))
        .or_else(|| {
            ptr_obj_id.and_then(|obj_id| {
                ctx.heap_state
                    .local_idx_for_obj_id(obj_id)
                    .map(|local| RefTarget::with_projections(local, vec![]))
            })
        });
    if let Some(ref_target) = ref_target {
        ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    } else {
        ctx.ref_resolution.ref_targets.remove(&dest_local);
        ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
    }
}

fn trace_nonnull_raw_parts_ref_target(ctx: &ChcCtx<'_, '_>, local_idx: usize) -> Option<RefTarget> {
    let mut seen = std::collections::HashSet::new();
    trace_nonnull_raw_parts_ref_target_inner(ctx, local_idx, &mut seen)
}

fn trace_nonnull_raw_parts_ref_target_inner(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
    seen: &mut std::collections::HashSet<usize>,
) -> Option<RefTarget> {
    if !seen.insert(local_idx) {
        return None;
    }
    if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&local_idx).cloned() {
        return Some(ref_target);
    }

    for bb_data in &ctx.body.blocks {
        for stmt in &bb_data.statements {
            let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            if lhs.local != local_idx || !lhs.projection.is_empty() {
                continue;
            }
            if let Some(ref_target) = trace_nonnull_raw_parts_stmt_ref_target(ctx, rhs, seen) {
                return Some(ref_target);
            }
        }
    }

    for bb_data in &ctx.body.blocks {
        let rustc_public::mir::TerminatorKind::Call { destination, func, args, .. } =
            &bb_data.terminator.kind
        else {
            continue;
        };
        if destination.local != local_idx {
            continue;
        }
        let Some(callee) = ctx.resolve_callee_path(func) else {
            continue;
        };
        if !is_nonnull_raw_parts_ref_target_identity_call(&callee) {
            continue;
        }
        let Some(arg_local) = args.first().and_then(|arg| match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }) else {
            continue;
        };
        if let Some(ref_target) = trace_nonnull_raw_parts_ref_target_inner(ctx, arg_local, seen) {
            return Some(ref_target);
        }
    }

    None
}

fn trace_nonnull_raw_parts_stmt_ref_target(
    ctx: &ChcCtx<'_, '_>,
    rhs: &rustc_public::mir::Rvalue,
    seen: &mut std::collections::HashSet<usize>,
) -> Option<RefTarget> {
    use rustc_public::mir::{ProjectionElem, Rvalue};

    match rhs {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
            if place.projection.is_empty() =>
        {
            trace_nonnull_raw_parts_ref_target_inner(ctx, place.local, seen)
        }
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
            if place.projection.is_empty() {
                return Some(RefTarget::with_projections(place.local, Vec::new()));
            }
            if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                return ctx
                    .ref_resolution
                    .ref_targets
                    .get(&place.local)
                    .cloned()
                    .or_else(|| trace_nonnull_raw_parts_ref_target_inner(ctx, place.local, seen));
            }
            None
        }
        _ => None,
    }
}

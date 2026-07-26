// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ref-target tracing for pointer identity/passthrough calls.

use tracing::debug;

use super::ChcCtx;
use super::codegen_ctx::types::RefTarget;

pub(super) fn propagate_ref_target(
    ctx: &mut ChcCtx<'_, '_>,
    dest_local: usize,
    src_local: Option<usize>,
    ptr_obj_id: Option<u32>,
) {
    if let Some(sl) = src_local {
        if let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&sl).cloned() {
            debug!(
                dest_local,
                src_local = sl,
                target = ref_target.local,
                "pointer identity: propagated direct ref_target"
            );
            ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
            ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
            return;
        }
        if let Some(ref_target) = trace_pointer_identity_ref_target(ctx, sl) {
            debug!(
                dest_local,
                src_local = sl,
                target = ref_target.local,
                "pointer identity: propagated traced ref_target"
            );
            ctx.ref_resolution.ref_targets.insert(dest_local, ref_target);
            ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
            return;
        }
    }

    if let Some(obj_id) = ptr_obj_id
        && let Some(owning_local) = ctx.heap_state.local_idx_for_obj_id(obj_id)
    {
        debug!(dest_local, obj_id, owning_local, "pointer identity: propagated obj_id ref_target");
        ctx.ref_resolution
            .ref_targets
            .insert(dest_local, RefTarget::with_projections(owning_local, vec![]));
        ctx.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
    } else {
        debug!(dest_local, ?src_local, ?ptr_obj_id, "pointer identity: no ref_target propagated");
    }
}

pub(in crate::codegen_ay::chc) fn trace_pointer_identity_ref_target(
    ctx: &ChcCtx<'_, '_>,
    local_idx: usize,
) -> Option<RefTarget> {
    let mut seen = std::collections::HashSet::new();
    trace_pointer_identity_ref_target_inner(ctx, local_idx, &mut seen)
}

fn trace_pointer_identity_ref_target_inner(
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
            if let Some(ref_target) = trace_pointer_identity_stmt_ref_target(ctx, rhs, seen) {
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
        if !is_pointer_ref_target_identity_call(&callee) {
            continue;
        }
        let Some(arg_local) = args.first().and_then(|arg| match arg {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
                if place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        }) else {
            continue;
        };
        if let Some(ref_target) = trace_pointer_identity_ref_target_inner(ctx, arg_local, seen) {
            return Some(ref_target);
        }
    }

    None
}

fn trace_pointer_identity_stmt_ref_target(
    ctx: &ChcCtx<'_, '_>,
    rhs: &rustc_public::mir::Rvalue,
    seen: &mut std::collections::HashSet<usize>,
) -> Option<RefTarget> {
    use rustc_public::mir::{ProjectionElem, Rvalue};

    match rhs {
        Rvalue::Use(
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place),
        )
        | Rvalue::Cast(
            _,
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place),
            _,
        ) if place.projection.is_empty() => {
            trace_pointer_identity_ref_target_inner(ctx, place.local, seen)
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
                    .or_else(|| trace_pointer_identity_ref_target_inner(ctx, place.local, seen));
            }
            None
        }
        Rvalue::Aggregate(_, operands) if operands.len() == 1 => {
            let (rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)) =
                &operands[0]
            else {
                return None;
            };
            if place.projection.is_empty() {
                trace_pointer_identity_ref_target_inner(ctx, place.local, seen)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_pointer_ref_target_identity_call(path: &str) -> bool {
    let lower = path.to_ascii_lowercase();
    (lower.contains("nonnull") || lower.contains("non_null"))
        && (path.ends_with("::new")
            || path.ends_with("::new_unchecked")
            || path.ends_with("::as_ptr")
            || path.ends_with("::cast")
            || path.ends_with("::from_raw_parts"))
        || (path.contains("Option") && (path.ends_with("::unwrap") || path.ends_with("::expect")))
}

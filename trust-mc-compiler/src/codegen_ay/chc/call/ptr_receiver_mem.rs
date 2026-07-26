// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared CHC raw-pointer receiver resolution and memory-model helpers.
//!
//! This module provides the single contract for resolving raw pointer operands
//! to stack locals or heap-backed (addr, pointee_ty) pairs. Both the atomic
//! and volatile intrinsic families consume these helpers.
//!
//! Extracted from `codegen_call_atomic_mem.rs` to eliminate the duplicated
//! `resolve_ptr_target_local` in the volatile module.
//!
//! Part of #3697, #3094.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;

/// Resolve the MIR local that a pointer operand points to via `ref_targets`.
///
/// Returns `None` if the pointer cannot be resolved (projection, missing
/// entry, constant operand). Shared by both atomic and volatile families.
pub(in crate::codegen_ay::chc) fn resolve_ptr_target_local(
    ctx: &ChcCtx<'_, '_>,
    arg: &Operand,
) -> Option<usize> {
    let place = match arg {
        Operand::Copy(place) | Operand::Move(place) => place,
        _ => return None,
    };
    if !place.projection.is_empty() {
        return None;
    }
    let ptr_local: usize = place.local;
    let ref_target = ctx.ref_resolution.ref_targets.get(&ptr_local)?;
    if !ref_target.projections.is_empty() {
        return None;
    }
    Some(ref_target.local)
}

/// Resolve a raw pointer operand to a BV64 address plus pointee type.
///
/// Works for heap-backed receivers where the pointee has no stack-local owner
/// (e.g. `AtomicUsize::from_ptr(Box::into_raw(...))`).
pub(in crate::codegen_ay::chc) fn receiver_mem_target(
    ctx: &mut ChcCtx<'_, '_>,
    arg: &Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<(Expr, Ty)> {
    let pointee_ty = arg.ty(ctx.body.locals()).ok().and_then(|ty| match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    })?;
    let addr = match arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => ctx
            .trace_deref_store_alloc_id(place.local)
            .map(|obj_id| Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32)))
            .or_else(|| ctx.translate_operand_with_modified(arg, modified_locals)),
        _ => ctx.translate_operand_with_modified(arg, modified_locals),
    }?;
    (addr.sort().bitvec_width() == Some(64)).then_some((addr, pointee_ty))
}

/// Load a value from the CHC memory model at a given address.
///
/// Phase 1: concrete address → extract obj_id → owning local's type.
/// Phase 2: if pointee array unwritten, find aliased array with same elem_sort.
/// Part of #3452, #3697.
pub(in crate::codegen_ay::chc) fn load_from_memory(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &Expr,
    pointee_ty: Ty,
) -> Option<Expr> {
    // Phase 1: Concrete addresses — resolve owning local's type.
    let load_ty = ChcCtx::try_extract_obj_id(addr)
        .and_then(|obj_id| ctx.heap_state.local_idx_for_obj_id(obj_id))
        .and_then(|local_idx| ctx.body.locals().get(local_idx))
        .map(|decl| decl.ty)
        .unwrap_or(pointee_ty);

    // Part of #3661: resolve generic params for consistent type keys.
    let type_key = ctx.type_key_for_body_ty(load_ty);
    let arr_written = ctx
        .heap_state
        .type_arrays
        .get(type_key.as_ref())
        .map(|(n, _)| ctx.heap_state.write_used_type_arrays.contains_key(n))
        .unwrap_or(false);

    if arr_written {
        return ctx.load_from_memory(addr.clone(), load_ty);
    }

    // Phase 2: search for aliased repr(transparent) array with matching elem_sort.
    let target_sort = ctx.elem_sort_for_memory_array(load_ty);
    let alt = ctx
        .heap_state
        .type_arrays
        .iter()
        .find(|(_, (arr_name, sort))| {
            *sort == target_sort && ctx.heap_state.write_used_type_arrays.contains_key(arr_name)
        })
        .map(|(key, (arr_name, sort))| (key.clone(), arr_name.clone(), sort.clone()));

    if let Some((alt_key, alt_arr_name, alt_elem_sort)) = alt {
        let arr_sort = Sort::array(crate::codegen_ay::types::ptr_sort(), alt_elem_sort);
        let arr_expr = if let Some(chain) = ctx.heap_state.get_store_chain(&alt_key) {
            chain.clone()
        } else {
            Expr::var(&*alt_arr_name, arr_sort)
        };
        ctx.heap_state.mark_type_array_read(&alt_arr_name, ctx.current_encode_bb);
        tracing::debug!(
            alt_key = %alt_key,
            "ptr_receiver: repr(transparent) alias fallback (#3452)"
        );
        return Some(arr_expr.select(addr.clone()));
    }

    // No aliased array found — fall back to primary (value will be unconstrained).
    ctx.load_from_memory(addr.clone(), load_ty)
}

/// Register a raw-pointer argument as call-forwarded when its ref_target resolves.
///
/// At Mem track level, raw pointer dereferences are routed through the memory
/// path (not ref_targets) to match the store side. Atomic handlers update the
/// referent via the register (ref_target) path, so subsequent dereferences of
/// the same pointer must also use ref_targets for consistency. Without this,
/// `*ptr` after `atomic_xadd(ptr, val)` reads stale/unconstrained memory
/// instead of the atomic update.
///
/// Part of #3761: raw-pointer unstable atomic CTREX after dispatch fix.
pub(in crate::codegen_ay::chc) fn mark_atomic_ptr_forwarded(
    ctx: &mut ChcCtx<'_, '_>,
    arg: &Operand,
) {
    if let Operand::Copy(place) | Operand::Move(place) = arg
        && place.projection.is_empty()
    {
        let ptr_local: usize = place.local;
        let is_raw_ptr =
            ctx.body.locals().get(ptr_local).is_some_and(|decl| {
                matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(_, _)))
            });
        if is_raw_ptr && ctx.ref_resolution.ref_targets.contains_key(&ptr_local) {
            debug!(ptr_local, "atomic: marking raw ptr as call_forwarded (#3761)");
            ctx.ref_resolution.call_forwarded_raw_ptrs.insert(ptr_local);
        }
    }
}

/// Drain pending_checks into error rules. Call terminators bypass the
/// statement-level drain at codegen_stmt.rs:602 (#2905, #3636).
pub(in crate::codegen_ay::chc) fn drain_pending_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    for check in ctx.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
        ctx.emit_error_rule_for_condition(dcx.from_app, check, dcx.stmt_constraints, target);
    }
}

/// Flush heap side effects emitted by call-terminator memory stores.
pub(in crate::codegen_ay::chc) fn drain_pending_updates(
    ctx: &mut ChcCtx<'_, '_>,
    extra: &mut Vec<Expr>,
) {
    extra.append(&mut ctx.heap_state.pending_updates);
    extra.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
}

/// Emit a memory-backed store transition for heap-addressable receivers.
///
/// Shared by both atomic and volatile store paths.
/// Part of #3710: `build_memory_store` accumulates store constraints into
/// heap store chains (returns None on success). Constraints are flushed by
/// `drain_pending_updates` which calls `drain_store_chains`.
pub(in crate::codegen_ay::chc) fn emit_mem_store_transition(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    value: Expr,
    addr: Expr,
    pointee_ty: Ty,
) -> bool {
    let dest_local: usize = dcx.destination.local;
    // build_memory_store accumulates the store into heap store chains
    // and returns None (success). The accumulated constraint is flushed
    // by drain_pending_updates → drain_store_chains below.
    ctx.build_memory_store(addr, value, pointee_ty);

    let mut extra = Vec::new();
    drain_pending_updates(ctx, &mut extra);
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    drain_pending_checks(ctx, dcx, target);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    true
}

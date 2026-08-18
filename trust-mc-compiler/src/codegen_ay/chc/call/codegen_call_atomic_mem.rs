// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Atomic-family re-exports of shared CHC memory-model helpers.
//!
//! The generic raw-pointer receiver logic now lives in `ptr_receiver_mem.rs`.
//! This module re-exports with atomic-prefixed names so existing atomic call
//! sites compile unchanged.
//!
//! Part of #3697, #3598.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use rustc_public::ty::Ty;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::ptr_receiver_mem;
use crate::codegen_ay::provenance::{MaybeLoc, Val};

/// Re-export: load from CHC memory model at a given address.
/// A load is the one legal `Loc -> Val` crossing, so this is the one place in
/// the atomic path where an address becomes a datum. The address half is a
/// [`MaybeLoc`] because that is what the receiver resolver can honestly report
/// (§4 item 10); the *result* is unambiguous — whatever was read out of memory
/// is a value.
pub(in crate::codegen_ay::chc) fn atomic_load_from_memory(
    ctx: &mut ChcCtx<'_, '_>,
    addr: &MaybeLoc,
    pointee_ty: Ty,
) -> Option<Val> {
    ptr_receiver_mem::load_from_memory(ctx, addr, pointee_ty)
}

/// Re-export: drain pending_checks into error rules.
pub(in crate::codegen_ay::chc) fn drain_atomic_pending_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    ptr_receiver_mem::drain_pending_checks(ctx, dcx, target)
}

/// Re-export: resolve raw pointer operand to (addr, pointee_ty).
///
/// The address half is a [`MaybeLoc`]: `Known` when the encoder built it from a
/// traced allocation id, `Unknown` when it came from a general operand
/// translation that reports no provenance.
pub(in crate::codegen_ay::chc) fn atomic_receiver_mem_target(
    ctx: &mut ChcCtx<'_, '_>,
    arg: &rustc_public::mir::Operand,
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<(MaybeLoc, Ty)> {
    ptr_receiver_mem::receiver_mem_target(ctx, arg, modified_locals)
}

/// Re-export: emit memory-backed store transition.
///
/// `value` and `addr` used to be two adjacent `Expr` parameters — one datum,
/// one address, same type, trivially transposable at any call site. That is the
/// canonical slot-misalign shape (see wave 13), and typing them [`Val`] and
/// [`MaybeLoc`] makes the transposition a compile error.
pub(in crate::codegen_ay::chc) fn emit_atomic_mem_store_transition(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    value: Val,
    addr: MaybeLoc,
    pointee_ty: Ty,
) -> bool {
    ptr_receiver_mem::emit_mem_store_transition(
        ctx,
        dcx,
        target,
        value.into_expr(),
        addr.into_addr_expr(),
        pointee_ty,
    )
}

/// Re-export: emit constraints for RMW when receiver is heap-addressable.
pub(in crate::codegen_ay::chc) fn emit_rmw_constraints_mem(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    old_value: Expr,
    new_value: Expr,
    addr: MaybeLoc,
    pointee_ty: Ty,
) {
    let dest_local: usize = dcx.destination.local;
    let mut extra = Vec::new();

    if let Some((_, dv)) = ctx.resolve_destination(dest_local) {
        let s = dv.sort().clone();
        if let Some(eq) =
            ctx.make_coerced_eq_constraint(&dv, old_value, &s, dest_local, "atomic_rmw_dest")
        {
            extra.push(eq);
        }
    }

    // Part of #3710: build_memory_store accumulates into store chains
    // (returns None on success). Drain via drain_pending_updates below.
    ctx.build_memory_store_untyped(addr.into_addr_expr(), new_value, pointee_ty);
    ptr_receiver_mem::drain_pending_updates(ctx, &mut extra);

    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ptr_receiver_mem::drain_pending_checks(ctx, dcx, target);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
}

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
use tracing::debug;

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
    emit_register_coherent_atomic_store(
        ctx,
        dcx,
        target,
        value.into_expr(),
        addr,
        pointee_ty,
        None,
        "atomic_store",
    );
    true
}

/// A Mem-level atomic store (`store`, and the write half of an RMW) with the
/// Cell lane's register coherence (`codegen_call_cell_register.rs`, R5).
///
/// The store writes the atomic's memory-mirror address only. The atomic's
/// owning local keeps its register, and the next whole-local borrow copied
/// that stale register back over the store: `s.a.store(200, SeqCst);
/// assert!(read_sa(&s) < 100)` verified SUCCESSFUL clean and its `== 200`
/// twin FAILED Genuine (review of fix/chc-cell-set-write, 2026-09-26). The
/// owner's register is rebound to the stored value exactly, or havoced.
/// `old`, when given, is bound to the destination (the RMW result).
#[allow(clippy::too_many_arguments)]
pub(in crate::codegen_ay::chc) fn emit_register_coherent_atomic_store(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    value: Expr,
    addr: MaybeLoc,
    pointee_ty: Ty,
    old: Option<Expr>,
    site: &'static str,
) {
    use super::codegen_call_cell_register::{CellRegisterSync, substitute_vars};

    let dest_local: usize = dcx.destination.local;
    let receiver = &dcx.args[0];
    // D7(b): an atomic whose address const-folds into a static the harness
    // keeps a state variable for (`RA.store(5)` for `static RA: &AtomicU32 =
    // &ATOMS[1]`), or whose receiver the MIR derives from the static's own
    // address (`AS[1].store(7)`, `CT.b.store(9)`), writes that state variable
    // too, along the static place path, and the static's memory image with
    // it; the block's earlier binding of it is rewritten onto the pre-store
    // value first. Without it the store reached typed memory only and
    // `ATOMS[1].load() == 2` PROVED.
    let static_routes = ctx.plan_static_store_route(
        &addr.clone().into_addr_expr(),
        receiver,
        dcx.modified_locals,
        dcx.stmt_constraints,
    );
    let store_target = ctx.cell_store_target(receiver, &addr, pointee_ty);
    let plan = ctx.plan_cell_register_mirror(
        &store_target,
        &value,
        pointee_ty,
        dcx.modified_locals,
        dcx.stmt_constraints,
    );
    let mut substitution = plan.substitution;
    let mut superseded = plan.superseded;
    for route in &static_routes {
        substitution.extend(route.substitution.clone());
        superseded.extend(route.superseded.iter().copied());
    }
    let kept: Vec<Expr> = dcx
        .stmt_constraints
        .iter()
        .enumerate()
        .filter(|(idx, _)| !superseded.contains(idx))
        .map(|(_, c)| substitute_vars(c, &substitution))
        .collect();
    let value = substitute_vars(&value, &substitution);
    let old = old.map(|old| substitute_vars(&old, &substitution));
    if !substitution.is_empty() {
        ctx.heap_state.rewrite_pending_terms(|e| substitute_vars(e, &substitution));
    }
    let addr_expr = substitute_vars(&addr.into_addr_expr(), &substitution);
    if ChcCtx::try_extract_obj_id(&addr_expr).is_none() {
        ctx.note_symbolic_store_may_alias_regions(&addr_expr);
    }
    let mut extra = Vec::new();
    ctx.with_static_store_routing(|ctx| {
        ctx.build_memory_store_untyped(addr_expr.clone(), value.clone(), pointee_ty);
        ctx.constrain_static_store_routes(
            &static_routes,
            pointee_ty,
            &value,
            &addr_expr,
            &mut extra,
        );
    });
    let mut out_locals = vec![dest_local];
    match plan.sync {
        CellRegisterSync::Synced { local, constraints } => {
            debug!(local, site, "atomic: register mirror bound to the stored value");
            ctx.encode.invalidate_local_cache(local);
            extra.extend(constraints);
            if local != dest_local {
                out_locals.push(local);
            }
        }
        CellRegisterSync::Havoc { locals, reason, cause } => {
            debug!(site, reason, cause, ?locals, "atomic: register mirror havoced");
            ctx.record_cell_register_havoc(reason, cause, &locals);
            for local in locals {
                ctx.encode.invalidate_local_cache(local);
                if !out_locals.contains(&local) {
                    out_locals.push(local);
                }
            }
        }
        CellRegisterSync::NotNeeded => {}
    }
    if let Some(old) = old
        && let Some((_, dv)) = ctx.resolve_destination(dest_local)
    {
        let s = dv.sort().clone();
        if let Some(eq) = ctx.make_coerced_eq_constraint(&dv, old, &s, dest_local, site) {
            extra.push(eq);
        }
    }
    ptr_receiver_mem::drain_pending_updates(ctx, &mut extra);
    let out = ctx.build_output_args(dcx.modified_locals, &out_locals);
    // Partition the actual runtime address, keeping an explicit symbolic
    // catch-all. Substitute under each equality into BOTH the successor and
    // the checks; this is a tautological case split, not a coverage assumption.
    if let ay_bindings::ExprValue::Var { name } = addr_expr.value()
        && let Some(cases) = ctx.static_array_store_address_cases(&static_routes, pointee_ty)
    {
        let checks = std::mem::take(&mut ctx.heap_state.pending_checks);
        let mut rest_guard = Expr::bool_const(true);
        for case in &cases {
            rest_guard = rest_guard.and(addr_expr.clone().eq(case.clone()).not());
        }
        for case in cases.iter().map(Some).chain(std::iter::once(None)) {
            let substitution = case
                .map(|c| std::collections::HashMap::from([(name.to_string(), c.clone())]))
                .unwrap_or_default();
            let rewrite = |e: &Expr| substitute_vars(e, &substitution);
            let mut constraints: Vec<_> = kept.iter().map(rewrite).collect();
            constraints.push(
                case.map(|c| addr_expr.clone().eq(c.clone())).unwrap_or_else(|| rest_guard.clone()),
            );
            let branch_out: Vec<_> = out.iter().map(rewrite).collect();
            let branch_extra: Vec<_> = extra.iter().map(rewrite).collect();
            ctx.heap_state.pending_checks = checks.iter().map(rewrite).collect();
            let branch = DispatchCallContext {
                bb_idx: dcx.bb_idx,
                func: dcx.func,
                args: dcx.args,
                destination: dcx.destination,
                target: dcx.target,
                from_app: dcx.from_app,
                stmt_constraints: &constraints,
                modified_locals: dcx.modified_locals,
                callee_path: dcx.callee_path.clone(),
            };
            ptr_receiver_mem::drain_pending_checks(ctx, &branch, target);
            ctx.emit_goto_rule_extra(dcx.from_app, target, &branch_out, &constraints, branch_extra);
        }
        return;
    }
    let rewritten = DispatchCallContext {
        bb_idx: dcx.bb_idx,
        func: dcx.func,
        args: dcx.args,
        destination: dcx.destination,
        target: dcx.target,
        from_app: dcx.from_app,
        stmt_constraints: &kept,
        modified_locals: dcx.modified_locals,
        callee_path: dcx.callee_path.clone(),
    };
    ptr_receiver_mem::drain_pending_checks(ctx, &rewritten, target);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &out, &kept, extra);
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
    // Part of #3710: build_memory_store accumulates into store chains
    // (returns None on success), drained by the coherent store below.
    emit_register_coherent_atomic_store(
        ctx,
        dcx,
        target,
        new_value,
        addr,
        pointee_ty,
        Some(old_value),
        "atomic_rmw_dest",
    );
}

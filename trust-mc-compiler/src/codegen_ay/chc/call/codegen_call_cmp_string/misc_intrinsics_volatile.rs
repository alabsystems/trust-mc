// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Volatile memory intrinsic handlers for CHC codegen.
//!
//! Handles value-propagating memory intrinsics that lack MIR bodies:
//! - `volatile_load` / `unaligned_volatile_load` — `dest = *ptr`
//! - `volatile_store` — `*ptr = val` (simple and projected paths)
//! - `volatile_copy_memory` / `volatile_copy_nonoverlapping_memory` — `copy(dst, src, count)`
//! - `typed_swap_nonoverlapping` — `*x = old_*y, *y = old_*x`
//!
//! Extracted from `misc_intrinsics.rs` to keep volatile memory handling localized.
//!
//! Part of #3444, #3464, #3697: Shared raw-pointer Mem bridge.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place, ProjectionElem};
use rustc_public::CrateDef as _;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_rules::CodegenRules;
use super::super::ptr_receiver_mem::{
    drain_pending_checks, drain_pending_updates, emit_mem_store_transition, load_from_memory,
    receiver_mem_target, resolve_ptr_target_local,
};
use super::misc_intrinsics_volatile_helpers::{
    find_ptr_add_base_and_count, projected_vec_data_slot_for_ptr, try_extract_vec_element_for_load,
    try_volatile_load_via_projected_vec, try_volatile_load_via_ptr_add,
    try_volatile_load_via_vec_trace,
};
use crate::codegen_ay::provenance::Val;

/// The locals with their own state that the pointer operands of a write this
/// module could not resolve may address (see
/// `ChcCtx::stack_locals_pointer_may_address`).
fn unresolved_write_candidates(
    ctx: &ChcCtx<'_, '_>,
    pointer_args: &[rustc_public::mir::Operand],
) -> Vec<usize> {
    let mut candidates = Vec::new();
    for arg in pointer_args {
        let Some(ptr_local) = extract_plain_operand_local(arg) else {
            continue;
        };
        let (found, _complete) = ctx.stack_locals_pointer_may_address(ptr_local);
        for local in found {
            if !candidates.contains(&local) {
                candidates.push(local);
            }
        }
    }
    candidates
}

/// A write through pointer operands that could not be resolved to exact
/// targets. Dropping it leaves every local the pointers address at its old
/// value — after `mem::swap(&mut o, &mut q)` on a joined `o`, `o == None` was
/// proved false (tools/soundness-duals/negative/review_r18_mutate_then_compare.rs).
/// The locals the pointers may address are left unconstrained, and `reason` is
/// a fail-close fallback: the harness cannot come back clean.
fn emit_unresolved_pointer_write(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    pointer_args: &[rustc_public::mir::Operand],
    reason: &'static str,
) {
    let dest_local: usize = dcx.destination.local;
    let mut outputs = vec![dest_local];
    for local in unresolved_write_candidates(ctx, pointer_args) {
        if !outputs.contains(&local) {
            outputs.push(local);
        }
    }
    debug!(reason, ?outputs, "CHC: pointer write with unresolved targets (fail closed)");
    ctx.record_sound_fallback_reason(reason);
    let out = ctx.build_output_args(dcx.modified_locals, &outputs);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
}

/// Bring the typed-memory image of `local` in step with `new_value`, the value
/// an exact local update in this transition gave its state.
///
/// A local's image is written when the local is assigned and when it is
/// borrowed. An update that constrains only its state (a swap, replace or
/// volatile store through a resolved target) left the image at the old value,
/// and a read through a pointer made before the write — one joined from two
/// borrows, which has no single points-at edge — loaded that old value:
/// `let r: *const u8 = if b { &m } else { &n }; mem::swap(&mut m, &mut n);`
/// then `*r` was the pre-swap `m`, and --ay-chc proved `*r != 2` on the path
/// that took `&m` (tools/soundness-duals/negative/stale_memory_image_writes.rs).
///
/// `modified` must already contain `local`. Returns `false` when the image
/// could not be written; the caller then fails closed.
pub(in crate::codegen_ay::chc) fn refresh_local_memory_image(
    ctx: &mut ChcCtx<'_, '_>,
    local: usize,
    new_value: &Expr,
    modified: &HashSet<usize>,
    constraints: &mut Vec<Expr>,
) -> bool {
    if ctx.track_level < ChcTrackLevel::Mem {
        return true;
    }
    let place = Place { local, projection: Vec::new() };
    let Some(loc) = ctx.translate_ref_to_address(&place, modified) else {
        return false;
    };
    let Some(local_ty) = ctx.body.locals().get(local).map(|decl| decl.ty) else {
        return false;
    };
    let addr = loc.into_expr();
    ctx.mirror_ref_value_to_memory(&addr, new_value, local_ty, local, modified, constraints);
    true
}

fn extract_plain_operand_local(arg: &rustc_public::mir::Operand) -> Option<usize> {

    let place = match arg {
        Operand::Copy(place) | Operand::Move(place) => place,
        _ => return None,
    };
    if !place.projection.is_empty() {
        return None;
    }
    Some(place.local)
}

/// P4-3: real UB obligations for a volatile access — the pointer must be
/// aligned for `T` and the single-element span must fit its allocation
/// (Kani emits both; `store_fail.rs` is the alignment fail-oracle).
///
/// Gated on a CONST-folding obj_id: for symbolic provenance (heap/Vec
/// pointers) the offset lane carries no real alignment information — an
/// unconditional `sym % align == 0` obligation is a spurious-FP factory,
/// and the projected-Vec lanes below already resolve those accesses to
/// element-boundary reads/writes (aligned by construction). Symbolic-
/// provenance volatile accesses keep the historical skip, except for a
/// pointer whose provenance walk names a global object: it gets the object
/// bound.
///
/// Pushed onto `pending_checks`; drained by the caller's emission paths.
fn push_volatile_span_checks(
    ctx: &mut ChcCtx<'_, '_>,
    arg: &rustc_public::mir::Operand,
    modified_locals: &std::collections::HashSet<usize>,
) {
    use rustc_public::ty::{RigidTy, TyKind};

    if !ctx.memory_safety_checks {
        return;
    }
    let Some(pointee_ty) = arg.ty(ctx.body.locals()).ok().and_then(|ty| match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    }) else {
        return;
    };
    let Some(addr) = ctx.translate_operand_with_modified(arg, modified_locals) else {
        return;
    };
    let const_obj = ctx
        .split_pointer(&addr)
        .and_then(|(obj_id, _)| ChcCtx::const_obj_id_u32(&obj_id))
        .is_some();
    if !const_obj {
        // A pointer that walks back to a constant pointer into a static or a
        // constant allocation has a known object, so its access bound is
        // real (`codegen_stmt_rvalue_offset_const_object`):
        // `read_volatile((&V as *const u32).add(1))` proved clean, on main
        // too, where Kani reports "pointer outside object bounds".
        if let Some(local) = extract_plain_operand_local(arg)
            && let Some(provenance) = ctx.const_provenance_for_local(local)
            && let Some(access_size) = ctx
                .get_type_size(pointee_ty)
                .filter(|&size| size > 0)
                .and_then(|size| u32::try_from(size).ok())
        {
            let checks =
                ctx.const_provenance_checks(provenance, local, Some(&addr), access_size, Some(0));
            ctx.push_pending_checks_dedup(checks);
        }
        return;
    }
    let one = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);
    let checks = ctx.heap_span_access_checks(&addr, pointee_ty, &one);
    ctx.heap_state.pending_checks.extend(checks);
}

/// Handle `volatile_load(ptr) -> T` and `unaligned_volatile_load(ptr) -> T`.
///
/// Modeled as `dest = *ptr`. Uses a 4-tier resolution cascade (see body).
/// Part of #3464, #3697, #4074.
pub(in crate::codegen_ay::chc) fn codegen_volatile_load(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.is_empty() {
        debug!("CHC: volatile_load with no args — unconstrained fallback");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        drain_pending_checks(ctx, dcx, target);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    // #3636: volatile_load must check obj_valid like a normal dereference.
    if let Some(ptr_local) = extract_plain_operand_local(&dcx.args[0]) {
        ctx.emit_ptr_obj_valid_check(ptr_local, dcx.modified_locals);
    }
    // P4-3: alignment + span-fits obligations for stack-backed pointers.
    push_volatile_span_checks(ctx, &dcx.args[0], dcx.modified_locals);

    // Resolve the pointed-to value via ref_targets / const_ref resolution.
    let resolved = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);

    // Part of #3485, #4074: Resolution cascade for volatile_load pointer:
    //   Tier 1: ptr.add/BinOp::Offset → fld_data[count] (preserves offset)
    //   Tier 2: Projected Vec data array → data_var[0] (matches slice_index path)
    //   Tier 3: ref_target → Datatype → fld_data[0] (non-projected Vec fallback)
    //   Tier 4: Backward MIR trace to Vec local (post-inline as_ptr, no ref_target)
    //
    // Tier 1 must precede Tier 2/3 because ptr.add results may have ref_targets
    // pointing to the Vec, but Tier 2/3 would discard the offset → always fld_data[0].
    // Tier 2 must precede Tier 3 because the projected state variable tracks push
    // updates correctly, while Datatype reconstruction may not (#4074).
    let t1 = try_volatile_load_via_ptr_add(ctx, &dcx.args[0], dcx.modified_locals);
    let t2 = if t1.is_none() {
        try_volatile_load_via_projected_vec(ctx, &dcx.args[0], dcx.modified_locals)
    } else {
        None
    };
    let resolved_val = t1.or(t2).or_else(|| match resolved {
        Some(val) if val.sort().is_datatype() => Some(val),
        _ => try_volatile_load_via_vec_trace(ctx, &dcx.args[0], dcx.modified_locals),
    });

    if let Some(val) = resolved_val {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let s = dest_var.sort().clone();
            // Extract element from Vec-like Datatype if sort mismatch exists.
            // Part of #3485: volatile_load Vec pointer element extraction.
            let val = try_extract_vec_element_for_load(val, &s);
            let eq =
                ctx.make_coerced_eq_constraint(&dest_var, val, &s, dest_local, "volatile_load");
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            if let Some(eq) = eq {
                drain_pending_checks(ctx, dcx, target);
                ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
            } else {
                drain_pending_checks(ctx, dcx, target);
                ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
            }
        } else {
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            drain_pending_checks(ctx, dcx, target);
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        }
        return;
    }

    // #3697: Mem-level load via shared raw-pointer bridge.
    if let Some((addr, pointee_ty)) = receiver_mem_target(ctx, &dcx.args[0], dcx.modified_locals) {
        if let Some(mem_val) = load_from_memory(ctx, &addr, pointee_ty).map(Val::into_expr) {
            if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
                let s = dest_var.sort().clone();
                let eq = ctx.make_coerced_eq_constraint(
                    &dest_var,
                    mem_val,
                    &s,
                    dest_local,
                    "volatile_load_mem",
                );
                let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
                if let Some(eq) = eq {
                    drain_pending_checks(ctx, dcx, target);
                    ctx.emit_goto_rule_extra(
                        dcx.from_app,
                        target,
                        &out,
                        dcx.stmt_constraints,
                        [eq],
                    );
                } else {
                    drain_pending_checks(ctx, dcx, target);
                    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
                }
            } else {
                let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
                drain_pending_checks(ctx, dcx, target);
                ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
            }
            debug!(dest_local, "CHC: volatile_load via Mem bridge (#3697)");
            return;
        }
    }

    debug!("CHC: volatile_load — pointer not resolvable, unconstrained fallback (Part of #3464)");
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    drain_pending_checks(ctx, dcx, target);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
}

/// Handle `volatile_store(ptr, val) -> ()`.
///
/// Volatile stores have no hardware side effects relevant to verification.
/// Modeled as `*ptr = val` — identical to a regular store. Uses the same
/// resolution strategy as `atomic_store` (ref_target pointer resolution +
/// operand translation for the value).
///
/// Resolution order:
/// 1. **Simple path**: pointer targets a whole local (no projections).
/// 2. **Projected path**: pointer targets a struct field via `addr_of_mut!(s.field)`.
/// 3. **Mem path**: heap-backed raw pointer via shared bridge (#3697).
/// 4. Unconstrained fallback.
///
/// Part of #3464, #3697: volatile_store CHC handler.
pub(in crate::codegen_ay::chc) fn codegen_volatile_store(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 2 {
        debug!("CHC: volatile_store with < 2 args — unconstrained fallback");
        emit_unresolved_pointer_write(
            ctx,
            dcx,
            target,
            dcx.args,
            "volatile_store_target_unresolved",
        );
        return;
    }

    // #3636: volatile_store must check obj_valid like a normal store through a raw pointer.
    // Same gap as volatile_load — writing through a freed/stale pointer is unsound.
    if let Some(ptr_local) = extract_plain_operand_local(&dcx.args[0]) {
        ctx.emit_ptr_obj_valid_check(ptr_local, dcx.modified_locals);
    }
    // P4-3: alignment + span-fits obligations for stack-backed pointers
    // (the REAL failing check for `store_fail.rs`'s packed-field store).
    push_volatile_span_checks(ctx, &dcx.args[0], dcx.modified_locals);

    // Path 0 (P4-3): projected-Vec precise write-through —
    // `volatile_store(vec.as_mut_ptr(), v)` / `volatile_store(ptr.add(k), v)`.
    // Must precede Path 1: the generic whole-local store would coerce the
    // value onto the Vec's BASE state var (fld_ptr) instead of the data array.
    if try_volatile_store_projected_vec(ctx, dcx, target) {
        return;
    }

    // Path 1: Simple whole-local target (no projections).
    if let Some(referent_local) = resolve_ptr_target_local(ctx, &dcx.args[0]) {
        let Some(new_value) =
            ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
        else {
            debug!("CHC: volatile_store — value not translatable, unconstrained fallback");
            // The target is havocked, but its typed-memory image keeps the old
            // value; nothing may be proved from either.
            ctx.record_sound_fallback_reason("volatile_store_value_untranslatable");
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
            drain_pending_checks(ctx, dcx, target);
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
            return;
        };

        debug!(referent_local, "CHC: volatile_store encoded (Part of #3464)");

        // A store of another type than the referent's (`write_volatile(&mut x
        // as *mut u32 as *mut u8, 0)`) writes some of its bytes, at the
        // pointer's offset: the same reinterpretation a plain `*p = v` through
        // a cast takes (`ref_store_reinterpretation`). Coerced onto the whole
        // referent, the byte replaced all of `x`, zero-extended
        // (third review: `ns_write_volatile_bug` a clean proof, its safe twin
        // FAILED certified Genuine, on main and the branch alike).
        let new_value = match volatile_store_reinterpretation(
            ctx,
            &dcx.args[0],
            referent_local,
            &new_value,
            dcx.modified_locals,
        ) {
            Ok(value) => value,
            Err(why) => {
                debug!(referent_local, why, "CHC: volatile_store reinterpretation not modeled");
                ctx.record_sound_fallback_reason("volatile_store_reinterpretation_unmodeled");
                let out =
                    ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
                drain_pending_checks(ctx, dcx, target);
                ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
                return;
            }
        };

        let mut extra = Vec::new();
        if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
            let s = rv.sort().clone();
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &rv,
                new_value.clone(),
                &s,
                referent_local,
                "volatile_store",
            ) {
                extra.push(eq);
            }
        }
        // The store wrote the referent's state; its typed-memory image follows.
        let mut after = dcx.modified_locals.clone();
        after.insert(referent_local);
        if !refresh_local_memory_image(ctx, referent_local, &new_value, &after, &mut extra) {
            ctx.record_sound_fallback_reason("volatile_store_memory_image_unrefreshed");
        }
        drain_pending_updates(ctx, &mut extra);

        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
        drain_pending_checks(ctx, dcx, target);
        if extra.is_empty() {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        } else {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
        }
        return;
    }

    // Path 2: Projected target (pointer to struct field).
    // Drain pending checks before the projected path emits its own rules.
    drain_pending_checks(ctx, dcx, target);
    if try_volatile_store_projected(ctx, dcx, target) {
        return;
    }

    // Path 3: Mem-level store via shared raw-pointer bridge (#3697).
    if let Some(new_value) = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
    {
        if let Some((addr, pointee_ty)) =
            receiver_mem_target(ctx, &dcx.args[0], dcx.modified_locals)
            && emit_mem_store_transition(
                ctx,
                dcx,
                target,
                new_value,
                addr.into_addr_expr(),
                pointee_ty,
            )
        {
            debug!(dest_local, "CHC: volatile_store via Mem bridge (#3697)");
            return;
        }
    }

    // Unconstrained fallback.
    debug!("CHC: volatile_store — pointer not resolvable, unconstrained fallback (Part of #3464)");
    emit_unresolved_pointer_write(
        ctx,
        dcx,
        target,
        &dcx.args[..1],
        "volatile_store_target_unresolved",
    );
}

/// The referent's new value after `volatile_store(ptr, value)` writes `value`
/// through `ptr` into the whole local `referent_local`: `value` itself when its
/// type is the referent's, otherwise the reinterpretation a plain store through
/// the cast pointer takes ([`ChcCtx::ref_store_reinterpretation`]). `Err` when
/// that is not modeled.
fn volatile_store_reinterpretation(
    ctx: &ChcCtx<'_, '_>,
    ptr: &rustc_public::mir::Operand,
    referent_local: usize,
    value: &Expr,
    modified: &std::collections::HashSet<usize>,
) -> Result<Expr, &'static str> {
    use crate::codegen_ay::chc::stmt::codegen_stmt_store::RefStoreReinterpretation;
    let Some(ptr_local) = extract_plain_operand_local(ptr) else {
        return Err("pointer operand is not a local");
    };
    let locals = ctx.body.locals();
    let written_ty = rustc_public::mir::Place {
        local: ptr_local,
        projection: vec![rustc_public::mir::ProjectionElem::Deref],
    }
    .ty(locals)
    .ok()
    .map(|ty| ctx.resolve_body_ty(ty));
    let referent_ty = locals.get(referent_local).map(|decl| ctx.resolve_body_ty(decl.ty));
    if written_ty.is_some() && written_ty == referent_ty {
        return Ok(value.clone());
    }
    let Some(ref_target) = ctx.ref_resolution.ref_targets.get(&ptr_local).cloned() else {
        return Err("store of another type without a ref target");
    };
    if ref_target.local != referent_local || !ref_target.projections.is_empty() {
        return Err("store of another type into a sub-place");
    }
    let lhs = rustc_public::mir::Place {
        local: ptr_local,
        projection: vec![rustc_public::mir::ProjectionElem::Deref],
    };
    match ctx.ref_store_reinterpretation(&ref_target, &lhs, value, ptr_local, modified) {
        RefStoreReinterpretation::SameType => Ok(value.clone()),
        RefStoreReinterpretation::Converted(converted)
        | RefStoreReinterpretation::ConvertedLocal(converted) => Ok(converted),
        RefStoreReinterpretation::OutOfBounds => Err("a wider store past its object"),
        RefStoreReinterpretation::Unmodeled(why) => Err(why),
    }
}

/// P4-3: precise volatile_store write-through to a projected Vec's data array.
///
/// Handles the symmetric shapes of the volatile_load Tier-1/Tier-2 cascade:
/// - `volatile_store(vec.as_mut_ptr(), v)`        → `data' = store(data, 0, v)`
/// - `volatile_store(vec.as_mut_ptr().add(k), v)` → `data' = store(data, k, v)`
/// including the post-inline `BinOp::Offset` form of `ptr.add` (backward
/// MIR trace when no ref_target exists).
///
/// `fld_data` uses LOGICAL element indices, so the ptr.add count IS the
/// store index. Returns `false` when the pointer does not resolve to a
/// projected Vec (caller continues its cascade). When the target resolves
/// but the value/index cannot be encoded, the data array is left
/// unconstrained (sound over-approximation, marked) instead of falling into
/// the whole-local path, which would corrupt the Vec base state var.
fn try_volatile_store_projected_vec(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) -> bool {
    let dest_local: usize = dcx.destination.local;
    let Some(arg_local) = extract_plain_operand_local(&dcx.args[0]) else {
        return false;
    };

    // Direct data-start pointer → index 0; ptr.add(k) → index k.
    let (slot, index_operand) =
        match projected_vec_data_slot_for_ptr(ctx, arg_local, dcx.modified_locals) {
            Some(slot) => (slot, None),
            None => {
                let Some((base_local, count_op)) = find_ptr_add_base_and_count(ctx, arg_local)
                else {
                    return false;
                };
                let Some(slot) =
                    projected_vec_data_slot_for_ptr(ctx, base_local, dcx.modified_locals)
                else {
                    return false;
                };
                (slot, Some(count_op))
            }
        };

    let idx_expr = match &index_operand {
        None => Some(Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH)),
        Some(op) => ctx
            .translate_operand_with_modified(op, dcx.modified_locals)
            .and_then(|e| ctx.coerce_to_pointer_width(e)),
    };
    let new_value = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);

    // Circularity guard: if the Vec local was already modified in this
    // block, `slot.data_expr` is the OUTPUT var and `data_out =
    // store(data_out, ...)` would be infeasible — take the marked-havoc
    // branch instead.
    let already_modified = dcx.modified_locals.contains(&slot.coll_local);
    let store_eq = match (idx_expr, new_value) {
        (Some(idx), Some(val)) if !already_modified => {
            let val =
                ChcCtx::coerce_store_value(slot.data_expr.sort(), val, false, &ctx.diagnostics);
            ctx.state_var_mgr.output_state_vars.get(slot.data_idx).cloned().map(
                |(out_name, out_sort)| {
                    Expr::var(&*out_name, out_sort).eq(slot.data_expr.clone().store(idx, val))
                },
            )
        }
        _ => None,
    };
    if store_eq.is_none() {
        // Resolved a projected-Vec target but could not encode the store:
        // havoc ONLY the data array (sound over-approximation, marked).
        ctx.record_sound_fallback_reason("volatile_store_vec_data_unencoded");
    }
    ctx.mark_state_var_modified(slot.data_idx);

    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    drain_pending_checks(ctx, dcx, target);
    if let Some(eq) = store_eq {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
    } else {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    }
    debug!(
        arg_local,
        data_idx = slot.data_idx,
        "CHC: volatile_store projected-Vec write-through encoded (P4-3)"
    );
    true
}

/// Try to handle volatile_store where the pointer targets a struct field.
///
/// When `addr_of_mut!(struct_local.field)` is used, `ref_targets` maps the
/// pointer to `RefTarget { local, projections: [Field(idx, ty)] }`. For
/// flattened locals, computes the leaf slot and constrains that specific field
/// while preserving all other fields of the parent struct.
///
/// Returns true if the projected path was handled (constraints emitted).
///
/// Part of #3464: volatile_store projected field support.
fn try_volatile_store_projected(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) -> bool {

    let dest_local: usize = dcx.destination.local;

    // Extract the pointer operand's ref_target (including projections).
    let place = match &dcx.args[0] {
        Operand::Copy(place) | Operand::Move(place) => place,
        _ => return false,
    };
    if !place.projection.is_empty() {
        return false;
    }
    let ptr_local: usize = place.local;
    let ref_target = match ctx.ref_resolution.ref_targets.get(&ptr_local) {
        Some(rt) => rt,
        None => return false,
    };
    if ref_target.projections.is_empty() {
        return false; // No projection — should have been handled by simple path.
    }

    let parent_local = ref_target.local;

    // The projection chain as a typed Field path; any other projection
    // (a Deref, an Index) is not a path into the parent's flattened slots,
    // and skipping it walked the remaining indices from the wrong level.
    let Some(field_path) = ref_target
        .projections
        .iter()
        .map(|p| match p {
            ProjectionElem::Field(idx, ty) => Some(crate::codegen_ay::chc::FieldProjection {
                field_idx: *idx,
                cons_idx: None,
                field_ty: Some(*ty),
            }),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if field_path.is_empty() {
        return false;
    }

    // Translate the value to store.
    let Some(new_value) = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
    else {
        return false;
    };

    // Only handle flattened locals for now.
    if !ctx.flatten.flattened_tuple_locals.contains(&parent_local) {
        debug!(
            parent_local,
            "CHC: volatile_store projected — parent not flattened, unconstrained fallback"
        );
        return false;
    }

    // The flat slot for the target field, through the checked walk (C5b).
    let flat_slot = match ctx.flat_slot_for(parent_local, &field_path) {
        Ok(slot) => slot,
        Err(why) => {
            debug!(
                parent_local,
                why, "CHC: volatile_store projected — flat slot computation failed"
            );
            return false;
        }
    };

    let field_count = ctx.flattened_field_count(parent_local);
    let Some(base_idx) = ctx.try_state_idx_for_local(parent_local) else {
        return false;
    };

    // Build constraints: target field = new_value, other fields = input values.
    let mut extra = Vec::new();
    for fld in 0..field_count {
        let slot = base_idx + fld;
        let Some((out_name, out_sort)) = ctx.state_var_mgr.output_state_vars.get(slot).cloned()
        else {
            return false;
        };
        let out_var = Expr::var(&*out_name, out_sort.clone());

        if fld == flat_slot {
            // Target field: constrain to new_value.
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &out_var,
                new_value.clone(),
                &out_sort,
                parent_local,
                "volatile_store_field",
            ) {
                extra.push(eq);
            }
        } else {
            // Other fields: preserve input values.
            if let Some((in_name, in_sort)) = ctx.state_var_mgr.state_vars.get(slot).cloned() {
                let in_var = Expr::var(&*in_name, in_sort);
                extra.push(out_var.eq(in_var));
            }
        }
    }

    debug!(
        parent_local,
        flat_slot, field_count, "CHC: volatile_store projected field encoded (Part of #3464)"
    );

    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, parent_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
    true
}

/// Handle `std::mem::replace(&mut T, T) -> T`: read old, write new, return old.
/// Mirrors `codegen_typed_swap` with `build_local_update_constraints`. Part of #4092.
pub(in crate::codegen_ay::chc) fn codegen_mem_replace(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 2 {
        emit_unresolved_pointer_write(ctx, dcx, target, dcx.args, "mem_replace_target_unresolved");
        return;
    }
    let Some(referent_local) = resolve_ptr_target_local(ctx, &dcx.args[0]) else {
        debug!("CHC: mem::replace — target not resolvable, fail-closed fallback (#4092)");
        emit_unresolved_pointer_write(
            ctx,
            dcx,
            target,
            &dcx.args[..1],
            "mem_replace_target_unresolved",
        );
        return;
    };
    let old_val = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let new_val = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);
    let (Some(old_val), Some(new_val)) = (old_val, new_val) else {
        debug!("CHC: mem::replace — values not resolvable, unconstrained fallback (#4092)");
        ctx.record_sound_fallback_reason("mem_replace_value_unresolved");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };
    debug!(referent_local, dest_local, "CHC: mem::replace encoded (#4092)");
    let mut extra = Vec::new();
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(referent_local, new_val.clone(), "mem_replace_store")
    {
        extra.append(&mut eqs);
    }
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(dest_local, old_val, "mem_replace_return")
    {
        extra.append(&mut eqs);
    }
    // The replace wrote the referent's state; its typed-memory image follows.
    let mut after = dcx.modified_locals.clone();
    after.insert(referent_local);
    if !refresh_local_memory_image(ctx, referent_local, &new_val, &after, &mut extra) {
        ctx.record_sound_fallback_reason("mem_replace_memory_image_unrefreshed");
    }
    drain_pending_updates(ctx, &mut extra);
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

/// Handle `typed_swap_nonoverlapping(x: *mut T, y: *mut T) -> ()`.
///
/// Modeled as simultaneous swap: `*x = old_*y` and `*y = old_*x`.
/// Reads both current values via `resolve_ref_or_const_referent`, then
/// cross-constrains the output state variables. Falls back to unconstrained
/// (both targets left unconstrained) if either pointer cannot be resolved.
///
/// Part of #3464: typed_swap_nonoverlapping CHC handler.
pub(in crate::codegen_ay::chc) fn codegen_typed_swap(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 2 {
        debug!("CHC: typed_swap with < 2 args — fail-closed fallback");
        emit_unresolved_pointer_write(ctx, dcx, target, dcx.args, "typed_swap_target_unresolved");
        return;
    }

    // Resolve both pointer target locals.
    let x_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    let y_local = resolve_ptr_target_local(ctx, &dcx.args[1]);

    let (Some(x_local), Some(y_local)) = (x_local, y_local) else {
        debug!("CHC: typed_swap — pointer(s) not resolvable, fail-closed fallback (Part of #3464)");
        emit_unresolved_pointer_write(
            ctx,
            dcx,
            target,
            &dcx.args[..2],
            "typed_swap_target_unresolved",
        );
        return;
    };

    // The resolved target must BE the thing the pointer points at. `&mut h.a`
    // with `h.a: *mut u8` resolved all the way through to `*h.a`'s referent
    // (`x: u8`), so `mem::swap(&mut h.a, &mut h.b)` exchanged the VALUES of `x`
    // and `y` instead of the two pointers: `*h.a = 9` afterwards still wrote
    // `x`, and both `assert!(y == 2)` and its safe twin `assert!(x == 1 && y ==
    // 9)` came back FAILED [AY:CTREX_CAT:Genuine] — a false certificate on the
    // safe one (fourth adversarial review of m3/soundness-fixes-2, 2026-09-14,
    // defect M2/D3, the struct-field half). A type mismatch between the
    // argument's POINTEE type and the resolved local's type is exactly that
    // collapse, and it is not something this handler can encode.
    let target_ty_matches = |arg: &rustc_public::mir::Operand, local: usize| {
        let Some(pointee) = arg.ty(ctx.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                Some(pointee)
            }
            _ => None,
        }) else {
            return true;
        };
        ctx.body.locals().get(local).is_none_or(|decl| decl.ty == pointee)
    };
    if !target_ty_matches(&dcx.args[0], x_local) || !target_ty_matches(&dcx.args[1], y_local) {
        debug!(
            x_local,
            y_local,
            "CHC: typed_swap — the resolved target is not the pointee, fail-closed fallback"
        );
        emit_unresolved_pointer_write(
            ctx,
            dcx,
            target,
            &dcx.args[..2],
            "typed_swap_target_type_mismatch",
        );
        return;
    }

    // Read current (input-state) values of both referents.
    let x_val = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let y_val = ctx.resolve_ref_or_const_referent(&dcx.args[1], dcx.modified_locals);

    let (Some(x_val), Some(y_val)) = (x_val, y_val) else {
        debug!("CHC: typed_swap — values not resolvable, unconstrained fallback (Part of #3464)");
        ctx.record_sound_fallback_reason("typed_swap_value_unresolved");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, x_local, y_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    debug!(x_local, y_local, "CHC: typed_swap encoded (Part of #3464)");

    // Cross-constrain: output *x = old *y, output *y = old *x.
    // Use the shared local-update helper so flattened aggregate referents
    // decompose into all destination slots instead of constraining only slot 0.
    let mut extra = Vec::new();
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(x_local, y_val.clone(), "typed_swap_x")
    {
        extra.append(&mut eqs);
    }
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(y_local, x_val.clone(), "typed_swap_y")
    {
        extra.append(&mut eqs);
    }
    // A collection's length, capacity and key presence live in side state
    // keyed by its local, not in the value the update above exchanged.
    if !swap_collection_side_state(ctx, x_local, y_local, &mut extra) {
        ctx.record_sound_fallback_reason("typed_swap_collection_side_state_unmodelled");
    }
    // The swap wrote both locals' state; their typed-memory images follow.
    let mut after = dcx.modified_locals.clone();
    after.insert(x_local);
    after.insert(y_local);
    let x_image = refresh_local_memory_image(ctx, x_local, &y_val, &after, &mut extra);
    let y_image = refresh_local_memory_image(ctx, y_local, &x_val, &after, &mut extra);
    if !(x_image && y_image) {
        ctx.record_sound_fallback_reason("typed_swap_memory_image_unrefreshed");
    }
    drain_pending_updates(ctx, &mut extra);

    swap_pointee_bindings(ctx, x_local, y_local);

    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, x_local, y_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

/// Exchange the collection side state of the two locals `mem::swap` (or
/// `typed_swap_nonoverlapping`) exchanged: `x`'s length, capacity and key
/// presence become `y`'s and the reverse. The value exchange above swaps the
/// locals' datatypes only, while `Vec::len`, `capacity` and a map's
/// membership read the side state keyed by the local, so `mem::swap(&mut v,
/// &mut w); assert!(v.len() == 0)` with `w = vec![1, 2]` verified clean where
/// Kani fails, and the true `v.len() == 2` was certified a Genuine failure
/// (walker fail-closed repair round 4, finding 7's class,
/// `r3_vec_through_ref.rs` `d3_mem_swap_len_bug`; capacity, `String` and
/// `BTreeSet` alike). `false` when one side carries a kind of side state the
/// other lacks, or a kind cannot be written: the caller fails closed.
fn swap_collection_side_state(
    ctx: &mut ChcCtx<'_, '_>,
    x_local: usize,
    y_local: usize,
    extra: &mut Vec<Expr>,
) -> bool {
    use super::super::call_accumulator::CallAccumulator;
    if x_local == y_local {
        return true;
    }
    let state = &ctx.collections.len_state;
    let lens = (state.get_len_var(x_local).cloned(), state.get_len_var(y_local).cloned());
    let caps = (state.get_cap_var(x_local).cloned(), state.get_cap_var(y_local).cloned());
    let presents =
        (state.get_present_var(x_local).cloned(), state.get_present_var(y_local).cloned());
    let mut dests = Vec::new();
    let mut ok = true;
    match lens {
        (None, None) => {}
        (Some(x), Some(y)) if x == y => {}
        (Some(x), Some(y)) => {
            let (x_now, y_now) = (ctx.collection_current_len(&x), ctx.collection_current_len(&y));
            let mut acc = CallAccumulator::new(extra, &mut dests);
            ok &= ctx.collection_len_set(&x, y_now, &mut acc);
            ok &= ctx.collection_len_set(&y, x_now, &mut acc);
        }
        _ => ok = false,
    }
    match caps {
        (None, None) => {}
        (Some(x), Some(y)) if x == y => {}
        (Some(x), Some(y)) => {
            let (x_now, y_now) = (ctx.collection_current_cap(&x), ctx.collection_current_cap(&y));
            let mut acc = CallAccumulator::new(extra, &mut dests);
            ok &= ctx.collection_cap_set(&x, y_now, &mut acc);
            ok &= ctx.collection_cap_set(&y, x_now, &mut acc);
        }
        _ => ok = false,
    }
    match presents {
        (None, None) => {}
        (Some(x), Some(y)) if x == y => {}
        (Some(x), Some(y)) => {
            let sort_of = |ctx: &ChcCtx<'_, '_>, name: &str| {
                ctx.state_var_index_by_name(name)
                    .and_then(|idx| ctx.state_var_mgr.state_vars.get(idx))
                    .map(|(_, sort)| sort.clone())
            };
            match (sort_of(ctx, &x), sort_of(ctx, &y)) {
                (Some(x_sort), Some(y_sort)) if x_sort == y_sort => {
                    let x_now = Expr::var(&*x, x_sort);
                    let y_now = Expr::var(&*y, y_sort);
                    let mut acc = CallAccumulator::new(extra, &mut dests);
                    ok &= ctx.collection_present_set(&x, y_now, &mut acc);
                    ok &= ctx.collection_present_set(&y, x_now, &mut acc);
                }
                _ => ok = false,
            }
        }
        _ => ok = false,
    }
    ok
}

/// The two swapped storages may themselves hold POINTERS
/// (`mem::swap(&mut p, &mut q)` with `p, q: &mut u8`). Their VALUES were
/// exchanged above, so the referent each one names was exchanged too, and the
/// `ref_targets` bindings have to travel with them — otherwise a later `*p = 7`
/// resolves through `p`'s OLD binding and writes the wrong object:
/// `swap_refs_store_must_fail` (`assert!(a == 7)` after the swap made `p` point
/// at `b`) verified SUCCESSFUL and its safe twin certified a Genuine
/// counterexample (negative/merged_pointer_shapes.rs, main 31793ccc3).
///
/// Exchanged when both sides have a binding and nothing else about them is
/// resolved; otherwise every binding under both names is dropped AND the
/// statement records a fail-closed reason, because a kept binding would name
/// the pre-swap referent.
fn swap_pointee_bindings(ctx: &mut ChcCtx<'_, '_>, x_local: usize, y_local: usize) {
    // `Box`, `Rc`, `Arc`, `NonNull` and `Unique` are pointers too: swapping two
    // `Box` locals exchanges which allocation each names, and a later `*b1 = 9`
    // through the OLD binding wrote the wrong one — `swap_boxes_store_safe` was
    // FAILED [AY:CTREX_CAT:Genuine] (adversarial review, 2026-09-14).
    let is_ptr = |local: usize| {
        ctx.body.locals().get(local).is_some_and(|d| match d.ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.name();
                let trimmed = def.trimmed_name();
                matches!(
                    name.as_str(),
                    "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "std::rc::Rc"
                        | "alloc::rc::Rc"
                        | "std::sync::Arc"
                        | "alloc::sync::Arc"
                ) || trimmed == "NonNull"
                    || trimmed == "Unique"
                    || trimmed == "Box"
            }
            _ => false,
        })
    };
    if x_local == y_local {
        return;
    }
    if !is_ptr(x_local) || !is_ptr(y_local) {
        // The swapped value need not BE a pointer: an `Option<*mut u8>`, a
        // `Result`, a tuple, an array or a struct CARRIES one, and the swap
        // moves it just the same. `ref_targets` is keyed by LOCAL, so there is
        // no per-slot binding to exchange for a carrier — and answering `false`
        // here exchanged nothing and recorded nothing:
        // `let mut a: Option<*mut u8> = Some(&mut x); let mut b = Some(&mut y);
        // mem::swap(&mut a, &mut b); *a.unwrap() = 9; assert!(y == 2)` verified
        // SUCCESSFUL with `[AY:PROOF_QUALIFIERS:clean]` and its safe twin was
        // FAILED [AY:CTREX_CAT:Genuine] (fourth adversarial review of
        // m3/soundness-fixes-2, 2026-09-14, defect M2/D3). Fail closed.
        let carries = |local: usize| {
            ctx.body
                .locals()
                .get(local)
                .is_some_and(|d| ChcCtx::ty_carries_a_pointer_value(d.ty))
        };
        if carries(x_local) || carries(y_local) {
            ctx.ref_resolution.clear_path_insensitive_ref_metadata(x_local);
            ctx.ref_resolution.clear_path_insensitive_ref_metadata(y_local);
            debug!(
                x_local,
                y_local,
                "CHC: typed_swap of values CARRYING pointers — fail closed"
            );
            ctx.record_sound_fallback_reason("typed_swap_carried_pointer_not_exchanged");
        }
        return;
    }
    // A pointer's identity is not only `ref_targets`. A slice reference also
    // carries a sub-slice offset and a length, an argument reference a pointee
    // slot, a static reference a state index, a collection reference an index —
    // and NONE of those travel with an exchanged value. `let mut s = &a[..];
    // let mut t = &b[..]; mem::swap(&mut s, &mut t); assert!(s[0] == 1)`
    // verified SUCCESSFUL in CHC with both views starting at index 0, so no
    // offset was even involved (adversarial review of m3/soundness-fixes-2,
    // 2026-09-14). Exchange what can be exchanged exactly; anything else fails
    // closed with both sides' metadata dropped.
    let other_meta = |ctx: &ChcCtx<'_, '_>, local: usize| {
        ctx.ref_resolution.subslice_offset.contains_key(&local)
            || ctx.ref_resolution.subslice_len.contains_key(&local)
            || ctx.ref_resolution.ref_arg_pointee_idx.contains_key(&local)
            || ctx.ref_resolution.static_ref_to_state_idx.contains_key(&local)
            || ctx.ref_resolution.collection_mut_refs.contains_key(&local)
            || ctx.ref_resolution.collection_index_refs.contains_key(&local)
            || ctx.ref_resolution.const_ref_slice_views.contains_key(&local)
    };
    let wide = |ctx: &ChcCtx<'_, '_>, local: usize| {
        ctx.body.locals().get(local).is_some_and(|d| match d.ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                matches!(
                    pointee.kind(),
                    TyKind::RigidTy(
                        RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..)
                    )
                )
            }
            _ => false,
        })
    };
    let inexact = other_meta(ctx, x_local)
        || other_meta(ctx, y_local)
        || wide(ctx, x_local)
        || wide(ctx, y_local);
    if inexact {
        ctx.ref_resolution.clear_path_insensitive_ref_metadata(x_local);
        ctx.ref_resolution.clear_path_insensitive_ref_metadata(y_local);
        debug!(
            x_local,
            y_local,
            "CHC: typed_swap of pointers carrying view metadata — fail closed"
        );
        ctx.record_sound_fallback_reason("typed_swap_pointer_view_not_exchanged");
        return;
    }
    let xt = ctx.ref_resolution.ref_targets.get(&x_local).cloned();
    let yt = ctx.ref_resolution.ref_targets.get(&y_local).cloned();
    match (xt, yt) {
        (Some(xt), Some(yt)) => {
            ctx.ref_resolution.ref_targets.insert(x_local, yt);
            ctx.ref_resolution.ref_targets.insert(y_local, xt);
            debug!(x_local, y_local, "CHC: typed_swap exchanged the pointee bindings");
        }
        (None, None) => {}
        _ => {
            ctx.ref_resolution.clear_path_insensitive_ref_metadata(x_local);
            ctx.ref_resolution.clear_path_insensitive_ref_metadata(y_local);
            debug!(
                x_local,
                y_local,
                "CHC: typed_swap of pointers with a one-sided binding — fail closed"
            );
            ctx.record_sound_fallback_reason("typed_swap_pointee_bindings_not_exchanged");
        }
    }
}


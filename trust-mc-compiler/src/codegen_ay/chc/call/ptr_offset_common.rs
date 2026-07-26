// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared CHC lowering for pointer-distance operations.
//!
//! Routes both Kani model hooks and std/core method-form `offset_from` /
//! `offset_from_unsigned` through the same `(lhs - rhs) / size_of::<T>()`
//! arithmetic so CHC does not drift between the two call paths.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, chc_debug_enabled};
use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

pub(in crate::codegen_ay::chc) fn codegen_ptr_offset_from_call(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    unsigned: bool,
    constraint_label: &'static str,
) {
    let dest_local = dcx.destination.local;
    let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    let eq = match dcx.args {
        [lhs_op, rhs_op, ..] => build_ptr_offset_constraint(
            ctx,
            dcx,
            lhs_op,
            rhs_op,
            dest_local,
            unsigned,
            constraint_label,
        ),
        _ => {
            if chc_debug_enabled() {
                debug!(
                    call = constraint_label,
                    args = dcx.args.len(),
                    "pointer offset fallback to nondet (expected >= 2 args)"
                );
            }
            ctx.record_sound_fallback_reason("ptr_offset_from_arg_count");
            None
        }
    };

    ctx.emit_goto_rule_extra(dcx.from_app, target, &new_output_args, dcx.stmt_constraints, eq);
}

fn build_ptr_offset_constraint(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    lhs_op: &Operand,
    rhs_op: &Operand,
    dest_local: usize,
    unsigned: bool,
    constraint_label: &'static str,
) -> Option<Expr> {
    let modified_locals = dcx.modified_locals;
    let lhs = ctx.translate_operand_with_modified(lhs_op, modified_locals);
    let rhs = ctx.translate_operand_with_modified(rhs_op, modified_locals);

    let (lhs, rhs) = match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => (lhs, rhs),
        _ => {
            if chc_debug_enabled() {
                debug!(
                    call = constraint_label,
                    "pointer offset fallback to nondet (arg translation failed)"
                );
            }
            ctx.record_sound_fallback_reason("ptr_offset_arg_translation_failed");
            return None;
        }
    };

    let lhs = if lhs.sort().is_int() { lhs.int2bv(POINTER_WIDTH) } else { lhs };
    let rhs = if rhs.sort().is_int() { rhs.int2bv(POINTER_WIDTH) } else { rhs };

    if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
        debug!(
            call = constraint_label,
            lhs_sort = ?lhs.sort(),
            rhs_sort = ?rhs.sort(),
            "pointer offset fallback to nondet (non-bitvec operand sort)"
        );
        ctx.record_sound_fallback_reason("ptr_offset_non_bitvec_sort");
        return None;
    }

    let Some(pointee_size) = extract_pointee_size(ctx, lhs_op) else {
        warn!(
            call = constraint_label,
            "pointer offset pointee size unknown — sound over-approximation"
        );
        ctx.record_sound_fallback_reason("ptr_offset_pointee_size_unknown");
        return None;
    };

    let (_, dest_var) = if let Some(dest) = ctx.resolve_destination(dest_local) {
        dest
    } else {
        ctx.record_sound_fallback_reason("ptr_offset_dest_unresolvable");
        return None;
    };

    let lhs_ptr = coerce_bitvec_width_safe(lhs, POINTER_WIDTH, SignExtension::ZeroExtend);
    let rhs_ptr = coerce_bitvec_width_safe(rhs, POINTER_WIDTH, SignExtension::ZeroExtend);

    // Emit `offset_from` / `offset_from_unsigned` UB safety checks. The Kani
    // library model (`ptr_offset_from`) carries these, but the CHC path
    // intercepts the model and previously dropped them, yielding false PROOFs.
    //
    // The checks are pure bit-vector predicates over the split-pointer
    // representation `obj_id(hi 32) ++ offset(lo 32)`, so they never introduce
    // false positives for genuinely same-allocation in-bounds pointers (whose
    // object id is preserved by pointer arithmetic) and are accepted by the
    // CHC backend.
    let mut assume_cond: Option<Expr> = None;
    if POINTER_WIDTH == 64 && !ctx.int_lift {
        // Same-allocation: both pointers must share an object id. Distinct
        // allocations get distinct ids, so this is UB when they differ.
        let mut same_alloc = lhs_ptr.clone().extract(63, 32).eq(rhs_ptr.clone().extract(63, 32));
        // Part of #72: the kani_core model (models.rs `ptr_offset_from`)
        // demands same object AND the range between the pointers in bounds
        // of that object. The obj-id lane equality alone false-proved
        // wrapped pointers (offset-wraps-around `original_harness`): the
        // wrapping-add stub propagates the id lane while the offset lane
        // leaves the allocation. Conjoin a per-operand
        // `offset_lane <= alloc_size` bound (one-past-end inclusive, per
        // the mem-predicate docs) whenever the operand's stack provenance
        // resolves through the fail-closed single-assignment walk. When
        // provenance does not resolve, the id-lane equality remains the
        // (weaker but sound-in-that-lane) check — no new fail-open is
        // introduced relative to the pre-#72 state.
        for (op, ptr) in [(lhs_op, &lhs_ptr), (rhs_op, &rhs_ptr)] {
            if let Some(in_bounds) = stack_offset_lane_in_bounds(ctx, op, ptr) {
                same_alloc = same_alloc.and(in_bounds);
            }
        }
        // models.rs:90-91 — equal pointers short-circuit to distance 0 with
        // no same-allocation requirement (never UB, even out of bounds).
        let same_alloc_ok = lhs_ptr.clone().eq(rhs_ptr.clone()).or(same_alloc);
        // Part of #72: exact kani_core model message (models.rs) so the
        // expected-output comparison matches Kani verbatim.
        ctx.emit_error_rule_for_condition_with_kind(
            dcx.from_app,
            same_alloc_ok.clone(),
            dcx.stmt_constraints,
            dcx.bb_idx,
            trust_mc_core::violation::PropertyKind::Assertion,
            Some(
                "Offset result and original pointer should point to the same allocation"
                    .to_string(),
            ),
        );
        let mut assumed = same_alloc_ok;
        // `offset_from_unsigned` additionally requires a non-negative distance
        // (`self >= origin`); a smaller `self` is UB.
        if unsigned {
            let non_negative = lhs_ptr.clone().bvuge(rhs_ptr.clone());
            ctx.emit_error_rule_for_condition_with_kind(
                dcx.from_app,
                non_negative.clone(),
                dcx.stmt_constraints,
                dcx.bb_idx,
                trust_mc_core::violation::PropertyKind::Assertion,
                Some("Expected non-negative distance between pointers".to_string()),
            );
            assumed = assumed.and(non_negative);
        }
        // Part of #72: `kani::safety_check` is assert+assume — the model
        // halts the path once the check fails, so downstream properties are
        // evaluated only on check-passing paths (Kani-parity vacuous
        // successes, never a masked bug: the check itself already FAILS on
        // the pruned paths).
        assume_cond = Some(assumed);
        debug!(call = constraint_label, "CHC: emitted offset_from same-allocation safety check");
    }

    let diff_bytes = lhs_ptr.bvsub(rhs_ptr);
    let elem_size = Expr::bitvec_const(pointee_size.max(1) as u128, POINTER_WIDTH);
    let offset = if unsigned { diff_bytes.bvudiv(elem_size) } else { diff_bytes.bvsdiv(elem_size) };

    let out_sort = dest_var.sort();
    let eq =
        ctx.make_coerced_eq_constraint(&dest_var, offset, &out_sort, dest_local, constraint_label);
    match (eq, assume_cond) {
        (Some(eq), Some(cond)) => Some(eq.and(cond)),
        (Some(eq), None) => Some(eq),
        (None, cond) => cond,
    }
}

/// Part of #72: the IN-BOUNDS half of the `offset_from` same-allocation UB
/// check — `offset_lane(ptr) <= alloc_size` (one-past-end allowed), emitted
/// only when the operand's base allocation resolves through the fail-closed
/// single-assignment provenance walk (`provenance_alloc_size_for_local`:
/// stack owner or promoted-const ref), so the bound is always the exact
/// object extent. Returns `None` (caller keeps the id-lane-only check) for
/// unresolvable or projected operands.
fn stack_offset_lane_in_bounds(ctx: &mut ChcCtx<'_, '_>, op: &Operand, ptr: &Expr) -> Option<Expr> {
    let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
    if !place.projection.is_empty() {
        return None;
    }
    let alloc_size = ctx.provenance_alloc_size_for_local(place.local)?;
    let (_, offset_lane) = ctx.split_pointer(ptr)?;
    Some(offset_lane.bvule(Expr::bitvec_const(alloc_size as u128, 32)))
}

fn extract_pointee_size(ctx: &ChcCtx<'_, '_>, operand: &Operand) -> Option<usize> {
    let ty = operand.ty(ctx.body.locals()).ok()?;
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ctx.get_type_size(pointee),
        TyKind::RigidTy(RigidTy::Adt(def, args)) if is_pointer_wrapper_adt(&def.trimmed_name()) => {
            args.0.iter().find_map(|arg| match arg {
                GenericArgKind::Type(pointee) => ctx.get_type_size(*pointee),
                _ => None,
            })
        }
        _ => None,
    }
}

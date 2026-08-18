// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Atomic compare-exchange and read-modify-write (RMW) handlers for CHC codegen.
//!
//! Split from `codegen_call_atomic.rs` for file-size compliance.
//! Handles `atomic_cxchg`, `atomic_xchg`, `fetch_add/sub/and/or/xor/nand`,
//! and `fetch_max/min/umax/umin`.
//!
//! Part of #3435: CHC Atomic intrinsic handlers.
//! Part of #3452: Atomic/Stable dispatch gap.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;
use trust_mc_codegen_types::types::unwrap_single_field_datatype;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_atomic::AtomicKind;
use super::codegen_call_atomic_mem::{
    atomic_load_from_memory, atomic_receiver_mem_target, emit_rmw_constraints_mem,
};
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_misc::CallMisc;
use super::codegen_call_result_mem::build_call_result_memory_bridge_constraints;
use super::codegen_rules::CodegenRules;
use super::ptr_receiver_mem::{mark_atomic_ptr_forwarded, resolve_ptr_target_local};
use crate::codegen_ay::provenance::Val;

/// Coerce Bool↔BV operands to same sort for atomic ops. AtomicBool stores as
/// BV8 but args may be Bool; BV ops require matching sorts. Part of #3452.
pub(in crate::codegen_ay::chc) fn coerce_atomic_bool_sorts(a: Expr, b: Expr) -> (Expr, Expr) {
    if a.sort() == b.sort() {
        return (a, b);
    }
    if a.sort().is_bitvec() && b.sort().is_bool() {
        let width = a.sort().bitvec_width().expect("invariant: checked is_bitvec");
        let coerced =
            Expr::ite(b, Expr::bitvec_const(1u64, width), Expr::bitvec_const(0u64, width));
        (a, coerced)
    } else if a.sort().is_bool() && b.sort().is_bitvec() {
        let width = b.sort().bitvec_width().expect("invariant: checked is_bitvec");
        let coerced =
            Expr::ite(a, Expr::bitvec_const(1u64, width), Expr::bitvec_const(0u64, width));
        (coerced, b)
    } else {
        (a, b)
    }
}

// ---------------------------------------------------------------------------
// Compare-exchange handlers
// ---------------------------------------------------------------------------

/// Stable `compare_exchange` → `Result<T, T>` flattened as 2–3 fields.
/// Slot 0 = is_ok, Slot 1 = ok_payload (old_value), Slot 2 = err_payload.
/// Part of #3452, #3490.
pub(in crate::codegen_ay::chc) fn codegen_atomic_compare_exchange(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    // args: &self, current, new, success_ordering, failure_ordering
    if dcx.args.len() < 3 {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    let old_value = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let referent_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    // Part of #3761: register raw pointer as call-forwarded for consistent deref.
    if referent_local.is_some() {
        mark_atomic_ptr_forwarded(ctx, &dcx.args[0]);
    }
    // Part of #3492: args[1]/[2] are VALUES (not refs). translate_operand gives
    // the direct value for all atomic types (bool, integers, pointers).
    let expected = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);
    let new_value = ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals);

    let (Some(old_value), Some(referent_local), Some(expected), Some(new_value)) =
        (old_value, referent_local, expected, new_value)
    else {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    // Unwrap repr(transparent) datatype wrappers (Part of #3452).
    let old_value = unwrap_single_field_datatype(&old_value).unwrap_or(old_value);
    let expected = unwrap_single_field_datatype(&expected).unwrap_or(expected);
    let new_value = unwrap_single_field_datatype(&new_value).unwrap_or(new_value);

    // Coerce Bool↔BV for AtomicBool compare_exchange (Part of #3452).
    let (old_value, expected) = coerce_atomic_bool_sorts(old_value, expected);
    let (old_value, new_value) = coerce_atomic_bool_sorts(old_value, new_value);

    // Sort guard: fall back if coercion didn't unify sorts.
    if old_value.sort() != expected.sort() {
        debug!(
            "CHC compare_exchange: sort mismatch old={:?} expected={:?}, sound fallback",
            old_value.sort(),
            expected.sort()
        );
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }
    let success = old_value.clone().eq(expected);
    // Conditional store: *self = ite(success, new, old)
    let cond_new = Expr::ite(success.clone(), new_value, old_value.clone());
    let mut extra = Vec::new();
    // Part of #3490: constrain all Result fields for correct ITE reconstruction.
    let dest_vec_idx = ctx.try_state_idx_for_local(dest_local);
    if dest_vec_idx.is_none() {
        ctx.record_sound_fallback_reason("state_idx_missing_compare_exchange_dest");
    }
    let n_fields = ctx.flattened_field_count(dest_local);
    if let Some(dest_vec_idx) = dest_vec_idx
        && ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        && n_fields >= 2
    {
        assert!(
            dest_vec_idx + 1 < ctx.state_var_mgr.output_state_vars.len(),
            "compare_exchange: contiguous slot invariant violated for local {dest_local}"
        );
        // Part of #3962: preserve success expr for flattened_field_env update below.
        let success_for_env = success.clone();
        // Slot 0: is_ok (Bool discriminant — true = Ok/success).
        if let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
        {
            let is_ok_var = Expr::var(&*out_name, out_sort.clone());
            if out_sort.is_bool() {
                extra.push(is_ok_var.eq(success));
            } else if let Some(w) = out_sort.bitvec_width() {
                let coerced =
                    Expr::ite(success, Expr::bitvec_const(1, w), Expr::bitvec_const(0, w));
                extra.push(is_ok_var.eq(coerced));
            }
        }
        // Slot 1: ok_payload (always old_value — the previous value on success).
        if let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx + 1).cloned()
        {
            let payload_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &payload_var,
                old_value.clone(),
                &out_sort,
                dest_local,
                "compare_exchange_ok_payload",
            ) {
                extra.push(eq);
            }
        }
        // Slot 2: err_payload (Part of #3490: 3-field Result<T, T>).
        if n_fields >= 3 {
            if let Some((out_name, out_sort)) =
                ctx.state_var_mgr.output_state_vars.get(dest_vec_idx + 2).cloned()
            {
                let err_payload_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(eq) = ctx.make_coerced_eq_constraint(
                    &err_payload_var,
                    old_value.clone(),
                    &out_sort,
                    dest_local,
                    "compare_exchange_err_payload",
                ) {
                    extra.push(eq);
                }
            }
        }
        // Part of #3962: update flattened_field_env so translate_place_with_modified
        // can reconstruct the Result value for downstream reference-based reads
        // (e.g., PartialEq::eq via &result). Without this, typed memory loads see
        // unconstrained values — Ok(0) accidentally passes (BV 0x0000) but Err(0)
        // = 0x8000 fails.
        let mut field_values: Vec<Option<Expr>> =
            vec![Some(success_for_env), Some(old_value.clone())];
        if n_fields >= 3 {
            field_values.push(Some(old_value));
        }
        ctx.constrain_flattened_fields_for_call(dest_local, &field_values, &mut extra);
        // Part of #3962: serialize flattened Result to typed memory so reference-based
        // reads (e.g., `&result` in PartialEq::eq) load the correct value.
        let mem_bridge = build_call_result_memory_bridge_constraints(
            ctx,
            dest_local,
            &Expr::bool_const(true), // placeholder — bridge reads from flattened_field_env
            dcx.modified_locals,
        );
        extra.extend(mem_bridge);
    }
    // Conditional store: referent = ite(success, new, old).
    if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
        let s = rv.sort().clone();
        if let Some(eq) = ctx.make_coerced_eq_constraint(
            &rv,
            cond_new,
            &s,
            referent_local,
            "compare_exchange_store",
        ) {
            extra.push(eq);
        }
    }
    ctx.encode.invalidate_local_cache(referent_local);
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

/// `atomic_cxchg(ptr, expected, new)` → `(old, old == expected)`; conditionally
/// stores new. Returns a flattened tuple: slot 0 = old, slot 1 = success flag.
pub(in crate::codegen_ay::chc) fn codegen_atomic_cxchg(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 3 {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    let old_value = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let referent_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    // Part of #3761: register raw pointer as call-forwarded for consistent deref.
    if referent_local.is_some() {
        mark_atomic_ptr_forwarded(ctx, &dcx.args[0]);
    }
    // Part of #3492: args[1]/[2] are VALUES (not refs), same as stable compare_exchange.
    let expected = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);
    let new_value = ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals);
    let (Some(old_value), Some(referent_local), Some(expected), Some(new_value)) =
        (old_value, referent_local, expected, new_value)
    else {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };
    // Unwrap repr(transparent) + coerce Bool↔BV (Part of #3452).
    let old_value = unwrap_single_field_datatype(&old_value).unwrap_or(old_value);
    let expected = unwrap_single_field_datatype(&expected).unwrap_or(expected);
    let new_value = unwrap_single_field_datatype(&new_value).unwrap_or(new_value);
    let (old_value, expected) = coerce_atomic_bool_sorts(old_value, expected);
    let (old_value, new_value) = coerce_atomic_bool_sorts(old_value, new_value);
    // Sort guard: fall back if sorts don't match after coercion.
    if old_value.sort() != expected.sort() {
        debug!(
            "CHC atomic_cxchg: sort mismatch old={:?} expected={:?}, sound fallback",
            old_value.sort(),
            expected.sort()
        );
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }
    let success = old_value.clone().eq(expected);
    // Conditional store: *ptr = ite(success, new, old)
    let cond_new = Expr::ite(success.clone(), new_value, old_value.clone());
    let mut extra = Vec::new();

    // Flattened tuple return: slot 0 = old, slot 1 = success flag.
    // Slots are contiguous by construction (flatten_local_nfield pushes
    // state vars consecutively).
    let dest_vec_idx = ctx.try_state_idx_for_local(dest_local);
    if dest_vec_idx.is_none() {
        ctx.record_sound_fallback_reason("state_idx_missing_cxchg_dest");
    }
    let n_fields_cxchg = ctx.flattened_field_count(dest_local);
    if let Some(dest_vec_idx) = dest_vec_idx
        && ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        && n_fields_cxchg >= 2
    {
        assert!(
            dest_vec_idx + 1 < ctx.state_var_mgr.output_state_vars.len(),
            "cxchg: contiguous slot invariant violated for local {dest_local}"
        );
        // Part of #3962: preserve values for flattened_field_env update below.
        let old_value_for_env = old_value.clone();
        let success_for_env = success.clone();
        // Slot 0: old value.
        if let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
        {
            let old_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &old_var,
                old_value,
                &out_sort,
                dest_local,
                "atomic_cxchg_old",
            ) {
                extra.push(eq);
            }
        }
        // Slot 1: success flag (bool → bitvec if needed).
        if let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx + 1).cloned()
        {
            let success_var = Expr::var(&*out_name, out_sort.clone());
            let coerced = if let Some(w) = out_sort.bitvec_width() {
                Expr::ite(success, Expr::bitvec_const(1, w), Expr::bitvec_const(0, w))
            } else {
                success
            };
            extra.push(success_var.eq(coerced));
        }
        // Part of #3962: update flattened_field_env + typed memory bridge.
        let field_values: Vec<Option<Expr>> = vec![Some(old_value_for_env), Some(success_for_env)];
        ctx.constrain_flattened_fields_for_call(dest_local, &field_values, &mut extra);
        let mem_bridge = build_call_result_memory_bridge_constraints(
            ctx,
            dest_local,
            &Expr::bool_const(true),
            dcx.modified_locals,
        );
        extra.extend(mem_bridge);
    }

    // Conditional store: referent = ite(success, new, old).
    if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
        let s = rv.sort().clone();
        if let Some(eq) =
            ctx.make_coerced_eq_constraint(&rv, cond_new, &s, referent_local, "atomic_cxchg_store")
        {
            extra.push(eq);
        }
    }
    ctx.encode.invalidate_local_cache(referent_local);
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

// ---------------------------------------------------------------------------
// Shared RMW (read-modify-write) handler
// ---------------------------------------------------------------------------

/// Compute the new stored value for an atomic RMW operation.
pub(in crate::codegen_ay::chc) fn compute_rmw_value(
    kind: &AtomicKind,
    old: Expr,
    operand: Expr,
) -> Expr {
    match kind {
        AtomicKind::FetchAdd => old.bvadd(operand),
        AtomicKind::FetchSub => old.bvsub(operand),
        AtomicKind::FetchAnd => old.bvand(operand),
        AtomicKind::FetchOr => old.bvor(operand),
        AtomicKind::FetchXor => old.bvxor(operand),
        AtomicKind::FetchNand => old.bvand(operand).bvnot(),
        AtomicKind::FetchMax => Expr::ite(old.clone().bvsgt(operand.clone()), old, operand),
        AtomicKind::FetchMin => Expr::ite(old.clone().bvslt(operand.clone()), old, operand),
        AtomicKind::FetchUmax => Expr::ite(old.clone().bvugt(operand.clone()), old, operand),
        AtomicKind::FetchUmin => Expr::ite(old.clone().bvult(operand.clone()), old, operand),
        _ => unreachable!("not an RMW operation"),
    }
}

/// Shared handler: `old = *ptr; *ptr = f(old, operand); return old`.
///
/// Covers exchange, fetch-add/sub/and/or/xor/nand, and fetch-min/max.
pub(in crate::codegen_ay::chc) fn codegen_atomic_rmw(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: AtomicKind,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 2 {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    let referent_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    // Part of #3761: register raw pointer as call-forwarded for consistent deref.
    if referent_local.is_some() {
        mark_atomic_ptr_forwarded(ctx, &dcx.args[0]);
    }
    debug!(
        bb_idx = dcx.bb_idx,
        ?kind,
        referent_local = ?referent_local,
        n_args = dcx.args.len(),
        dest_local,
        "codegen_atomic_rmw entry"
    );
    let mem_target = if referent_local.is_none() {
        atomic_receiver_mem_target(ctx, &dcx.args[0], dcx.modified_locals)
    } else {
        None
    };

    let old_value = if referent_local.is_some() {
        ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals)
    } else if let Some((addr, pointee_ty)) = mem_target.as_ref() {
        // A load is the legal `Loc -> Val` crossing; the referent lane above is
        // NOT tagged, because `resolve_ref_or_const_referent` does not report
        // whether it dereferenced or handed back the pointer (§4 item 1).
        atomic_load_from_memory(ctx, addr, *pointee_ty).map(Val::into_expr)
    } else {
        None
    };

    // Exchange: arg[1] directly. Fetch-*: computed from old and operand.
    let is_exchange = matches!(kind, AtomicKind::Exchange);
    let rhs = if is_exchange {
        ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
    } else {
        ctx.resolve_ref_or_const_referent(&dcx.args[1], dcx.modified_locals)
    };

    let (Some(old_value), Some(rhs)) = (old_value, rhs) else {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    // Unwrap repr(transparent) + coerce Bool↔BV (Part of #3452).
    let old_value = unwrap_single_field_datatype(&old_value).unwrap_or(old_value);
    let rhs = unwrap_single_field_datatype(&rhs).unwrap_or(rhs);
    let (old_value, rhs) = coerce_atomic_bool_sorts(old_value, rhs);

    let new_value =
        if is_exchange { rhs } else { compute_rmw_value(&kind, old_value.clone(), rhs) };

    if let Some(referent_local) = referent_local {
        debug!(
            "CHC atomic_rmw: referent_local={} (bb{}->bb{})",
            referent_local, dcx.bb_idx, target
        );
        emit_rmw_constraints(ctx, dcx, target, old_value, new_value, referent_local);
    } else if let Some((addr, pointee_ty)) = mem_target {
        debug!(bb_idx = dcx.bb_idx, "CHC atomic_rmw: Mem-level receiver");
        emit_rmw_constraints_mem(ctx, dcx, target, old_value, new_value, addr, pointee_ty);
    } else {
        ctx.record_fallback(); // Part of #3721: write-dropping fallback
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    }
}

/// Emit constraints for RMW: `dest = old_value`, `referent = new_value`, then goto.
fn emit_rmw_constraints(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    old_value: Expr,
    new_value: Expr,
    referent_local: usize,
) {
    let dest_local: usize = dcx.destination.local;
    let mut extra = Vec::new();

    // dest = old value (fetch returns the OLD value).
    if let Some((_, dv)) = ctx.resolve_destination(dest_local) {
        let s = dv.sort().clone();
        if let Some(eq) =
            ctx.make_coerced_eq_constraint(&dv, old_value, &s, dest_local, "atomic_rmw_dest")
        {
            extra.push(eq);
        }
    }
    // referent = new value.
    if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
        let s = rv.sort().clone();
        if let Some(eq) =
            ctx.make_coerced_eq_constraint(&rv, new_value, &s, referent_local, "atomic_rmw_store")
        {
            extra.push(eq);
        }
    }
    ctx.encode.invalidate_local_cache(referent_local);
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

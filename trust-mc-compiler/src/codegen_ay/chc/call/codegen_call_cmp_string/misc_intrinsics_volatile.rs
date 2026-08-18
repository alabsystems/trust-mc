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

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, ProjectionElem};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_decl_flatten::compute_nested_flat_slot;
use super::super::codegen_rules::CodegenRules;
use super::super::codegen_types::CodegenTypes;
use super::super::ptr_receiver_mem::{
    drain_pending_checks, emit_mem_store_transition, load_from_memory, receiver_mem_target,
    resolve_ptr_target_local,
};
use super::misc_intrinsics_volatile_helpers::{
    find_ptr_add_base_and_count, projected_vec_data_slot_for_ptr, try_extract_vec_element_for_load,
    try_volatile_load_via_projected_vec, try_volatile_load_via_ptr_add,
    try_volatile_load_via_vec_trace,
};
use crate::codegen_ay::provenance::Val;

fn extract_plain_operand_local(arg: &rustc_public::mir::Operand) -> Option<usize> {
    use rustc_public::mir::Operand;

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
/// provenance volatile accesses keep the historical skip.
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
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
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
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
            drain_pending_checks(ctx, dcx, target);
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
            return;
        };

        debug!(referent_local, "CHC: volatile_store encoded (Part of #3464)");

        let mut extra = Vec::new();
        if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
            let s = rv.sort().clone();
            if let Some(eq) =
                ctx.make_coerced_eq_constraint(&rv, new_value, &s, referent_local, "volatile_store")
            {
                extra.push(eq);
            }
        }

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
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
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
    use rustc_public::mir::Operand;

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

    // Extract field indices from the projection chain.
    let field_indices: Vec<usize> = ref_target
        .projections
        .iter()
        .filter_map(|p| match p {
            ProjectionElem::Field(idx, _) => Some(*idx),
            _ => None,
        })
        .collect();
    if field_indices.is_empty() {
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

    // Compute the flat slot for the target field.
    let parent_decl = match ctx.body.locals().get(parent_local) {
        Some(d) => d,
        None => return false,
    };
    let Some(parent_sort) = ChcCtx::translate_ty(parent_decl.ty) else {
        return false;
    };
    let Some(flat_slot) = compute_nested_flat_slot(&parent_sort, &field_indices) else {
        debug!(
            parent_local,
            ?field_indices,
            "CHC: volatile_store projected — flat slot computation failed"
        );
        return false;
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
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }
    let Some(referent_local) = resolve_ptr_target_local(ctx, &dcx.args[0]) else {
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };
    let old_val = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let new_val = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);
    let (Some(old_val), Some(new_val)) = (old_val, new_val) else {
        debug!("CHC: mem::replace — values not resolvable, unconstrained fallback (#4092)");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };
    debug!(referent_local, dest_local, "CHC: mem::replace encoded (#4092)");
    let mut extra = Vec::new();
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(referent_local, new_val, "mem_replace_store")
    {
        extra.append(&mut eqs);
    }
    if let Some(mut eqs) =
        ctx.build_local_update_constraints(dest_local, old_val, "mem_replace_return")
    {
        extra.append(&mut eqs);
    }
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
        debug!("CHC: typed_swap with < 2 args — unconstrained fallback");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    // Resolve both pointer target locals.
    let x_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    let y_local = resolve_ptr_target_local(ctx, &dcx.args[1]);

    let (Some(x_local), Some(y_local)) = (x_local, y_local) else {
        debug!(
            "CHC: typed_swap — pointer(s) not resolvable, unconstrained fallback (Part of #3464)"
        );
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    // Read current (input-state) values of both referents.
    let x_val = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let y_val = ctx.resolve_ref_or_const_referent(&dcx.args[1], dcx.modified_locals);

    let (Some(x_val), Some(y_val)) = (x_val, y_val) else {
        debug!("CHC: typed_swap — values not resolvable, unconstrained fallback (Part of #3464)");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, x_local, y_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    debug!(x_local, y_local, "CHC: typed_swap encoded (Part of #3464)");

    // Cross-constrain: output *x = old *y, output *y = old *x.
    // Use the shared local-update helper so flattened aggregate referents
    // decompose into all destination slots instead of constraining only slot 0.
    let mut extra = Vec::new();
    if let Some(mut eqs) = ctx.build_local_update_constraints(x_local, y_val, "typed_swap_x") {
        extra.append(&mut eqs);
    }
    if let Some(mut eqs) = ctx.build_local_update_constraints(y_local, x_val, "typed_swap_y") {
        extra.append(&mut eqs);
    }

    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, x_local, y_local]);
    if extra.is_empty() {
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    } else {
        ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
    }
}

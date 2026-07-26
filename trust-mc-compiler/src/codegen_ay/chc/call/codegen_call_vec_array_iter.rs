// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array-inner iterator call handling for Vec/Array into-iter patterns.
//!
//! Split from `codegen_call_vec.rs` for module size (Part of #4135).
//! Contains three handlers:
//! - `codegen_call_array_inner_iter_next_impl`: PolymorphicIter::next / IndexRange::next
//!   on inner fields of ArrayIntoIter locals.
//! - `codegen_call_array_index_range_next_impl`: IndexRange::next() returning Option<usize>.
//! - `try_codegen_array_inner_option_map_impl`: Option::map lifting Option<usize> → Option<T>
//!   using parent array data.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use super::ChcCtx;
use super::canonical_zst_expr_for_sort;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_kani_model_dst::is_zst_ty;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::stubs_option_helpers::OptionHelpers;
use tracing::debug;

/// Handle array inner iterator next() calls via parent IntoIter reconstruction.
///
/// Part of #3984: PolymorphicIter::next / IndexRange::next are called on inner
/// fields of ArrayIntoIter locals. The receiver is a BV64 heap pointer (not in
/// ref_targets or projection_locals). We find the parent IntoIter local, reconstruct
/// it from flattened state vars, run the iteration core logic, then decompose the
/// updated iterator back to flattened field constraints.
pub(in crate::codegen_ay::chc) fn codegen_call_array_inner_iter_next_impl(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    let destination = dcx.destination;
    let target = dcx.target;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    let Some(target) = target else {
        return;
    };

    // Step 1: Find parent ArrayIntoIter local.
    let parent_local = match ctx.find_parent_array_into_iter_local() {
        Some(l) => l,
        None => {
            ctx.record_sound_fallback_reason("array_inner_iter_no_parent");
            emit_sound_fallback_goto(
                ctx,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        }
    };

    // Step 2: Read flattened state vars directly — NO Datatype reconstruction.
    // ArrayIntoIter deep-flattened layout: [start: bv64, end: bv64, data: Array<bv64, T>]
    // This avoids the construct-then-decompose pattern that creates deeply nested
    // Datatype expressions the solver struggles to simplify.
    let start = ctx.flattened_local_field_expr(parent_local, 0, modified_locals);
    let end = ctx.flattened_local_field_expr(parent_local, 1, modified_locals);
    let data = ctx.flattened_local_field_expr(parent_local, 2, modified_locals);

    let (Some(start), Some(end), Some(data)) = (start, end, data) else {
        ctx.record_sound_fallback_reason("array_inner_iter_flat_read_fail");
        emit_sound_fallback_goto(
            ctx,
            from_app,
            *target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
        return;
    };

    // Step 3: Compute iteration result directly on flat expressions.
    let in_bounds = start.clone().bvult(end.clone());
    let raw_element = data.clone().select(start.clone());
    let element = canonical_zst_option_payload_for_local(ctx, dest_local, raw_element.sort())
        .unwrap_or(raw_element);
    let one = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);
    let new_start = Expr::ite(in_bounds.clone(), start.clone().bvadd(one), start);

    // Step 4: Constrain parent iterator flattened fields.
    let mut extra_constraints: Vec<Expr> = Vec::new();
    let mut extra_dests: Vec<usize> = Vec::new();

    let iter_field_values: Vec<Option<Expr>> = vec![Some(new_start), Some(end), Some(data)];
    if ctx.constrain_flattened_fields_for_call(
        parent_local,
        &iter_field_values,
        &mut extra_constraints,
    ) {
        extra_dests.push(parent_local);
    } else {
        ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
    }

    // Step 5: Write result (element + Option) to destination.
    if ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        // DT-free flattened Option path: write (is_some, value) directly.
        let mut field_values: Vec<Option<Expr>> = vec![Some(in_bounds)];
        let mut payload_fields = Vec::new();
        super::codegen_stmt_flatten::collect_leaf_exprs(&element, &mut payload_fields);
        field_values.extend(payload_fields);
        while field_values.len() < ctx.flattened_field_count(dest_local) {
            field_values.push(None);
        }
        if ctx.constrain_flattened_fields_for_call(
            dest_local,
            &field_values,
            &mut extra_constraints,
        ) {
            extra_dests.push(dest_local);
        } else {
            ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
        }
    } else if let Some(dest_vec_idx) = ctx.try_state_idx_for_local(dest_local)
        && let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
    {
        // Non-flattened Option path: construct ITE(in_bounds, Some(elem), None).
        let some_expr = ctx.make_some_expr_for_option(element, &out_sort);
        let none_expr = ctx.make_none_expr_for_option(&out_sort);
        if let (Some(some_expr), Some(none_expr)) = (some_expr, none_expr) {
            let option_result = Expr::ite(in_bounds, some_expr, none_expr);
            let dest_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                option_result,
                &out_sort,
                dest_local,
                "array_inner_iter_next::option_result",
            ) {
                extra_constraints.push(eq);
            }
            extra_dests.push(dest_local);
        }
    }

    // Step 6: Emit rule.
    let new_output_args = ctx.build_output_args(modified_locals, &extra_dests);
    ctx.emit_goto_rule_extra(
        from_app,
        *target,
        &new_output_args,
        stmt_constraints,
        extra_constraints,
    );
}

/// Handle IndexRange::next() — returns Option<usize> (index into array).
///
/// Part of #3984: IndexRange::next increments start if in-bounds and returns
/// Option<usize>. The value returned is the current start index (before increment),
/// which the MIR then feeds through Option::map to extract array[index].
pub(in crate::codegen_ay::chc) fn codegen_call_array_index_range_next_impl(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    let destination = dcx.destination;
    let target = dcx.target;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    let Some(target) = target else {
        return;
    };

    // Step 1: Find parent ArrayIntoIter local.
    let parent_local = match ctx.find_parent_array_into_iter_local() {
        Some(l) => l,
        None => {
            ctx.record_sound_fallback_reason("array_index_range_no_parent");
            emit_sound_fallback_goto(
                ctx,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        }
    };

    // Step 2: Read start and end from flattened IntoIter fields.
    // ArrayIntoIter deep-flattened layout: [start: bv64, end: bv64, data: Array<bv64, T>]
    let start = ctx.flattened_local_field_expr(parent_local, 0, modified_locals);
    let end = ctx.flattened_local_field_expr(parent_local, 1, modified_locals);
    let data = ctx.flattened_local_field_expr(parent_local, 2, modified_locals);

    let (Some(start), Some(end), Some(data)) = (start, end, data) else {
        ctx.record_sound_fallback_reason("array_index_range_flat_read_fail");
        emit_sound_fallback_goto(
            ctx,
            from_app,
            *target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
        return;
    };

    // Step 3: Compute iteration: in_bounds, new_start.
    // IndexRange::next returns Option<usize> where the usize IS the start index.
    let in_bounds = start.clone().bvult(end.clone());
    let one = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);
    let new_start = Expr::ite(in_bounds.clone(), start.clone().bvadd(one), start.clone());

    // Step 4: Constrain parent iterator flattened fields (start updated, end/data unchanged).
    let mut extra_constraints: Vec<Expr> = Vec::new();
    let mut extra_dests: Vec<usize> = Vec::new();

    let iter_field_values: Vec<Option<Expr>> = vec![Some(new_start), Some(end), Some(data)];
    if ctx.constrain_flattened_fields_for_call(
        parent_local,
        &iter_field_values,
        &mut extra_constraints,
    ) {
        extra_dests.push(parent_local);
    } else {
        ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
    }

    // Step 5: Write Option<usize> result to destination.
    // The result is Option<usize> = ITE(in_bounds, Some(start), None).
    // `start` here is a BV64 — the index value.
    if ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        // DT-free flattened Option path: write (is_some, value) directly.
        let field_values: Vec<Option<Expr>> = vec![Some(in_bounds), Some(start)];
        if ctx.constrain_flattened_fields_for_call(
            dest_local,
            &field_values,
            &mut extra_constraints,
        ) {
            extra_dests.push(dest_local);
        } else {
            ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
        }
    } else if let Some(dest_vec_idx) = ctx.try_state_idx_for_local(dest_local)
        && let Some((out_name, out_sort)) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
    {
        // Non-flattened Option<usize> path: construct ITE.
        let some_expr = ctx.make_some_expr_for_option(start, &out_sort);
        let none_expr = ctx.make_none_expr_for_option(&out_sort);
        if let (Some(some_expr), Some(none_expr)) = (some_expr, none_expr) {
            let option_result = Expr::ite(in_bounds, some_expr, none_expr);
            let dest_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                option_result,
                &out_sort,
                dest_local,
                "array_index_range_next::option_result",
            ) {
                extra_constraints.push(eq);
            }
            extra_dests.push(dest_local);
        }
    }

    // Step 6: Emit rule.
    let new_output_args = ctx.build_output_args(modified_locals, &extra_dests);
    ctx.emit_goto_rule_extra(
        from_app,
        *target,
        &new_output_args,
        stmt_constraints,
        extra_constraints,
    );
}

/// Array-inner OptionMap: lift Option<usize> to Option<T> using parent array data.
///
/// Part of #3984: After IndexRange::next produces Option<usize>, the standard
/// library calls Option::map with a closure that reads data[idx]. This handler
/// replaces the generic symbolic combinator to produce a precise result.
///
/// Returns true if it handled the call, false to fall through to generic path.
pub(in crate::codegen_ay::chc) fn try_codegen_array_inner_option_map_impl(
    ctx: &mut ChcCtx<'_, '_>,
    cx: &ChcCallContext<'_>,
) -> bool {
    let dest_local: usize = cx.destination.local;
    let modified_locals = cx.modified_locals;

    // Step 1: Find parent ArrayIntoIter local.
    let Some(parent_local) = ctx.find_parent_array_into_iter_local() else {
        return false;
    };

    // Step 2: Read the data array from flattened parent fields.
    // ArrayIntoIter deep-flattened layout: [start: bv64, end: bv64, data: Array<bv64, T>]
    let Some(data) = ctx.flattened_local_field_expr(parent_local, 2, modified_locals) else {
        debug!(parent_local, "array_inner_option_map: cannot read parent data field");
        return false;
    };

    // Step 3: Resolve the receiver Option<usize> (args[0]).
    // args[0] is the Option<usize> produced by the preceding IndexRange::next.
    let Some(receiver_arg) = cx.args.first() else {
        return false;
    };
    let receiver_local = match receiver_arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return false,
    };

    // Step 4: Extract is_some and index from receiver.
    // The receiver is a flattened Option<usize>: [is_some: Bool, value: BV64].
    let is_some = ctx.flattened_local_field_expr(receiver_local, 0, modified_locals);
    let index = ctx.flattened_local_field_expr(receiver_local, 1, modified_locals);
    let (Some(is_some), Some(index)) = (is_some, index) else {
        debug!(receiver_local, "array_inner_option_map: cannot read receiver flattened fields");
        return false;
    };

    // Step 5: Compute element = data[index].
    let raw_element = data.select(index);
    let element = canonical_zst_option_payload_for_local(ctx, dest_local, raw_element.sort())
        .unwrap_or(raw_element);
    debug!(elem_sort = %element.sort(), "array_inner_option_map: element from data[idx]");

    // Step 6: Write Option<T> result to destination.
    let dest_vec_idx = ctx.try_state_idx_for_local(dest_local);
    let dest_info =
        dest_vec_idx.and_then(|idx| ctx.state_var_mgr.output_state_vars.get(idx).cloned());

    if ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        // Flattened Option<T>: write (is_some, element) directly.
        let field_values: Vec<Option<Expr>> = vec![Some(is_some), Some(element)];
        let mut extra_constraints: Vec<Expr> = Vec::new();
        if !ctx.constrain_flattened_fields_for_call(
            dest_local,
            &field_values,
            &mut extra_constraints,
        ) {
            ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
        }
        let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
        return true;
    } else if let Some((out_name, out_sort)) = dest_info {
        // Non-flattened Option<T>: construct ITE(is_some, Some(element), None).
        let some_expr = ctx.make_some_expr_for_option(element, &out_sort);
        let none_expr = ctx.make_none_expr_for_option(&out_sort);
        if let (Some(some_expr), Some(none_expr)) = (some_expr, none_expr) {
            let option_result = Expr::ite(is_some, some_expr, none_expr);
            let dest_var = Expr::var(&*out_name, out_sort.clone());
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                option_result,
                &out_sort,
                dest_local,
                "array_inner_option_map::option_result",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                eq,
            );
            return true;
        }
    }

    debug!(dest_local, "array_inner_option_map: cannot write dest — falling through");
    false
}

pub(in crate::codegen_ay::chc) fn canonical_zst_option_payload_for_local(
    ctx: &ChcCtx<'_, '_>,
    dest_local: usize,
    payload_sort: &ay_bindings::Sort,
) -> Option<Expr> {
    let dest_ty = ctx.resolve_body_ty(ctx.body.locals().get(dest_local)?.ty);
    let payload_ty = option_payload_ty(ctx, dest_ty)?;
    let (payload_ty, _) = ChcCtx::deref_ref_ty(payload_ty);
    let payload_ty = ctx.resolve_body_ty(payload_ty);
    if !is_zst_ty(payload_ty) {
        return None;
    }
    canonical_zst_expr_for_sort(payload_ty, payload_sort).filter(|expr| expr.sort() == payload_sort)
}

fn option_payload_ty(ctx: &ChcCtx<'_, '_>, ty: Ty) -> Option<Ty> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        return None;
    };
    let variants = def.variants();
    if variants.len() != 2 {
        return None;
    }
    let v0_fields = variants[0].fields().len();
    let v1_fields = variants[1].fields().len();
    let some_idx = match (v0_fields, v1_fields) {
        (1, 0) => 0,
        (0, 1) => 1,
        _ => return None,
    };
    let fields = variants[some_idx].fields();
    let field = fields.first()?;
    Some(ctx.resolve_body_ty(field.ty_with_args(&args)))
}

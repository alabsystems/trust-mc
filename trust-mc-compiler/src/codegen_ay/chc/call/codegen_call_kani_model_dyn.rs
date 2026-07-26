// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Dyn-object size/alignment model function helpers for CHC codegen.
//!
//! Implements `AlignOfDynObject` and `SizeOfDynObject` via vtable_type_metadata
//! ITE chains. Part of #3210 Phase 2.

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;

/// Raw dyn-object computation result: value and "is_none" condition.
struct DynObjectResult {
    value: Expr,
    is_none: Expr,
}

/// Emit flattened or non-flattened Option<usize> constraints for dyn-object model results.
/// Shared by both AlignOfDynObject and SizeOfDynObject dispatchers.
/// Part of #3445: fixes flattened destination sort mismatch (same pattern as SizeOfSliceObject).
fn emit_dyn_object_option_constraints(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    result: DynObjectResult,
    site_label: &'static str,
) {
    let dest_local = dcx.destination.local;
    // Part of #3124: graceful fallback instead of panic.
    // Callers guard dcx.target before calling this, but defensive early-return
    // prevents catch_unwind boundary propagation.
    let Some(target) = *dcx.target else {
        warn!("emit_dyn_object_option_constraints called without target");
        return;
    };

    // Part of #3631: use shared helper for flattened field emission.
    // Replaces manual fld0/fld1 constraint construction that was missing
    // flattened_field_env updates entirely.
    let is_some = result.is_none.clone().not();
    let field_values = vec![
        Some(ctx.reshape_flattened_bool_field_for_call(dest_local, 0, is_some)),
        Some(result.value.clone()),
    ];
    if ctx.emit_flattened_call_fields(
        dest_local,
        &field_values,
        dcx.from_app,
        target,
        dcx.modified_locals,
        dcx.stmt_constraints,
    ) {
        debug!(dest_local, site_label, "flattened Option(is_some, value) (#3445/#3631)");
    } else {
        // Non-flattened: build Option<usize> Datatype and constrain as single value.
        use crate::codegen_ay::chc::stubs_option_helpers::{OptionHelpers, make_option_sort};
        let usize_sort = Sort::bitvec(POINTER_WIDTH);
        let option_sort = make_option_sort(&usize_sort);
        let built =
            ctx.make_some_expr_for_option(result.value, &option_sort).and_then(|some_expr| {
                let none_expr = ctx.make_none_expr_for_option(&option_sort)?;
                Some((some_expr, none_expr))
            });
        if let Some((some_expr, none_expr)) = built {
            let option_expr = Expr::ite(result.is_none, none_expr, some_expr);
            let mut extra = Vec::new();
            if let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local) {
                if let Some((out_name, out_sort)) =
                    ctx.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                {
                    let out_var = Expr::var(&*out_name, out_sort);
                    extra.push(out_var.eq(option_expr));
                }
            }
            let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                dcx.stmt_constraints,
                extra,
            );
        } else {
            emit_sound_fallback_goto(
                ctx,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
        }
    }
}

/// Dispatch `KaniModel::AlignOfDynObject` — vtable-based alignment lookup.
///
/// Args from MIR: `(ptr, head_align) -> Option<usize>`.
/// Computes `max(vtable_align, head_align)` via ITE chain over vtable_type_metadata.
/// Part of #3210 Phase 2, #3445 flattened-destination fix.
pub(in crate::codegen_ay::chc) fn dispatch_align_of_dyn_object(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    let dest_local = dcx.destination.local;
    if let Some(target) = dcx.target {
        let result = compute_align_of_dyn_raw(ctx, dcx.args, dcx.modified_locals);
        if let Some(dyn_result) = result {
            emit_dyn_object_option_constraints(
                ctx,
                dcx,
                dyn_result,
                "align_of_dyn_object::is_some",
            );
        } else {
            emit_sound_fallback_goto(
                ctx,
                dcx.from_app,
                *target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
        }
    } else {
        ctx.record_diverging_call_drop(
            dcx.func,
            Some(dcx.bb_idx),
            "kani_model::AlignOfDynObject",
            None,
        );
    }
}

/// Dispatch `KaniModel::SizeOfDynObject` — vtable-based size computation.
///
/// Args from MIR: `(ptr, head_size, head_align) -> Option<usize>`.
/// Computes size with alignment rounding via vtable_type_metadata ITE chain.
/// Part of #3210 Phase 2, #3445 flattened-destination fix.
pub(in crate::codegen_ay::chc) fn dispatch_size_of_dyn_object(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    let dest_local = dcx.destination.local;
    if let Some(target) = dcx.target {
        let result = compute_size_of_dyn_raw(ctx, dcx.args, dcx.modified_locals);
        if let Some(dyn_result) = result {
            emit_dyn_object_option_constraints(ctx, dcx, dyn_result, "size_of_dyn_object::is_some");
        } else {
            emit_sound_fallback_goto(
                ctx,
                dcx.from_app,
                *target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
        }
    } else {
        ctx.record_diverging_call_drop(
            dcx.func,
            Some(dcx.bb_idx),
            "kani_model::SizeOfDynObject",
            None,
        );
    }
}

/// Extract the vtable discriminant from a model function's ptr argument.
pub(in crate::codegen_ay::chc) fn extract_vtable_disc_from_ptr_arg(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let ptr_arg = args.first()?;
    let ptr_expr = ctx.translate_operand_with_modified(ptr_arg, modified_locals)?;
    let receiver_local = match ptr_arg {
        rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p)
            if p.projection.is_empty() =>
        {
            Some(p.local)
        }
        _ => None,
    };
    Some(ctx.try_extract_vtable_discriminant(&[ptr_expr], receiver_local))
}

/// Build an ITE chain selecting a vtable metadata value (size or align) by vtable ID.
pub(in crate::codegen_ay::chc) fn build_vtable_metadata_ite(
    ctx: &ChcCtx<'_, '_>,
    vtable_disc: &Expr,
    select_size: bool,
) -> Expr {
    // Part of #3447: Record that vtable metadata ITE default is unconstrained
    // (fires when vtable ID doesn't match any registered concrete type).
    ctx.record_aggregate_gap("dyn_vtable_metadata_default_unconstrained");
    let mut result = super::declare_pending_var(
        super::chc_fresh_name("__dyn_meta"),
        Sort::bitvec(POINTER_WIDTH),
    );
    for (&vtable_id, &(size, align)) in &ctx.vtable_type_metadata {
        let value = if select_size { size } else { align };
        let cond = vtable_disc.clone().eq(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
        let val_expr = Expr::bitvec_const(value as u128, POINTER_WIDTH);
        result = Expr::ite(cond, val_expr, result);
    }
    result
}

/// Compute raw align_of_dyn_object components: (value, is_none).
/// Part of #3445: returns raw components for flattened-destination support.
fn compute_align_of_dyn_raw(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<DynObjectResult> {
    if args.len() < 2 {
        debug!("compute_align_of_dyn_raw: expected 2 args, got {}", args.len());
        return None;
    }
    if ctx.vtable_type_metadata.is_empty() {
        debug!("compute_align_of_dyn_raw: no vtable_type_metadata, fallback");
        return None;
    }

    let vtable_disc = extract_vtable_disc_from_ptr_arg(ctx, args, modified_locals)?;
    let dyn_align = build_vtable_metadata_ite(ctx, &vtable_disc, false);

    let head_align = ctx.translate_operand_with_modified(&args[1], modified_locals)?;
    let head_align = coerce_bitvec_width_safe(head_align, POINTER_WIDTH, SignExtension::ZeroExtend);

    // align = max(dyn_align, head_align)
    let align = Expr::ite(dyn_align.clone().bvugt(head_align.clone()), dyn_align, head_align);

    // is_power_of_two: align & (align - 1) == 0 && align != 0
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let is_pot = align
        .clone()
        .bvand(align.clone().bvsub(one))
        .eq(zero.clone())
        .and(align.clone().eq(zero).not());

    Some(DynObjectResult { value: align, is_none: is_pot.not() })
}

/// Compute raw size_of_dyn_object components: (value, is_none).
/// Part of #3445: returns raw components for flattened-destination support.
fn compute_size_of_dyn_raw(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<DynObjectResult> {
    if args.len() < 3 {
        debug!("compute_size_of_dyn_raw: expected 3 args, got {}", args.len());
        return None;
    }
    if ctx.vtable_type_metadata.is_empty() {
        debug!("compute_size_of_dyn_raw: no vtable_type_metadata, fallback");
        return None;
    }

    let vtable_disc = extract_vtable_disc_from_ptr_arg(ctx, args, modified_locals)?;
    let dyn_size = build_vtable_metadata_ite(ctx, &vtable_disc, true);
    let dyn_align = build_vtable_metadata_ite(ctx, &vtable_disc, false);

    let head_size = ctx.translate_operand_with_modified(&args[1], modified_locals)?;
    let head_size = coerce_bitvec_width_safe(head_size, POINTER_WIDTH, SignExtension::ZeroExtend);
    let head_align = ctx.translate_operand_with_modified(&args[2], modified_locals)?;
    let head_align = coerce_bitvec_width_safe(head_align, POINTER_WIDTH, SignExtension::ZeroExtend);

    // align = max(dyn_align, head_align)
    let align = Expr::ite(dyn_align.clone().bvugt(head_align.clone()), dyn_align, head_align);

    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);

    // is_power_of_two check
    let is_pot = align
        .clone()
        .bvand(align.clone().bvsub(one.clone()))
        .eq(zero.clone())
        .and(align.clone().eq(zero.clone()).not());

    // total = dyn_size + head_size (checked add)
    let total = dyn_size.clone().bvadd(head_size);
    let sum_overflow = total.clone().bvult(dyn_size);

    // adjust = total + (align - 1)
    let align_sub_1 = align.clone().bvsub(one);
    let adjust = total.clone().bvadd(align_sub_1);
    let adjust_overflow = adjust.clone().bvult(total);

    // adjusted_size = adjust & align.wrapping_neg()
    let align_neg = zero.bvsub(align);
    let adjusted_size = adjust.bvand(align_neg);

    // isize::MAX overflow check
    let isize_max = Expr::bitvec_const(i64::MAX as u64, POINTER_WIDTH);
    let size_overflow = adjusted_size.clone().bvugt(isize_max);

    let any_bad = is_pot.not().or(sum_overflow).or(adjust_overflow).or(size_overflow);

    Some(DynObjectResult { value: adjusted_size, is_none: any_bad })
}

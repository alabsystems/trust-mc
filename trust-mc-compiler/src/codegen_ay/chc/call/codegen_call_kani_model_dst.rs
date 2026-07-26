// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! DST (Dynamically Sized Type) model function helpers for CHC codegen.
//!
//! Extracted from codegen_call_kani_model.rs — Part of #3210, #2408.

use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::{
    CtorFieldExt, POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe,
};
use crate::kani_middle::abi::LayoutOf;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_extra,
};
use super::codegen_rules::CodegenRules;

/// Dispatch `KaniModel::SizeOfSliceObject` — compute exact size for slice-tail DSTs.
///
/// Args from MIR: `(len, elem_size, head_size, align) -> Option<usize>`.
/// Part of #3210, #3445: Handles both flattened and non-flattened Option<usize>
/// destinations. Flattened destinations have (fld0=is_some: Bool, fld1=value: BV64)
/// as separate state variables; non-flattened use a single Option Datatype variable.
pub(in crate::codegen_ay::chc) fn dispatch_size_of_slice_object(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    let bb_idx = dcx.bb_idx;
    let func = dcx.func;
    let args = dcx.args;
    let destination = dcx.destination;
    let target = dcx.target;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;

    if let Some(target) = target {
        let dest_local = destination.local;
        let result = compute_slice_size_raw(ctx, args, modified_locals);
        if let Some(SliceSizeResult { adjusted_size, any_overflow }) = result {
            // Part of #3445: Handle flattened Option<usize> destinations correctly.
            // When Option<usize> is flattened, state vars are (fld0=Bool, fld1=BV64).
            // We must constrain each field individually, not as a single Datatype.
            if ctx.flatten.flattened_tuple_locals.contains(&dest_local)
                && let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local)
            {
                let mut constraints = Vec::new();

                // fld0: is_some = !any_overflow
                if let Some((out_name, out_sort)) =
                    ctx.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                {
                    let out_var = Expr::var(&*out_name, out_sort.clone());
                    let is_some = any_overflow.not();
                    ctx.push_coerced_eq_constraint(
                        &mut constraints,
                        &out_var,
                        is_some,
                        &out_sort,
                        dest_local,
                        "size_of_slice_object::is_some",
                    );
                }
                // fld1: value = adjusted_size (meaningful only when is_some=true)
                if let Some((out_name, out_sort)) =
                    ctx.state_var_mgr.output_state_vars.get(vec_idx + 1).cloned()
                {
                    let out_var = Expr::var(&*out_name, out_sort.clone());
                    ctx.push_coerced_eq_constraint(
                        &mut constraints,
                        &out_var,
                        adjusted_size,
                        &out_sort,
                        dest_local,
                        "size_of_slice_object::value",
                    );
                }

                debug!(dest_local, "SizeOfSliceObject: flattened Option (#3445)");
                let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    constraints,
                );
            } else {
                // Non-flattened: build Option<usize> Datatype and constrain as single value.
                use crate::codegen_ay::chc::stubs_option_helpers::{
                    OptionHelpers, make_option_sort,
                };
                let usize_sort = Sort::bitvec(POINTER_WIDTH);
                let option_sort = make_option_sort(&usize_sort);
                let built = ctx.make_some_expr_for_option(adjusted_size, &option_sort).and_then(
                    |some_expr| {
                        let none_expr = ctx.make_none_expr_for_option(&option_sort)?;
                        Some((some_expr, none_expr))
                    },
                );
                if let Some((some_expr, none_expr)) = built {
                    let option_expr = Expr::ite(any_overflow, none_expr, some_expr);
                    let mut extra = Vec::new();
                    if let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local) {
                        if let Some((out_name, out_sort)) =
                            ctx.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                        {
                            let out_var = Expr::var(&*out_name, out_sort);
                            extra.push(out_var.eq(option_expr));
                        }
                    }
                    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                    ctx.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        extra,
                    );
                } else {
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                }
            }
        } else {
            // Fallback: unconstrained (sound over-approximation).
            emit_sound_fallback_goto(
                ctx,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
    } else {
        ctx.record_diverging_call_drop(func, Some(bb_idx), "kani_model::SizeOfSliceObject", None);
    }
}

/// Raw size computation result for slice-tail DSTs.
///
/// Contains the decomposed `adjusted_size` and `any_overflow` flag before
/// wrapping into an Option<usize> Datatype. Used by `dispatch_size_of_slice_object`
/// to constrain either flattened or non-flattened destinations.
struct SliceSizeResult {
    adjusted_size: Expr,
    any_overflow: Expr,
}

/// Compute raw slice-tail size with overflow detection.
///
/// Implements the exact semantics from `library/kani_core/src/models.rs:498-518`:
/// ```text
/// slice_sz = elem_size * len              (checked mul)
/// total = slice_sz + head_size            (checked add)
/// adjust = total + (align - 1)            (checked add)
/// adjusted_size = adjust & align.wrapping_neg()
/// any_overflow = mul_overflow || sum_overflow || adjust_overflow || size_overflow
/// ```
///
/// Part of #3210, #3445: Returns raw components for flattened-destination support.
fn compute_slice_size_raw(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<SliceSizeResult> {
    if args.len() < 4 {
        debug!("compute_slice_size_raw: expected 4 args, got {}", args.len());
        return None;
    }

    // Translate operands to BV64 expressions.
    let len = ctx.translate_operand_with_modified(&args[0], modified_locals)?;
    let elem_size = ctx.translate_operand_with_modified(&args[1], modified_locals)?;
    let head_size = ctx.translate_operand_with_modified(&args[2], modified_locals)?;
    let align = ctx.translate_operand_with_modified(&args[3], modified_locals)?;

    let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);
    let elem_size = coerce_bitvec_width_safe(elem_size, POINTER_WIDTH, SignExtension::ZeroExtend);
    let head_size = coerce_bitvec_width_safe(head_size, POINTER_WIDTH, SignExtension::ZeroExtend);
    let align = coerce_bitvec_width_safe(align, POINTER_WIDTH, SignExtension::ZeroExtend);

    // Compute slice_sz = elem_size * len
    // Overflow check: slice_sz < elem_size (when elem_size != 0 and len != 0)
    let slice_sz = elem_size.clone().bvmul(len.clone());
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let mul_overflow = elem_size
        .clone()
        .eq(zero.clone())
        .not()
        .and(len.eq(zero.clone()).not())
        .and(slice_sz.clone().bvult(elem_size));

    // Compute total = slice_sz + head_size
    let total = slice_sz.clone().bvadd(head_size);
    let sum_overflow = total.clone().bvult(slice_sz);

    // Compute adjust = total + (align - 1)
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let align_sub_1 = align.clone().bvsub(one);
    let adjust = total.clone().bvadd(align_sub_1);
    let adjust_overflow = adjust.clone().bvult(total);

    // adjusted_size = adjust & align.wrapping_neg()
    let align_neg = zero.bvsub(align);
    let adjusted_size = adjust.bvand(align_neg);

    // isize::MAX overflow check
    let isize_max = Expr::bitvec_const(i64::MAX as u64, POINTER_WIDTH);
    let size_overflow = adjusted_size.clone().bvugt(isize_max);

    // any_overflow = mul_overflow || sum_overflow || adjust_overflow || size_overflow
    let any_overflow = mul_overflow.or(sum_overflow).or(adjust_overflow).or(size_overflow);

    Some(SliceSizeResult { adjusted_size, any_overflow })
}

/// Dispatch `KaniModel::SizeOfVal` (#3210).
pub(in crate::codegen_ay::chc) fn dispatch_size_of_val(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    dispatch_size_or_align_of_val(ctx, dcx, true);
}

/// Dispatch `KaniModel::AlignOfVal` (#3210).
pub(in crate::codegen_ay::chc) fn dispatch_align_of_val(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) {
    dispatch_size_or_align_of_val(ctx, dcx, false);
}

fn dispatch_size_or_align_of_val(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    is_size: bool,
) {
    let dest_local = dcx.destination.local;
    if let Some(target) = dcx.target {
        // Soundness (DST size_of_val overflow): `size_of_val_raw` on a slice-tail
        // fat pointer with a symbolic length is UB when `elem_size * len (+head)`
        // exceeds `isize::MAX`. The value path wraps silently; stage a hard
        // obligation that the computed size does not overflow. (size_of_dst.rs.)
        if is_size {
            emit_slice_tail_size_overflow_check(ctx, dcx);
        }
        // Try compile-time resolution (sized types, slice-tail alignment).
        let eq = resolve_pointee_layout(ctx, dcx.args, dcx.modified_locals, dest_local, is_size);
        debug!(is_size, resolved = eq.is_some(), dest_local, "dispatch_size_or_align_of_val");
        if eq.is_some() {
            let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            emit_sound_fallback_goto_extra(
                ctx,
                dcx.from_app,
                *target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
                eq,
            );
        }
    } else {
        let label = if is_size { "kani_model::SizeOfVal" } else { "kani_model::AlignOfVal" };
        ctx.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), label, None);
    }
}

pub(in crate::codegen_ay::chc) fn compute_size_or_align_value(
    ctx: &mut ChcCtx<'_, '_>,
    pointee: rustc_public::ty::Ty,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
    is_size: bool,
) -> Option<Expr> {
    if pointee.layout().is_ok() {
        let layout = LayoutOf::new(pointee);
        let layout_value = if is_size { layout.size_of() } else { layout.align_of() };
        return layout_value
            .map(|value| {
                debug!(value, pointee = %pointee, "compute_size_or_align_value: constant");
                Expr::bitvec_const(value as u128, POINTER_WIDTH)
            })
            .or_else(|| resolve_unsized_value(ctx, args, modified_locals, &layout, is_size));
    }

    let value = if is_size {
        ctx.get_type_size(pointee).map(|value| value as u128)
    } else {
        ctx.get_type_align(pointee).map(|value| value as u128)
    };
    value.map(|value| Expr::bitvec_const(value, POINTER_WIDTH))
}

/// Extract the pointee type from a pointer/reference type.
pub(in crate::codegen_ay::chc) fn extract_pointee_from_ptr_arg(
    arg_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    match arg_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
        | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(pointee),
        _ => None, // external enum: TyKind
    }
}

fn resolve_pointee_layout(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
    dest_local: usize,
    is_size: bool,
) -> Option<Expr> {
    let arg_ty = args.first()?.ty(ctx.body.locals()).ok()?;
    let pointee = extract_pointee_from_ptr_arg(arg_ty)?;
    let value_expr = compute_size_or_align_value(ctx, pointee, args, modified_locals, is_size)?;

    let vec_idx = ctx.try_state_idx_for_local(dest_local)?;
    let (out_name, out_sort) = ctx.state_var_mgr.output_state_vars.get(vec_idx)?;
    let out_sort = out_sort.clone();
    let dest_var = Expr::var(&**out_name, out_sort.clone());
    ctx.make_coerced_eq_constraint(
        &dest_var,
        value_expr,
        &out_sort,
        dest_local,
        if is_size {
            "codegen_call_kani_model::SizeOfVal"
        } else {
            "codegen_call_kani_model::AlignOfVal"
        },
    )
}

/// Runtime SizeOfVal/AlignOfVal for unsized types (dyn-trait or slice-tail).
fn resolve_unsized_value(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
    layout: &LayoutOf,
    is_size: bool,
) -> Option<Expr> {
    if layout.has_trait_tail() {
        compute_dyn_val(ctx, args, modified_locals, layout, is_size)
    } else if layout.has_slice_tail() && is_size {
        compute_slice_tail_size_val(ctx, args, modified_locals, layout)
    } else {
        None
    }
}

/// Dyn-trait SizeOfVal/AlignOfVal via vtable_type_metadata ITE (#3210 Dir 3).
fn compute_dyn_val(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
    layout: &LayoutOf,
    is_size: bool,
) -> Option<Expr> {
    if ctx.vtable_type_metadata.is_empty() {
        return None;
    }
    let vtable_disc = super::codegen_call_kani_model_dyn::extract_vtable_disc_from_ptr_arg(
        ctx,
        args,
        modified_locals,
    )?;
    let dyn_align =
        super::codegen_call_kani_model_dyn::build_vtable_metadata_ite(ctx, &vtable_disc, false);
    let head_align = Expr::bitvec_const(layout.align_of_head() as u64, POINTER_WIDTH);
    // align = max(dyn_align, head_align)
    let align = Expr::ite(dyn_align.clone().bvugt(head_align.clone()), dyn_align, head_align);

    if !is_size {
        // AlignOfVal: return the max alignment directly.
        debug!("compute_dyn_val: AlignOfVal dyn-trait resolved");
        return Some(align);
    }
    // SizeOfVal: compute aligned total = (dyn_size + head_size) rounded up to align.
    let dyn_size =
        super::codegen_call_kani_model_dyn::build_vtable_metadata_ite(ctx, &vtable_disc, true);
    let head_size = Expr::bitvec_const(layout.size_of_head() as u64, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let total = dyn_size.bvadd(head_size);
    let adjust = total.bvadd(align.clone().bvsub(one));
    let adjusted_size = adjust.bvand(zero.bvsub(align));
    debug!("compute_dyn_val: SizeOfVal dyn-trait resolved");
    Some(adjusted_size)
}

/// Slice-tail SizeOfVal: layout constants + runtime len (#3210 Dir 3).
fn compute_slice_tail_size_val(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
    layout: &LayoutOf,
) -> Option<Expr> {
    let elem_size_val = LayoutOf::new(layout.unsized_tail_elem_ty()?).size_of()? as u64;
    let head_size_val = layout.size_of_head() as u64;
    let align_val = layout.align_of()? as u64;
    let len = extract_fat_ptr_len(ctx, args, modified_locals)?;
    debug!(elem_size_val, head_size_val, align_val, "compute_slice_tail_size_val: resolved");
    let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);
    let elem_size = Expr::bitvec_const(elem_size_val, POINTER_WIDTH);
    let head_size = Expr::bitvec_const(head_size_val, POINTER_WIDTH);
    let align = Expr::bitvec_const(align_val, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    // size = round_up(elem_size * len + head_size, align)
    // NOTE: this arithmetic wraps modulo 2^64. The corresponding no-overflow
    // obligation is staged separately by `emit_slice_tail_size_overflow_check`
    // (called from `dispatch_size_or_align_of_val`), so a length that overflows
    // `isize::MAX` produces a CTREX rather than a silently-wrapped SUCCESSFUL.
    let total = elem_size.bvmul(len).bvadd(head_size);
    let adjusted_size = total.bvadd(align.clone().bvsub(one)).bvand(zero.bvsub(align));
    Some(adjusted_size)
}

/// Stage a "no unsigned overflow" obligation for slice-tail `size_of_val_raw`.
///
/// `size_of_val` on a `[T]` / `Wrapper<[T]>` fat pointer with a symbolic length
/// is UB (Rust: "failed to compute `size_of_val`") when the computed size
/// exceeds `isize::MAX`. `compute_slice_tail_size_val` produces the value as a
/// WRAPPING 64-bit bitvector, so without this obligation an overflowing length
/// verifies SUCCESSFUL. Emits an error rule for the negation of:
///   no_mul_overflow ∧ no_add_overflow ∧ no_adjust_overflow ∧ adjusted ≤ isize::MAX
/// mirroring `compute_slice_size_raw`'s overflow decomposition. Only slice-tail
/// (`has_slice_tail`) size queries are affected; sized/dyn-trait/align paths and
/// small-concrete lengths (where the obligation is trivially provable) are not.
fn emit_slice_tail_size_overflow_check(ctx: &mut ChcCtx<'_, '_>, dcx: &DispatchCallContext<'_>) {
    if !ctx.memory_safety_checks {
        return;
    }
    let Some(arg_ty) = dcx.args.first().and_then(|a| a.ty(ctx.body.locals()).ok()) else {
        return;
    };
    let Some(pointee) = extract_pointee_from_ptr_arg(arg_ty) else {
        return;
    };
    let layout = LayoutOf::new(pointee);
    if !layout.has_slice_tail() {
        return;
    }
    let Some(elem_ty) = layout.unsized_tail_elem_ty() else {
        return;
    };
    let Some(elem_size_val) = LayoutOf::new(elem_ty).size_of() else {
        return;
    };
    let Some(align_val) = layout.align_of() else {
        return;
    };
    let head_size_val = layout.size_of_head() as u64;
    let Some(len) = extract_fat_ptr_len(ctx, dcx.args, dcx.modified_locals) else {
        return;
    };
    let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);

    // ZST / zero-length elements can never overflow — nothing to prove.
    if elem_size_val == 0 {
        return;
    }

    let elem_size = Expr::bitvec_const(elem_size_val as u128, POINTER_WIDTH);
    let head_size = Expr::bitvec_const(head_size_val as u128, POINTER_WIDTH);
    let align = Expr::bitvec_const(align_val as u128, POINTER_WIDTH);
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let isize_max = Expr::bitvec_const(i64::MAX as u64, POINTER_WIDTH);

    let slice_sz = elem_size.clone().bvmul(len.clone());
    let mul_no_ovf = elem_size.bvmul_no_overflow_unsigned(len);
    let total = slice_sz.clone().bvadd(head_size);
    let add_no_ovf = total.clone().bvuge(slice_sz);
    let adjust = total.clone().bvadd(align.clone().bvsub(one));
    let adjust_no_ovf = adjust.clone().bvuge(total);
    let adjusted = adjust.bvand(zero.bvsub(align));
    let fits_isize = adjusted.bvule(isize_max);

    // Positive condition that must HOLD; the error-rule generator negates it so
    // an overflowing length reaches error() ("failed to compute size_of_val").
    let no_overflow = mul_no_ovf.and(add_no_ovf).and(adjust_no_ovf).and(fits_isize);
    debug!("CHC: staged slice-tail size_of_val overflow obligation (size_of_dst)");
    ctx.emit_error_rule_for_condition(dcx.from_app, no_overflow, dcx.stmt_constraints, dcx.bb_idx);
}

/// Extract the slice length from a fat pointer argument's CHC expression.
pub(in crate::codegen_ay::chc) fn extract_fat_ptr_len(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    modified_locals: &std::collections::HashSet<usize>,
) -> Option<Expr> {
    let operand = args.first()?;

    // Part of #4163: check subslice_len side table first.
    if let rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) = operand {
        if p.projection.is_empty() {
            if let Some(len) = ctx.ref_resolution.subslice_len.get(&p.local) {
                debug!(p.local, "extract_fat_ptr_len: resolved from subslice_len");
                return Some(len.clone());
            }
        }
    }

    // Datatype fld_len extraction (concrete, non-symbolic).
    if let Some(ptr_expr) = ctx.translate_operand_with_modified(operand, modified_locals) {
        if let Some(dt) = ptr_expr.sort().datatype_sort() {
            if dt.constructors.first().is_some_and(|c| c.has_field("fld_len")) {
                let dt_name = dt.name.clone();
                debug!("extract_fat_ptr_len: resolved from datatype fld_len");
                return Some(ptr_expr.field_select(
                    &dt_name,
                    "fld_len",
                    Sort::bitvec(POINTER_WIDTH),
                ));
            }
        }
    }

    // Part of #4163: MIR trace before BV128 — precise metadata for array-loaded fat ptrs.
    if let Some(len) = ctx.translate_ptr_metadata(operand, modified_locals) {
        debug!("extract_fat_ptr_len: resolved from translate_ptr_metadata");
        return Some(len);
    }

    // BV128 fat pointer high-bits extraction as last resort.
    if let Some(ptr_expr) = ctx.translate_operand_with_modified(operand, modified_locals) {
        if ptr_expr.sort().bitvec_width() == Some(128) {
            debug!("extract_fat_ptr_len: resolved from BV128 extraction");
            return Some(ptr_expr.extract(127, 64));
        }
    }

    debug!("extract_fat_ptr_len: FAILED to resolve fat pointer length");
    None
}

/// Check if a type is zero-sized (unit, never, zero-length arrays, ZST element arrays).
/// Used by `KaniModel::Any`/`KaniHook::AnyRaw` to avoid spurious nondeterminism.
pub(in crate::codegen_ay::chc) fn is_zst_ty(ty: rustc_public::ty::Ty) -> bool {
    if ty
        .layout()
        .ok()
        .is_some_and(|layout| layout.shape().is_sized() && layout.shape().size.bytes() == 0)
    {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => true,
        TyKind::RigidTy(RigidTy::Never) => true,
        TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
            if len.eval_target_usize().ok() == Some(0) {
                return true;
            }
            is_zst_ty(elem_ty)
        }
        _ => false, // external enum: TyKind
    }
}

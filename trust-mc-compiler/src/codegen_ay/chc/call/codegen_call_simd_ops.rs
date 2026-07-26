// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SIMD intrinsic handler implementations for CHC code generation (Part of #3441).

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, BinOp};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

mod safety_checks;
mod select;
use safety_checks::{
    emit_simd_arith_overflow_checks, emit_simd_shift_safety_checks, emit_simd_shuffle_index_checks,
};
use select::build_ite_select;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_simd::{
    SimdIntrinsicKind, SimdLayoutInfo, coerce_to_pointer_width, emit_simd_dest_constraint,
    emit_simd_sound_fallback, extract_simd_layout, neutral_simd_result_array_like,
    resolve_simd_array,
};
use crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::{
    division_by_zero_condition, signed_div_overflow_condition,
};
use crate::codegen_ay::float_arithmetic::bv_float_binop_chc;
use crate::codegen_ay::float_compare::{bv_float_gt, bv_float_lt};
use crate::codegen_ay::types::POINTER_WIDTH;

/// Element-wise binary op handler (add, sub, mul, div, rem, and, or, xor).
pub(in crate::codegen_ay::chc) fn codegen_simd_elementwise_binop(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: SimdIntrinsicKind,
) {
    let dest_local: usize = dcx.destination.local;

    let lhs_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let rhs_arr = resolve_simd_array(ctx, &dcx.args[1], dcx.modified_locals);

    let layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));

    if let (Some(lhs), Some(rhs), Some(layout)) = (lhs_arr, rhs_arr, layout) {
        // Part of the UB-soundness fixes: emit per-lane divide-by-zero and signed
        // INT_MIN/-1 overflow error rules for simd_div / simd_rem. These are pure
        // per-lane BV predicates identical to the scalar div/rem checks and carry
        // no memory-model dependency. Emitted regardless of whether the result
        // encodes precisely so the UB is caught even on the sound-fallback path.
        emit_simd_div_rem_safety_checks(ctx, dcx, &lhs, &rhs, &layout, kind);
        // Part of the UB-soundness fixes: emit per-lane arithmetic overflow
        // error rules for simd_add / simd_sub / simd_mul. Kani reports these as
        // "attempt to compute simd_<op> which would overflow" — the SIMD path
        // must mirror the scalar overflow check (gated by overflow_checks) so a
        // program that can overflow any lane is never proved safe.
        emit_simd_arith_overflow_checks(ctx, dcx, &lhs, &rhs, &layout, kind);

        if let Some(result) = build_elementwise_result(Some(ctx), &lhs, &rhs, &layout, kind) {
            emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
        } else {
            debug!("CHC simd binop: symbolic float lane not soundly encodable, sound fallback");
            emit_simd_sound_fallback(ctx, dcx, target);
        }
    } else {
        debug!("CHC simd binop: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Emit per-lane divide-by-zero and signed INT_MIN/-1 overflow safety error
/// rules for `simd_div` / `simd_rem`.
///
/// Integer lanes only — floating-point division by zero is well-defined
/// (produces ±inf/NaN), so float lanes are skipped. For each integer lane the
/// divisor-nonzero predicate `b != 0` is emitted (unless the divisor lane is a
/// nonzero `BitVecConst`, in which case the check is trivially satisfiable and
/// skipped), and for signed lanes the `!(a == INT_MIN && b == -1)` predicate is
/// emitted. Both reuse the scalar div/rem predicates so the SIMD and scalar
/// paths cannot drift.
fn emit_simd_div_rem_safety_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    lhs: &Expr,
    rhs: &Expr,
    layout: &SimdLayoutInfo,
    kind: SimdIntrinsicKind,
) {
    if layout.is_float || !matches!(kind, SimdIntrinsicKind::Div | SimdIntrinsicKind::Rem) {
        return;
    }
    for i in 0..layout.lane_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let a = lhs.clone().select(idx.clone());
        let b = rhs.clone().select(idx);
        // Divide-by-zero: divisor lane must be nonzero. Skip only when the
        // divisor lane is a proven-nonzero constant.
        // Kani parity: CBMC reports this class as "division by zero" — the
        // DivisionByZero kind text supplies exactly that Description line.
        if !is_nonzero_bitvec_const(&b)
            && let Some(nonzero) = division_by_zero_condition(&b)
        {
            ctx.emit_error_rule_for_condition_with_kind(
                dcx.from_app,
                nonzero,
                dcx.stmt_constraints,
                dcx.bb_idx,
                PropertyKind::DivisionByZero,
                None,
            );
        }
        // Signed overflow: INT_MIN / -1. Constant-folds to trivially-true (and is
        // skipped by emit_error_rule_for_condition) when operands are constants.
        // Kani parity: Kani's simd overflow check text is
        // "attempt to compute {intrinsic} which would overflow".
        if layout.is_signed
            && let Some(no_overflow) = signed_div_overflow_condition(&a, &b)
        {
            let intrinsic_name = match kind {
                SimdIntrinsicKind::Div => "simd_div",
                _ => "simd_rem",
            };
            ctx.emit_error_rule_for_condition_with_kind(
                dcx.from_app,
                no_overflow,
                dcx.stmt_constraints,
                dcx.bb_idx,
                PropertyKind::ArithmeticOverflow,
                Some(format!("attempt to compute {intrinsic_name} which would overflow")),
            );
        }
    }
}

/// Returns `true` when `expr` is a `BitVecConst` proven to be nonzero.
///
/// A constant that does not fit in `u64` (very large or negative bit pattern)
/// is necessarily a nonzero value, so a failed `try_from` counts as nonzero.
/// Only an exact zero constant returns `false`.
fn is_nonzero_bitvec_const(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value) != Ok(0u64),
        _ => false,
    }
}

/// Shift handler (shl, shr). shr uses bvashr for signed, bvlshr for unsigned.
pub(in crate::codegen_ay::chc) fn codegen_simd_shift(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: SimdIntrinsicKind,
) {
    let dest_local: usize = dcx.destination.local;

    let lhs_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let rhs_arr = resolve_simd_array(ctx, &dcx.args[1], dcx.modified_locals);

    let layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));

    if let (Some(lhs), Some(rhs), Some(layout)) = (lhs_arr, rhs_arr, layout) {
        // Part of the UB-soundness fixes: emit per-lane shift-distance error
        // rules for simd_shl / simd_shr. Kani reports UB when any lane's shift
        // amount is >= the lane bit-width or (signed shift amount) is negative.
        // Reuses the scalar shift-distance predicate so the SIMD and scalar
        // paths cannot drift.
        emit_simd_shift_safety_checks(ctx, dcx, &lhs, &rhs, &layout);

        let mut result =
            neutral_simd_result_array_like(&lhs, layout.elem_width).unwrap_or_else(|| lhs.clone());
        for i in 0..layout.lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let a = lhs.clone().select(idx.clone());
            let b = rhs.clone().select(idx.clone());
            let val = match kind {
                SimdIntrinsicKind::Shl => a.bvshl(b),
                SimdIntrinsicKind::Shr if layout.is_signed => a.bvashr(b),
                SimdIntrinsicKind::Shr => a.bvlshr(b),
                _ => unreachable!(),
            };
            result = result.store(idx, val);
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd shift: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Comparison handler (eq, ne, lt, le, gt, ge). Returns SIMD mask (all-ones/-zeros).
pub(in crate::codegen_ay::chc) fn codegen_simd_comparison(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: SimdIntrinsicKind,
) {
    let dest_local: usize = dcx.destination.local;

    let lhs_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let rhs_arr = resolve_simd_array(ctx, &dcx.args[1], dcx.modified_locals);

    let src_layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));
    // Part of #3453: mask width from destination type (cross-type comparisons).
    let dest_ty = ctx.body.locals()[dest_local].ty;
    let dest_layout = extract_simd_layout(dest_ty);

    if let (Some(lhs), Some(rhs), Some(src_ly), Some(dest_ly)) =
        (lhs_arr, rhs_arr, src_layout, dest_layout)
    {
        let mask_width = dest_ly.elem_width;
        let all_ones = if mask_width >= 128 {
            // Part of #3453: overflow-safe
            Expr::bitvec_const(u128::MAX, mask_width)
        } else {
            Expr::bitvec_const((1u128 << mask_width) - 1, mask_width)
        };
        let all_zeros = Expr::bitvec_const(0u64, mask_width);
        let lane_count = src_ly.lane_count.min(dest_ly.lane_count);

        // Build result array with destination element sort for correct mask width.
        let idx_sort = Sort::bitvec(POINTER_WIDTH);
        let mut result = Expr::const_array(idx_sort, all_zeros.clone());
        for i in 0..lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let a = lhs.clone().select(idx.clone());
            let b = rhs.clone().select(idx.clone());
            let cmp = apply_simd_comparison(
                &a,
                &b,
                kind,
                src_ly.is_signed,
                src_ly.is_float,
                src_ly.elem_width,
            );
            let val = Expr::ite(cmp, all_ones.clone(), all_zeros.clone());
            result = result.store(idx, val);
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd comparison: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Extract a single element: `simd_extract(vec, idx)` → `vec[idx]`.
pub(in crate::codegen_ay::chc) fn codegen_simd_extract(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    let vec_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let idx_expr = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);

    if let (Some(arr), Some(idx)) = (vec_arr, idx_expr) {
        let idx = coerce_to_pointer_width(&idx);
        let elem = arr.select(idx);
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, elem);
    } else {
        debug!("CHC simd extract: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Insert a single element: `simd_insert(vec, idx, val)` → `vec[idx] = val`.
pub(in crate::codegen_ay::chc) fn codegen_simd_insert(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    let vec_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let idx_expr = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);
    let val_expr = ctx.translate_operand_with_modified(&dcx.args[2], dcx.modified_locals);
    let layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));

    if let (Some(arr), Some(idx), Some(val), Some(layout)) = (vec_arr, idx_expr, val_expr, layout) {
        let idx = coerce_to_pointer_width(&idx);
        // Part of #4212: coerce value to match array element sort before store.
        let val = ChcCtx::coerce_store_value(arr.sort(), val, false, &ctx.diagnostics);
        let result = build_insert_result(&arr, &idx, &val, &layout);
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd insert: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Reduce a SIMD vector to a scalar via fold (Add/Mul/And/Or/Xor/Min/Max).
pub(in crate::codegen_ay::chc) fn codegen_simd_reduce(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: SimdIntrinsicKind,
) {
    let dest_local: usize = dcx.destination.local;

    let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));

    if let (Some(arr), Some(layout)) = (src_arr, layout) {
        let elements: Vec<Expr> = (0..layout.lane_count)
            .map(|i| arr.clone().select(Expr::bitvec_const(i as u64, POINTER_WIDTH)))
            .collect();

        if elements.is_empty() {
            debug!("CHC simd reduce: empty lane count, sound fallback");
            emit_simd_sound_fallback(ctx, dcx, target);
            return;
        }

        let mut result = Some(elements[0].clone());
        for elem in &elements[1..] {
            result = result.and_then(|acc| {
                apply_simd_reduce_op(
                    acc,
                    elem.clone(),
                    kind,
                    layout.is_signed,
                    layout.is_float,
                    layout.elem_width,
                )
            });
            if result.is_none() {
                break;
            }
        }
        if let Some(result) = result {
            emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
        } else {
            debug!("CHC simd reduce: symbolic float lane not soundly encodable, sound fallback");
            emit_simd_sound_fallback(ctx, dcx, target);
        }
    } else {
        debug!("CHC simd reduce: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Reduce SIMD vector to Bool: `all` (all non-zero) or `any` (any non-zero).
pub(in crate::codegen_ay::chc) fn codegen_simd_reduce_bool(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    is_all: bool,
) {
    let dest_local: usize = dcx.destination.local;
    let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));
    if let (Some(arr), Some(layout)) = (src_arr, layout) {
        let zero = Expr::bitvec_const(0u64, layout.elem_width);
        let mut result = if is_all { Expr::bool_const(true) } else { Expr::bool_const(false) };

        for i in 0..layout.lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let elem = arr.clone().select(idx);
            let is_nonzero = elem.eq(zero.clone()).not();
            result = if is_all { result.and(is_nonzero) } else { result.or(is_nonzero) };
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd reduce_bool: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Shuffle elements from two SIMD vectors: `result[i] = (a++b)[idx[i]]`.
pub(in crate::codegen_ay::chc) fn codegen_simd_shuffle(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    if dcx.args.len() < 3 {
        debug!("CHC simd shuffle: expected 3 args, got {}", dcx.args.len());
        emit_simd_sound_fallback(ctx, dcx, target);
        return;
    }

    let a_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let b_arr = resolve_simd_array(ctx, &dcx.args[1], dcx.modified_locals);
    let idx_arr = resolve_simd_array(ctx, &dcx.args[2], dcx.modified_locals);
    let src_layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));
    let dest_ty = ctx.body.locals()[dest_local].ty;
    let dest_layout = extract_simd_layout(dest_ty);

    if let (Some(a), Some(b), Some(idx), Some(src_ly), Some(dest_ly)) =
        (a_arr, b_arr, idx_arr, src_layout, dest_layout)
    {
        let combined_len = src_ly.lane_count * 2;
        // Part of the UB-soundness fixes: emit per-output-lane bounds error
        // rules for simd_shuffle. Each shuffle index must be < 2 * src_len
        // (the combined length of the two input vectors); an index >= that is
        // UB (Kani: "index out of bounds").
        emit_simd_shuffle_index_checks(ctx, dcx, &idx, dest_ly.lane_count, combined_len);

        let combined: Vec<Expr> = (0..combined_len)
            .map(|i| {
                let (arr, offset) =
                    if i < src_ly.lane_count { (&a, i) } else { (&b, i - src_ly.lane_count) };
                arr.clone().select(Expr::bitvec_const(offset as u64, POINTER_WIDTH))
            })
            .collect();

        let mut result = Expr::const_array(
            Sort::bitvec(POINTER_WIDTH),
            Expr::bitvec_const(0u64, dest_ly.elem_width),
        );
        for i in 0..dest_ly.lane_count {
            let out_idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let sel_idx = idx.clone().select(out_idx.clone());
            let val = build_ite_select(&combined, &sel_idx);
            result = result.store(out_idx, val);
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd shuffle: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Cast each SIMD element to a different width (identity/extend/truncate).
pub(in crate::codegen_ay::chc) fn codegen_simd_cast(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let src_layout = dcx.args.first().and_then(|op| operand_ty_layout(ctx, op));
    let dest_ty = ctx.body.locals()[dest_local].ty;
    let dest_layout = extract_simd_layout(dest_ty);
    if let (Some(arr), Some(src_ly), Some(dest_ly)) = (src_arr, src_layout, dest_layout) {
        let lane_count = src_ly.lane_count.min(dest_ly.lane_count);
        // Build a fresh result array with the destination element sort.
        // Use const_array so the result array has correct (BV_idx -> BV_dest_elem) sort.
        let idx_sort = Sort::bitvec(POINTER_WIDTH);
        let mut result = Expr::const_array(idx_sort, Expr::bitvec_const(0u64, dest_ly.elem_width));

        for i in 0..lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let elem = arr.clone().select(idx.clone());
            let converted = if src_ly.elem_width == dest_ly.elem_width {
                elem
            } else if dest_ly.elem_width > src_ly.elem_width {
                let extend_by = dest_ly.elem_width - src_ly.elem_width;
                if src_ly.is_signed {
                    elem.sign_extend(extend_by)
                } else {
                    elem.zero_extend(extend_by)
                }
            } else {
                elem.extract(dest_ly.elem_width - 1, 0)
            };
            result = result.store(idx, converted);
        }
        // Wrap in destination Datatype if needed
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd cast: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Build the result array by applying a binary operation element-wise.
///
/// Returns `None` when any lane cannot be soundly encoded (currently only
/// symbolic float lanes — see `apply_simd_binop`). The caller is expected
/// to fall back to `emit_simd_sound_fallback`.
fn build_elementwise_result(
    ctx: Option<&ChcCtx<'_, '_>>,
    lhs: &Expr,
    rhs: &Expr,
    layout: &SimdLayoutInfo,
    kind: SimdIntrinsicKind,
) -> Option<Expr> {
    let mut result =
        neutral_simd_result_array_like(lhs, layout.elem_width).unwrap_or_else(|| lhs.clone());
    for i in 0..layout.lane_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let a = lhs.clone().select(idx.clone());
        let b = rhs.clone().select(idx.clone());
        let val = apply_simd_binop(ctx, a, b, kind, layout)?;
        result = result.store(idx, val);
    }
    Some(result)
}

/// Build the finite SIMD result for `simd_insert`.
///
/// Rust SIMD vectors have a fixed finite lane set; rooting the SMT array at a
/// neutral const-array and explicitly storing every lane keeps scalarization
/// independent of the infinite-array background value.
fn build_insert_result(arr: &Expr, idx: &Expr, val: &Expr, layout: &SimdLayoutInfo) -> Expr {
    let mut result =
        neutral_simd_result_array_like(arr, layout.elem_width).unwrap_or_else(|| arr.clone());
    for i in 0..layout.lane_count {
        let lane_idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let old_lane = arr.clone().select(lane_idx.clone());
        let lane_value = if idx == &lane_idx {
            val.clone()
        } else if bitvec_consts_distinct(idx, &lane_idx) {
            old_lane
        } else {
            Expr::ite(idx.clone().eq(lane_idx.clone()), val.clone(), old_lane)
        };
        result = result.store(lane_idx, lane_value);
    }
    result
}

fn bitvec_consts_distinct(lhs: &Expr, rhs: &Expr) -> bool {
    match (lhs.value(), rhs.value()) {
        (
            ExprValue::BitVecConst { value: lhs_value, width: lhs_width },
            ExprValue::BitVecConst { value: rhs_value, width: rhs_width },
        ) => lhs_width == rhs_width && lhs_value != rhs_value,
        _ => false,
    }
}

/// Apply element-wise SIMD binary op. Part of #3857/#3870: float lanes use
/// pure-BV encoding for comparisons and constant-folded arithmetic.
///
/// Symbolic float lanes route through the CONGRUENT float-binop table
/// (`float_binop_chc_term`) — the same single entry point the scalar float
/// path uses — so `assert_eq!(scalar_op, simd_op)` becomes an equality of
/// structurally identical table selects and static-discharges (FastMath #54
/// precedent). Returns `None` only when the table lane is unavailable
/// (undeclared width / int-lift); the caller falls back to
/// `emit_simd_sound_fallback`. Part of ay#6370.
fn apply_simd_binop(
    ctx: Option<&ChcCtx<'_, '_>>,
    a: Expr,
    b: Expr,
    kind: SimdIntrinsicKind,
    layout: &SimdLayoutInfo,
) -> Option<Expr> {
    if layout.is_float {
        let ctx = ctx?;
        let mir_op = match kind {
            SimdIntrinsicKind::Add => Some(BinOp::Add),
            SimdIntrinsicKind::Sub => Some(BinOp::Sub),
            SimdIntrinsicKind::Mul => Some(BinOp::Mul),
            SimdIntrinsicKind::Div => Some(BinOp::Div),
            SimdIntrinsicKind::Rem => Some(BinOp::Rem),
            _ => None,
        };
        // Float lane: constant fold, else the congruent table term (both via
        // float_binop_chc_term — identical key construction to the scalar site).
        return mir_op.and_then(|op| ctx.float_binop_chc_term(op, a, b, layout.elem_width));
    }
    Some(match kind {
        SimdIntrinsicKind::Add => a.bvadd(b),
        SimdIntrinsicKind::Sub => a.bvsub(b),
        SimdIntrinsicKind::Mul => a.bvmul(b),
        SimdIntrinsicKind::Div if layout.is_signed => a.bvsdiv(b),
        SimdIntrinsicKind::Div => a.bvudiv(b),
        SimdIntrinsicKind::Rem if layout.is_signed => a.bvsrem(b),
        SimdIntrinsicKind::Rem => a.bvurem(b),
        SimdIntrinsicKind::And => a.bvand(b),
        SimdIntrinsicKind::Or => a.bvor(b),
        SimdIntrinsicKind::Xor => a.bvxor(b),
        _ => unreachable!("apply_simd_binop called with non-binop kind: {:?}", kind),
    })
}

/// Apply BV comparison for a SIMD comparison op. Float lanes use IEEE-754-aware
/// comparison (bv_float_eq, etc.) for correct NaN/-0.0 handling (Part of #3768).
fn apply_simd_comparison(
    a: &Expr,
    b: &Expr,
    kind: SimdIntrinsicKind,
    is_signed: bool,
    is_float: bool,
    elem_width: u32,
) -> Expr {
    use crate::codegen_ay::float_compare::{
        bv_float_eq, bv_float_ge, bv_float_gt, bv_float_le, bv_float_lt, bv_float_ne,
    };
    if is_float {
        return match kind {
            SimdIntrinsicKind::Eq => bv_float_eq(a, b, elem_width),
            SimdIntrinsicKind::Ne => bv_float_ne(a, b, elem_width),
            SimdIntrinsicKind::Lt => bv_float_lt(a, b, elem_width),
            SimdIntrinsicKind::Le => bv_float_le(a, b, elem_width),
            SimdIntrinsicKind::Gt => bv_float_gt(a, b, elem_width),
            SimdIntrinsicKind::Ge => bv_float_ge(a, b, elem_width),
            _ => unreachable!("apply_simd_comparison called with non-cmp kind: {:?}", kind),
        };
    }
    match kind {
        SimdIntrinsicKind::Eq => a.clone().eq(b.clone()),
        SimdIntrinsicKind::Ne => a.clone().ne(b.clone()),
        SimdIntrinsicKind::Lt if is_signed => a.clone().bvslt(b.clone()),
        SimdIntrinsicKind::Lt => a.clone().bvult(b.clone()),
        SimdIntrinsicKind::Le if is_signed => a.clone().bvsle(b.clone()),
        SimdIntrinsicKind::Le => a.clone().bvule(b.clone()),
        SimdIntrinsicKind::Gt if is_signed => a.clone().bvsgt(b.clone()),
        SimdIntrinsicKind::Gt => a.clone().bvugt(b.clone()),
        SimdIntrinsicKind::Ge if is_signed => a.clone().bvsge(b.clone()),
        SimdIntrinsicKind::Ge => a.clone().bvuge(b.clone()),
        _ => unreachable!("apply_simd_comparison called with non-cmp kind: {:?}", kind),
    }
}

/// Extract SIMD layout from an operand's type.
fn operand_ty_layout(
    ctx: &ChcCtx<'_, '_>,
    operand: &rustc_public::mir::Operand,
) -> Option<SimdLayoutInfo> {
    let ty = operand.ty(ctx.body.locals()).ok()?;
    extract_simd_layout(ty)
}

/// Apply a reduce fold operation: `acc op elem`.
///
/// Returns `None` when the lane is float and `bv_float_binop_chc` cannot
/// constant-fold — falling back to integer BV ops on IEEE 754 bit patterns
/// would be unsound. The caller is expected to fall back to
/// `emit_simd_sound_fallback`. Part of ay#6370.
/// Part of #3882: float lanes route through IEEE-754-aware BV helpers.
fn apply_simd_reduce_op(
    acc: Expr,
    elem: Expr,
    kind: SimdIntrinsicKind,
    is_signed: bool,
    is_float: bool,
    elem_width: u32,
) -> Option<Expr> {
    Some(match kind {
        SimdIntrinsicKind::ReduceAdd if is_float => {
            bv_float_binop_chc(BinOp::Add, acc, elem, elem_width)?
        }
        SimdIntrinsicKind::ReduceAdd => acc.bvadd(elem),
        SimdIntrinsicKind::ReduceMul if is_float => {
            bv_float_binop_chc(BinOp::Mul, acc, elem, elem_width)?
        }
        SimdIntrinsicKind::ReduceMul => acc.bvmul(elem),
        SimdIntrinsicKind::ReduceAnd => acc.bvand(elem),
        SimdIntrinsicKind::ReduceOr => acc.bvor(elem),
        SimdIntrinsicKind::ReduceXor => acc.bvxor(elem),
        SimdIntrinsicKind::ReduceMin | SimdIntrinsicKind::ReduceMax => {
            let is_min = matches!(kind, SimdIntrinsicKind::ReduceMin);
            let cmp = if is_float {
                if is_min {
                    bv_float_lt(&acc, &elem, elem_width)
                } else {
                    bv_float_gt(&acc, &elem, elem_width)
                }
            } else if is_signed {
                if is_min {
                    acc.clone().bvslt(elem.clone())
                } else {
                    acc.clone().bvsgt(elem.clone())
                }
            } else if is_min {
                acc.clone().bvult(elem.clone())
            } else {
                acc.clone().bvugt(elem.clone())
            };
            Expr::ite(cmp, acc, elem)
        }
        _ => unreachable!("apply_simd_reduce_op: unexpected kind {:?}", kind),
    })
}

#[cfg(test)]
mod tests;

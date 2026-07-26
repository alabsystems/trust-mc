// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-lane undefined-behavior safety checks for SIMD intrinsics (CHC path).
//!
//! trust-mc previously lowered `simd_shl`/`simd_shr`/`simd_shuffle` and the
//! SIMD arithmetic intrinsics (`simd_add`/`simd_sub`/`simd_mul`) but emitted no
//! UB checks, so an intentionally-buggy SIMD harness (excessive/negative shift
//! distance, out-of-bounds shuffle index, arithmetic overflow) was proved
//! SUCCESSFUL — a soundness bug. These helpers emit the analogous per-lane
//! error rules Kani reports, reusing the exact scalar predicates so the SIMD
//! and scalar paths cannot drift. Each error rule is `from ∧ constraints ∧
//! ¬valid → error()`, so a violable lane makes the aggregate `error` reachable
//! and the harness reports FAILED instead of SUCCESSFUL.

use ay_bindings::Expr;
use rustc_public::mir::BinOp;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_simd::{SimdIntrinsicKind, SimdLayoutInfo};
use super::ChcCtx;
use crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::unchecked_shift_distance_condition;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Emit per-lane arithmetic-overflow error rules for `simd_add` / `simd_sub` /
/// `simd_mul`.
///
/// Kani reports a hard failure ("attempt to compute simd_<op> which would
/// overflow") when any lane of a SIMD add/sub/mul overflows its lane width.
/// This mirrors the scalar unchecked-overflow predicate ([`ChcCtx::
/// unchecked_overflow_condition`]) applied lane-by-lane, so the SIMD and scalar
/// paths cannot drift. Gated by `overflow_checks` exactly like the scalar path.
/// Integer lanes only — floating-point add/sub/mul do not have overflow UB.
pub(super) fn emit_simd_arith_overflow_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    lhs: &Expr,
    rhs: &Expr,
    layout: &SimdLayoutInfo,
    kind: SimdIntrinsicKind,
) {
    if !ctx.overflow_checks || layout.is_float {
        return;
    }
    let op = match kind {
        SimdIntrinsicKind::Add => BinOp::AddUnchecked,
        SimdIntrinsicKind::Sub => BinOp::SubUnchecked,
        SimdIntrinsicKind::Mul => BinOp::MulUnchecked,
        _ => return,
    };
    for i in 0..layout.lane_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let a = lhs.clone().select(idx.clone());
        let b = rhs.clone().select(idx);
        if let Some(no_overflow) =
            ChcCtx::unchecked_overflow_condition(op, &a, &b, layout.is_signed)
        {
            ctx.emit_error_rule_for_condition(
                dcx.from_app,
                no_overflow,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
        }
    }
}

/// Emit per-lane shift-distance error rules for `simd_shl` / `simd_shr`.
///
/// Kani reports UB ("attempt to simd_<op> with excessive / negative shift
/// distance") when any lane's shift amount is `>=` the lane bit-width or, for a
/// signed shift amount, is negative. For `simd_shl`/`simd_shr` both operands
/// share the lane type `T`, so the shift-amount signedness equals
/// `layout.is_signed`. Reuses the scalar shift-distance predicate and is gated
/// by `overflow_checks` to match the scalar `ShlUnchecked`/`ShrUnchecked` path.
pub(super) fn emit_simd_shift_safety_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    lhs: &Expr,
    rhs: &Expr,
    layout: &SimdLayoutInfo,
) {
    if !ctx.overflow_checks {
        return;
    }
    for i in 0..layout.lane_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let a = lhs.clone().select(idx.clone());
        let b = rhs.clone().select(idx);
        if let Some(valid) = unchecked_shift_distance_condition(&a, &b, layout.is_signed) {
            ctx.emit_error_rule_for_condition(
                dcx.from_app,
                valid,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
        }
    }
}

/// Emit per-output-lane index-bounds error rules for `simd_shuffle`.
///
/// Each shuffle index selects from the concatenation of the two input vectors,
/// so a valid index is `< 2 * src_len` (`combined_len`). An index `>=` that is
/// UB (Kani: "index out of bounds: the length is less than or equal to the
/// given index"). Shuffle indices are unsigned, so only the upper bound is
/// checked. Not gated by `overflow_checks`: an out-of-bounds shuffle is a
/// memory-safety violation, always checked (mirrors the div-by-zero handling).
pub(super) fn emit_simd_shuffle_index_checks(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    idx_arr: &Expr,
    dest_lane_count: usize,
    combined_len: usize,
) {
    for i in 0..dest_lane_count {
        let out_idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let sel = idx_arr.clone().select(out_idx);
        if let Some(valid) = shuffle_index_in_bounds_condition(&sel, combined_len) {
            ctx.emit_error_rule_for_condition(
                dcx.from_app,
                valid,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
        }
    }
}

/// Build the "shuffle index in bounds" predicate: `index < combined_len`.
///
/// Returns `None` if the selector is not a bit-vector (should not happen for a
/// well-typed shuffle index array).
pub(super) fn shuffle_index_in_bounds_condition(sel: &Expr, combined_len: usize) -> Option<Expr> {
    let width = sel.sort().bitvec_width()?;
    let bound = Expr::bitvec_const(combined_len as u128, width);
    Some(sel.clone().bvult(bound))
}

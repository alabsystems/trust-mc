// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bitvector width coercion and overflow helpers for CHC arithmetic encoding.
//!
//! Extracted from `codegen_stmt_arithmetic.rs` per #4130.
//!
//! Contains: coerce_shift_amount, coerce_eq_operands, coerce_arithmetic_operands,
//! coerce_bitwise_operands, unchecked_overflow_condition.

use ay_bindings::Expr;
use rustc_public::mir::BinOp;

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Coerce a bitvector shift amount to the target width.
    ///
    /// - If narrower: zero-extend to target width
    /// - If wider: truncate to target width (extract low bits)
    /// - If same width: return unchanged
    ///
    /// This is needed because MIR allows different-width shift operands (e.g., `u64 << u32`)
    /// but SMT-LIB requires same-width operands for bvshl/bvlshr/bvashr.
    ///
    /// Part of #729: BigInt CHC tests panic on bvlshr width mismatch.
    ///
    /// REQUIRES: expr.sort().is_bitvec() (returns expr unchanged if not)
    #[must_use]
    pub(in crate::codegen_ay::chc) fn coerce_shift_amount(expr: Expr, target_width: u32) -> Expr {
        // Delegate to shared implementation with defensive handling and unsigned semantics
        coerce_bitvec_width_safe(expr, target_width, SignExtension::ZeroExtend)
    }

    /// Coerce operands for equality/inequality comparisons.
    ///
    /// Handles Bool↔BV mismatches that arise from flattened enum locals (e.g.,
    /// a Bool discriminant compared against a BV1 value) and BV width mismatches
    /// (e.g., BV32 vs BV64 from different-width locals).
    ///
    /// Part of #2244: Sort mismatch panics in BinOp::Eq/Ne after flattening.
    pub(in crate::codegen_ay::chc) fn coerce_eq_operands(
        lhs: Expr,
        rhs: Expr,
        signed: bool,
    ) -> (Expr, Expr) {
        let lhs = crate::codegen_ay::types::unwrap_single_field_datatype(&lhs).unwrap_or(lhs);
        let rhs = crate::codegen_ay::types::unwrap_single_field_datatype(&rhs).unwrap_or(rhs);
        let lhs_sort = lhs.sort().clone();
        let rhs_sort = rhs.sort().clone();

        // Same sort — no coercion needed
        if lhs_sort == rhs_sort {
            return (lhs, rhs);
        }

        // Bool vs BV: coerce_bitvec_width_safe handles Bool→BV directly
        let (lhs, rhs) = match (lhs_sort.is_bool(), rhs_sort.is_bool()) {
            (true, false) if rhs_sort.is_bitvec() => match rhs_sort.bitvec_width() {
                Some(target_width) => {
                    (coerce_bitvec_width_safe(lhs, target_width, SignExtension::ZeroExtend), rhs)
                }
                None => (lhs, rhs),
            },
            (false, true) if lhs_sort.is_bitvec() => match lhs_sort.bitvec_width() {
                Some(target_width) => {
                    (lhs, coerce_bitvec_width_safe(rhs, target_width, SignExtension::ZeroExtend))
                }
                None => (lhs, rhs),
            },
            _ => (lhs, rhs), // non-enum: tuple (Option<u32>, Option<u32>)
        };

        // BV width mismatch: coerce to max width, respecting signedness
        let lhs_width = lhs.sort().bitvec_width();
        let rhs_width = rhs.sort().bitvec_width();
        let ext = SignExtension::for_signedness(signed);
        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) if lw != rw => {
                let max_width = lw.max(rw);
                let lhs_coerced = coerce_bitvec_width_safe(lhs, max_width, ext);
                let rhs_coerced = coerce_bitvec_width_safe(rhs, max_width, ext);
                (lhs_coerced, rhs_coerced)
            }
            _ => (lhs, rhs), // non-enum: tuple (Option<u32>, Option<u32>)
        }
    }

    /// Coerce bitvector operands to the same width for arithmetic and comparison operations.
    ///
    /// ay_bindings requires identical-width operands for bvadd/bvsub/bvmul/bvdiv/bvrem and
    /// comparison ops (bvslt, bvult, etc.). This coerces both operands to max(lhs_width,
    /// rhs_width) using sign- or zero-extension.
    ///
    /// Part of #2007: BigInt CHC crash from mixed-width arithmetic operands.
    pub(in crate::codegen_ay::chc) fn coerce_arithmetic_operands(
        lhs: Expr,
        rhs: Expr,
        signed: bool,
    ) -> (Expr, Expr) {
        let lhs_width = lhs.sort().bitvec_width();
        let rhs_width = rhs.sort().bitvec_width();
        let ext = SignExtension::for_signedness(signed);
        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) if lw == rw => (lhs, rhs),
            (Some(lw), Some(rw)) => {
                let max_width = lw.max(rw);
                let lhs_coerced = coerce_bitvec_width_safe(lhs, max_width, ext);
                let rhs_coerced = coerce_bitvec_width_safe(rhs, max_width, ext);
                (lhs_coerced, rhs_coerced)
            }
            _ => (lhs, rhs), // non-enum: tuple (Option<u32>, Option<u32>) — non-bitvec passthrough
        }
    }

    /// Coerce bitvector operands to the same width for bitwise operations.
    ///
    /// ay_bindings requires identical-width operands for bvand/bvor/bvxor.
    /// This coerces both operands to max(lhs_width, rhs_width) using sign- or zero-extension.
    ///
    /// Part of #1894: CHC bitwise ops lack width coercion.
    pub(in crate::codegen_ay::chc) fn coerce_bitwise_operands(
        lhs: Expr,
        rhs: Expr,
        signed: bool,
    ) -> (Expr, Expr) {
        let lhs_width = lhs.sort().bitvec_width();
        let rhs_width = rhs.sort().bitvec_width();
        let ext = SignExtension::for_signedness(signed);
        match (lhs_width, rhs_width) {
            (Some(lw), Some(rw)) if lw == rw => (lhs, rhs),
            (Some(lw), Some(rw)) => {
                let max_width = lw.max(rw);
                let lhs_coerced = coerce_bitvec_width_safe(lhs, max_width, ext);
                let rhs_coerced = coerce_bitvec_width_safe(rhs, max_width, ext);
                (lhs_coerced, rhs_coerced)
            }
            _ => (lhs, rhs), // non-enum: tuple (Option<u32>, Option<u32>) — non-bitvec passthrough
        }
    }

    /// Compute the "no overflow" condition for unchecked arithmetic ops.
    ///
    /// Returns a boolean expression that is `true` when the operation does NOT
    /// overflow. The caller should push this to `safety_checks` so the rule
    /// generator emits `¬no_overflow → error()`.
    ///
    /// Mirrors `statement::arithmetic_checks::overflow_check` for the CHC path.
    /// Part of #3299: CHC path had no overflow checks for unchecked ops.
    pub(in crate::codegen_ay::chc) fn unchecked_overflow_condition(
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        is_signed: bool,
    ) -> Option<Expr> {
        // Coerce operands to matching widths (ay overflow methods require same width).
        let (lhs, rhs) = Self::coerce_arithmetic_operands(lhs.clone(), rhs.clone(), is_signed);
        match (op, is_signed) {
            (BinOp::AddUnchecked, true) => Some(lhs.bvadd_no_overflow_signed(rhs)),
            (BinOp::AddUnchecked, false) => Some(lhs.bvadd_no_overflow_unsigned(rhs)),
            (BinOp::SubUnchecked, true) => Some(lhs.bvsub_no_overflow_signed(rhs)),
            (BinOp::SubUnchecked, false) => Some(lhs.bvsub_no_underflow_unsigned(rhs)),
            (BinOp::MulUnchecked, true) => Some(lhs.bvmul_no_overflow_signed(rhs)),
            (BinOp::MulUnchecked, false) => {
                let width = lhs.sort().bitvec_width()?;
                Some(unsigned_mul_no_overflow_condition(lhs, rhs, width))
            }
            _ => None,
        }
    }
}

fn unsigned_mul_no_overflow_condition(lhs: Expr, rhs: Expr, width: u32) -> Expr {
    let zero = Expr::bitvec_const(0u64, width);
    let max = unsigned_max_value(width);

    rhs.clone().eq(zero).or(lhs.bvule(max.bvudiv(rhs)))
}

fn unsigned_max_value(width: u32) -> Expr {
    let value = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
    Expr::bitvec_const(value, width)
}

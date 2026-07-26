// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trailing-zero intrinsic encoding.

use ay_bindings::Expr;

/// Compute `cttz` (count trailing zeros) for a bitvector expression.
///
/// Uses a binary-search encoding instead of a linear per-bit ITE cascade. For
/// u64/usize this keeps the result expression at six decision levels, which is
/// important for replacement proofs that compare the intrinsic against an
/// independent symbolic reference.
///
/// If x == 0, result is width. Rust intrinsic `cttz::<T>(x: T) -> u32` always
/// returns u32 regardless of input width, so the result is BV32.
pub(super) fn compute_cttz(x: &Expr) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;
    let out_width: u32 = 32;

    let zero_input = dup_expr(x).eq(Expr::bitvec_const(0u64, width));
    let mut shifted = dup_expr(x);
    let mut count = Expr::bitvec_const(0u64, out_width);

    let mut step = largest_power_of_two_less_than(width);
    while step > 0 {
        let mask = low_bits_mask(step)?;
        let low_bits_zero = dup_expr(&shifted)
            .bvand(Expr::bitvec_const(mask, width))
            .eq(Expr::bitvec_const(0u64, width));
        let shifted_if_zero = dup_expr(&shifted).bvlshr(Expr::bitvec_const(step as u64, width));
        let count_if_zero = dup_expr(&count).bvadd(Expr::bitvec_const(step as u64, out_width));
        shifted = Expr::ite(dup_expr(&low_bits_zero), shifted_if_zero, shifted);
        count = Expr::ite(low_bits_zero, count_if_zero, count);
        step >>= 1;
    }

    Some(Expr::ite(zero_input, Expr::bitvec_const(width as u64, out_width), count))
}

fn dup_expr(expr: &Expr) -> Expr {
    // clone: ay Expr builders consume operands; shared subexpressions are reused
    // in both ITE branches and in paired shifted/count updates.
    expr.clone()
}

fn largest_power_of_two_less_than(width: u32) -> u32 {
    if width <= 1 { 0 } else { 1 << (u32::BITS - (width - 1).leading_zeros() - 1) }
}

fn low_bits_mask(bits: u32) -> Option<u64> {
    match bits {
        0 => Some(0),
        1..64 => Some((1u64 << bits) - 1),
        64 => Some(u64::MAX),
        _ => None,
    }
}

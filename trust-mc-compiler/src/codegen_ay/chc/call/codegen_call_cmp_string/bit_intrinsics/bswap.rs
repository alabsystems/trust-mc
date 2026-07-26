// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Byte-swap intrinsic encoding.

use ay_bindings::Expr;

/// Compute `bswap` (byte reversal) for a bitvector expression.
///
/// Reverses the byte order: bswap(0x12345678_u32) = 0x78563412.
/// Requires width is a multiple of 8.
pub(super) fn compute_bswap(x: &Expr) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;
    if width % 8 != 0 {
        return None;
    }
    let num_bytes = width / 8;

    if num_bytes == 1 {
        // Preserve the identity semantics while keeping the emitted CHC query
        // in the BV fragment. A raw clone can leave a degenerate equality-only
        // Horn query that AY reports UNKNOWN for one-byte bswap harnesses.
        return Some(x.clone().bvor(Expr::bitvec_const(0u64, width)));
    }

    // Use mask/shift/or instead of extract/concat. The tests and common Rust
    // byte-manipulation code use this shape, and it keeps AY in the bitwise BV
    // fragment instead of forcing it to prove concat/extract equivalences.
    let mut result = Expr::bitvec_const(0u64, width);
    let byte_mask = Expr::bitvec_const(0xFFu64, width);
    for src_byte in 0..num_bytes {
        let src_shift = src_byte * 8;
        let dst_shift = (num_bytes - src_byte - 1) * 8;
        let mask = shift_left_const(byte_mask.clone(), src_shift, width);
        let byte = x.clone().bvand(mask);
        let shifted = if dst_shift > src_shift {
            shift_left_const(byte, dst_shift - src_shift, width)
        } else {
            shift_right_const(byte, src_shift - dst_shift, width)
        };
        result = result.bvor(shifted);
    }

    Some(result)
}

fn shift_left_const(expr: Expr, shift: u32, width: u32) -> Expr {
    if shift == 0 { expr } else { expr.bvshl(Expr::bitvec_const(shift as u64, width)) }
}

fn shift_right_const(expr: Expr, shift: u32, width: u32) -> Expr {
    if shift == 0 { expr } else { expr.bvlshr(Expr::bitvec_const(shift as u64, width)) }
}

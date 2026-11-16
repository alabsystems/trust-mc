// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Equivalent finite range-copy representation after constant propagation.

use ay_bindings::{Expr, ExprValue};

/// Exact finite expansion after bounds become constants. This does not infer a
/// bound from a Vec constructor or omit long copies: unknown/large ranges keep
/// their original range-copy expression. Empty unsigned intervals are identity.
pub(super) fn lower_small_range_copy(
    original: &Expr,
    dst: Expr,
    src: Expr,
    lo: Expr,
    hi: Expr,
    src_start: Expr,
) -> Expr {
    let Ok(fallback) =
        dst.clone().try_array_range_copy(src.clone(), lo.clone(), hi.clone(), src_start.clone())
    else {
        return original.clone();
    };
    let bound = |expr: &Expr| match expr.value() {
        ExprValue::BitVecConst { value, width: 64 } => u64::try_from(value).ok(),
        _ => None,
    };
    if let (Some(low), Some(high)) = (bound(&lo), bound(&hi)) {
        if high <= low {
            return dst;
        }
        // Match the native initialization/finite-store precision envelope.
        // The threshold only selects an equivalent representation.
        if high - low <= 64 {
            let mut result = dst;
            for offset in 0..high - low {
                let source_index = if let Some(start) = bound(&src_start) {
                    Expr::bitvec_const(start.wrapping_add(offset), 64)
                } else if offset == 0 {
                    src_start.clone()
                } else {
                    src_start.clone().bvadd(Expr::bitvec_const(offset, 64))
                };
                result = result
                    .store(Expr::bitvec_const(low + offset, 64), src.clone().select(source_index));
            }
            return result;
        }
    }
    fallback
}

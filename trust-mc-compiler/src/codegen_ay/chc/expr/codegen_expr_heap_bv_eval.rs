// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bitvector constant evaluation for heap pointer tracing.
//!
//! Extracted from `codegen_expr_heap.rs` to stay under the 500-line limit.
//! These functions evaluate BV expressions to concrete values, enabling
//! `const_obj_id_u32` to trace pointers through arithmetic/coercion chains.
//!
//! Part of #4249: kani::mem fallback reduction.

use ay_bindings::{Expr, ExprValue};

/// Tries to evaluate a bitvector expression to a concrete value.
///
/// Supports structural forms used by split-pointer addresses:
/// constants, concatenation, extraction, addition, subtraction,
/// bitwise AND, zero/sign extension, and int-to-bv coercion.
pub(in crate::codegen_ay::chc) fn const_bv_value(expr: &Expr) -> Option<(num_bigint::BigInt, u32)> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } => Some((value.clone(), *width)),
        ExprValue::BvConcat(high, low) => {
            let (high_value, high_width) = const_bv_value(high)?;
            let (low_value, low_width) = const_bv_value(low)?;
            let width = high_width.checked_add(low_width)?;
            let value = (high_value << low_width) | low_value;
            Some((value, width))
        }
        ExprValue::BvExtract { expr, high, low } => const_extract_value(expr, *high, *low),
        ExprValue::BvAdd(a, b) => {
            let (a_value, a_width) = const_bv_value(a)?;
            let (b_value, b_width) = const_bv_value(b)?;
            if a_width != b_width {
                return None;
            }
            let mask = (num_bigint::BigInt::from(1u8) << a_width) - 1u8;
            let value = (a_value + b_value) & mask;
            Some((value, a_width))
        }
        ExprValue::BvSub(a, b) => {
            let (a_value, a_width) = const_bv_value(a)?;
            let (b_value, b_width) = const_bv_value(b)?;
            if a_width != b_width {
                return None;
            }
            let modulus = num_bigint::BigInt::from(1u8) << a_width;
            let value = ((a_value - b_value) % &modulus + &modulus) % modulus;
            Some((value, a_width))
        }
        ExprValue::BvAnd(a, b) => {
            let (a_value, a_width) = const_bv_value(a)?;
            let (b_value, b_width) = const_bv_value(b)?;
            if a_width != b_width {
                return None;
            }
            Some((a_value & b_value, a_width))
        }
        ExprValue::BvZeroExtend { expr: inner, extra_bits } => {
            let (value, width) = const_bv_value(inner)?;
            Some((value, width + extra_bits))
        }
        ExprValue::BvSignExtend { expr: inner, extra_bits } => {
            let (value, width) = const_bv_value(inner)?;
            let new_width = width + extra_bits;
            let sign_bit = num_bigint::BigInt::from(1u8) << (width - 1);
            if value >= sign_bit {
                let extension_mask = ((num_bigint::BigInt::from(1u8) << new_width) - 1u8)
                    - ((num_bigint::BigInt::from(1u8) << width) - 1u8);
                Some((value | extension_mask, new_width))
            } else {
                Some((value, new_width))
            }
        }
        ExprValue::Int2Bv(inner, width) => {
            if let ExprValue::IntConst(int_val) = inner.value() {
                if int_val.sign() == num_bigint::Sign::Minus {
                    let modulus = num_bigint::BigInt::from(1u8) << *width;
                    let bv_val = (int_val % &modulus + &modulus) % modulus;
                    Some((bv_val, *width))
                } else {
                    let mask = (num_bigint::BigInt::from(1u8) << *width) - 1u8;
                    Some((int_val.clone() & mask, *width))
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Evaluates `extract(high, low)` over `expr`, folding through structure whose
/// extracted lane is independent of symbolic bits outside it.
///
/// The split-pointer model builds addresses as `concat(obj_id, offset)`, and
/// split-add pointer arithmetic (`pointer_step.rs`) keeps that shape with a
/// constant obj_id lane and a symbolic offset lane. Whole-expression constant
/// evaluation cannot fold `extract(63,32)(concat(const_id, symbolic_offset))`
/// because the offset lane is symbolic — but the extracted obj_id lane does not
/// depend on it. Recursing into the relevant lane recovers the constant obj_id,
/// which is what gates the heap bounds check emission in `heap_access_checks`.
fn const_extract_value(expr: &Expr, high: u32, low: u32) -> Option<(num_bigint::BigInt, u32)> {
    if low > high {
        return None;
    }
    match expr.value() {
        ExprValue::BvConcat(hi_lane, lo_lane) => {
            let lo_width = lo_lane.sort().bitvec_width()?;
            if high < lo_width {
                // Range lies entirely within the low lane.
                const_extract_value(lo_lane, high, low)
            } else if low >= lo_width {
                // Range lies entirely within the high lane.
                const_extract_value(hi_lane, high - lo_width, low - lo_width)
            } else {
                // Straddles the seam — both lanes contribute.
                const_extract_fallback(expr, high, low)
            }
        }
        // Compose nested extracts: bits [high:low] of extract(_, inner_low)
        // are bits [inner_low+high : inner_low+low] of the inner expression.
        ExprValue::BvExtract { expr: inner, high: _, low: inner_low } => {
            const_extract_value(inner, inner_low + high, inner_low + low)
        }
        ExprValue::BvZeroExtend { expr: inner, extra_bits: _ } => {
            let inner_width = inner.sort().bitvec_width()?;
            if high < inner_width {
                const_extract_value(inner, high, low)
            } else if low >= inner_width {
                // Entirely within the zero extension.
                Some((num_bigint::BigInt::from(0u8), high - low + 1))
            } else {
                const_extract_fallback(expr, high, low)
            }
        }
        ExprValue::BvSignExtend { expr: inner, extra_bits: _ } => {
            let inner_width = inner.sort().bitvec_width()?;
            if high < inner_width {
                const_extract_value(inner, high, low)
            } else {
                const_extract_fallback(expr, high, low)
            }
        }
        _ => const_extract_fallback(expr, high, low),
    }
}

/// Whole-expression fallback for `const_extract_value`: evaluate `expr` to a
/// constant, then shift/mask out the requested bit range.
fn const_extract_fallback(expr: &Expr, high: u32, low: u32) -> Option<(num_bigint::BigInt, u32)> {
    let (value, width) = const_bv_value(expr)?;
    if high >= width {
        return None;
    }
    let out_width = high - low + 1;
    let shifted = value >> low;
    let mask = (num_bigint::BigInt::from(1u8) << out_width) - 1u8;
    Some((shifted & mask, out_width))
}

/// Extracts a concrete `u32` from a bv32 object-id expression.
pub(in crate::codegen_ay::chc) fn const_obj_id_u32(obj_id: &Expr) -> Option<u32> {
    let (value, width) = const_bv_value(obj_id)?;
    if width != 32 {
        return None;
    }
    let (_sign, digits) = value.to_u32_digits();
    match digits.as_slice() {
        [] => Some(0),
        [single] => Some(*single),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use ay_bindings::Sort;

    use super::*;

    /// The split-add shape: `extract(63,32)(concat(const_id, symbolic_offset))`
    /// must fold to the constant obj_id even though the offset lane is symbolic.
    #[test]
    fn test_extract_high_lane_of_concat_with_symbolic_low_folds() {
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let sym_offset = Expr::var("sym_offset", Sort::bitvec(32));
        let ptr = obj_id.concat(sym_offset);

        let extracted = ptr.extract(63, 32);
        assert_eq!(const_obj_id_u32(&extracted), Some(0x42));
    }

    /// Low-lane extract folds when only the high lane is symbolic.
    #[test]
    fn test_extract_low_lane_of_concat_with_symbolic_high_folds() {
        let sym_id = Expr::var("sym_id", Sort::bitvec(32));
        let offset = Expr::bitvec_const(0x10u128, 32);
        let ptr = sym_id.concat(offset);

        let extracted = ptr.extract(31, 0);
        let (value, width) = const_bv_value(&extracted).expect("low lane should fold");
        assert_eq!(width, 32);
        assert_eq!(value, num_bigint::BigInt::from(0x10u32));
    }

    /// A seam-straddling extract over a partially-symbolic concat must NOT fold.
    #[test]
    fn test_extract_straddling_seam_with_symbolic_lane_does_not_fold() {
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let sym_offset = Expr::var("sym_offset", Sort::bitvec(32));
        let ptr = obj_id.concat(sym_offset);

        let extracted = ptr.extract(47, 16);
        assert_eq!(const_bv_value(&extracted), None);
    }

    /// Chained split-adds: the obj_id lane survives
    /// `extract(63,32)(concat(extract(63,32)(concat(id, sym1)), sym2))`.
    #[test]
    fn test_extract_folds_through_chained_split_adds() {
        let obj_id = Expr::bitvec_const(0x7u128, 32);
        let sym1 = Expr::var("sym1", Sort::bitvec(32));
        let ptr1 = obj_id.concat(sym1);

        let carried_id = ptr1.extract(63, 32);
        let sym2 = Expr::var("sym2", Sort::bitvec(32));
        let ptr2 = carried_id.concat(sym2);

        let extracted = ptr2.extract(63, 32);
        assert_eq!(const_obj_id_u32(&extracted), Some(0x7));
    }

    /// Extract entirely within the zero-extension lane folds to zero.
    #[test]
    fn test_extract_within_zero_extension_folds_to_zero() {
        let sym = Expr::var("sym", Sort::bitvec(32));
        let extended = sym.zero_extend(32);

        let extracted = extended.extract(63, 32);
        assert_eq!(const_obj_id_u32(&extracted), Some(0));
    }

    /// Fully-constant extract still folds exactly as before (fallback path).
    #[test]
    fn test_fully_constant_extract_still_folds() {
        let ptr = Expr::bitvec_const(0x0000_0042_0000_0010u128, 64);
        let extracted = ptr.extract(63, 32);
        assert_eq!(const_obj_id_u32(&extracted), Some(0x42));
    }
}

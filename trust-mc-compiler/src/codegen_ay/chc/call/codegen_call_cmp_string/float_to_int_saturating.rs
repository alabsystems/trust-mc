// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Saturating float-to-int cast helpers for Rust `as` semantics.

use ay_bindings::Expr;

use super::float_predicates::{build_float_to_int_expr, ieee754_params};
use crate::codegen_ay::float_arithmetic::{int_max_bits, int_min_bits, unsigned_max_bits};

/// Build a BV expression for Rust `as` float-to-int casts with saturating
/// semantics for NaN, infinities, and out-of-range values.
///
/// Part of #3787.
pub(in crate::codegen_ay::chc) fn build_float_to_int_saturating_expr(
    value: &Expr,
    target_width: u32,
    is_signed: bool,
) -> Option<Expr> {
    let truncated = build_float_to_int_expr(value, target_width, is_signed)?;
    let width = value.sort().bitvec_width()?;
    let (exp_hi, exp_lo, _mant_bits, bias) = ieee754_params(width)?;
    let exp_width = exp_hi - exp_lo + 1;

    let sign = value.clone().extract(width - 1, width - 1);
    let exp_raw = value.clone().extract(exp_hi, exp_lo);
    let mantissa = value.clone().extract(exp_lo - 1, 0);

    let sign_is_neg = sign.eq(Expr::bitvec_const(1u64, 1));
    let mantissa_is_zero = mantissa.eq(Expr::bitvec_const(0u64, exp_lo));
    let special_exp =
        exp_raw.clone().eq(Expr::bitvec_const(unsigned_max_bits(exp_width), exp_width));
    let is_nan = special_exp.clone().and(mantissa_is_zero.clone().not());
    let is_pos_inf =
        special_exp.clone().and(mantissa_is_zero.clone()).and(sign_is_neg.clone().not());
    let is_neg_inf = special_exp.and(mantissa_is_zero).and(sign_is_neg.clone());

    let bias_bv = Expr::bitvec_const(bias as u64, exp_width);
    let exp_unbiased = exp_raw.bvsub(bias_bv);
    let work_width = target_width.max(exp_width) + 1;
    let exp_wide = exp_unbiased.sign_extend(work_width - exp_width);
    let overflow_threshold = target_width - u32::from(is_signed);
    let magnitude_exceeds_range =
        exp_wide.bvsge(Expr::bitvec_const(overflow_threshold as u128, work_width));

    let zero = Expr::bitvec_const(0u128, target_width);
    let int_min = Expr::bitvec_const(int_min_bits(target_width, is_signed), target_width);
    let int_max = Expr::bitvec_const(int_max_bits(target_width, is_signed), target_width);

    Some(Expr::ite(
        is_nan,
        zero,
        Expr::ite(
            is_pos_inf,
            int_max.clone(),
            Expr::ite(
                is_neg_inf,
                int_min.clone(),
                Expr::ite(
                    magnitude_exceeds_range.clone().and(sign_is_neg.clone().not()),
                    int_max,
                    Expr::ite(magnitude_exceeds_range.and(sign_is_neg), int_min, truncated),
                ),
            ),
        ),
    ))
}

/// Build the UB-free (safe) precondition for `float_to_int_unchecked::<Float, Int>`.
///
/// Rust's `to_int_unchecked` / `fptoui`/`fptosi` is Undefined Behavior unless the
/// source float is finite (not NaN, not infinite) and its truncation toward zero
/// fits the target integer type — i.e. the value lies in the open interval
/// `(INT_MIN - 1, INT_MAX + 1)` (signed) or `(-1, UINT_MAX + 1)` (unsigned).
///
/// Returns a boolean `Expr` that is **true exactly when the conversion is
/// well-defined**; a violated (false) predicate therefore marks UB. It is built
/// entirely from bit-vector operations (no FP-theory terms), so the CHC/HORN
/// backend accepts it, matching the pure-BV extraction path used for the result.
///
/// Precision: exact at every integer boundary. In particular it never reports a
/// well-defined conversion as UB (no false positives) — e.g. the exact value
/// `INT_MIN` and fractional values in `(INT_MIN - 1, INT_MIN)` remain safe
/// because truncation is toward zero.
pub(in crate::codegen_ay::chc) fn build_float_to_int_ub_free_predicate(
    value: &Expr,
    target_width: u32,
    is_signed: bool,
) -> Option<Expr> {
    let width = value.sort().bitvec_width()?;
    let (exp_hi, exp_lo, _mant_bits, bias) = ieee754_params(width)?;
    let exp_width = exp_hi - exp_lo + 1;

    let sign = value.clone().extract(width - 1, width - 1);
    let exp_raw = value.clone().extract(exp_hi, exp_lo);
    let mantissa = value.clone().extract(exp_lo - 1, 0);

    let sign_is_neg = sign.eq(Expr::bitvec_const(1u64, 1));
    let mantissa_nonzero = mantissa.eq(Expr::bitvec_const(0u64, exp_lo)).not();
    // Exponent all-ones ⇒ NaN or ±Inf; both are UB for to_int_unchecked.
    let special_exp =
        exp_raw.clone().eq(Expr::bitvec_const(unsigned_max_bits(exp_width), exp_width));

    // Unbiased exponent E as a signed value, widened so comparisons don't wrap.
    // For normal floats E = exp_raw - bias ∈ [-bias, bias]; the all-ones case
    // (which would overflow) is masked by `special_exp` below.
    let bias_bv = Expr::bitvec_const(bias as u64, exp_width);
    let exp_unbiased = exp_raw.bvsub(bias_bv);
    let work_width = target_width.max(exp_width) + 2;
    let e = exp_unbiased.sign_extend(work_width - exp_width);
    let e_ge = |k: u32| e.clone().bvsge(Expr::bitvec_const(k as u128, work_width));

    // A finite float has magnitude |v| ≥ 2^E and < 2^(E+1), so |v| ≥ 2^k iff E ≥ k.
    let ub = if is_signed {
        // Positive: value ≥ 2^(w-1) exceeds INT_MAX ⇒ UB.
        let pos_overflow = sign_is_neg.clone().not().and(e_ge(target_width - 1));
        // Negative: value ≤ INT_MIN - 1 ⇒ UB. |value| ≥ 2^(w-1) covers exactly
        // `INT_MIN` too, which is safe, so exclude E == w-1 with zero mantissa.
        let neg_overflow = sign_is_neg
            .clone()
            .and(e_ge(target_width).or(e_ge(target_width - 1).and(mantissa_nonzero)));
        special_exp.or(pos_overflow).or(neg_overflow)
    } else {
        // Positive: value ≥ 2^w exceeds UINT_MAX ⇒ UB.
        let pos_overflow = sign_is_neg.clone().not().and(e_ge(target_width));
        // Negative: value ≤ -1 (i.e. |value| ≥ 1, E ≥ 0) does not fit ⇒ UB.
        let neg_ub = sign_is_neg.clone().and(e_ge(0));
        special_exp.or(pos_overflow).or(neg_ub)
    };

    Some(ub.not())
}

#[cfg(test)]
mod tests {
    use super::build_float_to_int_saturating_expr;
    use super::build_float_to_int_ub_free_predicate;

    use ay_bindings::{Expr, ExprValue};
    use num_bigint::BigInt;

    #[derive(Debug, Clone, Eq, PartialEq)]
    enum ConstValue {
        Bool(bool),
        Bv(BigInt, u32),
    }

    fn assert_bv_expr_eq(expr: Expr, expected: Expr) {
        let actual = eval_bv_expr(&expr);
        let expected = eval_bv_expr(&expected);
        assert_eq!(actual, expected, "unexpected BV expression value for {expr}");
    }

    fn eval_bv_expr(expr: &Expr) -> (BigInt, u32) {
        match eval_const_expr(expr) {
            ConstValue::Bv(value, width) => (value, width),
            other => panic!("expected BV expression, got {other:?} from {expr}"),
        }
    }

    fn eval_bool_expr(expr: &Expr) -> bool {
        match eval_const_expr(expr) {
            ConstValue::Bool(value) => value,
            other => panic!("expected Bool expression, got {other:?} from {expr}"),
        }
    }

    fn eval_const_expr(expr: &Expr) -> ConstValue {
        match expr.value() {
            ExprValue::BoolConst(value) => ConstValue::Bool(*value),
            ExprValue::BitVecConst { value, width } => {
                ConstValue::Bv(normalize_bv(value.clone(), *width), *width)
            }
            ExprValue::Not(inner) => ConstValue::Bool(!eval_bool_expr(inner)),
            ExprValue::And(args) => ConstValue::Bool(args.iter().all(eval_bool_expr)),
            ExprValue::Or(args) => ConstValue::Bool(args.iter().any(eval_bool_expr)),
            ExprValue::Xor(lhs, rhs) => ConstValue::Bool(eval_bool_expr(lhs) ^ eval_bool_expr(rhs)),
            ExprValue::Implies(lhs, rhs) => {
                ConstValue::Bool(!eval_bool_expr(lhs) || eval_bool_expr(rhs))
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                if eval_bool_expr(cond) {
                    eval_const_expr(then_expr)
                } else {
                    eval_const_expr(else_expr)
                }
            }
            ExprValue::Eq(lhs, rhs) => {
                ConstValue::Bool(eval_const_expr(lhs) == eval_const_expr(rhs))
            }
            ExprValue::Distinct(args) => {
                ConstValue::Bool(args.iter().enumerate().all(|(i, lhs)| {
                    args.iter().skip(i + 1).all(|rhs| eval_const_expr(lhs) != eval_const_expr(rhs))
                }))
            }
            ExprValue::BvAdd(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs + rhs),
            ExprValue::BvSub(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs - rhs),
            ExprValue::BvMul(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs * rhs),
            ExprValue::BvNeg(inner) => {
                let (value, width) = eval_bv_expr(inner);
                ConstValue::Bv(normalize_bv(-value, width), width)
            }
            ExprValue::BvNot(inner) => {
                let (value, width) = eval_bv_expr(inner);
                ConstValue::Bv(low_mask(width) ^ value, width)
            }
            ExprValue::BvAnd(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs & rhs),
            ExprValue::BvOr(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs | rhs),
            ExprValue::BvXor(lhs, rhs) => eval_bv_binop(lhs, rhs, |lhs, rhs| lhs ^ rhs),
            ExprValue::BvShl(lhs, rhs) => {
                let (lhs, width) = eval_bv_expr(lhs);
                let (rhs, rhs_width) = eval_bv_expr(rhs);
                assert_eq!(width, rhs_width);
                let amount = small_usize_or_cap(&rhs, width as usize);
                let value =
                    if amount >= width as usize { BigInt::from(0u8) } else { lhs << amount };
                ConstValue::Bv(normalize_bv(value, width), width)
            }
            ExprValue::BvLShr(lhs, rhs) => {
                let (lhs, width) = eval_bv_expr(lhs);
                let (rhs, rhs_width) = eval_bv_expr(rhs);
                assert_eq!(width, rhs_width);
                let amount = small_usize_or_cap(&rhs, width as usize);
                let value =
                    if amount >= width as usize { BigInt::from(0u8) } else { lhs >> amount };
                ConstValue::Bv(value, width)
            }
            ExprValue::BvAShr(lhs, rhs) => {
                let (lhs, width) = eval_bv_expr(lhs);
                let (rhs, rhs_width) = eval_bv_expr(rhs);
                assert_eq!(width, rhs_width);
                let amount = small_usize_or_cap(&rhs, width as usize);
                let signed = signed_bv_value(&lhs, width);
                let value = if amount >= width as usize {
                    if signed < BigInt::from(0u8) { low_mask(width) } else { BigInt::from(0u8) }
                } else {
                    normalize_bv(signed >> amount, width)
                };
                ConstValue::Bv(value, width)
            }
            ExprValue::BvULt(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, _| lhs < rhs))
            }
            ExprValue::BvULe(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, _| lhs <= rhs))
            }
            ExprValue::BvUGt(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, _| lhs > rhs))
            }
            ExprValue::BvUGe(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, _| lhs >= rhs))
            }
            ExprValue::BvSLt(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, width| {
                    signed_bv_value(&lhs, width) < signed_bv_value(&rhs, width)
                }))
            }
            ExprValue::BvSLe(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, width| {
                    signed_bv_value(&lhs, width) <= signed_bv_value(&rhs, width)
                }))
            }
            ExprValue::BvSGt(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, width| {
                    signed_bv_value(&lhs, width) > signed_bv_value(&rhs, width)
                }))
            }
            ExprValue::BvSGe(lhs, rhs) => {
                ConstValue::Bool(eval_bv_pair(lhs, rhs, |lhs, rhs, width| {
                    signed_bv_value(&lhs, width) >= signed_bv_value(&rhs, width)
                }))
            }
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                let (value, width) = eval_bv_expr(expr);
                ConstValue::Bv(value, width + extra_bits)
            }
            ExprValue::BvSignExtend { expr, extra_bits } => {
                let (value, width) = eval_bv_expr(expr);
                ConstValue::Bv(
                    normalize_bv(signed_bv_value(&value, width), width + extra_bits),
                    width + extra_bits,
                )
            }
            ExprValue::BvExtract { expr, high, low } => {
                let (value, _) = eval_bv_expr(expr);
                let width = high - low + 1;
                ConstValue::Bv((value >> *low as usize) & low_mask(width), width)
            }
            ExprValue::BvConcat(lhs, rhs) => {
                let (lhs, lhs_width) = eval_bv_expr(lhs);
                let (rhs, rhs_width) = eval_bv_expr(rhs);
                ConstValue::Bv((lhs << rhs_width as usize) | rhs, lhs_width + rhs_width)
            }
            other => panic!("unsupported constant expression in test evaluator: {other:?}"),
        }
    }

    fn eval_bv_binop(
        lhs: &Expr,
        rhs: &Expr,
        op: impl FnOnce(BigInt, BigInt) -> BigInt,
    ) -> ConstValue {
        let (lhs, width) = eval_bv_expr(lhs);
        let (rhs, rhs_width) = eval_bv_expr(rhs);
        assert_eq!(width, rhs_width);
        ConstValue::Bv(normalize_bv(op(lhs, rhs), width), width)
    }

    fn eval_bv_pair(lhs: &Expr, rhs: &Expr, op: impl FnOnce(BigInt, BigInt, u32) -> bool) -> bool {
        let (lhs, width) = eval_bv_expr(lhs);
        let (rhs, rhs_width) = eval_bv_expr(rhs);
        assert_eq!(width, rhs_width);
        op(lhs, rhs, width)
    }

    fn normalize_bv(value: BigInt, width: u32) -> BigInt {
        let modulus = modulus(width);
        let mut value = value % &modulus;
        if value < BigInt::from(0u8) {
            value += modulus;
        }
        value
    }

    fn signed_bv_value(value: &BigInt, width: u32) -> BigInt {
        let sign_bit = BigInt::from(1u8) << (width - 1) as usize;
        if value >= &sign_bit { value - modulus(width) } else { value.clone() }
    }

    fn modulus(width: u32) -> BigInt {
        BigInt::from(1u8) << width as usize
    }

    fn low_mask(width: u32) -> BigInt {
        modulus(width) - BigInt::from(1u8)
    }

    fn small_usize_or_cap(value: &BigInt, cap: usize) -> usize {
        if value >= &BigInt::from(cap) {
            cap
        } else {
            value.to_string().parse().expect("small BV shift amount")
        }
    }

    #[test]
    fn test_build_float_to_int_saturating_expr_f32_above_max_to_u8() {
        let result =
            build_float_to_int_saturating_expr(&Expr::bitvec_const(0x4396_0000u64, 32), 8, false)
                .expect("f32→u8 saturating builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(255u64, 8));
    }

    #[test]
    fn test_build_float_to_int_saturating_expr_f32_neg_below_min_to_i8() {
        let result =
            build_float_to_int_saturating_expr(&Expr::bitvec_const(0xC348_0000u64, 32), 8, true)
                .expect("f32→i8 saturating builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(i8::MIN as i128, 8));
    }

    #[test]
    fn test_build_float_to_int_saturating_expr_f32_nan_to_u8() {
        let result =
            build_float_to_int_saturating_expr(&Expr::bitvec_const(0x7FC0_0000u64, 32), 8, false)
                .expect("f32→u8 saturating builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 8));
    }

    #[test]
    fn test_build_float_to_int_saturating_expr_f32_infinity_to_u8() {
        let result =
            build_float_to_int_saturating_expr(&Expr::bitvec_const(0x7F80_0000u64, 32), 8, false)
                .expect("f32→u8 saturating builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(255u64, 8));
    }

    #[test]
    fn test_build_float_to_int_saturating_expr_f32_truncation_preserved() {
        let result =
            build_float_to_int_saturating_expr(&Expr::bitvec_const(0xC2C7_CCCD_u64, 32), 8, true)
                .expect("f32→i8 saturating builder");
        assert_bv_expr_eq(result, Expr::bitvec_const((-99i8) as i128, 8));
    }

    fn ub_free_f32(bits: u32, target_width: u32, is_signed: bool) -> bool {
        let pred = build_float_to_int_ub_free_predicate(
            &Expr::bitvec_const(bits as u64, 32),
            target_width,
            is_signed,
        )
        .expect("f32 ub-free predicate");
        eval_bool_expr(&pred)
    }

    #[test]
    fn test_float_to_int_ub_free_predicate_well_defined_are_safe() {
        // In-range conversions must be reported safe (true) — no false positives.
        assert!(ub_free_f32((42.0f32).to_bits(), 32, true));
        assert!(ub_free_f32((42.0f32).to_bits(), 8, false));
        assert!(ub_free_f32((255.0f32).to_bits(), 8, false)); // == u8::MAX
        assert!(ub_free_f32((-0.5f32).to_bits(), 8, false)); // truncates to 0
        assert!(ub_free_f32((0.0f32).to_bits(), 8, false));
        // Exact i32::MIN is representable and safe (truncation toward zero).
        assert!(ub_free_f32((i32::MIN as f32).to_bits(), 32, true));
        // Largest f32 strictly below 2^31 fits i32.
        assert!(ub_free_f32((2_147_483_520.0f32).to_bits(), 32, true));
    }

    #[test]
    fn test_float_to_int_ub_free_predicate_undefined_are_flagged() {
        // NaN / infinities are always UB.
        assert!(!ub_free_f32(f32::NAN.to_bits(), 32, true));
        assert!(!ub_free_f32(f32::INFINITY.to_bits(), 32, true));
        assert!(!ub_free_f32(f32::NEG_INFINITY.to_bits(), 32, true));
        assert!(!ub_free_f32(f32::NAN.to_bits(), 8, false));
        // Out of range.
        assert!(!ub_free_f32((1e30f32).to_bits(), 32, true)); // > i32::MAX
        assert!(!ub_free_f32((-1e30f32).to_bits(), 32, true)); // < i32::MIN
        assert!(!ub_free_f32((256.0f32).to_bits(), 8, false)); // > u8::MAX
        assert!(!ub_free_f32((-1.0f32).to_bits(), 8, false)); // negative → unsigned
        // One ULP below i32::MIN (-(2^31) - 256) does not fit.
        assert!(!ub_free_f32(0xCF00_0001u32, 32, true));
    }
}

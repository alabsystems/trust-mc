// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Float predicate CHC handlers used by FastMath assumption paths.
//!
//! Handles `f32`/`f64` methods that return Bool based on the floating-point
//! bit pattern:
//! - `is_nan`
//! - `is_infinite`
//! - `is_normal`
//! - `is_finite`
//! - `is_sign_positive`
//! - `is_sign_negative`

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay::chc) enum FloatPredicateKind {
    Nan,
    Infinite,
    Normal,
    Finite,
    SignPositive,
    SignNegative,
}

pub(in crate::codegen_ay::chc) fn detect_float_predicate(path: &str) -> Option<FloatPredicateKind> {
    // Order matters: check is_infinite before is_finite (substring match)
    if path.contains("is_nan") {
        Some(FloatPredicateKind::Nan)
    } else if path.contains("is_infinite") {
        Some(FloatPredicateKind::Infinite)
    } else if path.contains("is_normal") {
        Some(FloatPredicateKind::Normal)
    } else if path.contains("is_finite") {
        Some(FloatPredicateKind::Finite)
    } else if path.contains("is_sign_positive") {
        Some(FloatPredicateKind::SignPositive)
    } else if path.contains("is_sign_negative") {
        Some(FloatPredicateKind::SignNegative)
    } else {
        None
    }
}

pub(in crate::codegen_ay::chc) fn codegen_float_predicate(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: FloatPredicateKind,
) {
    let dest_local: usize = dcx.destination.local;
    let modified_locals = dcx.modified_locals;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;

    let Some(value) =
        dcx.args.first().and_then(|arg| ctx.translate_operand_with_modified(arg, modified_locals))
    else {
        debug!(?kind, "float predicate missing/untranslatable receiver — sound fallback");
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, from_app, target, modified_locals, &[dest_local], stmt_constraints);
        return;
    };

    let Some(result_expr) = build_float_predicate_expr(&value, kind) else {
        debug!(?kind, sort = ?value.sort(), "float predicate unsupported receiver sort");
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, from_app, target, modified_locals, &[dest_local], stmt_constraints);
        return;
    };

    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
        && let Some(eq) = ctx.make_coerced_eq_constraint(
            &dest_var,
            result_expr,
            dest_var.sort(),
            dest_local,
            "codegen_float_predicate",
        )
    {
        let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, [eq]);
        return;
    }

    debug!(?kind, dest_local, "float predicate destination coercion failed — sound fallback");
    #[rustfmt::skip]
    emit_sound_fallback_goto(ctx, from_app, target, modified_locals, &[dest_local], stmt_constraints);
}

pub(in crate::codegen_ay::chc) fn build_float_predicate_expr(
    value: &Expr,
    kind: FloatPredicateKind,
) -> Option<Expr> {
    let width = value.sort().bitvec_width()?;
    let (exp_hi, exp_lo, mant_bits, _bias) = ieee754_params(width)?;
    let exp_width = exp_hi - exp_lo + 1;
    let exp_all_ones: u64 = (1u64 << exp_width) - 1;

    match kind {
        FloatPredicateKind::Nan => {
            // IEEE 754: NaN iff exponent all 1s AND mantissa non-zero
            let exp = value.clone().extract(exp_hi, exp_lo);
            let mant = value.clone().extract(exp_lo - 1, 0);
            let exp_max = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width));
            let mant_nonzero = mant.eq(Expr::bitvec_const(0u64, mant_bits)).not();
            Some(exp_max.and(mant_nonzero))
        }
        FloatPredicateKind::Infinite => {
            // IEEE 754: Inf iff exponent all 1s AND mantissa zero
            let exp = value.clone().extract(exp_hi, exp_lo);
            let mant = value.clone().extract(exp_lo - 1, 0);
            let exp_max = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width));
            let mant_zero = mant.eq(Expr::bitvec_const(0u64, mant_bits));
            Some(exp_max.and(mant_zero))
        }
        FloatPredicateKind::Normal => {
            // IEEE 754: Normal iff exponent != 0 AND exponent != all-ones
            // (excludes zero, subnormal, infinity, NaN)
            let exp = value.clone().extract(exp_hi, exp_lo);
            let exp_nonzero = exp.clone().eq(Expr::bitvec_const(0u64, exp_width)).not();
            let exp_not_max = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width)).not();
            Some(exp_nonzero.and(exp_not_max))
        }
        FloatPredicateKind::Finite => {
            // Finite: exponent NOT all 1s (excludes both NaN and Inf)
            let exp = value.clone().extract(exp_hi, exp_lo);
            Some(exp.eq(Expr::bitvec_const(exp_all_ones, exp_width)).not())
        }
        FloatPredicateKind::SignPositive | FloatPredicateKind::SignNegative => {
            let sign = value.clone().extract(width - 1, width - 1);
            let expected = if kind == FloatPredicateKind::SignPositive { 0u64 } else { 1u64 };
            Some(sign.eq(Expr::bitvec_const(expected, 1)))
        }
    }
}

/// Build a BV expression that extracts the truncating integer value from an
/// IEEE 754 float BV. Used for the in-range core of float-to-int conversion
/// and by `float_to_int_unchecked`, whose caller provides the preconditions.
///
/// Returns `None` for unsupported float widths (currently supports f16, f32,
/// f64, f128).
///
/// Part of #3668.
pub(in crate::codegen_ay::chc) fn build_float_to_int_expr(
    value: &Expr,
    target_width: u32,
    is_signed: bool,
) -> Option<Expr> {
    let width = value.sort().bitvec_width()?;
    let (exp_hi, exp_lo, mant_bits, bias) = ieee754_params(width)?;
    let exp_width = exp_hi - exp_lo + 1;

    // Extract IEEE 754 fields.
    let sign = value.clone().extract(width - 1, width - 1);
    let exp_raw = value.clone().extract(exp_hi, exp_lo);
    let mantissa = value.clone().extract(exp_lo - 1, 0);

    // Full mantissa with implicit leading 1 (normalized numbers).
    // Width: mant_bits + 1
    let full_mant = Expr::bitvec_const(1u64, 1).concat(mantissa);
    let full_mant_width = mant_bits + 1;

    // Unbiased exponent (signed): exp = exp_raw - bias
    let bias_bv = Expr::bitvec_const(bias as u64, exp_width);
    let exp_unbiased = exp_raw.bvsub(bias_bv);

    // We need to work in a width large enough to hold the result.
    // Use max(target_width, full_mant_width, exp_width) + some headroom.
    let work_width = target_width.max(full_mant_width).max(exp_width) + 1;

    // Widen full_mant and shift amounts to work_width.
    let mant_wide = full_mant.zero_extend(work_width - full_mant_width);
    let mant_bits_bv = Expr::bitvec_const(mant_bits as u64, work_width);

    // Widen exp_unbiased to work_width (sign-extend since it's signed).
    let exp_wide = exp_unbiased.sign_extend(work_width - exp_width);

    // Case 1: exp >= mant_bits → integer = full_mant << (exp - mant_bits)
    // Case 2: 0 <= exp < mant_bits → integer = full_mant >> (mant_bits - exp)
    // Case 3: exp < 0 → integer = 0 (|f| < 1, truncates to 0)
    let zero_wide = Expr::bitvec_const(0u64, work_width);

    // shift_left_amt = exp - mant_bits (used when exp >= mant_bits)
    let shift_left_amt = exp_wide.clone().bvsub(mant_bits_bv.clone());
    // shift_right_amt = mant_bits - exp (used when 0 <= exp < mant_bits)
    let shift_right_amt = mant_bits_bv.bvsub(exp_wide.clone());

    let case1_val = mant_wide.clone().bvshl(shift_left_amt);
    let case2_val = mant_wide.bvlshr(shift_right_amt);

    // exp >= mant_bits (signed comparison)
    let exp_ge_mant = exp_wide.clone().bvsge(Expr::bitvec_const(mant_bits as u64, work_width));
    // exp >= 0 (signed comparison)
    let exp_ge_zero = exp_wide.bvsge(zero_wide.clone());

    // integer_unsigned = ite(exp >= mant_bits, case1, ite(exp >= 0, case2, 0))
    let integer_unsigned =
        Expr::ite(exp_ge_mant, case1_val, Expr::ite(exp_ge_zero, case2_val, zero_wide));

    // Apply sign: signed targets negate; unsigned targets saturate to 0 (#3668).
    let sign_is_neg = sign.eq(Expr::bitvec_const(1u64, 1));
    let result = if is_signed {
        Expr::ite(sign_is_neg, integer_unsigned.clone().bvneg(), integer_unsigned)
    } else {
        Expr::ite(sign_is_neg, Expr::bitvec_const(0u64, work_width), integer_unsigned)
    };

    // Truncate or extend to target width.
    let final_result = if work_width > target_width {
        result.extract(target_width - 1, 0)
    } else if work_width < target_width {
        result.zero_extend(target_width - work_width)
    } else {
        result
    };

    Some(final_result)
}

/// Return IEEE 754 parameters for a given BV width.
/// Returns (exp_hi, exp_lo, mant_bits, bias) or None if unsupported.
pub(in crate::codegen_ay::chc) fn ieee754_params(width: u32) -> Option<(u32, u32, u32, u32)> {
    match width {
        16 => Some((14, 10, 10, 15)),        // f16: 1+5+10
        32 => Some((30, 23, 23, 127)),       // f32: 1+8+23
        64 => Some((62, 52, 52, 1023)),      // f64: 1+11+52
        128 => Some((126, 112, 112, 16383)), // f128: 1+15+112
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{FloatPredicateKind, build_float_predicate_expr, detect_float_predicate};

    use ay_bindings::{Expr, ExprValue};
    use num_bigint::BigInt;

    #[derive(Debug, Clone, Eq, PartialEq)]
    enum ConstValue {
        Bool(bool),
        Bv(BigInt, u32),
    }

    fn assert_bool_expr_eq(expr: Expr, expected: bool) {
        let actual = eval_bool_expr(&expr);
        assert_eq!(actual, expected, "unexpected Bool expression value for {expr}");
    }

    #[test]
    fn test_detect_float_predicate_recognizes_is_normal_paths() {
        assert_eq!(
            detect_float_predicate("core::num::<impl f32>::is_normal"),
            Some(FloatPredicateKind::Normal)
        );
        assert_eq!(
            detect_float_predicate("core::num::<impl f64>::is_normal"),
            Some(FloatPredicateKind::Normal)
        );
    }

    #[test]
    fn test_build_float_predicate_expr_normal_semantics_bv32() {
        let one = build_float_predicate_expr(
            &Expr::bitvec_const(0x3f80_0000u64, 32),
            FloatPredicateKind::Normal,
        )
        .expect("f32 normal builder");
        assert_bool_expr_eq(one, true);

        let zero =
            build_float_predicate_expr(&Expr::bitvec_const(0u64, 32), FloatPredicateKind::Normal)
                .expect("f32 zero builder");
        assert_bool_expr_eq(zero, false);

        let subnormal = build_float_predicate_expr(
            &Expr::bitvec_const(0x0000_0001u64, 32),
            FloatPredicateKind::Normal,
        )
        .expect("f32 subnormal builder");
        assert_bool_expr_eq(subnormal, false);

        let infinity = build_float_predicate_expr(
            &Expr::bitvec_const(0x7f80_0000u64, 32),
            FloatPredicateKind::Normal,
        )
        .expect("f32 infinity builder");
        assert_bool_expr_eq(infinity, false);

        let nan = build_float_predicate_expr(
            &Expr::bitvec_const(0x7fc0_0000u64, 32),
            FloatPredicateKind::Normal,
        )
        .expect("f32 NaN builder");
        assert_bool_expr_eq(nan, false);
    }

    #[test]
    fn test_build_float_predicate_expr_normal_semantics_bv64() {
        let one = build_float_predicate_expr(
            &Expr::bitvec_const(0x3ff0_0000_0000_0000u64, 64),
            FloatPredicateKind::Normal,
        )
        .expect("f64 normal builder");
        assert_bool_expr_eq(one, true);

        let zero =
            build_float_predicate_expr(&Expr::bitvec_const(0u64, 64), FloatPredicateKind::Normal)
                .expect("f64 zero builder");
        assert_bool_expr_eq(zero, false);

        let subnormal = build_float_predicate_expr(
            &Expr::bitvec_const(0x0000_0000_0000_0001u64, 64),
            FloatPredicateKind::Normal,
        )
        .expect("f64 subnormal builder");
        assert_bool_expr_eq(subnormal, false);

        let infinity = build_float_predicate_expr(
            &Expr::bitvec_const(0x7ff0_0000_0000_0000u64, 64),
            FloatPredicateKind::Normal,
        )
        .expect("f64 infinity builder");
        assert_bool_expr_eq(infinity, false);

        let nan = build_float_predicate_expr(
            &Expr::bitvec_const(0x7ff8_0000_0000_0000u64, 64),
            FloatPredicateKind::Normal,
        )
        .expect("f64 NaN builder");
        assert_bool_expr_eq(nan, false);
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

    // Part of #3668: float_to_int BV extraction tests.
    #[test]
    fn test_build_float_to_int_expr_f32_one_to_u32() {
        // f32 1.0 = 0x3f800000 → u32 1
        let result =
            super::build_float_to_int_expr(&Expr::bitvec_const(0x3f80_0000u64, 32), 32, false)
                .expect("f32→u32 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(1u64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f32_42_to_u32() {
        // f32 42.0 = 0x42280000 → u32 42
        let result =
            super::build_float_to_int_expr(&Expr::bitvec_const(0x4228_0000u64, 32), 32, false)
                .expect("f32→u32 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(42u64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f32_zero_to_u32() {
        // f32 0.0 = 0x00000000 → u32 0
        let result = super::build_float_to_int_expr(&Expr::bitvec_const(0u64, 32), 32, false)
            .expect("f32→u32 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f32_neg_one_to_i32() {
        // f32 -1.0 = 0xbf800000 → i32 -1 (= 0xFFFFFFFF as u32)
        let result =
            super::build_float_to_int_expr(&Expr::bitvec_const(0xbf80_0000u64, 32), 32, true)
                .expect("f32→i32 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(0xFFFF_FFFFu64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f64_one_to_u64() {
        // f64 1.0 = 0x3ff0000000000000 → u64 1
        let result = super::build_float_to_int_expr(
            &Expr::bitvec_const(0x3ff0_0000_0000_0000u64, 64),
            64,
            false,
        )
        .expect("f64→u64 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(1u64, 64));
    }

    #[test]
    fn test_build_float_to_int_expr_f64_255_to_u8() {
        // f64 255.0 = 0x406fe00000000000 → u8 255
        let result = super::build_float_to_int_expr(
            &Expr::bitvec_const(0x406f_e000_0000_0000u64, 64),
            8,
            false,
        )
        .expect("f64→u8 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(255u64, 8));
    }

    #[test]
    fn test_build_float_to_int_expr_f32_point_five_to_u32() {
        // f32 0.5 = 0x3f000000 → u32 0 (truncation toward zero)
        let result =
            super::build_float_to_int_expr(&Expr::bitvec_const(0x3f00_0000u64, 32), 32, false)
                .expect("f32→u32 builder for 0.5");
        assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f16_supported() {
        // f16 1.0 = 0x3C00 → u16 1
        let result = super::build_float_to_int_expr(&Expr::bitvec_const(0x3C00u64, 16), 16, false)
            .expect("f16→u16 builder");
        assert_bv_expr_eq(result, Expr::bitvec_const(1u64, 16));
    }

    #[test]
    fn test_build_float_to_int_expr_f32_neg_one_to_u32_saturates_zero() {
        // Part of #3668: f32 -1.0 → u32 0 (Rust `as` saturating semantics)
        let result =
            super::build_float_to_int_expr(&Expr::bitvec_const(0xbf80_0000u64, 32), 32, false)
                .expect("f32→u32 builder for -1.0");
        assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
    }

    #[test]
    fn test_build_float_to_int_expr_f64_neg_to_u64_saturates_zero() {
        // Part of #3668: f64 -42.0 → u64 0
        let r = super::build_float_to_int_expr(
            &Expr::bitvec_const(0xC045_0000_0000_0000u64, 64),
            64,
            false,
        )
        .expect("f64→u64 builder for -42.0");
        assert_bv_expr_eq(r, Expr::bitvec_const(0u64, 64));
    }

    #[test]
    fn test_ieee754_params_coverage() {
        assert!(super::ieee754_params(16).is_some());
        assert!(super::ieee754_params(32).is_some());
        assert!(super::ieee754_params(64).is_some());
        assert!(super::ieee754_params(128).is_some());
        assert!(super::ieee754_params(8).is_none());
    }
}

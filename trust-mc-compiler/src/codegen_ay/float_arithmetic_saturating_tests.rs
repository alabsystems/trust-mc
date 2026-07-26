// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::float_to_int_saturating_bv;

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;

#[derive(Debug, Clone, PartialEq)]
enum ConstValue {
    Bool(bool),
    Bv(BigInt, u32),
    Fp(FpConst),
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum FpConst {
    Finite(f64),
    PosInf,
    NegInf,
    Nan,
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
        ExprValue::Eq(lhs, rhs) => ConstValue::Bool(eval_const_expr(lhs) == eval_const_expr(rhs)),
        ExprValue::Distinct(args) => ConstValue::Bool(args.iter().enumerate().all(|(i, lhs)| {
            args.iter().skip(i + 1).all(|rhs| eval_const_expr(lhs) != eval_const_expr(rhs))
        })),
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
            let value = if amount >= width as usize { BigInt::from(0u8) } else { lhs << amount };
            ConstValue::Bv(normalize_bv(value, width), width)
        }
        ExprValue::BvLShr(lhs, rhs) => {
            let (lhs, width) = eval_bv_expr(lhs);
            let (rhs, rhs_width) = eval_bv_expr(rhs);
            assert_eq!(width, rhs_width);
            let amount = small_usize_or_cap(&rhs, width as usize);
            let value = if amount >= width as usize { BigInt::from(0u8) } else { lhs >> amount };
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
        ExprValue::FpPlusInfinity { .. } => ConstValue::Fp(FpConst::PosInf),
        ExprValue::FpMinusInfinity { .. } => ConstValue::Fp(FpConst::NegInf),
        ExprValue::FpNaN { .. } => ConstValue::Fp(FpConst::Nan),
        ExprValue::FpFromBvs(sign, exponent, significand) => {
            let (sign, sign_width) = eval_bv_expr(sign);
            let (exponent, eb) = eval_bv_expr(exponent);
            let (significand, sig_width) = eval_bv_expr(significand);
            assert_eq!(sign_width, 1);
            ConstValue::Fp(fp_from_bits(sign, exponent, significand, eb, sig_width + 1))
        }
        ExprValue::BvToFp(_, expr, eb, sb) => {
            let (value, width) = eval_bv_expr(expr);
            ConstValue::Fp(round_f64_to_fp(
                signed_bv_value(&value, width).to_string().parse().expect("signed BV as f64"),
                *eb,
                *sb,
            ))
        }
        ExprValue::BvToFpUnsigned(_, expr, eb, sb) => {
            let (value, _) = eval_bv_expr(expr);
            ConstValue::Fp(round_f64_to_fp(
                value.to_string().parse().expect("unsigned BV as f64"),
                *eb,
                *sb,
            ))
        }
        ExprValue::FpIsNaN(expr) => ConstValue::Bool(matches!(eval_fp_expr(expr), FpConst::Nan)),
        ExprValue::FpEq(lhs, rhs) => {
            let lhs = eval_fp_expr(lhs);
            let rhs = eval_fp_expr(rhs);
            ConstValue::Bool(
                !matches!(lhs, FpConst::Nan) && !matches!(rhs, FpConst::Nan) && lhs == rhs,
            )
        }
        ExprValue::FpLt(lhs, rhs) => {
            ConstValue::Bool(eval_fp_order(lhs, rhs, |lhs, rhs| lhs < rhs))
        }
        ExprValue::FpGt(lhs, rhs) => {
            ConstValue::Bool(eval_fp_order(lhs, rhs, |lhs, rhs| lhs > rhs))
        }
        other => panic!("unsupported constant expression in test evaluator: {other:?}"),
    }
}

fn eval_fp_expr(expr: &Expr) -> FpConst {
    match eval_const_expr(expr) {
        ConstValue::Fp(value) => value,
        other => panic!("expected FP expression, got {other:?} from {expr}"),
    }
}

fn fp_from_bits(sign: BigInt, exponent: BigInt, significand: BigInt, eb: u32, sb: u32) -> FpConst {
    let sig_width = sb - 1;
    let bits = (sign << (eb + sig_width) as usize) | (exponent << sig_width as usize) | significand;
    match (eb, sb) {
        (8, 24) => {
            FpConst::Finite(f32::from_bits(bits.to_string().parse().expect("f32 bits")).into())
        }
        (11, 53) => FpConst::Finite(f64::from_bits(bits.to_string().parse().expect("f64 bits"))),
        _ => panic!("unsupported FP width eb={eb}, sb={sb} in test evaluator"),
    }
}

fn round_f64_to_fp(value: f64, eb: u32, sb: u32) -> FpConst {
    match (eb, sb) {
        (8, 24) => FpConst::Finite((value as f32).into()),
        (11, 53) => FpConst::Finite(value),
        _ => panic!("unsupported FP width eb={eb}, sb={sb} in test evaluator"),
    }
}

fn eval_fp_order(lhs: &Expr, rhs: &Expr, op: impl FnOnce(f64, f64) -> bool) -> bool {
    let lhs = eval_fp_expr(lhs);
    let rhs = eval_fp_expr(rhs);
    if matches!(lhs, FpConst::Nan) || matches!(rhs, FpConst::Nan) {
        false
    } else {
        op(fp_as_ordered_f64(lhs), fp_as_ordered_f64(rhs))
    }
}

fn fp_as_ordered_f64(value: FpConst) -> f64 {
    match value {
        FpConst::Finite(value) => value,
        FpConst::PosInf => f64::INFINITY,
        FpConst::NegInf => f64::NEG_INFINITY,
        FpConst::Nan => panic!("NaN has no FP ordering"),
    }
}

fn eval_bv_binop(lhs: &Expr, rhs: &Expr, op: impl FnOnce(BigInt, BigInt) -> BigInt) -> ConstValue {
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
fn test_float_to_int_saturating_bv_f32_above_max_to_u8() {
    let src = Expr::bitvec_const(0x4396_0000u64, 32); // 300.0f32
    let result = float_to_int_saturating_bv(src, 8, false).expect("f32 supported");
    assert_bv_expr_eq(result, Expr::bitvec_const(255u64, 8));
}

#[test]
fn test_float_to_int_saturating_bv_f32_neg_below_min_to_i8() {
    let src = Expr::bitvec_const(0xC348_0000u64, 32); // -200.0f32
    let result = float_to_int_saturating_bv(src, 8, true).expect("f32 supported");
    assert_bv_expr_eq(result, Expr::bitvec_const(i8::MIN as i128, 8));
}

#[test]
fn test_float_to_int_saturating_bv_f32_infinity_to_u8() {
    let src = Expr::bitvec_const(0x7F80_0000u64, 32); // +inf
    let result = float_to_int_saturating_bv(src, 8, false).expect("f32 supported");
    assert_bv_expr_eq(result, Expr::bitvec_const(255u64, 8));
}

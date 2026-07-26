// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for pure BV rounding functions (float_rounding.rs).
//! Part of #3750.

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;

use crate::codegen_ay::chc::codegen_call_cmp_string::float_rounding;

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
        other => panic!("unsupported constant expression in test evaluator: {other:?}"),
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

// ===== trunc =====

#[test]
fn test_build_float_trunc_bv_f32_positive_frac() {
    // trunc(3.7f32) = 3.0f32
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0x404C_CCCDu64, 32))
        .expect("f32 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4040_0000u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_negative_frac() {
    // trunc(-2.3f32) = -2.0f32
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0xC013_3333u64, 32))
        .expect("f32 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC000_0000u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_sub_one() {
    // trunc(0.5f32) = 0.0f32
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0x3F00_0000u64, 32))
        .expect("f32 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_neg_sub_one() {
    // trunc(-0.5f32) = -0.0f32 = 0x80000000
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0xBF00_0000u64, 32))
        .expect("f32 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x8000_0000u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_integer() {
    // trunc(42.0f32) = 42.0f32 (unchanged)
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0x4228_0000u64, 32))
        .expect("f32 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4228_0000u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_nan_passthrough() {
    let nan = 0x7FC0_0000u64;
    let result =
        float_rounding::build_float_trunc_bv(&Expr::bitvec_const(nan, 32)).expect("f32 trunc NaN");
    assert_bv_expr_eq(result, Expr::bitvec_const(nan, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_inf_passthrough() {
    let inf = 0x7F80_0000u64;
    let result =
        float_rounding::build_float_trunc_bv(&Expr::bitvec_const(inf, 32)).expect("f32 trunc Inf");
    assert_bv_expr_eq(result, Expr::bitvec_const(inf, 32));
}

#[test]
fn test_build_float_trunc_bv_f32_zero() {
    let result = float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0u64, 32))
        .expect("f32 trunc zero");
    assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
}

#[test]
fn test_build_float_trunc_bv_f64() {
    // trunc(3.7f64) = 3.0f64
    let result =
        float_rounding::build_float_trunc_bv(&Expr::bitvec_const(0x400D_9999_9999_999Au64, 64))
            .expect("f64 trunc builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4008_0000_0000_0000u64, 64));
}

// ===== floor =====

#[test]
fn test_build_float_floor_bv_f32_positive() {
    // floor(3.7f32) = 3.0f32
    let result = float_rounding::build_float_floor_bv(&Expr::bitvec_const(0x404C_CCCDu64, 32))
        .expect("f32 floor builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4040_0000u64, 32));
}

#[test]
fn test_build_float_floor_bv_f32_negative() {
    // floor(-2.3f32) = -3.0f32
    let result = float_rounding::build_float_floor_bv(&Expr::bitvec_const(0xC013_3333u64, 32))
        .expect("f32 floor builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC040_0000u64, 32));
}

#[test]
fn test_build_float_floor_bv_f32_neg_sub_one() {
    // floor(-0.5f32) = -1.0f32 = 0xBF800000
    let result = float_rounding::build_float_floor_bv(&Expr::bitvec_const(0xBF00_0000u64, 32))
        .expect("f32 floor builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xBF80_0000u64, 32));
}

#[test]
fn test_build_float_floor_bv_f32_pos_zero_unchanged() {
    // floor(+0.0f32) = +0.0f32
    let result = float_rounding::build_float_floor_bv(&Expr::bitvec_const(0x0000_0000u64, 32))
        .expect("f32 floor +0.0");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x0000_0000u64, 32));
}

#[test]
fn test_build_float_floor_bv_f32_neg_zero_unchanged() {
    // floor(-0.0f32) = -0.0f32, not -1.0f32
    let result = float_rounding::build_float_floor_bv(&Expr::bitvec_const(0x8000_0000u64, 32))
        .expect("f32 floor -0.0");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x8000_0000u64, 32));
}

#[test]
fn test_build_float_floor_bv_f64_negative() {
    // floor(-2.3f64) = -3.0f64
    let result =
        float_rounding::build_float_floor_bv(&Expr::bitvec_const(0xC002_6666_6666_6666u64, 64))
            .expect("f64 floor builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC008_0000_0000_0000u64, 64));
}

// ===== ceil =====

#[test]
fn test_build_float_ceil_bv_f32_positive() {
    // ceil(1.1f32) = 2.0f32
    let result = float_rounding::build_float_ceil_bv(&Expr::bitvec_const(0x3F8C_CCCDu64, 32))
        .expect("f32 ceil builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4000_0000u64, 32));
}

#[test]
fn test_build_float_ceil_bv_f32_negative() {
    // ceil(-2.3f32) = -2.0f32 (toward +inf)
    let result = float_rounding::build_float_ceil_bv(&Expr::bitvec_const(0xC013_3333u64, 32))
        .expect("f32 ceil builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC000_0000u64, 32));
}

#[test]
fn test_build_float_ceil_bv_f32_pos_sub_one() {
    // ceil(0.5f32) = 1.0f32 = 0x3F800000
    let result = float_rounding::build_float_ceil_bv(&Expr::bitvec_const(0x3F00_0000u64, 32))
        .expect("f32 ceil builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x3F80_0000u64, 32));
}

#[test]
fn test_build_float_ceil_bv_f32_pos_zero_unchanged() {
    // ceil(+0.0f32) = +0.0f32, not +1.0f32
    let result = float_rounding::build_float_ceil_bv(&Expr::bitvec_const(0x0000_0000u64, 32))
        .expect("f32 ceil +0.0");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x0000_0000u64, 32));
}

#[test]
fn test_build_float_ceil_bv_f32_neg_zero_unchanged() {
    // ceil(-0.0f32) = -0.0f32
    let result = float_rounding::build_float_ceil_bv(&Expr::bitvec_const(0x8000_0000u64, 32))
        .expect("f32 ceil -0.0");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x8000_0000u64, 32));
}

// ===== round (ties away) =====

#[test]
fn test_build_float_round_bv_f32_ties_away() {
    // round(2.5f32) = 3.0f32 (ties away from zero)
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0x4020_0000u64, 32))
        .expect("f32 round builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4040_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_down() {
    // round(2.3f32) = 2.0f32
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0x4013_3333u64, 32))
        .expect("f32 round builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4000_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_sub_one_half() {
    // round(0.5f32) = 1.0f32 (ties away from zero)
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0x3F00_0000u64, 32))
        .expect("f32 round 0.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x3F80_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_sub_one_quarter() {
    // round(0.25f32) = 0.0f32 (< 0.5, round to zero)
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0x3E80_0000u64, 32))
        .expect("f32 round 0.25");
    assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
}

// Part of #3750: negative boundary tests for round().
// round(-0.5) = -1.0 (ties away from zero), round(-2.5) = -3.0, round(-0.25) = -0.0.

#[test]
fn test_build_float_round_bv_f32_neg_sub_one_half() {
    // round(-0.5f32) = -1.0f32 (ties away from zero)
    // -0.5f32 = 0xBF000000, -1.0f32 = 0xBF800000
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0xBF00_0000u64, 32))
        .expect("f32 round -0.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xBF80_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_neg_ties_away() {
    // round(-2.5f32) = -3.0f32 (ties away from zero)
    // -2.5f32 = 0xC0200000, -3.0f32 = 0xC0400000
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0xC020_0000u64, 32))
        .expect("f32 round -2.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC040_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_neg_sub_one_quarter() {
    // round(-0.25f32) = -0.0f32 (< 0.5, round to signed zero)
    // -0.25f32 = 0xBE800000, -0.0f32 = 0x80000000
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0xBE80_0000u64, 32))
        .expect("f32 round -0.25");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x8000_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f32_neg_down() {
    // round(-2.3f32) = -2.0f32 (fraction < 0.5, round toward zero)
    // -2.3f32 = 0xC0133333, -2.0f32 = 0xC0000000
    let result = float_rounding::build_float_round_bv(&Expr::bitvec_const(0xC013_3333u64, 32))
        .expect("f32 round -2.3");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC000_0000u64, 32));
}

#[test]
fn test_build_float_round_bv_f64_neg_ties_away() {
    // round(-2.5f64) = -3.0f64 (ties away from zero)
    // -2.5f64 = 0xC004000000000000, -3.0f64 = 0xC008000000000000
    let result =
        float_rounding::build_float_round_bv(&Expr::bitvec_const(0xC004_0000_0000_0000u64, 64))
            .expect("f64 round -2.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC008_0000_0000_0000u64, 64));
}

// ===== round_ties_even =====

#[test]
fn test_build_float_round_ties_even_bv_f32_half_to_even() {
    // round_ties_even(2.5f32) = 2.0f32 (tie: 2 is even)
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0x4020_0000u64, 32))
            .expect("f32 round_ties_even builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4000_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_half_to_even_up() {
    // round_ties_even(3.5f32) = 4.0f32 (tie: 4 is even)
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0x4060_0000u64, 32))
            .expect("f32 round_ties_even builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4080_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_above_half() {
    // round_ties_even(2.6f32) = 3.0f32 (fraction > 0.5, round away)
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0x4026_6666u64, 32))
            .expect("f32 round_ties_even builder");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x4040_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_sub_one_half() {
    // round_ties_even(0.5f32) = 0.0f32 (tie: 0 is even)
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0x3F00_0000u64, 32))
            .expect("f32 round_ties_even 0.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_sub_one_above_half() {
    // round_ties_even(0.6f32) = 1.0f32 (> 0.5, round away)
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0x3F19_999Au64, 32))
            .expect("f32 round_ties_even 0.6");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x3F80_0000u64, 32));
}

// Part of #3750: negative boundary tests for round_ties_even().
// Exercises sign-dependent paths in the BV rounding implementation.

#[test]
fn test_build_float_round_ties_even_bv_f32_neg_half_to_even() {
    // round_ties_even(-2.5f32) = -2.0f32 (tie: 2 is even, round toward zero)
    // -2.5f32 = 0xC0200000, -2.0f32 = 0xC0000000
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0xC020_0000u64, 32))
            .expect("f32 round_ties_even -2.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC000_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_neg_half_to_even_away() {
    // round_ties_even(-3.5f32) = -4.0f32 (tie: 4 is even, round away from zero)
    // -3.5f32 = 0xC0600000, -4.0f32 = 0xC0800000
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0xC060_0000u64, 32))
            .expect("f32 round_ties_even -3.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC080_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_neg_above_half() {
    // round_ties_even(-2.6f32) = -3.0f32 (fraction > 0.5, round away from zero)
    // -2.6f32 = 0xC0266666, -3.0f32 = 0xC0400000
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0xC026_6666u64, 32))
            .expect("f32 round_ties_even -2.6");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xC040_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_neg_sub_one_half() {
    // round_ties_even(-0.5f32) = -0.0f32 (tie: 0 is even)
    // -0.5f32 = 0xBF000000, -0.0f32 = 0x80000000
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0xBF00_0000u64, 32))
            .expect("f32 round_ties_even -0.5");
    assert_bv_expr_eq(result, Expr::bitvec_const(0x8000_0000u64, 32));
}

#[test]
fn test_build_float_round_ties_even_bv_f32_neg_sub_one_above_half() {
    // round_ties_even(-0.6f32) = -1.0f32 (> 0.5, round away from zero)
    // -0.6f32 = 0xBF19999A, -1.0f32 = 0xBF800000
    let result =
        float_rounding::build_float_round_ties_even_bv(&Expr::bitvec_const(0xBF19_999Au64, 32))
            .expect("f32 round_ties_even -0.6");
    assert_bv_expr_eq(result, Expr::bitvec_const(0xBF80_0000u64, 32));
}

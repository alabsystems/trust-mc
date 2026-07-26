// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for constant expression evaluation (chc_const_prop_eval).

use super::{
    eval_bv_binary_const, eval_select_store_const, flatten_conjunctions, has_false_conjunct,
    is_trivially_true, try_eval_to_bool, try_eval_to_const,
};
use crate::constraints::Constraints;
use ay_bindings::{Expr, Sort};

fn bv(value: i64, width: u32) -> Expr {
    Expr::bitvec_const(value, width)
}

fn eval_binary(expr: Expr, a: &Expr, b: &Expr) -> Option<Expr> {
    eval_bv_binary_const(expr.value(), a, b)
}

#[test]
fn test_eval_bv_binary_const_add_wraps_on_overflow() {
    let lhs = Expr::bitvec_const(0xFFu64, 8);
    let rhs = Expr::bitvec_const(1u64, 8);
    let result = eval_binary(lhs.clone().bvadd(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_urem_div_by_zero_returns_none() {
    let lhs = bv(7, 8);
    let rhs = bv(0, 8);
    let result = eval_binary(lhs.clone().bvurem(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "division-by-zero folding must stay conservative");
}

#[test]
fn test_eval_bv_binary_const_shift_past_width_returns_zero() {
    let lhs = bv(0b1010, 8);
    let rhs = bv(9, 8);
    let result = eval_binary(lhs.clone().bvshl(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_concat_merges_operands() {
    let lhs = Expr::bitvec_const(0xABu64, 8);
    let rhs = Expr::bitvec_const(0xCDu64, 8);
    let result = eval_binary(lhs.clone().concat(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0xABCDu64, 16)));
}

#[test]
fn test_eval_bv_binary_const_add_no_overflow_unsigned_false_on_carry() {
    let lhs = Expr::bitvec_const(0xFFu64, 8);
    let rhs = Expr::bitvec_const(1u64, 8);
    let result = eval_binary(lhs.clone().bvadd_no_overflow_unsigned(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(false)));
}

#[test]
fn test_eval_bv_binary_const_signed_division_rounds_toward_zero() {
    let lhs = bv(-7, 8);
    let rhs = bv(2, 8);
    let result = eval_binary(lhs.clone().bvsdiv(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-3, 8)));
}

#[test]
fn test_eval_bv_binary_const_signed_remainder_keeps_dividend_sign() {
    let lhs = bv(-7, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvsrem(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-1, 8)));
}

#[test]
fn test_eval_bv_binary_const_signed_division_int_min_overflow_matches_solver() {
    let lhs = bv(-128, 8);
    let rhs = bv(-1, 8);
    let result = eval_binary(lhs.clone().bvsdiv(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-128, 8)));
}

#[test]
fn test_eval_bv_binary_const_arithmetic_shift_preserves_sign_bit() {
    let lhs = bv(-1, 8);
    let rhs = bv(1, 8);
    let result = eval_binary(lhs.clone().bvashr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-1, 8)));
}

#[test]
fn test_eval_bv_binary_const_signed_comparison_uses_twos_complement_order() {
    let lhs = bv(-1, 8);
    let rhs = bv(1, 8);
    let result = eval_binary(lhs.clone().bvslt(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_select_store_const_same_symbolic_index_returns_stored_value() {
    let array = Expr::var("arr", Sort::array(Sort::bitvec(8), Sort::bool()));
    let index = Expr::var("idx", Sort::bitvec(8));
    let value = Expr::bool_const(false);
    let stored = array.store(index.clone(), value.clone());
    assert_eq!(eval_select_store_const(&stored, &index), Some(value));
}

#[test]
fn test_eval_select_store_const_different_constant_index_returns_none() {
    let array = Expr::var("arr", Sort::array(Sort::bitvec(8), Sort::bool()));
    let stored = array.store(bv(1, 8), Expr::bool_const(false));
    assert_eq!(eval_select_store_const(&stored, &bv(2, 8)), None);
}

#[test]
fn test_eval_select_store_const_nested_store_recurses_to_matching_write() {
    let array = Expr::var("arr", Sort::array(Sort::bitvec(8), Sort::bool()));
    let first = array.store(bv(1, 8), Expr::bool_const(false));
    let second = first.store(bv(2, 8), Expr::bool_const(true));
    assert_eq!(eval_select_store_const(&second, &bv(1, 8)), Some(Expr::bool_const(false)));
}

#[test]
fn test_has_false_conjunct_finds_nested_false() {
    let constraints = Constraints::Owned(vec![Expr::bool_const(true).and(Expr::bool_const(false))]);
    assert!(has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_ignores_true_only_constraints() {
    let constraints =
        Constraints::Owned(vec![Expr::bool_const(true).and(Expr::var("flag", Sort::bool()))]);
    assert!(!has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_not_eq_const_const() {
    // `(not (= #x00000000 #x00000000))` — dead branch from SwitchInt
    let zero = Expr::bitvec_const(0u64, 32);
    let eq = zero.clone().eq(zero);
    let not_eq = eq.not();
    let constraints = Constraints::Owned(vec![not_eq]);
    assert!(has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_eq_different_consts() {
    // `(= #x00000000 #x00000001)` — trivially false equality
    let zero = Expr::bitvec_const(0u64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    let constraints = Constraints::Owned(vec![zero.eq(one)]);
    assert!(has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_not_eq_different_consts_is_not_false() {
    // `(not (= #x00000000 #x00000001))` — trivially TRUE, not false
    let zero = Expr::bitvec_const(0u64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    let not_eq = zero.eq(one).not();
    let constraints = Constraints::Owned(vec![not_eq]);
    assert!(!has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_not_bvuge_const_const() {
    // cover_simple pattern: `(not (bvuge (bvadd (extract[31:0] (concat 3 0)) 1) (extract[31:0] (concat 3 0))))`
    // extract[31:0](concat(#x3, #x0)) = #x0, bvadd(#x0, #x1) = #x1, bvuge(1, 0) = true, not(true) = false
    let hi = Expr::bitvec_const(3u64, 32);
    let lo = Expr::bitvec_const(0u64, 32);
    let concat = hi.concat(lo);
    let extracted = concat.extract(31, 0);
    let one = Expr::bitvec_const(1u64, 32);
    let sum = extracted.clone().bvadd(one);
    let cmp = sum.bvuge(extracted);
    let negated = cmp.not();
    let constraints = Constraints::Owned(vec![negated]);
    assert!(has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_bvuge_const_true_is_not_false() {
    // bvuge(#x05, #x03) = true — should NOT be detected as false
    let a = bv(5, 8);
    let b = bv(3, 8);
    let cmp = a.bvuge(b);
    let constraints = Constraints::Owned(vec![cmp]);
    assert!(!has_false_conjunct(&constraints));
}

#[test]
fn test_is_trivially_true_bvuge_const() {
    // bvuge(#xFF, #x01) = true
    let a = Expr::bitvec_const(0xFFu64, 8);
    let b = Expr::bitvec_const(1u64, 8);
    assert!(is_trivially_true(&a.bvuge(b)));
}

#[test]
fn test_is_trivially_true_not_bvult_const() {
    // not(bvult(5, 3)) = not(false) = true
    let a = bv(5, 8);
    let b = bv(3, 8);
    assert!(is_trivially_true(&a.bvult(b).not()));
}

// =========================================================================
// eval_bv_binary_const: unsigned arithmetic coverage
// =========================================================================

#[test]
fn test_eval_bv_binary_const_sub_wraps_on_underflow() {
    // 0 - 1 should wrap to 0xFF for 8-bit unsigned
    let lhs = bv(0, 8);
    let rhs = bv(1, 8);
    let result = eval_binary(lhs.clone().bvsub(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0xFFu64, 8)));
}

#[test]
fn test_eval_bv_binary_const_sub_normal() {
    let lhs = bv(10, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvsub(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(7, 8)));
}

#[test]
fn test_eval_bv_binary_const_mul_normal() {
    let lhs = bv(6, 8);
    let rhs = bv(7, 8);
    let result = eval_binary(lhs.clone().bvmul(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(42, 8)));
}

#[test]
fn test_eval_bv_binary_const_mul_overflow_wraps() {
    // 128 * 3 = 384, mod 256 = 128
    let lhs = bv(128, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvmul(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(128, 8)));
}

#[test]
fn test_eval_bv_binary_const_udiv_normal() {
    let lhs = bv(42, 8);
    let rhs = bv(7, 8);
    let result = eval_binary(lhs.clone().bvudiv(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(6, 8)));
}

#[test]
fn test_eval_bv_binary_const_udiv_by_zero_returns_none() {
    let lhs = bv(42, 8);
    let rhs = bv(0, 8);
    let result = eval_binary(lhs.clone().bvudiv(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "unsigned division by zero must return None");
}

#[test]
fn test_eval_bv_binary_const_urem_normal() {
    let lhs = bv(17, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvurem(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(2, 8)));
}

// =========================================================================
// eval_bv_binary_const: bitwise operations
// =========================================================================

#[test]
fn test_eval_bv_binary_const_and() {
    let lhs = Expr::bitvec_const(0b1100_1010u64, 8);
    let rhs = Expr::bitvec_const(0b1010_0110u64, 8);
    let result = eval_binary(lhs.clone().bvand(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0b1000_0010u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_or() {
    let lhs = Expr::bitvec_const(0b1100_0000u64, 8);
    let rhs = Expr::bitvec_const(0b0000_1100u64, 8);
    let result = eval_binary(lhs.clone().bvor(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0b1100_1100u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_xor() {
    let lhs = Expr::bitvec_const(0b1111_0000u64, 8);
    let rhs = Expr::bitvec_const(0b1010_1010u64, 8);
    let result = eval_binary(lhs.clone().bvxor(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0b0101_1010u64, 8)));
}

// =========================================================================
// eval_bv_binary_const: shifts
// =========================================================================

#[test]
fn test_eval_bv_binary_const_shl_normal() {
    let lhs = bv(1, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvshl(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(8, 8)));
}

#[test]
fn test_eval_bv_binary_const_lshr_normal() {
    let lhs = Expr::bitvec_const(0x80u64, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvlshr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0x10u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_lshr_past_width_returns_zero() {
    let lhs = Expr::bitvec_const(0xFFu64, 8);
    let rhs = bv(8, 8);
    let result = eval_binary(lhs.clone().bvlshr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0u64, 8)));
}

#[test]
fn test_eval_bv_binary_const_ashr_positive_value() {
    // Arithmetic shift right of a positive value is same as logical shift right
    let lhs = bv(64, 8); // 0x40 — positive in 8-bit signed
    let rhs = bv(2, 8);
    let result = eval_binary(lhs.clone().bvashr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(16, 8)));
}

#[test]
fn test_eval_bv_binary_const_ashr_past_width_negative_returns_all_ones() {
    // Arithmetic shift of -1 by >= width gives -1 (all ones)
    let lhs = bv(-1, 8);
    let rhs = bv(100, 8);
    let result = eval_binary(lhs.clone().bvashr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-1, 8)));
}

#[test]
fn test_eval_bv_binary_const_ashr_past_width_positive_returns_zero() {
    // Arithmetic shift of 1 by >= width gives 0
    let lhs = bv(1, 8);
    let rhs = bv(100, 8);
    let result = eval_binary(lhs.clone().bvashr(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(0, 8)));
}

// =========================================================================
// eval_bv_binary_const: unsigned comparisons
// =========================================================================

#[test]
fn test_eval_bv_binary_const_ult_true() {
    let lhs = bv(3, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvult(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_ult_false_equal() {
    let lhs = bv(5, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvult(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(false)));
}

#[test]
fn test_eval_bv_binary_const_ule_true_equal() {
    let lhs = bv(5, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvule(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_ugt_true() {
    let lhs = bv(10, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvugt(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_uge_true_equal() {
    let lhs = bv(5, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvuge(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

// =========================================================================
// eval_bv_binary_const: signed comparisons (all 4 variants)
// =========================================================================

#[test]
fn test_eval_bv_binary_const_sle_true_equal() {
    let lhs = bv(-5, 8);
    let rhs = bv(-5, 8);
    let result = eval_binary(lhs.clone().bvsle(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sle_true_less() {
    let lhs = bv(-10, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvsle(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sgt_true() {
    let lhs = bv(5, 8);
    let rhs = bv(-1, 8);
    let result = eval_binary(lhs.clone().bvsgt(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sgt_false_equal() {
    let lhs = bv(5, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvsgt(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(false)));
}

#[test]
fn test_eval_bv_binary_const_sge_true_equal() {
    let lhs = bv(-128, 8);
    let rhs = bv(-128, 8);
    let result = eval_binary(lhs.clone().bvsge(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sge_false() {
    let lhs = bv(-128, 8);
    let rhs = bv(127, 8);
    let result = eval_binary(lhs.clone().bvsge(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(false)));
}

// =========================================================================
// eval_bv_binary_const: signed arithmetic edge cases
// =========================================================================

#[test]
fn test_eval_bv_binary_const_sdiv_by_zero_returns_none() {
    let lhs = bv(-7, 8);
    let rhs = bv(0, 8);
    let result = eval_binary(lhs.clone().bvsdiv(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "signed division by zero must return None");
}

#[test]
fn test_eval_bv_binary_const_srem_by_zero_returns_none() {
    let lhs = bv(10, 8);
    let rhs = bv(0, 8);
    let result = eval_binary(lhs.clone().bvsrem(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "signed remainder by zero must return None");
}

#[test]
fn test_eval_bv_binary_const_srem_both_negative() {
    // SMT-LIB: bvsrem(-7, -3) = -1 (sign of dividend)
    let lhs = bv(-7, 8);
    let rhs = bv(-3, 8);
    let result = eval_binary(lhs.clone().bvsrem(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(-1, 8)));
}

#[test]
fn test_eval_bv_binary_const_sdiv_positive_both() {
    let lhs = bv(20, 8);
    let rhs = bv(3, 8);
    let result = eval_binary(lhs.clone().bvsdiv(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(6, 8)));
}

// =========================================================================
// eval_bv_binary_const: overflow checks
// =========================================================================

#[test]
fn test_eval_bv_binary_const_add_no_overflow_unsigned_true_no_carry() {
    let lhs = bv(100, 8);
    let rhs = bv(50, 8);
    let result = eval_binary(lhs.clone().bvadd_no_overflow_unsigned(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sub_no_underflow_unsigned_true() {
    let lhs = bv(10, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_eval_bv_binary_const_sub_no_underflow_unsigned_false() {
    let lhs = bv(3, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(false)));
}

#[test]
fn test_eval_bv_binary_const_sub_no_underflow_unsigned_equal() {
    // a >= b when a == b is true
    let lhs = bv(5, 8);
    let rhs = bv(5, 8);
    let result = eval_binary(lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

// =========================================================================
// eval_bv_binary_const: non-constant operand returns None
// =========================================================================

#[test]
fn test_eval_bv_binary_const_non_constant_lhs_returns_none() {
    let lhs = Expr::var("x", Sort::bitvec(8));
    let rhs = bv(1, 8);
    let result = eval_binary(lhs.clone().bvadd(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "non-constant LHS must return None");
}

#[test]
fn test_eval_bv_binary_const_non_constant_rhs_returns_none() {
    let lhs = bv(1, 8);
    let rhs = Expr::var("x", Sort::bitvec(8));
    let result = eval_binary(lhs.clone().bvadd(rhs.clone()), &lhs, &rhs);
    assert!(result.is_none(), "non-constant RHS must return None");
}

// =========================================================================
// eval_bv_binary_const: 1-bit and 64-bit widths
// =========================================================================

#[test]
fn test_eval_bv_binary_const_1bit_add_wraps() {
    // 1-bit: 1 + 1 = 0 (mod 2)
    let lhs = bv(1, 1);
    let rhs = bv(1, 1);
    let result = eval_binary(lhs.clone().bvadd(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(bv(0, 1)));
}

#[test]
fn test_eval_bv_binary_const_64bit_add() {
    let lhs = Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64);
    let rhs = Expr::bitvec_const(1u64, 64);
    let result = eval_binary(lhs.clone().bvadd(rhs.clone()), &lhs, &rhs);
    assert_eq!(result, Some(Expr::bitvec_const(0x8000_0000_0000_0000u64, 64)));
}

// =========================================================================
// try_eval_to_const: unary operations
// =========================================================================

#[test]
fn test_try_eval_to_const_extract() {
    // extract[7:4](0xAB) = 0x0A
    let val = Expr::bitvec_const(0xABu64, 8);
    let expr = val.extract(7, 4);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(Expr::bitvec_const(0x0Au64, 4)));
}

#[test]
fn test_try_eval_to_const_extract_low_bits() {
    // extract[3:0](0xAB) = 0x0B
    let val = Expr::bitvec_const(0xABu64, 8);
    let expr = val.extract(3, 0);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(Expr::bitvec_const(0x0Bu64, 4)));
}

#[test]
fn test_try_eval_to_const_zero_extend() {
    // zero_extend(0xFF, 8) from 8-bit to 16-bit = 0x00FF
    let val = Expr::bitvec_const(0xFFu64, 8);
    let expr = val.zero_extend(8);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(Expr::bitvec_const(0xFFu64, 16)));
}

#[test]
fn test_try_eval_to_const_sign_extend_negative() {
    // sign_extend(-1, 8) from 8-bit to 16-bit = 0xFFFF (all ones)
    let val = bv(-1, 8);
    let expr = val.sign_extend(8);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(bv(-1, 16)));
}

#[test]
fn test_try_eval_to_const_sign_extend_positive() {
    // sign_extend(127, 8) from 8-bit to 16-bit = 127
    let val = bv(127, 8);
    let expr = val.sign_extend(8);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(bv(127, 16)));
}

#[test]
fn test_try_eval_to_const_bvnot() {
    // bvnot(0x0F) for 8-bit = 0xF0
    let val = Expr::bitvec_const(0x0Fu64, 8);
    let expr = val.bvnot();
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(Expr::bitvec_const(0xF0u64, 8)));
}

#[test]
fn test_try_eval_to_const_bvneg() {
    // bvneg(1) for 8-bit = 0xFF (two's complement of 1 = -1 = 255)
    let val = bv(1, 8);
    let expr = val.bvneg();
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(bv(-1, 8)));
}

#[test]
fn test_try_eval_to_const_bvneg_zero() {
    // bvneg(0) for 8-bit = 0
    let val = bv(0, 8);
    let expr = val.bvneg();
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(bv(0, 8)));
}

#[test]
fn test_try_eval_to_const_nested_arithmetic() {
    // (3 + 5) * 2 = 16
    let three = bv(3, 8);
    let five = bv(5, 8);
    let two = bv(2, 8);
    let sum = three.bvadd(five);
    let expr = sum.bvmul(two);
    let result = try_eval_to_const(&expr);
    assert_eq!(result, Some(bv(16, 8)));
}

#[test]
fn test_try_eval_to_const_non_constant_returns_none() {
    let var = Expr::var("x", Sort::bitvec(8));
    let result = try_eval_to_const(&var);
    assert!(result.is_none());
}

#[test]
fn test_try_eval_to_const_passthrough_bool() {
    let b = Expr::bool_const(true);
    let result = try_eval_to_const(&b);
    assert_eq!(result, Some(Expr::bool_const(true)));
}

#[test]
fn test_try_eval_to_const_passthrough_bv() {
    let bv_val = bv(42, 8);
    let result = try_eval_to_const(&bv_val);
    assert_eq!(result, Some(bv(42, 8)));
}

// =========================================================================
// try_eval_to_bool: boolean logic
// =========================================================================

#[test]
fn test_try_eval_to_bool_and_all_true() {
    let expr = Expr::bool_const(true).and(Expr::bool_const(true));
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_and_one_false() {
    let expr = Expr::bool_const(true).and(Expr::bool_const(false));
    assert_eq!(try_eval_to_bool(&expr), Some(false));
}

#[test]
fn test_try_eval_to_bool_and_with_unknown() {
    // And(true, unknown_var) — can't determine
    let expr = Expr::bool_const(true).and(Expr::var("x", Sort::bool()));
    assert_eq!(try_eval_to_bool(&expr), None);
}

#[test]
fn test_try_eval_to_bool_and_short_circuit_false() {
    // And(false, unknown_var) — short-circuits to false
    let expr = Expr::bool_const(false).and(Expr::var("x", Sort::bool()));
    assert_eq!(try_eval_to_bool(&expr), Some(false));
}

#[test]
fn test_try_eval_to_bool_or_one_true() {
    let expr = Expr::bool_const(false).or(Expr::bool_const(true));
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_or_all_false() {
    let expr = Expr::bool_const(false).or(Expr::bool_const(false));
    assert_eq!(try_eval_to_bool(&expr), Some(false));
}

#[test]
fn test_try_eval_to_bool_or_with_unknown() {
    // Or(false, unknown_var) — can't determine
    let expr = Expr::bool_const(false).or(Expr::var("x", Sort::bool()));
    assert_eq!(try_eval_to_bool(&expr), None);
}

#[test]
fn test_try_eval_to_bool_or_short_circuit_true() {
    // Or(true, unknown_var) — short-circuits to true
    let expr = Expr::bool_const(true).or(Expr::var("x", Sort::bool()));
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_not_true() {
    let expr = Expr::bool_const(true).not();
    assert_eq!(try_eval_to_bool(&expr), Some(false));
}

#[test]
fn test_try_eval_to_bool_not_false() {
    let expr = Expr::bool_const(false).not();
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_eq_same_expr() {
    // Eq(x, x) is true even when x is non-constant (structural equality)
    let x = Expr::var("x", Sort::bitvec(8));
    let expr = x.clone().eq(x);
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_eq_different_constants() {
    let expr = bv(3, 8).eq(bv(5, 8));
    assert_eq!(try_eval_to_bool(&expr), Some(false));
}

#[test]
fn test_try_eval_to_bool_eq_same_constants() {
    let expr = bv(7, 8).eq(bv(7, 8));
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_eq_nested_bool_expression() {
    let addr = Expr::bitvec_const(2u64, 32).concat(Expr::bitvec_const(0u64, 32));
    let align_mask = bv(4, 64).bvsub(bv(1, 64));
    let aligned = addr.bvand(align_mask).eq(bv(0, 64));
    let wrapped = aligned.eq(Expr::bool_const(true));

    assert_eq!(try_eval_to_bool(&wrapped), Some(true));
    assert_eq!(try_eval_to_bool(&wrapped.clone().not()), Some(false));

    let constraints = Constraints::Owned(vec![wrapped.not()]);
    assert!(
        has_false_conjunct(&constraints),
        "constant true safety guards wrapped as `(= guard true)` must fold to false violations"
    );
}

#[test]
fn test_try_eval_to_bool_signed_comparison_through_eval() {
    // bvslt(-128, 127) should be true through try_eval_to_bool
    let expr = bv(-128, 8).bvslt(bv(127, 8));
    assert_eq!(try_eval_to_bool(&expr), Some(true));
}

#[test]
fn test_try_eval_to_bool_non_constant_returns_none() {
    let expr = Expr::var("flag", Sort::bool());
    assert_eq!(try_eval_to_bool(&expr), None);
}

// =========================================================================
// flatten_conjunctions
// =========================================================================

#[test]
fn test_flatten_conjunctions_simple() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);
    let constraints = Constraints::Owned(vec![a.clone(), b.clone()]);
    let flat = flatten_conjunctions(&constraints);
    assert_eq!(flat.len(), 2);
    assert_eq!(flat[0], a);
    assert_eq!(flat[1], b);
}

#[test]
fn test_flatten_conjunctions_nested_and() {
    let a = bv(1, 8).eq(bv(1, 8));
    let b = bv(2, 8).eq(bv(2, 8));
    let c = bv(3, 8).eq(bv(3, 8));
    let and_bc = b.clone().and(c.clone());
    let and_abc = a.clone().and(and_bc);
    let constraints = Constraints::Owned(vec![and_abc]);
    let flat = flatten_conjunctions(&constraints);
    // Should flatten to [a, b, c] instead of [And(a, And(b, c))]
    assert_eq!(flat.len(), 3);
}

#[test]
fn test_flatten_conjunctions_empty() {
    let constraints = Constraints::Owned(vec![]);
    let flat = flatten_conjunctions(&constraints);
    assert!(flat.is_empty());
}

// =========================================================================
// eval_select_store_const: additional edge cases
// =========================================================================

#[test]
fn test_eval_select_store_const_non_store_returns_none() {
    // If array is not a store, returns None
    let array = Expr::var("arr", Sort::array(Sort::bitvec(8), Sort::bool()));
    let index = bv(0, 8);
    assert_eq!(eval_select_store_const(&array, &index), None);
}

#[test]
fn test_eval_select_store_const_symbolic_index_mismatch_returns_none() {
    // Two different symbolic indices: can't determine equality
    let array = Expr::var("arr", Sort::array(Sort::bitvec(8), Sort::bool()));
    let idx1 = Expr::var("idx1", Sort::bitvec(8));
    let idx2 = Expr::var("idx2", Sort::bitvec(8));
    let stored = array.store(idx1, Expr::bool_const(true));
    assert_eq!(eval_select_store_const(&stored, &idx2), None);
}

// =========================================================================
// is_trivially_true: additional coverage
// =========================================================================

#[test]
fn test_is_trivially_true_bool_const_true() {
    assert!(is_trivially_true(&Expr::bool_const(true)));
}

#[test]
fn test_is_trivially_true_bool_const_false() {
    assert!(!is_trivially_true(&Expr::bool_const(false)));
}

#[test]
fn test_is_trivially_true_eq_same_constants() {
    assert!(is_trivially_true(&bv(42, 8).eq(bv(42, 8))));
}

#[test]
fn test_is_trivially_true_signed_comparison() {
    // bvsge(127, -128) = true in signed 8-bit
    assert!(is_trivially_true(&bv(127, 8).bvsge(bv(-128, 8))));
}

// =========================================================================
// has_false_conjunct: signed comparison coverage
// =========================================================================

#[test]
fn test_has_false_conjunct_signed_lt_false() {
    // bvslt(5, -1) = false in signed 8-bit (5 is not less than -1)
    let constraints = Constraints::Owned(vec![bv(5, 8).bvslt(bv(-1, 8))]);
    assert!(has_false_conjunct(&constraints));
}

#[test]
fn test_has_false_conjunct_or_all_false() {
    // Or(false, false) = false
    let expr = Expr::bool_const(false).or(Expr::bool_const(false));
    let constraints = Constraints::Owned(vec![expr]);
    assert!(has_false_conjunct(&constraints));
}

// =========================================================================
// has_false_conjunct: overflow check through deep evaluation
// =========================================================================

#[test]
fn test_has_false_conjunct_sub_no_underflow_unsigned_false() {
    // bvsub_no_underflow_unsigned(3, 5) = (3 >= 5) = false
    let a = bv(3, 8);
    let b = bv(5, 8);
    let constraints = Constraints::Owned(vec![a.bvsub_no_underflow_unsigned(b)]);
    assert!(has_false_conjunct(&constraints));
}

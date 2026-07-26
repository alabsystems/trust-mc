// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_bindings::{ExprValue, Sort};

#[test]
fn bswap_uses_mask_shift_or_encoding_instead_of_extract_concat() {
    let x = Expr::var("x", Sort::bitvec(32));
    let result = compute_bswap(&x).expect("bswap expression");

    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(contains_bvor(&result), "bswap should join byte lanes with bvor");
    assert!(contains_bvshl(&result), "bswap should move low bytes upward with bvshl");
    assert!(contains_bvlshr(&result), "bswap should move high bytes downward with bvlshr");
    assert!(
        !contains_extract_or_concat(&result),
        "bswap should avoid extract/concat shape that is expensive for Intrinsics/bswap.rs"
    );
}

#[test]
fn bswap_u8_uses_bv_identity_fragment() {
    let x = Expr::var("x", Sort::bitvec(8));
    let result = compute_bswap(&x).expect("bswap expression");

    assert_eq!(result.sort().bitvec_width(), Some(8));
    assert!(contains_bvor(&result), "u8 bswap should stay in the BV fragment");
    assert!(
        !contains_extract_or_concat(&result),
        "u8 bswap should avoid extract/concat for identity byte swap"
    );
}

#[test]
fn ctpop_uses_minimal_safe_accumulator_width_then_bv32_result() {
    let x = Expr::var("x", Sort::bitvec(32));
    let result = compute_ctpop(&x).expect("ctpop expression");

    assert_eq!(result.sort().bitvec_width(), Some(32));
    match result.value() {
        ExprValue::BvZeroExtend { expr: inner, extra_bits } => {
            assert_eq!(*extra_bits, 24);
            assert_eq!(inner.sort().bitvec_width(), Some(8));
        }
        other => panic!("ctpop u32 should zero-extend a narrow accumulator, got {other:?}"),
    }

    assert_eq!(max_bvadd_width(&result), Some(8));
}

#[test]
fn ctpop_keeps_wide_inputs_on_bv32_accumulator() {
    let x = Expr::var("x", Sort::bitvec(64));
    let result = compute_ctpop(&x).expect("ctpop expression");

    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert_eq!(max_bvadd_width(&result), Some(32));
}

#[test]
fn ctpop_accumulator_width_covers_population_count_max() {
    assert_eq!(ctpop_accumulator_width(32, 32), 8);
    assert_eq!(ctpop_accumulator_width(64, 32), 32);
    assert_eq!(bit_width_for_unsigned_max(0), 1);
    assert_eq!(bit_width_for_unsigned_max(1), 1);
    assert_eq!(bit_width_for_unsigned_max(8), 4);
    assert_eq!(bit_width_for_unsigned_max(16), 8);
    assert_eq!(bit_width_for_unsigned_max(32), 8);
    assert_eq!(bit_width_for_unsigned_max(64), 8);
    assert_eq!(bit_width_for_unsigned_max(128), 8);
}

fn max_bvadd_width(expr: &Expr) -> Option<u32> {
    match expr.value() {
        ExprValue::BvAdd(lhs, rhs) => {
            let this = expr.sort().bitvec_width();
            [this, max_bvadd_width(lhs), max_bvadd_width(rhs)].into_iter().flatten().max()
        }
        ExprValue::BvZeroExtend { expr: inner, .. } => max_bvadd_width(inner),
        _ => None,
    }
}

fn contains_bvor(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvOr(_, _) => true,
        other => children(other).iter().any(|child| contains_bvor(child)),
    }
}

fn contains_bvshl(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvShl(_, _) => true,
        other => children(other).iter().any(|child| contains_bvshl(child)),
    }
}

fn contains_bvlshr(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvLShr(_, _) => true,
        other => children(other).iter().any(|child| contains_bvlshr(child)),
    }
}

fn contains_extract_or_concat(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvExtract { .. } | ExprValue::BvConcat(_, _) => true,
        other => children(other).iter().any(|child| contains_extract_or_concat(child)),
    }
}

fn children(value: &ExprValue) -> Vec<&Expr> {
    match value {
        ExprValue::BvAnd(lhs, rhs)
        | ExprValue::BvOr(lhs, rhs)
        | ExprValue::BvShl(lhs, rhs)
        | ExprValue::BvLShr(lhs, rhs) => vec![lhs, rhs],
        _ => Vec::new(),
    }
}

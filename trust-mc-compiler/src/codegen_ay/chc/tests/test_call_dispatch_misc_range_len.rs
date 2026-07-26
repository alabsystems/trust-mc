// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `ChcCtx::range_len_expr` — the static helper that computes
//! `ite(end >= start, end - start, 0)` for bitvec and Int-sorted range operands.
//!
//! Split from `test_call_dispatch_misc.rs` (D4 of #4010).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

/// Verify `range_len_expr` correctly computes `ite(end >= start, end - start, 0)`
/// for bitvec Range operands.
///
/// Tests the static helper directly with synthetic BV expressions rather than
/// relying on MIR patterns that may be optimized away by the compiler.
#[test]
fn test_range_len_expr_bitvec() {
    let start = Expr::var("start", Sort::bitvec(64));
    let end = Expr::var("end", Sort::bitvec(64));

    let len = ChcCtx::range_len_expr(start, end, false);
    assert!(len.is_some(), "range_len_expr should produce a result for matching BV widths");

    let len_expr = len.unwrap();
    assert!(
        len_expr.sort().is_bitvec(),
        "range length should be bitvec, got {:?}",
        len_expr.sort()
    );
    assert_eq!(
        len_expr.sort().bitvec_width(),
        Some(64),
        "range length width should match operand width"
    );

    // Structural guard: BV length must be clamped via ITE + unsigned compare.
    match len_expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            assert!(
                matches!(cond.value(), ExprValue::BvUGe(_, _)),
                "BV range len guard must use bvuge, got {:?}",
                cond.value()
            );
            assert!(
                matches!(then_expr.value(), ExprValue::BvSub(_, _)),
                "BV range len true branch must use bvsub, got {:?}",
                then_expr.value()
            );
            assert!(
                matches!(else_expr.value(), ExprValue::BitVecConst { .. }),
                "BV range len false branch must be BV zero, got {:?}",
                else_expr.value()
            );
        }
        other => unreachable!("range_len_expr should produce ITE for BV operands, got {:?}", other),
    }
}

/// Verify `range_len_expr` handles Int-sorted operands (for Int-lifted ranges).
#[test]
fn test_range_len_expr_int() {
    let start = Expr::var("start", Sort::int());
    let end = Expr::var("end", Sort::int());

    let len = ChcCtx::range_len_expr(start, end, false);
    assert!(len.is_some(), "range_len_expr should produce a result for Int operands");

    let len_expr = len.unwrap();
    assert!(len_expr.sort().is_int(), "range length for Int operands should be Int sort");
}

/// Verify `range_len_expr` returns None for mismatched sorts.
#[test]
fn test_range_len_expr_mismatched_sorts_returns_none() {
    let start = Expr::var("start", Sort::bitvec(64));
    let end = Expr::var("end", Sort::int());

    let len = ChcCtx::range_len_expr(start, end, false);
    assert!(len.is_none(), "range_len_expr should return None for BV/Int mismatch");
}

#[test]
fn test_range_len_expr_bitvec_semantics_with_constants() {
    let assert_eq_unsat = |lhs: Expr, rhs: Expr| {
        let smt = format!("(set-logic ALL)\n(assert (not (= {} {})))\n(check-sat)\n", lhs, rhs);
        assert_z3_result(&smt, "unsat");
    };

    // Well-formed range: 10 - 2 = 8.
    let len =
        ChcCtx::range_len_expr(Expr::bitvec_const(2u64, 64), Expr::bitvec_const(10u64, 64), false)
            .expect("matching BV widths should produce len expr");
    assert_eq_unsat(len, Expr::bitvec_const(8u64, 64));

    // Malformed range: end < start must clamp to 0 (not wrapped subtraction).
    let len =
        ChcCtx::range_len_expr(Expr::bitvec_const(10u64, 64), Expr::bitvec_const(2u64, 64), false)
            .expect("matching BV widths should produce len expr");
    assert_eq_unsat(len, Expr::bitvec_const(0u64, 64));

    // Width harmonization path: bv8 and bv16 must coerce to max width (16) before subtract.
    let len = ChcCtx::range_len_expr(
        Expr::bitvec_const(250u64, 8),
        Expr::bitvec_const(300u64, 16),
        false,
    )
    .expect("mixed BV widths should be harmonized");
    assert_eq!(len.sort().bitvec_width(), Some(16), "mixed BV widths should harmonize to max");
    assert_eq_unsat(len, Expr::bitvec_const(50u64, 16));
}

#[test]
fn test_range_len_expr_int_semantics_with_constants() {
    let assert_eq_unsat = |lhs: Expr, rhs: Expr| {
        let smt = format!("(set-logic ALL)\n(assert (not (= {} {})))\n(check-sat)\n", lhs, rhs);
        assert_z3_result(&smt, "unsat");
    };

    // Int-lifted range can include negatives; len should stay non-negative.
    // Int path ignores signed parameter (Int is inherently signed).
    let len = ChcCtx::range_len_expr(Expr::int_const(-5), Expr::int_const(3), true)
        .expect("Int operands should produce len expr");
    assert_eq_unsat(len, Expr::int_const(8));

    // Malformed Int range must clamp to zero.
    let len = ChcCtx::range_len_expr(Expr::int_const(7), Expr::int_const(-3), true)
        .expect("Int operands should produce len expr");
    assert_eq_unsat(len, Expr::int_const(0));
}

/// Part of #3247: `range_len_expr` now accepts a `signed` parameter.
/// With `signed=true`, `bvsge` is used instead of `bvuge`, correctly handling
/// signed BV ranges like `Range<i32>`.
///
/// Previously, unsigned comparison caused `Range<i32>` with `-2..2` to clamp
/// to 0 (bvuge(2, 0xFFFFFFFE) = false). Now with signed=true, bvsge(2, -2) = true
/// and the length is correctly computed as 4.
#[test]
fn test_range_len_expr_signed_bv_correct_with_signed_parameter() {
    let assert_eq_unsat = |lhs: Expr, rhs: Expr| {
        let smt = format!("(set-logic ALL)\n(assert (not (= {} {})))\n(check-sat)\n", lhs, rhs);
        assert_z3_result(&smt, "unsat");
    };

    // Range<i32>: -2..2 should have len 4.
    // In 32-bit BV: -2 is 0xFFFFFFFE, 2 is 0x00000002.
    // Signed: bvsge(2, -2) = true → len = 2 - (-2) = 4 (CORRECT).
    let neg2_bv32 = Expr::bitvec_const(0xFFFFFFFEu64, 32); // -2 as i32
    let pos2_bv32 = Expr::bitvec_const(2u64, 32);

    let len = ChcCtx::range_len_expr(neg2_bv32.clone(), pos2_bv32.clone(), true)
        .expect("matching BV widths should produce len expr");
    assert_eq_unsat(len, Expr::bitvec_const(4u64, 32));

    // Unsigned path still clamps to 0 (documents the unsigned behavior).
    let len_unsigned = ChcCtx::range_len_expr(neg2_bv32, pos2_bv32, false)
        .expect("matching BV widths should produce len expr");
    assert_eq_unsat(len_unsigned, Expr::bitvec_const(0u64, 32));

    // Int path handles negatives correctly regardless of signed parameter.
    let len_int = ChcCtx::range_len_expr(Expr::int_const(-2), Expr::int_const(2), true)
        .expect("Int operands should produce len expr");
    assert_eq_unsat(len_int, Expr::int_const(4));

    // Positive unsigned range still works correctly: 2..10 = 8.
    let len_pos =
        ChcCtx::range_len_expr(Expr::bitvec_const(2u64, 32), Expr::bitvec_const(10u64, 32), false)
            .expect("matching BV widths should produce len expr");
    assert_eq_unsat(len_pos, Expr::bitvec_const(8u64, 32));
}

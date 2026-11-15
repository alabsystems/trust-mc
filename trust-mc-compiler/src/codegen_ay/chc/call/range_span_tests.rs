// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The symbolic range count against `Step::steps_between`, evaluated on a
//! grid of signed, unsigned, `char` and 128-bit bounds.

use super::*;
use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;

/// A value of the evaluated subset: a boolean or a bitvector (width, bits).
#[derive(Clone, Debug, PartialEq)]
enum Val {
    Bool(bool),
    Bv(u32, BigInt),
}

fn modulus(width: u32) -> BigInt {
    BigInt::from(1u8) << width
}

fn signed(width: u32, bits: &BigInt) -> BigInt {
    if *bits >= (BigInt::from(1u8) << (width - 1)) { bits - modulus(width) } else { bits.clone() }
}

fn norm(width: u32, value: BigInt) -> BigInt {
    let m = modulus(width);
    ((value % &m) + &m) % m
}

/// Evaluates the constant-only terms `range_span` builds.
fn eval(e: &Expr) -> Val {
    let bv = |e: &Expr| match eval(e) {
        Val::Bv(w, v) => (w, v),
        other => panic!("expected a bitvector, got {other:?}"),
    };
    let b = |e: &Expr| match eval(e) {
        Val::Bool(v) => v,
        other => panic!("expected a boolean, got {other:?}"),
    };
    match e.value() {
        ExprValue::BoolConst(v) => Val::Bool(*v),
        ExprValue::BitVecConst { value, width } => Val::Bv(*width, value.clone()),
        ExprValue::Not(a) => Val::Bool(!b(a)),
        ExprValue::And(xs) => Val::Bool(xs.iter().all(b)),
        ExprValue::Or(xs) => Val::Bool(xs.iter().any(b)),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            if b(cond) { eval(then_expr) } else { eval(else_expr) }
        }
        ExprValue::Eq(x, y) => Val::Bool(eval(x) == eval(y)),
        ExprValue::BvAdd(x, y) => {
            let ((w, x), (_, y)) = (bv(x), bv(y));
            Val::Bv(w, norm(w, x + y))
        }
        ExprValue::BvSub(x, y) => {
            let ((w, x), (_, y)) = (bv(x), bv(y));
            Val::Bv(w, norm(w, x - y))
        }
        ExprValue::BvULt(x, y) => Val::Bool(bv(x).1 < bv(y).1),
        ExprValue::BvULe(x, y) => Val::Bool(bv(x).1 <= bv(y).1),
        ExprValue::BvUGt(x, y) => Val::Bool(bv(x).1 > bv(y).1),
        ExprValue::BvUGe(x, y) => Val::Bool(bv(x).1 >= bv(y).1),
        ExprValue::BvSLt(x, y) => {
            let ((w, x), (_, y)) = (bv(x), bv(y));
            Val::Bool(signed(w, &x) < signed(w, &y))
        }
        ExprValue::BvSLe(x, y) => {
            let ((w, x), (_, y)) = (bv(x), bv(y));
            Val::Bool(signed(w, &x) <= signed(w, &y))
        }
        ExprValue::BvZeroExtend { expr, extra_bits } => {
            let (w, v) = bv(expr);
            Val::Bv(w + extra_bits, v)
        }
        ExprValue::BvSignExtend { expr, extra_bits } => {
            let (w, v) = bv(expr);
            Val::Bv(w + extra_bits, norm(w + extra_bits, signed(w, &v)))
        }
        ExprValue::BvExtract { expr, high, low } => {
            let (_, v) = bv(expr);
            Val::Bv(high - low + 1, norm(high - low + 1, v >> *low))
        }
        other => panic!("unexpected term in a range span: {other:?}"),
    }
}

fn eval_bv(e: &Expr) -> BigInt {
    match eval(e) {
        Val::Bv(_, v) => v,
        other => panic!("expected a bitvector, got {other:?}"),
    }
}

fn eval_bool(e: &Expr) -> bool {
    match eval(e) {
        Val::Bool(v) => v,
        other => panic!("expected a boolean, got {other:?}"),
    }
}

/// Bounds of interest for each step kind, as numbers in the element's order.
fn grid(step: RangeStep) -> Vec<BigInt> {
    let w = step.width();
    let mut values: Vec<BigInt> = match step {
        RangeStep::Signed(_) => {
            let max: BigInt = (BigInt::from(1u8) << (w - 1)) - 1;
            let min: BigInt = -(BigInt::from(1u8) << (w - 1));
            vec![min.clone(), min + 1, BigInt::from(-3), BigInt::from(-1), max.clone() - 1, max]
        }
        RangeStep::Unsigned(_) => {
            let max: BigInt = modulus(w) - 1;
            vec![max.clone() - 1, max]
        }
        RangeStep::Char => vec![
            BigInt::from(0xD7FEu32),
            BigInt::from(0xD7FFu32),
            BigInt::from(0xE000u32),
            BigInt::from(0xE001u32),
            BigInt::from(0x10FFFFu32),
        ],
    };
    values.extend([0, 1, 2, 5].map(BigInt::from));
    values
}

#[test]
fn test_range_span_len_matches_steps_between() {
    let steps = [
        RangeStep::Signed(8),
        RangeStep::Unsigned(8),
        RangeStep::Signed(32),
        RangeStep::Signed(64),
        RangeStep::Unsigned(64),
        RangeStep::Signed(128),
        RangeStep::Unsigned(128),
        RangeStep::Char,
    ];
    let usize_max = modulus(64) - 1;
    for step in steps {
        let w = step.width();
        for s in grid(step) {
            for e in grid(step) {
                let start = Expr::bitvec_const(s.clone(), w);
                let end = Expr::bitvec_const(e.clone(), w);
                let span = range_span(step, &start, &end).expect("a well-sorted span");
                for inclusive in [false, true] {
                    for exhausted in [false, true] {
                        let want = range_count(step, &s, &e, inclusive, exhausted);
                        let got = span.len(inclusive, Expr::bool_const(exhausted));
                        assert_eq!(
                            eval_bool(&got.too_long),
                            want > usize_max,
                            "{step:?} {s}..{}{e} exhausted={exhausted}: too_long",
                            if inclusive { "=" } else { "" }
                        );
                        assert_eq!(
                            eval_bv(&got.len),
                            norm(64, want.clone()),
                            "{step:?} {s}..{}{e} exhausted={exhausted}: len",
                            if inclusive { "=" } else { "" }
                        );
                        let folded = fold_range_count(step, &start, &end, inclusive, exhausted);
                        assert_eq!(folded, Some(want), "{step:?} {s} {e}: fold");
                    }
                    // Back edges: the steps of a non-empty range, saturated.
                    let nonempty = if inclusive { s <= e } else { s < e };
                    let trips = if nonempty {
                        range_count(step, &s, &e, true, false) - 1
                    } else {
                        BigInt::from(0u8)
                    };
                    let trips = if trips > usize_max { usize_max.clone() } else { trips };
                    assert_eq!(eval_bv(&span.loop_trips(inclusive)), trips, "{step:?} {s} {e}: trips");
                }
            }
        }
    }
}

#[test]
fn test_range_span_review_rows() {
    // `-2i8..3` is five elements, `2i8..-1` none, and
    // `'\u{D7FF}'..'\u{E001}'` two (walker fail-closed repair round 5).
    let count = |step, s: i64, e: i64, inclusive| {
        let w = RangeStep::width(step);
        let start = Expr::bitvec_const(s, w);
        let end = Expr::bitvec_const(e, w);
        let span = range_span(step, &start, &end).expect("a well-sorted span");
        eval_bv(&span.len(inclusive, Expr::bool_const(false)).len)
    };
    assert_eq!(count(RangeStep::Signed(8), -2, 3, false), BigInt::from(5));
    assert_eq!(count(RangeStep::Signed(8), 2, -1, false), BigInt::from(0));
    assert_eq!(count(RangeStep::Signed(64), -1, 1, true), BigInt::from(3));
    assert_eq!(count(RangeStep::Char, 0xD7FF, 0xE001, false), BigInt::from(2));
    assert_eq!(count(RangeStep::Char, 0xD7FF, 0xE000, true), BigInt::from(2));
    assert_eq!(count(RangeStep::Unsigned(32), 0, 3, false), BigInt::from(3));
}

#[test]
fn test_range_span_refuses_a_mis_sorted_bound() {
    let start = Expr::bitvec_const(0u64, 64);
    let end = Expr::bitvec_const(3u64, 8);
    assert!(range_span(RangeStep::Signed(8), &start, &end).is_none());
}

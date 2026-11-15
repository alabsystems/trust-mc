// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rust float `%` in the BMC lane is C `fmod`, as ay decides it
//! (TRUST-MC-FREM-1).
//!
//! `bv_float_binop(BinOp::Rem, ..)` once lowered `%` to SMT-LIB `fp.rem`, the
//! IEEE 754 remainder: `fp.rem(5, 3) = -1`, while `5.0 % 3.0 = 2.0`. Each test
//! here builds the lane's own term and asks ay, the engine's solver, whether a
//! claim about it is VALID (its negation `unsat`) or refutable (`sat`). The
//! concrete cases are held bit for bit, sign of zero included, to host Rust
//! `%`. A NaN result is held to "is a NaN": SMT-LIB fixes no NaN bit pattern.

use super::{bv_float_binop, bv_to_ieee_fp, float_width_to_eb_sb};
use crate::codegen_ay::codegen_function::integration_ay_runner::run_ay_smt2;
use ay_bindings::{Expr, RoundingMode, Sort};
use rustc_public::mir::BinOp;

/// The BMC lane's `x % y` over IEEE bit patterns of `width` bits.
fn frem(x: Expr, y: Expr, width: u32) -> Expr {
    bv_float_binop(BinOp::Rem, x, y, width).expect("float `%` lowers at an IEEE width")
}

fn bits(value: u128, width: u32) -> Expr {
    Expr::bitvec_const(value, width)
}

fn as_fp(bv: Expr, width: u32) -> Expr {
    let (eb, sb) = float_width_to_eb_sb(width).expect("IEEE width");
    bv_to_ieee_fp(bv, eb, sb)
}

/// ay's verdict on `(assert (not claim))` with `vars` declared as bitvectors:
/// `unsat` means `claim` is valid, `sat` that it is refutable.
fn negation_verdict(claim: &Expr, vars: &[(&str, u32)]) -> String {
    let mut smt = String::from("(set-logic ALL)\n");
    for (name, width) in vars {
        smt.push_str(&format!("(declare-const {name} (_ BitVec {width}))\n"));
    }
    smt.push_str(&format!("(assert (not {claim}))\n(check-sat)\n"));
    run_ay_smt2(&smt).unwrap_or_else(|err| panic!("ay failed on:\n{smt}\nerror: {err}"))
}

/// The claim that `x % y` (bit patterns `x`, `y`) is the host's `expected`:
/// the same bits, or any NaN when `expected` is a NaN.
fn frem_is(x: u128, y: u128, expected: u128, expected_is_nan: bool, width: u32) -> Expr {
    let r = frem(bits(x, width), bits(y, width), width);
    if expected_is_nan { as_fp(r, width).fp_is_nan() } else { r.eq(bits(expected, width)) }
}

/// Every `(x, y)` pair must be VALID-ly equal to host `%`; collects all
/// mismatches before failing so one run names every wrong case.
fn assert_table_matches_host(width: u32, rows: &[(u128, u128, u128, bool, String)]) {
    let mut wrong = Vec::new();
    for (x, y, expected, expected_is_nan, label) in rows {
        let claim = frem_is(*x, *y, *expected, *expected_is_nan, width);
        let verdict = negation_verdict(&claim, &[]);
        if verdict != "unsat" {
            wrong.push(format!("{label}: ay says `(not claim)` is {verdict}"));
        }
    }
    assert!(wrong.is_empty(), "f{width} `%` disagrees with host Rust `%`:\n{}", wrong.join("\n"));
}

/// `5.0 % 3.0 == 2.0` is valid, and the false `5.0 % 3.0 < 0.0` is refutable.
/// Under the IEEE-remainder lowering (`fp.rem(5, 3) = -1`) the true equality
/// was refutable and the false bound was valid.
#[test]
fn frem_f64_5_by_3_is_2_and_not_negative() {
    let r = frem(bits(5.0f64.to_bits().into(), 64), bits(3.0f64.to_bits().into(), 64), 64);
    let two = bits(2.0f64.to_bits().into(), 64);
    assert_eq!(negation_verdict(&r.clone().eq(two), &[]), "unsat", "5.0 % 3.0 == 2.0 is true");

    let zero = as_fp(bits(0, 64), 64);
    let negative = as_fp(r.clone(), 64).fp_lt(zero.clone());
    assert_eq!(negation_verdict(&negative, &[]), "sat", "5.0 % 3.0 < 0.0 is false: never valid");
    let nonnegative = as_fp(r, 64).fp_ge(zero);
    assert_eq!(negation_verdict(&nonnegative, &[]), "unsat", "5.0 % 3.0 >= 0.0 is true");
}

/// The named cases, held to host `%` bit for bit: the dividend's sign
/// (`-5 % 3 == -2`, `-5 % -3 == -2`), a tie quotient (`3 % 2 == 1`, where IEEE
/// rounds 1.5 to 2 and gets -1), a negative zero from an exact multiple
/// (`-6 % 3 == -0.0`), a positive zero (`6 % -3 == +0.0`), and the special
/// operands `fp.rem` already got right (NaN, infinities, zero divisors, signed
/// zero dividends), which the correction must leave alone.
#[test]
fn frem_f64_matches_host_rem_bit_for_bit() {
    let sub = f64::from_bits;
    let cases: [(f64, f64); 24] = [
        (5.0, 3.0),
        (-5.0, 3.0),
        (5.0, -3.0),
        (-5.0, -3.0),
        (3.0, 2.0),
        (7.0, 2.0),
        (-6.0, 3.0),
        (6.0, -3.0),
        (5.25, 2.0),
        (1.0, 3.0),
        (0.1, 0.03),
        (1.0e300, 3.0),
        // Subnormals: 3q % 2q == q, and IEEE rounds 1.5 to 2 (the correction fires).
        (sub(3), sub(2)),
        (-sub(7), sub(4)),
        (0.0, 3.0),
        (-0.0, 3.0),
        (5.0, f64::INFINITY),
        (-5.0, f64::NEG_INFINITY),
        (f64::INFINITY, 3.0),
        (f64::NEG_INFINITY, -3.0),
        (5.0, 0.0),
        (5.0, -0.0),
        (f64::NAN, 3.0),
        (5.0, f64::NAN),
    ];
    let rows: Vec<_> = cases
        .iter()
        .map(|&(x, y)| {
            let r = x % y;
            (
                x.to_bits().into(),
                y.to_bits().into(),
                r.to_bits().into(),
                r.is_nan(),
                format!("{x:e} % {y:e} = {r:e} (bits {:#018x})", r.to_bits()),
            )
        })
        .collect();
    assert_table_matches_host(64, &rows);
}

#[test]
fn frem_f32_matches_host_rem_bit_for_bit() {
    let sub = f32::from_bits;
    let cases: [(f32, f32); 16] = [
        (5.0, 3.0),
        (-5.0, 3.0),
        (5.0, -3.0),
        (3.0, 2.0),
        (-6.0, 3.0),
        (6.0, -3.0),
        (5.25, 2.0),
        (1.0e30, 3.0),
        (16_777_215.0, 2.0),
        (sub(3), sub(2)),
        (-0.0, 3.0),
        (5.0, f32::INFINITY),
        (f32::INFINITY, 3.0),
        (5.0, 0.0),
        (f32::NAN, 3.0),
        (5.0, f32::NAN),
    ];
    let rows: Vec<_> = cases
        .iter()
        .map(|&(x, y)| {
            let r = x % y;
            (
                x.to_bits().into(),
                y.to_bits().into(),
                r.to_bits().into(),
                r.is_nan(),
                format!("{x:e} % {y:e} = {r:e} (bits {:#010x})", r.to_bits()),
            )
        })
        .collect();
    assert_table_matches_host(32, &rows);
}

/// f16 has no stable host type; the bit patterns are written out:
/// 5.0 = 0x4500, 3.0 = 0x4200, 2.0 = 0x4000, -5.0 = 0xC500, -2.0 = 0xC000,
/// -6.0 = 0xC600, -0.0 = 0x8000.
#[test]
fn frem_f16_matches_fmod() {
    let rows = [
        (0x4500, 0x4200, 0x4000, false, "f16 5 % 3 == 2".to_string()),
        (0xC500, 0x4200, 0xC000, false, "f16 -5 % 3 == -2".to_string()),
        (0xC600, 0x4200, 0x8000, false, "f16 -6 % 3 == -0.0".to_string()),
    ];
    assert_table_matches_host(16, &rows);
}

/// Symbolic: for every finite `x >= 0`, `x % 3.0 >= 0.0`. Under the IEEE
/// remainder `x = 2.0` gives `-1.0`, so the claim was refutable.
#[test]
fn frem_f32_nonnegative_dividend_gives_nonnegative_remainder() {
    let x = Expr::var("x", Sort::bitvec(32));
    let x_fp = as_fp(x.clone(), 32);
    let zero = as_fp(bits(0, 32), 32);
    let premise = x_fp.clone().fp_ge(zero.clone()).and(x_fp.fp_is_infinite().not());
    let r = frem(x, bits(3.0f32.to_bits().into(), 32), 32);
    let claim = premise.implies(as_fp(r, 32).fp_ge(zero));
    assert_eq!(negation_verdict(&claim, &[("x", 32)]), "unsat", "x >= 0 finite => x % 3 >= 0");
}

/// The correction's add is exact: rounded up and rounded down it is the same
/// float, the fmod result, so the RNE in the encoding never rounds anything.
#[test]
fn frem_correction_add_is_exact() {
    let x = as_fp(bits(5.25f64.to_bits().into(), 64), 64);
    let y = as_fp(bits(2.0f64.to_bits().into(), 64), 64);
    // fp.rem(5.25, 2) = -0.75 (quotient 2.625 rounds to 3), corrected by +|y|.
    let r = x.fp_rem(y.clone());
    let step = y.fp_abs();
    let fmod = as_fp(bits(1.25f64.to_bits().into(), 64), 64);
    let up = r.clone().fp_add(RoundingMode::RTP, step.clone());
    let down = r.fp_add(RoundingMode::RTN, step);
    let claim = up.fp_eq(fmod.clone()).and(down.fp_eq(fmod));
    assert_eq!(negation_verdict(&claim, &[]), "unsat", "fp.rem(5.25, 2) + 2 == 1.25 exactly");
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// V4 vacuity, CHC and BMC, with the shapes the CHC lane's cheap paths must NOT
// get wrong.
//
// Oracle: every `*_must_not_prove` harness is VACUOUS — its assumptions are
// contradictory, so every check it emits is unreachable and a SUCCESSFUL
// verdict would be a proof of nothing (`--allow-vacuous`'s own help: a vacuous
// harness is a FAILURE unless relaxed). Every `*_reachable_*` harness runs and
// its property holds: SUCCESSFUL, or the cheap reachability witness has claimed
// something false.
//
// The CHC lane answers the question with `vacuity_probe` (a solver) but skips
// the solver when `vacuity_reach_witness` shows a check site reachable along a
// derivation made only of definitions. The must-not-prove harnesses below place
// EVERY check site behind the contradiction, so the witness must stay silent
// and the probe must decide; the reachable ones place a check site in front of
// every guard, which is what the witness is for.
#![allow(unused)]

// Contradictory integer assumptions, the plainest shape.
#[kani::proof]
fn vacuity_int_contradiction_must_not_prove() {
    let x: u8 = kani::any();
    kani::assume(x > 200);
    kani::assume(x < 100);
    assert!(1 + 1 == 3);
}

// The contradiction is visible only THROUGH an assignment: `x.wrapping_add(1)`
// is 0 exactly when x is 255, never when x is 5. The assignment is a definition
// the witness reads; the assumptions after it are guards it must not read past.
#[kani::proof]
fn vacuity_contradiction_after_a_definition_must_not_prove() {
    let x: u8 = kani::any();
    let y = x.wrapping_add(1);
    kani::assume(y == 0);
    kani::assume(x == 5);
    assert!(1 + 1 == 3);
}

// A NaN that is also greater than zero: an IEEE contradiction, so no value
// satisfies both and the assertion under them is unreachable.
#[kani::proof]
fn vacuity_nan_contradiction_must_not_prove() {
    let x: f32 = kani::any();
    kani::assume(x.is_nan() && x > 0.0);
    assert!(1 + 1 == 3);
}

// The control the witness exists for: the check site sits in a straight line of
// assignments, no guard in front of it, and the property holds.
#[kani::proof]
fn vacuity_reachable_straight_line_holds() {
    let x: u8 = kani::any();
    let y = x.wrapping_add(1);
    assert!(y == x.wrapping_add(1));
}

// A reachable harness whose check site IS behind a guard: the witness must stay
// silent here (an assumption restricts the values), the probe decides, and the
// verdict is still a proof.
#[kani::proof]
fn vacuity_reachable_behind_a_guard_holds() {
    let x: u8 = kani::any();
    kani::assume(x > 10);
    kani::assume(x < 20);
    assert!(x > 10 && x < 20);
}

// A reachable harness whose property is FALSE: no cheap path may mask a real
// counterexample by re-statusing checks it did not decide.
#[kani::proof]
fn vacuity_reachable_but_false_must_fail() {
    let x: u8 = kani::any();
    kani::assume(x > 10);
    kani::assume(x < 20);
    assert!(x > 15);
}

// 2^64, written as a literal so no shift check sits in front of the assumption.
const TWO_64: u128 = 18446744073709551616;

// ay-bindings prints an unsigned u128 multiplication-overflow flag as the high
// half of a 256-bit product. `a` is 2^64 whatever `x` is, so `a * 2^64` is 2^128
// and always overflows: `o` is true, `assume(!o)` contradicts, and the assertion
// is unreachable (Kani: every check UNREACHABLE). The in-process witness once
// computed the 256-bit flag in a u128 and certified this site reachable in a
// release build (SUCCESSFUL, clean qualifiers) and panicked in a dev build.
#[kani::proof]
fn vacuity_u128_mul_overflow_flag_must_not_prove() {
    let x: u128 = kani::any();
    let a = (x ^ x) | TWO_64;
    let (_p, o) = a.overflowing_mul(TWO_64);
    kani::assume(!o);
    assert!(1 + 1 == 3);
}

// The reachable control of the same flag: every `a` reaches the check and the
// property holds. The witness cannot read the 256-bit term, so the external
// probe decides; a correct proof must not crash the driver.
#[kani::proof]
fn vacuity_reachable_u128_mul_overflow_flag_holds() {
    let a: u128 = kani::any();
    let (_p, o) = a.overflowing_mul(2);
    assert!(o == (a >= (1u128 << 127)));
}

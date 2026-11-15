// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Kani agrees on every row):
//   bug_u128_mul_overflows                 -> VERIFICATION:- FAILED (multiply with overflow)
//   bug_u128_flag_claimed_clear_at_two_127 -> VERIFICATION:- FAILED (assertion)
//   safe_u128_flag_set_at_two_127          -> VERIFICATION:- SUCCESSFUL
//   safe_u128_flag_clear_at_three          -> VERIFICATION:- SUCCESSFUL
//
// ay-bindings prints an unsigned u128 multiplication-overflow flag as the high
// half of a 256-bit product:
//   (= ((_ extract 255 128) (bvmul ((_ zero_extend 128) a) ((_ zero_extend 128) b))) #x0…0)
// The driver's model evaluator (call_ay/chc/model_eval.rs) once computed that
// term in a u128: `extract 255 128` became a shift right by 128, a panic under
// overflow checks (the CHC lane's exact-derivation refutation guard killed the
// driver on bug_u128_flag_claimed_clear_at_two_127) and `v >> 0` without them.
// 2^127 * 2 is exactly 2^128, the smallest product whose flag is set.
#![allow(unused)]

const TWO_64: u128 = 18446744073709551616;
const TWO_127: u128 = 170141183460469231731687303715884105728;

#[kani::proof]
fn bug_u128_mul_overflows() {
    let a: u128 = kani::any();
    kani::assume(a >= TWO_64);
    let _p = a * a;
}

#[kani::proof]
fn bug_u128_flag_claimed_clear_at_two_127() {
    let a: u128 = kani::any();
    kani::assume(a == TWO_127);
    let (_p, o) = a.overflowing_mul(2);
    assert!(!o);
}

#[kani::proof]
fn safe_u128_flag_set_at_two_127() {
    let a: u128 = kani::any();
    kani::assume(a == TWO_127);
    let (_p, o) = a.overflowing_mul(2);
    assert!(o);
}

#[kani::proof]
fn safe_u128_flag_clear_at_three() {
    let a: u128 = kani::any();
    kani::assume(a == 3);
    let (_p, o) = a.overflowing_mul(3);
    assert!(!o);
}

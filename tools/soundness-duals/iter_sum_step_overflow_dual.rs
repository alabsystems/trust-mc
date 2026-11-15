// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the overflow check of every step of
//! core's integer `Iterator::sum` (fix/chc-walker-fail-closed, walker
//! fail-closed repair round 5, review finding 7, `ck1`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   s1_i8_intermediate_overflow_bug -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   s1_i8_no_overflow_safe          -> VERIFICATION:- SUCCESSFUL
//!   s2_u8_symbolic_overflow_bug     -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!   s2_u8_symbolic_overflow_safe    -> VERIFICATION:- SUCCESSFUL
//!   s3_i16_negative_overflow_bug    -> VERIFICATION:- FAILED  ('attempt to add with overflow')
//!
//! MECHANISM UNDER TEST. Core's integer sum adds with `+` under the caller's
//! overflow checks (`#[rustc_inherit_overflow_checks]`). The BMC lane's
//! element-wise unroll added without a check, so an intermediate overflow
//! (`100 + 100` in `[100i8, 100, -100]`, whose total fits) verified clean.
//! Each kept step is checked now (`statement/collections/iter_adapters.rs`,
//! `try_iter_sum_unroll`), as the CHC lane's reduction does.

#[kani::proof]
fn s1_i8_intermediate_overflow_bug() {
    let a = [100i8, 100, -100];
    let s: i8 = a.iter().sum();
    assert!(s == 100);
}

#[kani::proof]
fn s1_i8_no_overflow_safe() {
    let a = [100i8, -100, 100];
    let s: i8 = a.iter().sum();
    assert!(s == 100);
}

#[kani::proof]
fn s2_u8_symbolic_overflow_bug() {
    let x: u8 = kani::any();
    let a = [x, 200u8];
    let s: u8 = a.iter().sum();
    assert!(s >= 200);
}

#[kani::proof]
fn s2_u8_symbolic_overflow_safe() {
    let x: u8 = kani::any();
    kani::assume(x <= 55);
    let a = [x, 200u8];
    let s: u8 = a.iter().sum();
    assert!(s >= 200);
}

#[kani::proof]
fn s3_i16_negative_overflow_bug() {
    let a = [i16::MIN, -1, 1];
    let s: i16 = a.iter().sum();
    assert!(s == i16::MIN);
}

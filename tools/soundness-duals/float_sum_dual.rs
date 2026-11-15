// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- `Iterator::sum` / `product` into a
//! float (fix/chc-walker-fail-closed, walker fail-closed repair round 5,
//! review finding 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   f1_f32_sum_value_bug     -> VERIFICATION:- FAILED  ('assertion failed: s == 3.0')
//!   f1_f32_sum_value_safe    -> VERIFICATION:- SUCCESSFUL
//!   f2_f64_rounding_bug      -> VERIFICATION:- FAILED  ('assertion failed: s == 0.3')
//!   f2_f64_rounding_safe     -> VERIFICATION:- SUCCESSFUL
//!   f3_f32_sum_to_inf_bug    -> VERIFICATION:- FAILED  ('assertion failed: s.is_finite()')
//!   f3_f32_sum_to_inf_safe   -> VERIFICATION:- SUCCESSFUL
//!   f4_f32_symbolic_sum_bug  -> VERIFICATION:- FAILED  ('assertion failed: s == x')
//!   f4_f32_symbolic_sum_safe -> VERIFICATION:- SUCCESSFUL
//!   f6_f64_product_inf_bug   -> VERIFICATION:- FAILED  ('assertion failed: p.is_finite()')
//!   f6_f64_product_inf_safe  -> VERIFICATION:- SUCCESSFUL
//!   f7_f64_owned_sum_bug     -> VERIFICATION:- FAILED  ('assertion failed: s == 6.0')
//!   f7_f64_owned_sum_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The sum model mapped a float target to checked
//! integer addition: it added the bit patterns as integers and checked them
//! for integer overflow, so an f32 sum Kani proves was certified a Genuine
//! "attempt to add with overflow", its true value was a Genuine failure, and
//! `f32::MAX + f32::MAX` stayed finite. Core's float sum is IEEE addition from
//! `-0.0` with no overflow check; float targets were left unmodelled
//! (`reduce_loop_rule::iter_sum_model`) and reached the ordinary call path.
//! Since the landing on main (2026-10-16) they are core's `Sum` again: main's
//! `Iterator::sum` rework adds them as IEEE floats (`SumSummand::Float`), with
//! Kani's NaN check under `--nan-check`, not as integers.

#[kani::proof]
fn f1_f32_sum_value_bug() {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    assert!(s == 3.0);
}

#[kani::proof]
fn f1_f32_sum_value_safe() {
    let s: f32 = [1.5f32, 2.25].iter().sum();
    assert!(s == 3.75);
}

#[kani::proof]
fn f2_f64_rounding_bug() {
    let s: f64 = [0.1f64, 0.2].iter().sum();
    assert!(s == 0.3);
}

#[kani::proof]
fn f2_f64_rounding_safe() {
    let s: f64 = [0.1f64, 0.2].iter().sum();
    assert!(s != 0.3);
}

#[kani::proof]
fn f3_f32_sum_to_inf_bug() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    assert!(s.is_finite());
}

#[kani::proof]
fn f3_f32_sum_to_inf_safe() {
    let s: f32 = [f32::MAX, f32::MAX].iter().sum();
    assert!(s.is_infinite());
}

#[kani::proof]
fn f4_f32_symbolic_sum_bug() {
    let x: f32 = kani::any();
    kani::assume(x.is_finite() && x > -10.0 && x < 10.0);
    let s: f32 = [x, 1.0].iter().sum();
    assert!(s == x);
}

#[kani::proof]
fn f4_f32_symbolic_sum_safe() {
    let x: f32 = kani::any();
    kani::assume(x.is_finite() && x > -10.0 && x < 10.0);
    let s: f32 = [x, 1.0].iter().sum();
    assert!(s == x + 1.0);
}

#[kani::proof]
fn f6_f64_product_inf_bug() {
    let p: f64 = [1e300f64, 1e300].iter().product();
    assert!(p.is_finite());
}

#[kani::proof]
fn f6_f64_product_inf_safe() {
    let p: f64 = [1e300f64, 1e300].iter().product();
    assert!(p.is_infinite());
}

#[kani::proof]
fn f7_f64_owned_sum_bug() {
    let s: f64 = [2.0f64, 3.0].into_iter().sum();
    assert!(s == 6.0);
}

#[kani::proof]
fn f7_f64_owned_sum_safe() {
    let s: f64 = [2.0f64, 3.0].into_iter().sum();
    assert!(s == 5.0);
}

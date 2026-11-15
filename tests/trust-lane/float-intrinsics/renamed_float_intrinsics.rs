// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The float intrinsics Trust core renamed, as pass/fail duals: `f64::abs` / `f32::abs` call
//! `fabs::<F>` on Trust and `fabsf64` / `fabsf32` on the frozen nightly; `min` / `max` call
//! `minimum_number_nsz_f*` / `maximum_number_nsz_f*` on Trust and `minnumf*` / `maxnumf*`
//! on the nightly. Both routes must model them identically: each `_holds` harness
//! SUCCESSFUL, each `_refuted` harness FAILED.

#[kani::proof]
fn abs_f64_clears_the_sign_holds() {
    let x: f64 = kani::any();
    assert!(x.abs().is_sign_positive(), "abs clears the sign bit");
}

#[kani::proof]
fn abs_f64_clears_the_sign_refuted() {
    let x: f64 = kani::any();
    assert!(x.abs().is_sign_negative(), "abs clears the sign bit");
}

#[kani::proof]
fn abs_f32_is_identity_on_positive_holds() {
    let x: f32 = kani::any();
    kani::assume(x.is_sign_positive());
    assert!(x.abs().to_bits() == x.to_bits(), "abs of a positive float");
}

#[kani::proof]
fn abs_f32_is_identity_on_positive_refuted() {
    let x: f32 = kani::any();
    assert!(x.abs().to_bits() == x.to_bits(), "abs of a positive float");
}

#[kani::proof]
fn min_f32_picks_an_argument_holds() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(!a.is_nan() && !b.is_nan());
    let m = a.min(b);
    assert!(m == a || m == b, "min is one of its arguments");
}

#[kani::proof]
fn min_f32_picks_an_argument_refuted() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(!a.is_nan() && !b.is_nan());
    let m = a.min(b);
    assert!(m == a, "min is its first argument");
}

#[kani::proof]
fn max_f64_ignores_nan_holds() {
    let a: f64 = kani::any();
    kani::assume(!a.is_nan());
    assert!(f64::NAN.max(a) == a, "max ignores a NaN argument");
}

#[kani::proof]
fn max_f64_ignores_nan_refuted() {
    let a: f64 = kani::any();
    kani::assume(!a.is_nan());
    assert!(f64::NAN.max(a) != a, "max ignores a NaN argument");
}

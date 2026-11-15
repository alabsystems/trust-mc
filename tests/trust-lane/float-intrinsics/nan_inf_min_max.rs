// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! NaN in either argument position, two NaNs, and infinities for `min` / `max`, as route
//! duals. "If one of the arguments is NaN, then the other argument is returned." Guards the
//! min/max encodings against losing their NaN cases while opposite zeros became a choice.

#[kani::proof]
fn min32_nan_second_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.min(f32::NAN) == x, "min ignores a NaN second argument");
}

#[kani::proof]
fn min32_nan_second_refuted() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.min(f32::NAN).is_nan(), "min ignores a NaN second argument");
}

#[kani::proof]
fn min32_nan_first_refuted() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(f32::NAN.min(x).is_nan(), "min ignores a NaN first argument");
}

#[kani::proof]
fn max64_nan_second_holds() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.max(f64::NAN) == x, "max ignores a NaN second argument");
}

#[kani::proof]
fn max64_nan_second_refuted() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.max(f64::NAN).is_nan(), "max ignores a NaN second argument");
}

#[kani::proof]
fn min32_conc_nan_second_holds() {
    let r = 1.5f32.min(f32::NAN);
    assert!(r == 1.5, "min(1.5, NaN) is 1.5");
}

#[kani::proof]
fn min32_conc_nan_second_refuted() {
    let r = 1.5f32.min(f32::NAN);
    assert!(r.is_nan(), "min(1.5, NaN) is 1.5");
}

#[kani::proof]
fn max64_conc_neg_nan_first_refuted() {
    let r = (-f64::NAN).max(-3.0);
    assert!(r.is_nan(), "max(-NaN, -3) is -3");
}

#[kani::proof]
fn min32_both_nan_holds() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let x = f32::from_bits(a);
    let y = f32::from_bits(b);
    kani::assume(x.is_nan() && y.is_nan());
    assert!(x.min(y).is_nan(), "min of two NaNs is NaN");
}

#[kani::proof]
fn min32_both_nan_refuted() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let x = f32::from_bits(a);
    let y = f32::from_bits(b);
    kani::assume(x.is_nan() && y.is_nan());
    assert!(!x.min(y).is_nan(), "min of two NaNs is NaN");
}

#[kani::proof]
fn min64_neg_inf_holds() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.min(f64::NEG_INFINITY) == f64::NEG_INFINITY, "-inf is the least");
}

#[kani::proof]
fn min64_neg_inf_refuted() {
    let x: f64 = kani::any();
    kani::assume(!x.is_nan());
    assert!(x.min(f64::NEG_INFINITY) == x, "-inf is the least");
}

#[kani::proof]
fn max32_inf_nan_holds() {
    assert!(f32::INFINITY.max(f32::NAN) == f32::INFINITY, "max(inf, NaN) is inf");
}

#[kani::proof]
fn max32_inf_nan_refuted() {
    assert!(f32::INFINITY.max(f32::NAN).is_nan(), "max(inf, NaN) is inf");
}

#[kani::proof]
fn max32_neg_inf_vs_nan_refuted() {
    let r = f32::NAN.max(f32::NEG_INFINITY);
    assert!(r != f32::NEG_INFINITY, "max(NaN, -inf) is -inf");
}

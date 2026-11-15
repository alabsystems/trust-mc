// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `f32::min` / `f64::max` on zeros of opposite sign and on two NaNs, as route duals.
//!
//! Rust (and Trust core's `minimum_number_nsz_*` / `maximum_number_nsz_*`): "If the inputs
//! compare equal (such as for the case of +0.0 and -0.0), either input may be returned
//! non-deterministically", and a NaN result's sign and payload are unspecified. Measured on
//! arm64 with trust 8571 and nightly-2025-12-03 (O0 and O3): at run time `min(+0, -0)` and
//! `min(-0, +0)` are `-0`, `max` of both orders is `+0`; const evaluation in the same
//! toolchains gives `min(+0, -0) = +0` and `max(-0, +0) = -0`. So every sign assertion below is
//! `_unprovable`: it must never be SUCCESSFUL on either route in either lane. `_holds` hold.
//! The parity-1 review found six of these SUCCESSFUL (CHC, both routes) and two more in the
//! BMC constant fold.

#[kani::proof]
fn min32_pz_nz_eq_zero_holds() {
    let r = 0.0f32.min(-0.0);
    assert!(r == 0.0, "min of zeros is a zero");
}

#[kani::proof]
fn min32_pz_nz_negative_unprovable() {
    let r = 0.0f32.min(-0.0);
    assert!(r.is_sign_negative(), "sign of min(+0,-0)");
}

#[kani::proof]
fn min32_pz_nz_positive_unprovable() {
    let r = 0.0f32.min(-0.0);
    assert!(r.is_sign_positive(), "sign of min(+0,-0)");
}

#[kani::proof]
fn min32_nz_pz_negative_unprovable() {
    let r = (-0.0f32).min(0.0);
    assert!(r.is_sign_negative(), "sign of min(-0,+0)");
}

#[kani::proof]
fn min32_nz_pz_positive_unprovable() {
    let r = (-0.0f32).min(0.0);
    assert!(r.is_sign_positive(), "sign of min(-0,+0)");
}

#[kani::proof]
fn max32_pz_nz_negative_unprovable() {
    let r = 0.0f32.max(-0.0);
    assert!(r.is_sign_negative(), "sign of max(+0,-0)");
}

#[kani::proof]
fn max32_pz_nz_positive_unprovable() {
    let r = 0.0f32.max(-0.0);
    assert!(r.is_sign_positive(), "sign of max(+0,-0)");
}

#[kani::proof]
fn max64_nz_pz_negative_unprovable() {
    let r = (-0.0f64).max(0.0);
    assert!(r.is_sign_negative(), "sign of max(-0,+0)");
}

#[kani::proof]
fn max64_nz_pz_positive_unprovable() {
    let r = (-0.0f64).max(0.0);
    assert!(r.is_sign_positive(), "sign of max(-0,+0)");
}

#[kani::proof]
fn min64_sym_zeros_negative_unprovable() {
    let a: f64 = kani::any();
    let b: f64 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_positive() && b.is_sign_negative());
    assert!(a.min(b).is_sign_negative(), "sign of min(+0,-0), symbolic");
}

#[kani::proof]
fn min64_sym_zeros_positive_unprovable() {
    let a: f64 = kani::any();
    let b: f64 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_positive() && b.is_sign_negative());
    assert!(a.min(b).is_sign_positive(), "sign of min(+0,-0), symbolic");
}

#[kani::proof]
fn min32_sym_nz_pz_positive_unprovable() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_negative() && b.is_sign_positive());
    assert!(a.min(b).is_sign_positive(), "min(-0,+0) sign, symbolic");
}

#[kani::proof]
fn max32_sym_zeros_negative_unprovable() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_negative() && b.is_sign_positive());
    assert!(a.max(b).is_sign_negative(), "sign of max(-0,+0), symbolic");
}

#[kani::proof]
fn max32_sym_zeros_positive_unprovable() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_negative() && b.is_sign_positive());
    assert!(a.max(b).is_sign_positive(), "sign of max(-0,+0), symbolic");
}

#[kani::proof]
fn max32_sym_pz_nz_negative_unprovable() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a == 0.0 && b == 0.0 && a.is_sign_positive() && b.is_sign_negative());
    assert!(a.max(b).is_sign_negative(), "max(+0,-0) sign, symbolic");
}

#[kani::proof]
fn max32_sym_zeros_eq_zero_holds() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    kani::assume(a == 0.0 && b == 0.0);
    assert!(a.max(b) == 0.0, "max of zeros is a zero, symbolic");
}

#[kani::proof]
fn min32_both_nan_bits_unprovable() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let x = f32::from_bits(a);
    let y = f32::from_bits(b);
    kani::assume(x.is_nan() && y.is_nan());
    // The NaN a min of two NaNs returns is not specified bit for bit.
    let bits = x.min(y).to_bits();
    assert!(bits == a || bits == b, "min of two NaNs returns one of them bit for bit");
}

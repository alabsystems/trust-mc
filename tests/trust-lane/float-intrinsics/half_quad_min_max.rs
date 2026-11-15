// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `f16` / `f128` min, max, abs and copysign, as route duals.
//!
//! No engine models f16/f128 min or max. On the frozen nightly `minnumf16` has no body, so the
//! call fails closed. `abs` is modelled as a sign-bit clear: the nightly's `f16::abs` computes
//! exactly that with bit operations, and Trust core's `f16::abs` calls `fabs::<f16>`. Trust core's `minimum_number_nsz_f16` carries a fallback body that
//! returns `y` whenever the arguments compare equal; the BMC mini-inliner executed it and proved
//! `(-0.0f16).min(0.0).is_sign_positive()`, which fails at run time (measured: `-0`). An
//! unmodelled intrinsic may cost a proof, never produce a false one: `_unprovable` and
//! `_refuted` are never SUCCESSFUL.

#![feature(f16, f128)]

#[kani::proof]
fn f16_min_holds() {
    let a: f16 = 1.0;
    let b: f16 = 2.0;
    assert!(a.min(b) == 1.0, "f16 min");
}

#[kani::proof]
fn f16_min_refuted() {
    let a: f16 = 1.0;
    let b: f16 = 2.0;
    assert!(a.min(b) == 2.0, "f16 min");
}

#[kani::proof]
fn f16_abs_holds() {
    let a: f16 = -3.0;
    assert!(a.abs() == 3.0, "f16 abs");
}

#[kani::proof]
fn f16_abs_refuted() {
    let a: f16 = -3.0;
    assert!(a.abs() == -3.0, "f16 abs");
}

#[kani::proof]
fn f128_max_holds() {
    let a: f128 = 1.0;
    let b: f128 = 2.0;
    assert!(a.max(b) == 2.0, "f128 max");
}

#[kani::proof]
fn f128_max_refuted() {
    let a: f128 = 1.0;
    let b: f128 = 2.0;
    assert!(a.max(b) == 1.0, "f128 max");
}

#[kani::proof]
fn f128_abs_sym_refuted() {
    let bits: u128 = kani::any();
    let x = f128::from_bits(bits);
    assert!(x.abs().to_bits() == bits, "f128 abs keeps the sign");
}

#[kani::proof]
fn f16_min_pz_nz_negative_unprovable() {
    let a: f16 = 0.0;
    let b: f16 = -0.0;
    assert!(a.min(b).is_sign_negative(), "f16 min(+0,-0) sign");
}

#[kani::proof]
fn f16_min_pz_nz_positive_unprovable() {
    let a: f16 = 0.0;
    let b: f16 = -0.0;
    assert!(a.min(b).is_sign_positive(), "f16 min(+0,-0) sign");
}

#[kani::proof]
fn f16_min_nz_pz_positive_unprovable() {
    let a: f16 = -0.0;
    let b: f16 = 0.0;
    assert!(a.min(b).is_sign_positive(), "f16 min(-0,+0) sign");
}

#[kani::proof]
fn f16_min_nz_pz_negative_unprovable() {
    let a: f16 = -0.0;
    let b: f16 = 0.0;
    assert!(a.min(b).is_sign_negative(), "f16 min(-0,+0) sign");
}

#[kani::proof]
fn f128_max_nz_pz_positive_unprovable() {
    let a: f128 = -0.0;
    let b: f128 = 0.0;
    assert!(a.max(b).is_sign_positive(), "f128 max(-0,+0) sign");
}

#[kani::proof]
fn f16_min_value_holds() {
    let a: f16 = 2.5;
    let b: f16 = -1.0;
    assert!(a.min(b) == -1.0, "f16 min value");
}

#[kani::proof]
fn f16_copysign_refuted() {
    let a: f16 = 1.0;
    assert!(a.copysign(-1.0) == 1.0, "f16 copysign");
}

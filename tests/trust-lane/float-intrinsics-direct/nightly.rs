// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The DevCli half of `trust.rs`: the same harnesses under the frozen nightly's spellings of
//! the float intrinsics (`fabsf32`, `fabsf64`, `minnumf32`, `maxnumf64`).

#![feature(core_intrinsics, f16)]
#![allow(internal_features, unused_unsafe)]
use std::intrinsics;

#[kani::proof]
fn direct_fabs32_holds() {
    let x: f32 = kani::any();
    assert!(unsafe { intrinsics::fabsf32(x) }.is_sign_positive(), "fabs clears the sign");
}

#[kani::proof]
fn direct_fabs32_refuted() {
    let x: f32 = kani::any();
    assert!(unsafe { intrinsics::fabsf32(x) }.to_bits() == x.to_bits(), "fabs keeps the sign");
}

#[kani::proof]
fn direct_fabs64_neg_zero_refuted() {
    assert!(unsafe { intrinsics::fabsf64(-0.0f64) }.is_sign_negative(), "fabs(-0) sign");
}

#[kani::proof]
fn direct_minnsz32_nan_second_holds() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(unsafe { intrinsics::minnumf32(x, f32::NAN) } == x, "NaN ignored");
}

#[kani::proof]
fn direct_minnsz32_nan_second_refuted() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(unsafe { intrinsics::minnumf32(x, f32::NAN) }.is_nan(), "NaN ignored");
}

#[kani::proof]
fn direct_minnsz32_zero_negative_unprovable() {
    assert!(unsafe { intrinsics::minnumf32(0.0, -0.0) }.is_sign_negative(), "sign");
}

#[kani::proof]
fn direct_minnsz32_zero_positive_unprovable() {
    assert!(unsafe { intrinsics::minnumf32(0.0, -0.0) }.is_sign_positive(), "sign");
}

#[kani::proof]
fn direct_maxnsz64_zero_negative_unprovable() {
    assert!(unsafe { intrinsics::maxnumf64(-0.0, 0.0) }.is_sign_negative(), "sign");
}

#[kani::proof]
fn direct_maxnsz64_zero_positive_unprovable() {
    assert!(unsafe { intrinsics::maxnumf64(-0.0, 0.0) }.is_sign_positive(), "sign");
}

#[kani::proof]
fn direct_minimum32_zero_holds() {
    assert!(unsafe { intrinsics::minimumf32(0.0, -0.0) }.is_sign_negative(), "minimum orders -0 < +0");
}

#[kani::proof]
fn direct_minimum32_zero_refuted() {
    assert!(unsafe { intrinsics::minimumf32(0.0, -0.0) }.is_sign_positive(), "minimum orders -0 < +0");
}

#[kani::proof]
fn direct_minimum32_nan_holds() {
    let x: f32 = kani::any();
    assert!(unsafe { intrinsics::minimumf32(x, f32::NAN) }.is_nan(), "minimum propagates NaN");
}

#[kani::proof]
fn direct_minimum32_nan_refuted() {
    let x: f32 = kani::any();
    kani::assume(!x.is_nan());
    assert!(unsafe { intrinsics::minimumf32(x, f32::NAN) } == x, "minimum propagates NaN");
}

// --- The intrinsic as a FUNCTION ITEM (parity-1 second review, F-dyn) -----------------------
// Reached through `F: Fn`, `&dyn Fn`, `Box<dyn Fn>`, `Iterator::reduce` / `fold` and a closure:
// call sites the rename table never sees as an intrinsic call. On Trust the CHC dyn-callable,
// `Fn`-trait and fn-pointer resolvers fetched the item's body directly and inlined Trust's
// fallback body (`y` for equal arguments), proving `f(-0.0, 0.0).is_sign_positive()` where the
// nightly route fails closed. Every codegen body fetch now goes through
// `CalleeBody::callee_body`, which refuses a renamed float intrinsic on both toolchains.

fn apply<F: Fn(f32, f32) -> f32>(f: F, a: f32, b: f32) -> f32 {
    f(a, b)
}

fn apply_mut<F: FnMut(f64, f64) -> f64>(mut f: F, a: f64, b: f64) -> f64 {
    f(a, b)
}

fn apply16<F: Fn(f16, f16) -> f16>(f: F, a: f16, b: f16) -> f16 {
    f(a, b)
}

#[kani::proof]
fn fnitem_min_value_holds() {
    assert!(apply(intrinsics::minnumf32, 1.0, 2.0) == 1.0);
}

#[kani::proof]
fn fnitem_min_value_refuted() {
    assert!(apply(intrinsics::minnumf32, 1.0, 2.0) == 2.0);
}

#[kani::proof]
fn fnitem_min_nz_pz_positive_unprovable() {
    assert!(apply(intrinsics::minnumf32, -0.0, 0.0).is_sign_positive());
}

#[kani::proof]
fn fnitem_max_pz_nz_negative_unprovable() {
    assert!(apply_mut(intrinsics::maxnumf64, 0.0, -0.0).is_sign_negative());
}

#[kani::proof]
fn fnitem_min16_nz_pz_positive_unprovable() {
    assert!(apply16(intrinsics::minnumf16, -0.0, 0.0).is_sign_positive());
}

#[kani::proof]
fn dynfn_min_nz_pz_positive_unprovable() {
    let f: &dyn Fn(f32, f32) -> f32 = &intrinsics::minnumf32;
    assert!(f(-0.0, 0.0).is_sign_positive());
}

#[kani::proof]
fn dynfn_min_value_holds() {
    let f: &dyn Fn(f32, f32) -> f32 = &intrinsics::minnumf32;
    assert!(f(3.0, -1.0) == -1.0);
}

#[kani::proof]
fn dynfn_min_value_refuted() {
    let f: &dyn Fn(f32, f32) -> f32 = &intrinsics::minnumf32;
    assert!(f(3.0, -1.0) == 3.0);
}

#[kani::proof]
fn boxdynfn_max_pz_nz_negative_unprovable() {
    let f: Box<dyn Fn(f64, f64) -> f64> = Box::new(intrinsics::maxnumf64);
    assert!(f(0.0, -0.0).is_sign_negative());
}

#[kani::proof]
fn boxdynfn_max_value_holds() {
    let f: Box<dyn Fn(f64, f64) -> f64> = Box::new(intrinsics::maxnumf64);
    assert!(f(1.0, 3.0) == 3.0);
}

#[kani::proof]
fn reduce_min_nz_pz_positive_unprovable() {
    let r = [-0.0f32, 0.0].iter().copied().reduce(intrinsics::minnumf32).unwrap();
    assert!(r.is_sign_positive());
}

#[kani::proof]
fn fold_max_pz_nz_negative_unprovable() {
    let r = [0.0f64, -0.0].iter().copied().fold(f64::NEG_INFINITY, intrinsics::maxnumf64);
    assert!(r.is_sign_negative());
}

#[kani::proof]
fn fold_max_value_holds() {
    let r = [1.0f64, 3.0, 2.0].iter().copied().fold(f64::NEG_INFINITY, intrinsics::maxnumf64);
    assert!(r == 3.0);
}

#[kani::proof]
fn method_fnitem_min_nz_pz_positive_unprovable() {
    assert!(apply(f32::min, -0.0, 0.0).is_sign_positive());
}

#[kani::proof]
fn method_dynfn_max_pz_nz_negative_unprovable() {
    let f: &dyn Fn(f64, f64) -> f64 = &f64::max;
    assert!(f(0.0, -0.0).is_sign_negative());
}

#[kani::proof]
fn method_dynfn_max_value_holds() {
    let f: &dyn Fn(f64, f64) -> f64 = &f64::max;
    assert!(f(-2.0, 2.0) == 2.0);
}

#[kani::proof]
fn closure_over_intrinsic_min_nz_pz_positive_unprovable() {
    let c = |a: f32, b: f32| intrinsics::minnumf32(a, b);
    assert!(c(-0.0, 0.0).is_sign_positive());
}

#[kani::proof]
fn closure_over_intrinsic_min_value_holds() {
    let c = |a: f32, b: f32| intrinsics::minnumf32(a, b);
    assert!(c(-1.0, 4.0) == -1.0);
}

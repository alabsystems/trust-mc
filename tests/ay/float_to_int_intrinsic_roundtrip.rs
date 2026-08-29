// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF

//! Part of #3465: constant intrinsic round-trip proof.
//!
//! Verifies `float_to_int_unchecked(f) as float == f.trunc()` on a constant
//! witness after the intrinsic lane moved to the parser-safe BV extractor and
//! the surrounding `as` / `trunc()` obligations moved to pure-BV CHC lowering.
//!
//! Recovered to PROOF: `u as f32` / `u as f64` and `f.trunc()` no longer emit
//! CHC FP rounding-mode terms, so the constant round-trip stays parser-safe on
//! current Z3 fixedpoint.

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::float_to_int_unchecked;

#[kani::proof]
fn check_f32_intrinsic_roundtrip_constant() {
    let f: f32 = kani::any();
    kani::assume(f == 42.0);
    let u: u32 = unsafe { float_to_int_unchecked(f) };
    assert_eq!(u as f32, f.trunc());
}

#[kani::proof]
fn check_f64_intrinsic_roundtrip_constant() {
    let f: f64 = kani::any();
    kani::assume(f == 42.0);
    let u: u32 = unsafe { float_to_int_unchecked(f) };
    assert_eq!(u as f64, f.trunc());
}

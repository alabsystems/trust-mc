// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF

//! Diagnostic harness: isolate the `any_where` precondition lane for #3465.
//!
//! This keeps the symbolic predicate shape from
//! `tests/trust_mc/Intrinsics/FloatToInt/float_to_int.rs` but removes the
//! `u as float == f.trunc()` round-trip assertion so the intrinsic path can be
//! checked without the `IntToFloat` obligation.
//!
//! Recovered to PROOF: `u32::MAX as f32` / `u32::MAX as f64` now lower through
//! the pure-BV IntToFloat cast path, so the symbolic `any_where` bounds stay on
//! parser-safe BV terms instead of emitting CHC FP rounding modes.

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::float_to_int_unchecked;

#[kani::proof]
fn check_f32_intrinsic_predicate_only() {
    let f: f32 = kani::any_where(|f: &f32| f.is_finite() && *f > 0.0 && *f < u32::MAX as f32);
    let _u: u32 = unsafe { float_to_int_unchecked(f) };
}

#[kani::proof]
fn check_f64_intrinsic_predicate_only() {
    let f: f64 = kani::any_where(|f: &f64| f.is_finite() && *f > 0.0 && *f < u32::MAX as f64);
    let _u: u32 = unsafe { float_to_int_unchecked(f) };
}

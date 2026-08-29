// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: --harness check_simd_bitmask_model
//
// NOTE: this is an `expected`-suite test — the expectation lives in the
// sibling `expected` file. (It shipped with a `kani-expect: PROOF` header,
// which is the tests/ay suite's directive, and WITHOUT an `expected` file,
// so compiletest panicked with `NotFound` before running the driver at all.)

//! Part of #2285: regression for simd_bitmask CHC encoding.
//! Previously returned CTREX because the model call left the return value
//! unconstrained. Now encodes lane-by-lane bitmask computation.
#![feature(repr_simd, core_intrinsics)]

use std::intrinsics::simd::simd_bitmask;

#[repr(simd)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
struct i32x4([i32; 4]);

#[kani::proof]
fn check_simd_bitmask_model() {
    let lanes = i32x4([0, 0, 0, 0]);
    let mask: u8 = unsafe { simd_bitmask(lanes) };
    assert_eq!(mask, 0);
}

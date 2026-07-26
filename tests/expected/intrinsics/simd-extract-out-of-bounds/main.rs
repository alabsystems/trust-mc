// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-verify-fail

//! Checks that `simd_extract` triggers an out-of-bounds failure when the
//! index is >= the number of lanes in the SIMD vector.
//! Part of #1516: SIMD extract/insert contracts missing index bounds.
#![feature(repr_simd, core_intrinsics)]
use std::intrinsics::simd::simd_extract;

#[repr(simd)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
pub struct i64x2([i64; 2]);

#[kani::proof]
fn main() {
    let y = i64x2([10, 20]);
    // Index 2 is out of bounds for a 2-element vector (valid: 0, 1)
    let _: i64 = unsafe { simd_extract(y, 2) };
}

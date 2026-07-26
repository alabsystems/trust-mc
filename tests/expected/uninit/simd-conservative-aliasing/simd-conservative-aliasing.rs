// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-flags: -Z uninit-checks

//! Regression test for #971: points_to_analysis should not panic on unsupported intrinsics.
//!
//! Previously, the points_to_analysis would call `unimplemented!()` for intrinsics
//! not explicitly handled, causing panics during analysis. The fix uses conservative
//! aliasing assumptions instead, allowing the analysis to proceed.
//!
//! This test uses SIMD intrinsics which fall into the conservative aliasing path.
//! Expected behavior: analysis completes with warning, verification succeeds.

#![feature(repr_simd, core_intrinsics)]

use std::intrinsics::simd::simd_add;

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct i32x2([i32; 2]);

impl i32x2 {
    fn sum(&self) -> i32 {
        self.0[0] + self.0[1]
    }
}

/// Tests that points_to_analysis handles SIMD intrinsics without panicking.
/// The simd_add intrinsic is not in the explicit handler list, so it triggers
/// the conservative aliasing fallback at points_to_analysis.rs:307-327.
#[kani::proof]
fn check_simd_conservative_aliasing() {
    let a = i32x2([1, 2]);
    let b = i32x2([3, 4]);
    let result = unsafe { simd_add(a, b) };
    assert!(result.sum() == 10);
}

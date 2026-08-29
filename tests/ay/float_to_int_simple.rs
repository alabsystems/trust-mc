// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// kani-expect: check_f32_to_u32_simple=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
//
// Minimal float-to-int test: single f32 → u32 conversion.
// Part of #3668: isolate BV extraction path.

#[kani::proof]
fn check_f32_to_u32_simple() {
    let f: f32 = 42.0;
    let u: u32 = f as u32;
    assert_eq!(u, 42);
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-track=mem
// kani-expect: PROOF
//
//! Regression test for #3879: `[v; N]` repeat init must populate
//! per-field typed memories so `assert_eq!` on struct fields works.
//! The value path (`kani::assert(a[i].x == 42)`) works because it
//! reads from the BV value directly. The memory path (`assert_eq!`)
//! dereferences through typed memory (`mem_u32`, `mem_u64`), which
//! was unpopulated before the fix.

#[derive(Copy, Clone, PartialEq, Eq)]
struct Pair {
    x: u32,
    y: u64,
}

#[kani::proof]
fn test_repeat_struct_assert_eq_field() {
    let a = [Pair { x: 42, y: 100 }; 4];
    // assert_eq! forces the deref/memory path — this was CTREX before #3879.
    assert_eq!(a[0].x, 42);
    assert_eq!(a[0].y, 100);
    assert_eq!(a[2].x, 42);
    assert_eq!(a[3].y, 100);
}

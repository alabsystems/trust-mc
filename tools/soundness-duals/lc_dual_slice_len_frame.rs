// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z loop-contracts
//
// A slice length replayed from a CHC side table after its source left the frame.
//
// `kani::slice::any_slice_of_array` builds `&a[from..to]` with `to <= 10` and
// `from <= to` assumed on the range local. The CHC encoder caches the slice
// length as `to - from` over that range local's columns (`subslice_len`) and
// replays the cached expression in later blocks, where liveness has already
// pruned the range local from the relation frame: the length becomes a free
// variable, `len` is unbounded, and `kani::index as u32 * u8::MAX as u32`
// "overflows". tests/expected/loop-contract/for_loop_for_slice.rs reported that
// as FAILED with [AY:CTREX_CAT:Genuine]; Kani 0.67.0 reports SUCCESSFUL.
//
// Oracles (each confirmed with Kani 0.67.0):
//   slice_loop_len_safe  NOT-GENUINE  (Kani SUCCESSFUL; a certified counterexample is false)
//   slice_loop_len_bug   MUST FAIL    (a 10-element slice exists: `len < 10` is violable)
#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn slice_loop_len_safe() {
    let mut sum: u32 = 0;
    let a: [u8; 10] = kani::any();
    let s = kani::slice::any_slice_of_array(&a);
    let len = s.len();
    #[kani::loop_invariant( sum <= (kani::index as u32 * u8::MAX as u32) )]
    for j in s {
        sum = sum + (j as u32);
    }
    assert!(sum <= (255 as u32 * len as u32));
}

#[kani::proof]
fn slice_loop_len_bug() {
    let mut sum: u32 = 0;
    let a: [u8; 10] = kani::any();
    let s = kani::slice::any_slice_of_array(&a);
    let len = s.len();
    #[kani::loop_invariant( sum <= (kani::index as u32 * u8::MAX as u32) )]
    for j in s {
        sum = sum + (j as u32);
    }
    assert!(len < 10);
}

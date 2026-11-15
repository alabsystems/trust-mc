// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the loop
//! the kani library's `Arbitrary::any_array` runs for `kani::any::<[bool; N]>()`,
//! which both lanes model as a fresh array, under a declared unwind bound
//! (walker fail-closed review, round 1 of the repair after the merge with
//! main's Rule D, 2026-10-14, finding 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-14):
//!   k1_bool_array4_u4_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k1_bool_array4_u5_safe       -> VERIFICATION:- SUCCESSFUL
//!   k2_vec_bool_n4_u4_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k2_vec_bool_n3_u4_safe       -> VERIFICATION:- SUCCESSFUL
//!   k3_nested_bool_u3_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k3_nested_bool_u4_safe       -> VERIFICATION:- SUCCESSFUL
//!   k4_option_bool_array_u3_bug  -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   k5_u8_array8_u2_safe         -> VERIFICATION:- SUCCESSFUL
//!   k6_bool_array_in_fn_u3_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. The library's `Arbitrary for [T; N]` is
//! `T::any_array::<N>()`, and only the integers, floats and `()` override
//! `any_array` without a loop; `bool` runs `[(); N].map(|_| bool::any())`, `N`
//! passes, so `unwind(U)` with `U <= N` fails Kani's unwinding assertion. Both
//! lanes keep `kani::any::<[bool; N]>()` as a model call
//! (`inline/handler_boundaries.rs`) and produced a fresh array without that
//! loop: the bug rows verified clean on main and on the branch. The model
//! sites now state the assertion when the declared bound does not cover the
//! loop (`shared/kani_any_loops.rs`; CHC `kani_any_unwinding_check`, its walker
//! half, BMC `bmc_kani_any_unwinding_check`). The pass count is a constant, so
//! the check is exact.
//!
//! Lane scope: BMC and CHC.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s kani_any_array_unwind_dual.rs

#[kani::proof]
#[kani::unwind(4)]
fn k1_bool_array4_u4_bug() {
    let a: [bool; 4] = kani::any();
    assert!(a.len() == 4);
}

#[kani::proof]
#[kani::unwind(5)]
fn k1_bool_array4_u5_safe() {
    let a: [bool; 4] = kani::any();
    assert!(a.len() == 4);
}

#[kani::proof]
#[kani::unwind(4)]
fn k2_vec_bool_n4_u4_bug() {
    let v: Vec<bool> = kani::bounded_any::<_, 4>();
    assert!(v.len() <= 4);
}

#[kani::proof]
#[kani::unwind(4)]
fn k2_vec_bool_n3_u4_safe() {
    let v: Vec<bool> = kani::bounded_any::<_, 3>();
    assert!(v.len() <= 3);
}

#[kani::proof]
#[kani::unwind(3)]
fn k3_nested_bool_u3_bug() {
    let a: [[bool; 2]; 3] = kani::any();
    assert!(a.len() == 3);
}

#[kani::proof]
#[kani::unwind(4)]
fn k3_nested_bool_u4_safe() {
    let a: [[bool; 2]; 3] = kani::any();
    assert!(a.len() == 3);
}

#[kani::proof]
#[kani::unwind(3)]
fn k4_option_bool_array_u3_bug() {
    let a: Option<[bool; 3]> = kani::any();
    assert!(a.is_none() || a.unwrap().len() == 3);
}

#[kani::proof]
#[kani::unwind(2)]
fn k5_u8_array8_u2_safe() {
    let a: [u8; 8] = kani::any();
    assert!(a.len() == 8);
}

#[inline(never)]
fn flags() -> [bool; 3] {
    kani::any()
}

#[kani::proof]
#[kani::unwind(3)]
fn k6_bool_array_in_fn_u3_bug() {
    let a = flags();
    assert!(a.len() == 3);
}

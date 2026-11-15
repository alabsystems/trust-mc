// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the
//! comparison loop of `==` on an `Option`, `Result` or `Box` of an array or a
//! `str`, a comparison both lanes model as one value comparison, under a
//! declared unwind bound (walker fail-closed review, round 1 of the repair
//! after the merge with main's Rule D, 2026-10-14, findings 4 and 5).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-14):
//!   w1_option_u8_array_u3_bug    -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   w1_option_u8_array_u5_safe   -> VERIFICATION:- SUCCESSFUL
//!   w2_option_u16_array_u3_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   w2_option_u16_array_u9_safe  -> VERIFICATION:- SUCCESSFUL
//!   w3_option_str_u3_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   w3_option_str_u6_safe        -> VERIFICATION:- SUCCESSFUL
//!   w4_box_array_u3_bug          -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   w4_box_array_u5_safe         -> VERIFICATION:- SUCCESSFUL
//!   w5_result_array_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   w5_result_array_u5_safe      -> VERIFICATION:- SUCCESSFUL
//!   w6_option_scalar_u2_safe     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. A wrapper compares its parts with no loop of its own;
//! an array part `[P; N]` of a primitive `P` runs Kani's `memcmp` over its
//! `N * size_of::<P>()` bytes and a `str` part a loop over its length
//! (`shared/compare_loops.rs`). The BMC lane's comparison check
//! (`bmc_compare_unwinding_check`) read only bare arrays, slices, `str` and
//! `Vec`, so the u3 bug rows of `Option` verified clean there; it now bounds
//! a wrapper by its parts and fails a `str` part closed. The CHC lane had no
//! trip-count row for a wrapper and failed every safe row closed; the row
//! (`model_call_trip_bound`) now bounds it the same way, and a `str` part
//! keeps the plain check.
//!
//! Lane scope: BMC and CHC.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s model_call_unwind_wrapped_eq_dual.rs

#[kani::proof]
#[kani::unwind(3)]
fn w1_option_u8_array_u3_bug() {
    let a = Some([1u8, 2, 3, 4]);
    let b = Some([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(5)]
fn w1_option_u8_array_u5_safe() {
    let a = Some([1u8, 2, 3, 4]);
    let b = Some([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w2_option_u16_array_u3_bug() {
    let a = Some([1u16, 2, 3, 4]);
    let b = a;
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(9)]
fn w2_option_u16_array_u9_safe() {
    let a = Some([1u16, 2, 3, 4]);
    let b = a;
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w3_option_str_u3_bug() {
    let a: Option<&str> = Some("hello");
    let b: Option<&str> = Some("hello");
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(6)]
fn w3_option_str_u6_safe() {
    let a: Option<&str> = Some("hello");
    let b: Option<&str> = Some("hello");
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w4_box_array_u3_bug() {
    let a: Box<[u8; 4]> = Box::new([1u8, 2, 3, 4]);
    let b: Box<[u8; 4]> = Box::new([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(5)]
fn w4_box_array_u5_safe() {
    let a: Box<[u8; 4]> = Box::new([1u8, 2, 3, 4]);
    let b: Box<[u8; 4]> = Box::new([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(3)]
fn w5_result_array_u3_bug() {
    let a: Result<[u8; 4], u8> = Ok([1u8, 2, 3, 4]);
    let b: Result<[u8; 4], u8> = Ok([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(5)]
fn w5_result_array_u5_safe() {
    let a: Result<[u8; 4], u8> = Ok([1u8, 2, 3, 4]);
    let b: Result<[u8; 4], u8> = Ok([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(2)]
fn w6_option_scalar_u2_safe() {
    let x: u32 = kani::any();
    let a = Some(x);
    let b = Some(x);
    assert!(a == b);
}

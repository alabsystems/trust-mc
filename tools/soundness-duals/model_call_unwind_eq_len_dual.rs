// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the
//! comparison loop of an array, `str` or `Vec` equality the CHC lane models,
//! under a declared unwind bound (fix/chc-walker-fail-closed, the merge with
//! main's Rule D, 2026-10-14; the corpus units `FunctionAbstractions/mem_swap.rs`,
//! `mem_replace.rs`, `Slice/main.rs`, `Vectors/vector_extend_bytes.rs`,
//! `Vectors/any/resize.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-14):
//!   e1_array_eq_generic_u9_safe -> VERIFICATION:- SUCCESSFUL
//!   e1_array_eq_generic_u3_bug  -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   e2_str_eq_u6_safe           -> VERIFICATION:- SUCCESSFUL
//!   e2_str_eq_u3_bug            -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   e3_vec_eq_array_u4_safe     -> VERIFICATION:- SUCCESSFUL
//!   e3_vec_eq_array_u2_bug      -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. A modelled call whose callee may loop states
//! Kani's unwinding assertion as `B < U ∨ t` with `B` its trip bound
//! (`codegen_call_model_unwind.rs`, repair rounds 4 and 5). The array row
//! matched only the instance spelling of the callee (`<[u16; 4] as
//! PartialEq>::eq`), not its definition path (`std::array::equality::<impl
//! PartialEq<[U; N]> for [T; N]>::eq`, what a generic caller's call prints
//! as), and the slice row had no length for a `str::as_bytes` view or a
//! `Vec`'s slice view; both fell to the bound-less check `t` and failed
//! closed where main and Kani prove the safe rows. The bound is now the
//! array's byte count and the slice length the lane tracks
//! (`ref_resolution.subslice_len`); the bug rows still fail on the bound.
//!
//! Lane scope: BMC and CHC (the BMC lane has no trip-count row for these and
//! fails the modelled loop closed).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s model_call_unwind_eq_len_dual.rs

fn same<T: kani::Arbitrary + PartialEq + Clone>() {
    let a = kani::any::<T>();
    let b = a.clone();
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(9)]
fn e1_array_eq_generic_u9_safe() {
    same::<[u16; 4]>();
}

#[kani::proof]
#[kani::unwind(3)]
fn e1_array_eq_generic_u3_bug() {
    same::<[u16; 4]>();
}

#[kani::proof]
#[kani::unwind(6)]
fn e2_str_eq_u6_safe() {
    let name: &str = "hello";
    assert!(name == "hello");
}

#[kani::proof]
#[kani::unwind(3)]
fn e2_str_eq_u3_bug() {
    let name: &str = "hello";
    assert!(name == "hello");
}

#[kani::proof]
#[kani::unwind(4)]
fn e3_vec_eq_array_u4_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(b"Hi");
    assert_eq!(v, [72, 105]);
}

#[kani::proof]
#[kani::unwind(2)]
fn e3_vec_eq_array_u2_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(b"Hi");
    assert_eq!(v, [72, 105]);
}

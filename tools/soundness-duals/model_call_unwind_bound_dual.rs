// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the trip-count bounds of modelled std
//! calls under a declared unwind bound, at their boundaries
//! (fix/chc-walker-fail-closed, repair round 4: the class of walker
//! fail-closed review 6 round 3 finding 6).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   b2_reverse_n4_u2_bug         -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b2_reverse_n4_u3_safe        -> VERIFICATION:- SUCCESSFUL
//!   b3_extend_range_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b3_extend_range_u5_safe      -> VERIFICATION:- SUCCESSFUL
//!   b4_from_elem_n4_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b4_from_elem_n4_u5_safe      -> VERIFICATION:- SUCCESSFUL
//!   b5_array_eq_n6_u4_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b5_array_eq_n6_u8_safe       -> VERIFICATION:- SUCCESSFUL
//!   b6_swap_u1_safe              -> VERIFICATION:- SUCCESSFUL
//!   b7_extend_incl_n4_u3_bug     -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   b7_extend_incl_n4_u4_safe    -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. A modelled call whose callee may loop states Kani's
//! unwinding assertion as `bound < U ∨ t` (`codegen_call_model_unwind.rs`),
//! where `bound` counts the back edges of every loop the callee runs (the
//! `pow` rule's rows are in `model_call_unwind_pow_dual.rs`, CHC only):
//! `max(len / 2, size / 8)` for
//! `reverse`, `end - start` for `extend` from a `Range` or `RangeInclusive`
//! (one fewer than the inclusive range's length), `n` for `vec![x; n]`, `N`
//! for an array comparison, `size / 8` for `mem::swap`. Each `_bug` row needs
//! a pass past the bound and fails; each `_safe` row stays within it and
//! proves, as Kani does (the reverse, extend and array-comparison rules were
//! measured over grids, `probes/g2_reverse_grid.rs`, `probes/g3_extend_grid.rs`). Two bounds were wrong on the first cut and
//! these rows caught them: `extend` used the range's length (`b3` and `b7`
//! safe rows failed) and an array `==` the harness inliner unfolds into
//! `a[..] == b[..]` had no length (`b5_array_eq_n6_u8_safe` failed).

#[kani::proof]
#[kani::unwind(2)]
fn b2_reverse_n4_u2_bug() {
    let mut a = [0u64; 4];
    a[0] = kani::any();
    a.reverse();
}

#[kani::proof]
#[kani::unwind(3)]
fn b2_reverse_n4_u3_safe() {
    let mut a = [0u64; 4];
    a[0] = kani::any();
    a.reverse();
}

#[kani::proof]
#[kani::unwind(3)]
fn b3_extend_range_u3_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..4u32);
}

#[kani::proof]
#[kani::unwind(5)]
fn b3_extend_range_u5_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..4u32);
    assert!(v.len() == 4);
}

#[kani::proof]
#[kani::unwind(3)]
fn b4_from_elem_n4_u3_bug() {
    let x: u32 = kani::any();
    let v = vec![x; 4];
    let _ = v;
}

#[kani::proof]
#[kani::unwind(5)]
fn b4_from_elem_n4_u5_safe() {
    let x: u32 = kani::any();
    let v = vec![x; 4];
    assert!(v.len() == 4);
}

#[kani::proof]
#[kani::unwind(4)]
fn b5_array_eq_n6_u4_bug() {
    let a: [(); 6] = kani::any();
    let b: [(); 6] = kani::any();
    let _ = a == b;
}

#[kani::proof]
#[kani::unwind(8)]
fn b5_array_eq_n6_u8_safe() {
    let a: [(); 6] = kani::any();
    let b: [(); 6] = kani::any();
    assert!(a == b);
}

#[kani::proof]
#[kani::unwind(1)]
fn b6_swap_u1_safe() {
    let mut a: u32 = kani::any();
    let mut b: u32 = 7;
    std::mem::swap(&mut a, &mut b);
    assert!(a == 7);
}

#[kani::proof]
#[kani::unwind(3)]
fn b7_extend_incl_n4_u3_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..=3u32);
}

#[kani::proof]
#[kani::unwind(4)]
fn b7_extend_incl_n4_u4_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0..=3u32);
    assert!(v.len() == 4);
}

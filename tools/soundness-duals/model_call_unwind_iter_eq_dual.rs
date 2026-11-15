// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the
//! loops `Iterator::eq` / `ne` runs, with an adapter on the OTHER side
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 2).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   z1_eq_filter_other_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   z1_eq_filter_other_u7_safe      -> VERIFICATION:- SUCCESSFUL
//!   z2_eq_skip_while_other_u3_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   z3_ne_filter_other_u3_bug       -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   z4_eq_filter_other_cover_u3_bug -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   z5_eq_slice_other_u3_bug        -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   z5_eq_slice_other_u6_safe       -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The trip bound of a modelled `Iterator::eq` bounded
//! every loop by the receiver's remaining length, but `iter_compare` calls
//! the other iterator's `next` once per element, and a `Filter`'s `next` is a
//! `find` loop of its own: a one-element receiver bounded the filter's loop
//! over five elements by 1 and discharged Kani's unwinding assertion. The
//! bound now applies only when the other operand iterates a slice or an
//! array of primitive items (`codegen_call_model_unwind.rs`).

#[kani::proof]
#[kani::unwind(3)]
fn z1_eq_filter_other_u3_bug() {
    let r = [1u32].iter().eq([1u32, 2, 3, 4, 5].iter().filter(|x| **x > 100));
    assert!(r || !r);
}

#[kani::proof]
#[kani::unwind(7)]
fn z1_eq_filter_other_u7_safe() {
    let r = [1u32].iter().eq([1u32, 2, 3, 4, 5].iter().filter(|x| **x > 100));
    assert!(!r);
}

#[kani::proof]
#[kani::unwind(3)]
fn z2_eq_skip_while_other_u3_bug() {
    let r = [1u32].iter().eq([1u32, 2, 3, 4, 5].iter().skip_while(|x| **x < 100));
    assert!(r || !r);
}

#[kani::proof]
#[kani::unwind(3)]
fn z3_ne_filter_other_u3_bug() {
    let r = [1u32].iter().ne([1u32, 2, 3, 4, 5].iter().filter(|x| **x > 100));
    assert!(r || !r);
}

#[kani::proof]
#[kani::unwind(3)]
fn z4_eq_filter_other_cover_u3_bug() {
    let r = [1u32].iter().eq([1u32, 2, 3, 4, 5].iter().filter(|x| **x > 100));
    kani::cover!(!r);
}

#[kani::proof]
#[kani::unwind(3)]
fn z5_eq_slice_other_u3_bug() {
    let a = [1u32, 2, 3, 4];
    let b = [1u32, 2, 3, 4];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
#[kani::unwind(6)]
fn z5_eq_slice_other_u6_safe() {
    let a = [1u32, 2, 3, 4];
    let b = [1u32, 2, 3, 4];
    assert!(a.iter().eq(b.iter()));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- the VALUE of `Iterator::eq` over two
//! slice iterators (found while landing fix/chc-walker-fail-closed on main
//! c67e38435, 2026-10-16; on main and on the branch alike).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-16):
//!   e1_u32_last_differs_bug  -> VERIFICATION:- FAILED  ('assertion failed')
//!   e1_u32_equal_safe        -> VERIFICATION:- SUCCESSFUL
//!   e2_u8_last_differs_bug   -> VERIFICATION:- FAILED  ('assertion failed')
//!   e3_u8_any_last_bug       -> VERIFICATION:- FAILED  ('assertion failed')
//!   e3_u8_any_last_safe      -> VERIFICATION:- SUCCESSFUL
//!   e4_u8_equal_ne_bug       -> VERIFICATION:- FAILED  ('assertion failed')
//!   e5_u8_lengths_differ_bug -> VERIFICATION:- FAILED  ('assertion failed')
//!
//! MECHANISM UNDER TEST. The CHC lane's `Iterator::eq` fast path
//! (`chc/call/inline_known_calls.rs`, `iterator_eq_condition`) answers from
//! the two iterators' STATES: their buffer pointers, lengths and positions.
//! Two slice iterators over different arrays of one length carry equal
//! pointer fields, so the fast path read them as one buffer and answered
//! `true` whatever the elements: `e1`, `e2` and `e3` verified clean where Kani
//! fails. Known red on the CHC lane; the BMC lane decides the value from the
//! elements.

#[kani::proof]
fn e1_u32_last_differs_bug() {
    let a = [1u32, 2, 3, 4];
    let b = [1u32, 2, 3, 5];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn e1_u32_equal_safe() {
    let a = [1u32, 2, 3, 4];
    let b = [1u32, 2, 3, 4];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn e2_u8_last_differs_bug() {
    let a = [1u8, 2];
    let b = [1u8, 3];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn e3_u8_any_last_bug() {
    let a = [1u8, 2];
    let b = [1u8, kani::any()];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn e3_u8_any_last_safe() {
    let a = [1u8, 2];
    let x: u8 = kani::any();
    kani::assume(x == 2);
    let b = [1u8, x];
    assert!(a.iter().eq(b.iter()));
}

#[kani::proof]
fn e4_u8_equal_ne_bug() {
    let a = [1u8, 2];
    let b = [1u8, 2];
    assert!(!a.iter().eq(b.iter()));
}

#[kani::proof]
fn e5_u8_lengths_differ_bug() {
    let a = [1u8, 2];
    let b = [1u8, 2, 3];
    assert!(a.iter().eq(b.iter()));
}

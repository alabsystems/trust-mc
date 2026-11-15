// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a by-value argument moved into an inlined call, assigned
//! earlier in the same block (decision REDS-REST). The moved-out local's dead
//! placeholder is stated slot by slot for a flattened local; it must not
//! contradict the block's own assignment of it, which would make the call's
//! rule vacuous and prove anything after it.
//!
//! Oracle: the native run, measured 2026-10-14 (each harness 4096 times with
//! `kani::any` as a xorshift source and `kani::assume` as a retry, built by
//! trustc with verification off): no safe_ row panics, every bug_ row panics
//! on some input.

#[kani::proof]
fn bug_range_from_five() {
    let n: u32 = kani::any();
    kani::assume(n > 5 && n < 9);
    let mut it = (5..n).into_iter();
    assert!(it.next() != Some(5));
}

#[kani::proof]
fn safe_range_from_five() {
    let n: u32 = kani::any();
    kani::assume(n > 5 && n < 9);
    let mut it = (5..n).into_iter();
    assert!(it.next() == Some(5));
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct P {
    a: u8,
    b: u16,
}

#[inline(never)]
fn take(p: P) -> u16 {
    p.b
}

#[kani::proof]
fn bug_struct_moved_into_call() {
    let b: u16 = kani::any();
    kani::assume(b > 3);
    let p = P { a: 7, b };
    let got = take(p);
    assert!(got != b);
}

#[kani::proof]
fn safe_struct_moved_into_call() {
    let b: u16 = kani::any();
    let p = P { a: 7, b };
    let got = take(p);
    assert!(got == b);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a callee that REBINDS its reference parameter
//! (`cur = next`) does not write the caller's referent (decision REDS-REST).
//! The CHC walker reported the rebinding as an alias update: with the
//! parameter held as an address, the caller's `Span` took a pointer's bits.
//! The caller's value after the call must be its value before it.
//!
//! Oracle: the native run, measured 2026-10-14 (each harness 4096 times with
//! `kani::any` as a xorshift source and `kani::assume` as a retry, built by
//! trustc with verification off): no safe_ row panics, every bug_ row panics
//! on some input.

#[derive(Clone, Copy)]
pub struct Span {
    lo: u8,
    hi: u8,
}

#[inline(never)]
fn moved_guard<'x>(mut cur: &'x Span, next: &'x Span, len: u8) -> u8 {
    cur = next;
    if cur.lo < cur.hi { len } else { len.wrapping_sub(1) }
}

pub trait Cursor {
    fn moved(&self, a: &Span, b: &Span, len: u8) -> u8;
}
pub struct CA;
pub struct CB;
impl Cursor for CA {
    fn moved(&self, a: &Span, b: &Span, len: u8) -> u8 {
        moved_guard(a, b, len)
    }
}
impl Cursor for CB {
    fn moved(&self, a: &Span, b: &Span, len: u8) -> u8 {
        moved_guard(a, b, len)
    }
}

#[kani::proof]
fn safe_head_unchanged_after_dyn_rebind() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn Cursor> = if kani::any() { Box::new(CA) } else { Box::new(CB) };
    let _ = o.moved(&head, &tail, 1);
    assert!(head.lo < head.hi);
}

#[kani::proof]
fn bug_head_unchanged_after_dyn_rebind() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn Cursor> = if kani::any() { Box::new(CA) } else { Box::new(CB) };
    let _ = o.moved(&head, &tail, 1);
    assert!(head.lo >= head.hi);
}

#[kani::proof]
fn safe_head_unchanged_after_direct_rebind() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let _ = moved_guard(&head, &tail, 1);
    assert!(head.lo < head.hi);
}

#[kani::proof]
fn bug_head_unchanged_after_direct_rebind() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let _ = moved_guard(&head, &tail, 1);
    assert!(head.lo >= head.hi);
}

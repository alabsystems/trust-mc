// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (regression tripwire) -- a comparison call inside a
//! dyn-dispatched method body whose `&T` arguments the CHC INLINE WALKER holds
//! as ADDRESSES, not as the values they point at.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_param2_lt_true      -> VERIFICATION:- FAILED  ('p.a < p.b')
//!   bug_param2_lt_false     -> VERIFICATION:- FAILED  ('p.a >= p.b')
//!   safe_param2_lt          -> VERIFICATION:- SUCCESSFUL
//!   bug_window_guard_dyn    -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_sub` which would overflow')
//!   safe_window_guard_dyn   -> VERIFICATION:- SUCCESSFUL
//!   bug_reads_reassigned    -> VERIFICATION:- FAILED  ('reads the reassigned pair')
//!   safe_reads_reassigned   -> VERIFICATION:- SUCCESSFUL
//!   bug_moved_guard         -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_sub` which would overflow')
//!   safe_moved_guard        -> VERIFICATION:- SUCCESSFUL
//!   bug_maybe_moved_guard   -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_sub` which would overflow')
//!   safe_maybe_moved_guard  -> VERIFICATION:- SUCCESSFUL
//!
//! WHAT IT GUARDS. A 2026-09-24 precision repair (`nested_call.rs`,
//! `comparison_arg_referent_value`, since removed) answered such a comparison
//! by reading the borrowed place back through the walker's place resolver. The
//! resolver does not return the referent there:
//! * for a NON-FIRST reference parameter (`r.a` with `r` the second argument)
//!   the self-field map has no entry, and `try_unflatten_bv_to_datatype` read
//!   the BV64 ADDRESS as the struct, so `r.a < r.b` compared pointer bits
//!   (always `0 < 0`): `bug_param2_lt_true` and `bug_window_guard_dyn` were
//!   SUCCESSFUL clean;
//! * after the FIRST parameter is reassigned (`r = other;`), the self-field
//!   snapshot taken at entry answered `r.a`: `bug_reads_reassigned` and
//!   `bug_moved_guard` were SUCCESSFUL clean.
//! Main refused the comparison ("comparison argument is not its referent's
//! value; not inlined") and left its result unconstrained, which is sound and
//! is again the behaviour. The safe rows record what that costs.
//!
//! KNOWN-RED (pre-existing, not fixed): `bug_maybe_moved_guard` reassigns the
//! first reference parameter only on one arm (`if let Some(n) = next { cur =
//! n; }`), then `cur.lo < cur.hi` guards `len.unchecked_sub(1)`. It is the
//! conditional twin of `bug_moved_guard`, and unlike it the walked body misses
//! the underflow; see the manifest row for the verdicts measured.
//!
//! Promoted from the 2026-09-24 adversarial review's probes a7_param2.rs,
//! a8_window_guard.rs, a2_reassign_first.rs and a5b_cursor_guard.rs (its
//! fail_moved_guard and fail_maybe_moved_guard); the safe_param2_lt /
//! safe_window_guard_dyn / safe_moved_guard / safe_maybe_moved_guard twins are
//! new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_referent_read_dual.rs

// --- a comparison on the walked body's SECOND parameter ---------------------

pub struct Pair {
    pub a: u8,
    pub b: u8,
}

#[inline(never)]
fn cmp_second(_x: u8, r: &Pair) -> bool {
    PartialOrd::lt(&r.a, &r.b)
}

pub trait Second {
    fn go(&self, x: u8, r: &Pair) -> bool;
}
pub struct SA;
pub struct SB;
impl Second for SA {
    fn go(&self, x: u8, r: &Pair) -> bool {
        cmp_second(x, r)
    }
}
impl Second for SB {
    fn go(&self, x: u8, r: &Pair) -> bool {
        cmp_second(x, r)
    }
}

// --- the same comparison as the guard of an unchecked subtraction -----------

pub struct Window<T> {
    pub start: T,
    pub end: T,
}

#[inline(never)]
fn shrink<T: PartialOrd>(len: u8, w: &Window<T>) -> u8 {
    if w.start < w.end {
        // UB when len == 0 and the window is non-empty.
        unsafe { len.unchecked_sub(1) }
    } else {
        len
    }
}

pub trait Shrink {
    fn go(&self, len: u8, w: &Window<u8>) -> u8;
}
pub struct WA;
pub struct WB;
impl Shrink for WA {
    fn go(&self, len: u8, w: &Window<u8>) -> u8 {
        shrink(len, w)
    }
}
impl Shrink for WB {
    fn go(&self, len: u8, w: &Window<u8>) -> u8 {
        shrink(len, w)
    }
}

// --- the FIRST parameter reassigned before the borrow -----------------------

pub struct GPair<T> {
    pub a: T,
    pub b: T,
}

#[inline(never)]
fn reassign_first<'x, T: PartialOrd>(mut r: &'x GPair<T>, other: &'x GPair<T>) -> bool {
    r = other;
    PartialOrd::lt(&r.a, &r.b)
}

pub trait Reassign {
    fn go(&self, p: &GPair<u8>, q: &GPair<u8>) -> bool;
}
pub struct RA;
pub struct RB;
impl Reassign for RA {
    fn go(&self, p: &GPair<u8>, q: &GPair<u8>) -> bool {
        reassign_first(p, q)
    }
}
impl Reassign for RB {
    fn go(&self, p: &GPair<u8>, q: &GPair<u8>) -> bool {
        reassign_first(p, q)
    }
}

// --- a cursor moved to another span, then its guard -------------------------

pub struct Span {
    pub lo: u8,
    pub hi: u8,
}

#[inline(never)]
fn moved_guard<'x>(mut cur: &'x Span, next: &'x Span, len: u8) -> u8 {
    cur = next;
    if PartialOrd::lt(&cur.lo, &cur.hi) {
        len
    } else {
        // UB when len == 0 and the current span is empty.
        unsafe { len.unchecked_sub(1) }
    }
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

// --- the cursor moved on ONE arm only, then its guard -----------------------

#[inline(never)]
fn maybe_moved_guard<'x>(mut cur: &'x Span, next: Option<&'x Span>, len: u8) -> u8 {
    if let Some(n) = next {
        cur = n;
    }
    if PartialOrd::lt(&cur.lo, &cur.hi) {
        len
    } else {
        // UB when len == 0 and the current span is empty.
        unsafe { len.unchecked_sub(1) }
    }
}

// A trait of its own, so the Cursor rows above keep their vtables.
pub trait MaybeCursor {
    fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8;
}
pub struct MCA;
pub struct MCB;
impl MaybeCursor for MCA {
    fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8 {
        maybe_moved_guard(a, b, len)
    }
}
impl MaybeCursor for MCB {
    fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8 {
        maybe_moved_guard(a, b, len)
    }
}

// The comparison reads p, and p.a < p.b holds.
#[kani::proof]
fn bug_param2_lt_true() {
    let p = Pair { a: kani::any(), b: kani::any() };
    kani::assume(p.a < p.b);
    let o: Box<dyn Second> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    assert!(!o.go(0, &p), "p.a < p.b");
}

#[kani::proof]
fn bug_param2_lt_false() {
    let p = Pair { a: kani::any(), b: kani::any() };
    kani::assume(p.a >= p.b);
    let o: Box<dyn Second> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    assert!(o.go(0, &p), "p.a >= p.b");
}

#[kani::proof]
fn safe_param2_lt() {
    let p = Pair { a: kani::any(), b: kani::any() };
    kani::assume(p.a < p.b);
    let o: Box<dyn Second> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    assert!(o.go(0, &p));
}

// The window is non-empty and len == 0, so 0 - 1 runs.
#[kani::proof]
fn bug_window_guard_dyn() {
    let w = Window { start: kani::any::<u8>(), end: kani::any::<u8>() };
    kani::assume(w.start < w.end);
    let o: Box<dyn Shrink> = if kani::any() { Box::new(WA) } else { Box::new(WB) };
    let _ = o.go(0, &w);
}

// len == 1: the subtraction cannot underflow whatever the window.
#[kani::proof]
fn safe_window_guard_dyn() {
    let w = Window { start: kani::any::<u8>(), end: kani::any::<u8>() };
    let o: Box<dyn Shrink> = if kani::any() { Box::new(WA) } else { Box::new(WB) };
    let _ = o.go(1, &w);
}

// The comparison reads q, and q.a >= q.b, so s is false.
#[kani::proof]
fn bug_reads_reassigned() {
    let p = GPair { a: kani::any::<u8>(), b: kani::any::<u8>() };
    let q = GPair { a: kani::any::<u8>(), b: kani::any::<u8>() };
    kani::assume(p.a < p.b);
    kani::assume(q.a >= q.b);
    let o: Box<dyn Reassign> = if kani::any() { Box::new(RA) } else { Box::new(RB) };
    let s = o.go(&p, &q);
    assert!(s, "reads the reassigned pair");
}

#[kani::proof]
fn safe_reads_reassigned() {
    let p = GPair { a: kani::any::<u8>(), b: kani::any::<u8>() };
    let q = GPair { a: kani::any::<u8>(), b: kani::any::<u8>() };
    kani::assume(p.a < p.b);
    kani::assume(q.a >= q.b);
    let o: Box<dyn Reassign> = if kani::any() { Box::new(RA) } else { Box::new(RB) };
    let s = o.go(&p, &q);
    assert!(!s);
}

// The current span is `tail`, which is empty, so 0 - 1 runs.
#[kani::proof]
fn bug_moved_guard() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn Cursor> = if kani::any() { Box::new(CA) } else { Box::new(CB) };
    let _ = o.moved(&head, &tail, 0);
}

// len == 1: the subtraction cannot underflow whichever span is current.
#[kani::proof]
fn safe_moved_guard() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn Cursor> = if kani::any() { Box::new(CA) } else { Box::new(CB) };
    let _ = o.moved(&head, &tail, 1);
}

// The cursor moves to `tail`, which is empty, so 0 - 1 runs.
#[kani::proof]
fn bug_maybe_moved_guard() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn MaybeCursor> = if kani::any() { Box::new(MCA) } else { Box::new(MCB) };
    let _ = o.maybe(&head, Some(&tail), 0);
}

// len == 1: the subtraction cannot underflow whichever span is current.
#[kani::proof]
fn safe_maybe_moved_guard() {
    let head = Span { lo: kani::any(), hi: kani::any() };
    let tail = Span { lo: kani::any(), hi: kani::any() };
    kani::assume(head.lo < head.hi);
    kani::assume(tail.lo >= tail.hi);
    let o: Box<dyn MaybeCursor> = if kani::any() { Box::new(MCA) } else { Box::new(MCB) };
    let _ = o.maybe(&head, Some(&tail), 1);
}

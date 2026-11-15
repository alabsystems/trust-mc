// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a two-variant enum whose payload variant comes FIRST
//! (`core::task::Poll`, `enum P { A(u8), B }`, `enum Rev { Has(Box<u16>), Empty }`)
//! read back whole after it was stored (review of fix/chc-lost-writes, lostwrite
//! track round 2, findings 1 and 5). The CHC datatype of an Option-like enum listed
//! its empty constructor first whatever the variant order, while the flattened
//! locals and every positional reader take a constructor's position for its variant
//! index; reading a flattened `Poll::Ready` whole (into a `Vec`, a tuple, a struct
//! field, a transmute to its bits) gave `Pending`. On main every bug row below was
//! missed and every safe row certified Genuine. The datatype now lists the
//! constructors in variant order.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_poll_vec            -> SUCCESSFUL
//!   bug_poll_vec             -> FAILED ('assertion failed: v[0].is_ready()')
//!   safe_poll_in_tuple       -> SUCCESSFUL
//!   bug_poll_in_tuple        -> FAILED ('assertion failed: h.1.is_ready()')
//!   safe_p_vec               -> SUCCESSFUL
//!   bug_p_vec                -> FAILED ('assertion failed: matches!(v[0], P::A(_))')
//!   safe_p_in_struct         -> SUCCESSFUL
//!   bug_p_in_struct          -> FAILED ('assertion failed: matches!(h.r, P::A(_))')
//!   safe_rev_vec             -> SUCCESSFUL
//!   bug_rev_vec              -> FAILED ('assertion failed: matches!(v[0], Rev::Has(_))')
//!   safe_rev_in_struct       -> SUCCESSFUL
//!   bug_rev_in_struct        -> FAILED ('assertion failed: matches!(h.r, Rev::Has(_))')
//!   safe_rev_ptr_cast_back   -> SUCCESSFUL
//!   bug_rev_ptr_cast_back    -> FAILED ('assertion failed: !p.is_null()')
//!   safe_rev_option_wrap     -> SUCCESSFUL
//!   bug_rev_option_wrap      -> FAILED ('empty')
//!
#![allow(unused)]
use std::task::Poll;

enum P {
    A(u8),
    B,
}

struct HolderP {
    tag: u8,
    r: P,
}

enum Rev {
    Has(Box<u16>),
    Empty,
}

struct HolderRev {
    tag: u8,
    r: Rev,
}

#[inline(never)]
fn mkp(c: bool) -> P {
    if c { P::A(7) } else { P::B }
}

#[inline(never)]
fn mkpoll(c: bool) -> Poll<u8> {
    if c { Poll::Ready(7) } else { Poll::Pending }
}

#[inline(never)]
fn mkrev(c: bool) -> Rev {
    if c { Rev::Has(Box::new(7)) } else { Rev::Empty }
}

#[kani::proof]
fn safe_poll_vec() {
    let c: bool = kani::any();
    let v = vec![mkpoll(c)];
    assert!(v[0].is_ready() == c);
}

#[kani::proof]
fn bug_poll_vec() {
    let v = vec![mkpoll(false)];
    assert!(v[0].is_ready());
}

#[kani::proof]
fn safe_poll_in_tuple() {
    let c: bool = kani::any();
    let h = (1u8, mkpoll(c));
    assert!(h.1.is_ready() == c);
}

#[kani::proof]
fn bug_poll_in_tuple() {
    let h = (1u8, mkpoll(false));
    assert!(h.1.is_ready());
}

#[kani::proof]
fn safe_p_vec() {
    let c: bool = kani::any();
    let v = vec![mkp(c)];
    assert!(matches!(v[0], P::A(_)) == c);
}

#[kani::proof]
fn bug_p_vec() {
    let v = vec![mkp(false)];
    assert!(matches!(v[0], P::A(_)));
}

#[kani::proof]
fn safe_p_in_struct() {
    let c: bool = kani::any();
    let h = HolderP { tag: 1, r: mkp(c) };
    assert!(matches!(h.r, P::A(_)) == c);
}

#[kani::proof]
fn bug_p_in_struct() {
    let h = HolderP { tag: 1, r: mkp(false) };
    assert!(matches!(h.r, P::A(_)));
}

#[kani::proof]
fn safe_rev_vec() {
    let c: bool = kani::any();
    let v = vec![mkrev(c)];
    assert!(matches!(v[0], Rev::Has(_)) == c);
}

#[kani::proof]
fn bug_rev_vec() {
    let v = vec![mkrev(false)];
    assert!(matches!(v[0], Rev::Has(_)));
}

#[kani::proof]
fn safe_rev_in_struct() {
    let c: bool = kani::any();
    let h = HolderRev { tag: 1, r: mkrev(c) };
    assert!(matches!(h.r, Rev::Has(_)) == c);
}

#[kani::proof]
fn bug_rev_in_struct() {
    let h = HolderRev { tag: 1, r: mkrev(false) };
    assert!(matches!(h.r, Rev::Has(_)));
}

#[kani::proof]
fn safe_rev_ptr_cast_back() {
    let r = mkrev(true);
    let p: *const u16 = unsafe { std::mem::transmute::<Rev, *const u16>(r) };
    assert!(!p.is_null());
}

#[kani::proof]
fn bug_rev_ptr_cast_back() {
    let r = mkrev(false);
    let p: *const u16 = unsafe { std::mem::transmute::<Rev, *const u16>(r) };
    assert!(!p.is_null());
}

#[kani::proof]
fn safe_rev_option_wrap() {
    let c: bool = kani::any();
    let o = Some(mkrev(c));
    match o {
        Some(Rev::Has(b)) => assert!(c && *b == 7),
        Some(Rev::Empty) => assert!(!c),
        None => panic!("none"),
    }
}

#[kani::proof]
fn bug_rev_option_wrap() {
    let o = Some(mkrev(false));
    match o {
        Some(Rev::Has(_)) => {}
        Some(Rev::Empty) => panic!("empty"),
        None => {}
    }
}

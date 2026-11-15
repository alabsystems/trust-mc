// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a user type named like a std adapter
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 7, `k6`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   k1_chain_first_value_bug  -> VERIFICATION:- FAILED  ('assertion failed: it.next() == Some(6)')
//!   k1_chain_first_value_safe -> VERIFICATION:- SUCCESSFUL
//!   k2_chain_unwrap_safe      -> VERIFICATION:- SUCCESSFUL
//!   k3_chain_second_none_bug  -> VERIFICATION:- FAILED  ('assertion failed: it.next().is_some()')
//!   k3_chain_second_none_safe -> VERIFICATION:- SUCCESSFUL
//!   k4_map_second_none_bug    -> VERIFICATION:- FAILED  ('assertion failed: it.next().is_some()')
//!   k4_map_first_value_safe   -> VERIFICATION:- SUCCESSFUL
//!   p1_plain_control_bug      -> VERIFICATION:- FAILED  ('assertion failed: it.next().is_some()')
//!   p1_plain_control_safe     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The stub registry matches std's methods by the text
//! of the callee's path: `<Chain<u8> as Iterator>::next` contains `Chain<` and
//! `next`, so a user `Chain<T>` that yields one element was read as std's
//! chain adapter. `it.next() == Some(5)` was certified a Genuine failure and a
//! second `next()` that returns `None` verified as `Some`. A callee that
//! resolves into the local crate is never a std stub; it is walked as its
//! code (`shared::callee_is_local_item`, both lanes, and the CHC walker's
//! path-text fast paths). `Plain` is the same type under another name.

pub struct Chain<T> {
    v: T,
    n: u8,
}

impl<T: Copy> Iterator for Chain<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.n > 0 {
            self.n -= 1;
            Some(self.v)
        } else {
            None
        }
    }
}

pub struct Plain<T> {
    v: T,
    n: u8,
}

impl<T: Copy> Iterator for Plain<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.n > 0 {
            self.n -= 1;
            Some(self.v)
        } else {
            None
        }
    }
}

pub struct Map<T> {
    v: T,
    n: u8,
}

impl<T: Copy> Iterator for Map<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.n > 0 {
            self.n -= 1;
            Some(self.v)
        } else {
            None
        }
    }
}

#[kani::proof]
fn k1_chain_first_value_bug() {
    let mut it = Chain { v: 5u8, n: 1 };
    assert!(it.next() == Some(6));
}

#[kani::proof]
fn k1_chain_first_value_safe() {
    let mut it = Chain { v: 5u8, n: 1 };
    assert!(it.next() == Some(5));
}

#[kani::proof]
fn k2_chain_unwrap_safe() {
    let mut it = Chain { v: 5u8, n: 1 };
    let x = it.next();
    assert!(x.unwrap() == 5);
}

#[kani::proof]
fn k3_chain_second_none_bug() {
    let mut it = Chain { v: 5u8, n: 1 };
    let _ = it.next();
    assert!(it.next().is_some());
}

#[kani::proof]
fn k3_chain_second_none_safe() {
    let mut it = Chain { v: 5u8, n: 1 };
    let _ = it.next();
    assert!(it.next().is_none());
}

#[kani::proof]
fn k4_map_second_none_bug() {
    let mut it = Map { v: 7u8, n: 1 };
    let _ = it.next();
    assert!(it.next().is_some());
}

#[kani::proof]
fn k4_map_first_value_safe() {
    let mut it = Map { v: 7u8, n: 1 };
    assert!(it.next() == Some(7));
}

#[kani::proof]
fn p1_plain_control_bug() {
    let mut it = Plain { v: 5u8, n: 1 };
    let _ = it.next();
    assert!(it.next().is_some());
}

#[kani::proof]
fn p1_plain_control_safe() {
    let mut it = Plain { v: 5u8, n: 1 };
    assert!(it.next() == Some(5));
}

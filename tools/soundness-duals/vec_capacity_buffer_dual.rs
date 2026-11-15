// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a read through the buffer pointer of a `Vec::with_capacity`
//! `Vec` (review of fix/chc-lost-writes, lostwrite track round 2, finding 5 and its
//! class). The constructor binds the buffer to a heap object and records its byte
//! size, the CAPACITY's; the `Vec` stubs keep the contents in the `Vec`'s own model
//! and neither write the buffer's memory nor move the pointer when a `push` grows
//! the `Vec`. A read within the new length then failed the stale bound, and a read
//! of a pushed element read a free cell; both were certified Genuine on programs
//! Kani proves (main, and the branch through round 1). A read past the capacity of
//! a `Vec` nothing changes was a missed bug on main. Where the `Vec` may change
//! (a mutable borrow or a move of it), the recorded bound is checked under a freed
//! variable and a read of the buffer is a free cell, accounted: proofs are
//! unchanged and no counterexample through them is certified.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_grown_by_push_read_last              -> SUCCESSFUL
//!   bug_grown_read_past_len                   -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_within_capacity_read_pushed          -> SUCCESSFUL
//!   bug_within_capacity_read_wrong_value      -> FAILED ('assertion failed: x == 7')
//!   safe_reserve_then_read                    -> SUCCESSFUL
//!   bug_unchanged_read_past_capacity          -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_unchanged_pointer_not_null           -> SUCCESSFUL
//!
#![allow(unused)]

#[kani::proof]
fn safe_grown_by_push_read_last() {
    let mut v: Vec<u8> = Vec::with_capacity(1);
    v.push(1);
    v.push(2);
    v.push(3);
    let p = v.as_ptr();
    let x = unsafe { *p.add(2) };
    assert!(x == 3);
}

#[kani::proof]
fn bug_grown_read_past_len() {
    let mut v: Vec<u8> = Vec::with_capacity(1);
    v.push(1);
    v.push(2);
    let p = v.as_ptr();
    let x = unsafe { *p.wrapping_add(64) };
    assert!(x == x);
}

#[kani::proof]
fn safe_within_capacity_read_pushed() {
    let mut v: Vec<u8> = Vec::with_capacity(4);
    v.push(7);
    v.push(8);
    let p = v.as_ptr();
    let x = unsafe { *p.add(1) };
    assert!(x == 8);
}

#[kani::proof]
fn bug_within_capacity_read_wrong_value() {
    let mut v: Vec<u8> = Vec::with_capacity(4);
    v.push(7);
    v.push(8);
    let p = v.as_ptr();
    let x = unsafe { *p.add(1) };
    assert!(x == 7);
}

#[kani::proof]
fn safe_reserve_then_read() {
    let mut v: Vec<u16> = Vec::with_capacity(1);
    v.push(5);
    v.reserve(8);
    v.push(6);
    v.push(9);
    let p = v.as_ptr();
    assert!(unsafe { *p.add(2) } == 9);
}

#[kani::proof]
fn bug_unchanged_read_past_capacity() {
    let v: Vec<u8> = Vec::with_capacity(2);
    let p = v.as_ptr();
    let x = unsafe { *p.wrapping_add(5) };
    assert!(x == x);
}

#[kani::proof]
fn safe_unchanged_pointer_not_null() {
    let v: Vec<u8> = Vec::with_capacity(2);
    let p = v.as_ptr();
    assert!(!p.is_null());
}

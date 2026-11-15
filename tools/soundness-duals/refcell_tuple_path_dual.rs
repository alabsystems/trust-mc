// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- C5b (design trust-mc-reds-final §4.2): a field path into
//! a `RefCell<(u8, u8)>` held by a struct, projected by an inlined std method
//! (`.value` then the tuple's `.1`). The flat-slot walk follows MIR field
//! indices over a sort tree that collapses wrappers by name, and the heap
//! model collapses even `RefCell`, which is not layout-transparent: a path
//! through it could land on the wrong lane.
//!
//! Oracle: the native run, measured 2026-10-14 (each harness 4096 times with
//! `kani::any` as a xorshift u8 source, built by trustc with verification
//! off): no safe_ row panics, every bug_ row panics on some input.

use std::cell::RefCell;

struct S {
    tag: u8,
    cell: RefCell<(u8, u8)>,
}

fn mk(a: u8, b: u8) -> S {
    S { tag: 1, cell: RefCell::new((a, b)) }
}

#[kani::proof]
fn safe_get_mut_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let mut s = mk(a, b);
    s.cell.get_mut().1 = 7;
    assert!(s.cell.get_mut().1 == 7);
    assert!(s.cell.get_mut().0 == a);
    assert!(s.tag == 1);
}

#[kani::proof]
fn bug_get_mut_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let mut s = mk(a, b);
    s.cell.get_mut().1 = 7;
    assert!(s.cell.get_mut().0 == 7);
}

#[kani::proof]
fn safe_into_inner_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    let t = s.cell.into_inner();
    assert!(t.1 == b);
    assert!(t.0 == a);
}

#[kani::proof]
fn bug_into_inner_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    let t = s.cell.into_inner();
    assert!(t.1 == a);
}

#[kani::proof]
fn safe_borrow_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    assert!(s.cell.borrow().1 == b);
}

#[kani::proof]
fn bug_borrow_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    assert!(s.cell.borrow().1 == a);
}

#[kani::proof]
fn safe_borrow_mut_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    s.cell.borrow_mut().1 = 9;
    assert!(s.cell.borrow().1 == 9);
    assert!(s.cell.borrow().0 == a);
}

#[kani::proof]
fn bug_borrow_mut_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    s.cell.borrow_mut().1 = 9;
    assert!(s.cell.borrow().0 == 9);
}

#[kani::proof]
fn safe_replace_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    let old = s.cell.replace((3, 4));
    assert!(old.1 == b);
    assert!(s.cell.borrow().1 == 4);
}

#[kani::proof]
fn bug_replace_second() {
    let (a, b): (u8, u8) = (kani::any(), kani::any());
    let s = mk(a, b);
    let old = s.cell.replace((3, 4));
    assert!(old.1 == 4);
}

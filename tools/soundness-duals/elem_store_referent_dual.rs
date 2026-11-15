// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- an element store `(*q)[i] = v` through a pointer to a `static mut` the encoder
//! does not tie to the static's state variable (a static holding the pointer, a struct field, an
//! Option payload, a Box, a symbolic index, a helper returning a reference), and the stack and Box
//! twins through helpers (review of fix/chc-lost-writes, lostwrite round 1, finding 1). The element
//! lane wrote typed memory only and returned before the generic unresolved-referent guard; it now
//! records deref_store_referent_unresolved unless the address names a heap allocation.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_static_via_fn_ref             -> SUCCESSFUL
//!   bug_static_via_fn_ref              -> FAILED ('assertion failed: unsafe { A2[1] } == 2')
//!   safe_static_via_static_ptr         -> SUCCESSFUL
//!   bug_static_via_static_ptr          -> FAILED ('assertion failed: B2[1] == 2')
//!   safe_static_via_struct_field       -> SUCCESSFUL
//!   bug_static_via_struct_field        -> FAILED ('assertion failed: unsafe { C2[1] } == 2')
//!   safe_static_via_option             -> SUCCESSFUL
//!   bug_static_via_option              -> FAILED ('assertion failed: unsafe { D2[1] } == 2')
//!   safe_static_sym_index_laundered    -> SUCCESSFUL
//!   bug_static_sym_index_laundered     -> FAILED ('assertion failed: unsafe { E2[i] } != 5')
//!   safe_stack_via_raw_helper          -> SUCCESSFUL
//!   bug_stack_via_raw_helper           -> FAILED ('assertion failed: a[1] == 2')
//!   safe_stack_via_struct_helper       -> SUCCESSFUL
//!   bug_stack_via_struct_helper        -> FAILED ('assertion failed: a[1] == 2')
//!   safe_stack_via_boxed_struct_helper -> SUCCESSFUL
//!   bug_stack_via_boxed_struct_helper  -> FAILED ('assertion failed: a[1] == 2')
//!   safe_box_payload_via_raw_helper    -> SUCCESSFUL
//!   bug_box_payload_via_raw_helper     -> FAILED ('assertion failed: b[1] == 2')
//!
#![allow(unused)]
use std::ptr::{addr_of_mut, null_mut};

static mut A1: [u16; 2] = [1, 2];
#[inline(never)]
fn get_a1() -> &'static mut [u16; 2] {
    unsafe { &mut *addr_of_mut!(A1) }
}
#[kani::proof]
fn safe_static_via_fn_ref() {
    let r = get_a1();
    r[1] = 5;
    assert!(unsafe { A1[1] } == 5);
}
static mut A2: [u16; 2] = [1, 2];
#[inline(never)]
fn get_a2() -> &'static mut [u16; 2] {
    unsafe { &mut *addr_of_mut!(A2) }
}
#[kani::proof]
fn bug_static_via_fn_ref() {
    let r = get_a2();
    r[1] = 5;
    assert!(unsafe { A2[1] } == 2);
}
static mut B1: [u16; 2] = [1, 2];
static mut PB1: *mut [u16; 2] = unsafe { addr_of_mut!(B1) };
#[kani::proof]
fn safe_static_via_static_ptr() {
    unsafe {
        (*PB1)[1] = 5;
        assert!(B1[1] == 5);
    }
}
static mut B2: [u16; 2] = [1, 2];
static mut PB2: *mut [u16; 2] = unsafe { addr_of_mut!(B2) };
#[kani::proof]
fn bug_static_via_static_ptr() {
    unsafe {
        (*PB2)[1] = 5;
        assert!(B2[1] == 2);
    }
}
struct H {
    r: &'static mut [u16; 2],
}
static mut C1: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_via_struct_field() {
    let h = H { r: unsafe { &mut *addr_of_mut!(C1) } };
    let b = Box::new(h);
    b.r[1] = 5;
    drop(b);
    assert!(unsafe { C1[1] } == 5);
}
static mut C2: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_via_struct_field() {
    let h = H { r: unsafe { &mut *addr_of_mut!(C2) } };
    let b = Box::new(h);
    b.r[1] = 5;
    drop(b);
    assert!(unsafe { C2[1] } == 2);
}
static mut D1: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_via_option() {
    let o: Option<&'static mut [u16; 2]> = Some(unsafe { &mut *addr_of_mut!(D1) });
    let b = Box::new(o);
    if let Some(r) = *b {
        r[1] = 5;
    }
    assert!(unsafe { D1[1] } == 5);
}
static mut D2: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_via_option() {
    let o: Option<&'static mut [u16; 2]> = Some(unsafe { &mut *addr_of_mut!(D2) });
    let b = Box::new(o);
    if let Some(r) = *b {
        r[1] = 5;
    }
    assert!(unsafe { D2[1] } == 2);
}
static mut E1: [u16; 2] = [1, 2];
#[kani::proof]
fn safe_static_sym_index_laundered() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let q = *Box::new(unsafe { addr_of_mut!(E1) });
    unsafe { (*q)[i] = 5 };
    assert!(unsafe { E1[i] } == 5);
}
static mut E2: [u16; 2] = [1, 2];
#[kani::proof]
fn bug_static_sym_index_laundered() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let q = *Box::new(unsafe { addr_of_mut!(E2) });
    unsafe { (*q)[i] = 5 };
    assert!(unsafe { E2[i] } != 5);
}
#[inline(never)]
fn set_raw(p: *mut [u16; 2]) {
    unsafe { (*p)[1] = 7 };
}
#[kani::proof]
fn safe_stack_via_raw_helper() {
    let mut a: [u16; 2] = [1, 2];
    set_raw(addr_of_mut!(a));
    assert!(a[1] == 7);
}
#[kani::proof]
fn bug_stack_via_raw_helper() {
    let mut a: [u16; 2] = [1, 2];
    set_raw(addr_of_mut!(a));
    assert!(a[1] == 2);
}
struct HP {
    p: *mut [u16; 2],
}
#[inline(never)]
fn set_hp(h: &HP) {
    unsafe { (*h.p)[1] = 7 };
}
#[kani::proof]
fn safe_stack_via_struct_helper() {
    let mut a: [u16; 2] = [1, 2];
    let h = HP { p: addr_of_mut!(a) };
    set_hp(&h);
    assert!(a[1] == 7);
}
#[kani::proof]
fn bug_stack_via_struct_helper() {
    let mut a: [u16; 2] = [1, 2];
    let h = HP { p: addr_of_mut!(a) };
    set_hp(&h);
    assert!(a[1] == 2);
}
#[kani::proof]
fn safe_stack_via_boxed_struct_helper() {
    let mut a: [u16; 2] = [1, 2];
    let h = Box::new(HP { p: addr_of_mut!(a) });
    set_hp(&h);
    assert!(a[1] == 7);
}
#[kani::proof]
fn bug_stack_via_boxed_struct_helper() {
    let mut a: [u16; 2] = [1, 2];
    let h = Box::new(HP { p: addr_of_mut!(a) });
    set_hp(&h);
    assert!(a[1] == 2);
}
#[kani::proof]
fn safe_box_payload_via_raw_helper() {
    let mut b: Box<[u16; 2]> = Box::new([1, 2]);
    set_raw(addr_of_mut!(*b));
    assert!(b[1] == 7);
}
#[kani::proof]
fn bug_box_payload_via_raw_helper() {
    let mut b: Box<[u16; 2]> = Box::new([1, 2]);
    set_raw(addr_of_mut!(*b));
    assert!(b[1] == 2);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_struct_copied_then_field  -> VERIFICATION:- SUCCESSFUL
//   bug_struct_copied_then_field   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_nested_struct_field       -> VERIFICATION:- SUCCESSFUL
//   bug_nested_struct_field        -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_option_held_read          -> VERIFICATION:- SUCCESSFUL
//   bug_option_held_read           -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_cell_held_read            -> VERIFICATION:- SUCCESSFUL
//   bug_cell_held_read             -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_cell_reset_read           -> VERIFICATION:- SUCCESSFUL
//   bug_cell_reset_read            -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_ptr_held_read      -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ptr_held_read       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_box_held_read             -> VERIFICATION:- SUCCESSFUL
//   bug_box_held_read              -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_ref_to_struct_field       -> VERIFICATION:- SUCCESSFUL
//   bug_ref_to_struct_field        -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_from_ptr_atomic_load      -> VERIFICATION:- SUCCESSFUL
//   bug_from_ptr_atomic_load       -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_array_of_struct_held      -> VERIFICATION:- SUCCESSFUL
//   bug_array_of_struct_held       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_closure_captured_ptr      -> VERIFICATION:- SUCCESSFUL
//   bug_closure_captured_ptr       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//
// More holders of a pointer into a static, reached from a constant pointer,
// and an access one past the static through it (round-3 review of
// fix/chc-atomic-as-ptr-live, beside const_pointer_live_held_dual.rs): a
// struct copied whole, a nested struct, a field read through a shared
// reference to the struct, an Option, a Cell (set or not), an AtomicPtr, a
// Box, an array of structs, a closure capture, and an atomic made by
// from_ptr. The global-object lane walks the shapes whose holder nothing can
// write (a field of a struct built once, a shared borrow of a Freeze local,
// from_ptr); the others are bounded or fail closed in their own lanes.
#![allow(dead_code, static_mut_refs)]
use std::cell::Cell;
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

static V: u32 = 7;
static ARR: [u32; 2] = [1, 2];
static A: AtomicU32 = AtomicU32::new(5);
static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];

#[derive(Clone, Copy)]
struct H {
    p: *const u32,
}
struct HH {
    h: H,
    pad: u8,
}

#[kani::proof]
fn safe_struct_copied_then_field() {
    let h = H { p: &ARR[0] };
    let h2 = h;
    assert!(unsafe { *h2.p.add(1) } == 2);
}
#[kani::proof]
fn bug_struct_copied_then_field() {
    let h = H { p: &V };
    let h2 = h;
    let v = unsafe { *h2.p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_nested_struct_field() {
    let hh = HH { h: H { p: &ARR[0] }, pad: 0 };
    assert!(unsafe { *hh.h.p.add(1) } == 2);
}
#[kani::proof]
fn bug_nested_struct_field() {
    let hh = HH { h: H { p: &V }, pad: 0 };
    let v = unsafe { *hh.h.p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_option_held_read() {
    let o: Option<*const u32> = Some(&ARR[0]);
    if let Some(q) = o {
        assert!(unsafe { *q.add(1) } == 2);
    }
}
#[kani::proof]
fn bug_option_held_read() {
    let o: Option<*const u32> = Some(&V);
    if let Some(q) = o {
        let v = unsafe { *q.add(1) };
        assert!(v == v);
    }
}
#[kani::proof]
fn safe_cell_held_read() {
    let c = Cell::new(&ARR[0] as *const u32);
    assert!(unsafe { *c.get().add(1) } == 2);
}
#[kani::proof]
fn bug_cell_held_read() {
    let c = Cell::new(&V as *const u32);
    let v = unsafe { *c.get().add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_cell_reset_read() {
    let c = Cell::new(&V as *const u32);
    c.set(&ARR[0]);
    assert!(unsafe { *c.get().add(1) } == 2);
}
#[kani::proof]
fn bug_cell_reset_read() {
    let c = Cell::new(&ARR[0] as *const u32);
    c.set(&V);
    let v = unsafe { *c.get().add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_ptr_held_read() {
    let ap = AtomicPtr::new(&ARR[0] as *const u32 as *mut u32);
    let q = ap.load(Ordering::SeqCst);
    assert!(unsafe { *q.add(1) } == 2);
}
#[kani::proof]
fn bug_atomic_ptr_held_read() {
    let ap = AtomicPtr::new(&V as *const u32 as *mut u32);
    let q = ap.load(Ordering::SeqCst);
    let v = unsafe { *q.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_box_held_read() {
    let b = Box::new(&ARR[0] as *const u32);
    assert!(unsafe { *(*b).add(1) } == 2);
}
#[kani::proof]
fn bug_box_held_read() {
    let b = Box::new(&V as *const u32);
    let v = unsafe { *(*b).add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_ref_to_struct_field() {
    let h = H { p: &ARR[0] };
    let r = &h;
    assert!(unsafe { *r.p.add(1) } == 2);
}
#[kani::proof]
fn bug_ref_to_struct_field() {
    let h = H { p: &V };
    let r = &h;
    let v = unsafe { *r.p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_from_ptr_atomic_load() {
    let a = unsafe { AtomicU32::from_ptr((&AP[0] as *const AtomicU32 as *mut u32).add(1)) };
    assert!(a.load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn bug_from_ptr_atomic_load() {
    let a = unsafe { AtomicU32::from_ptr((&A as *const AtomicU32 as *mut u32).add(1)) };
    let v = a.load(Ordering::SeqCst);
    assert!(v == v);
}
#[kani::proof]
fn safe_array_of_struct_held() {
    let hs = [H { p: &ARR[0] }];
    assert!(unsafe { *hs[0].p.add(1) } == 2);
}
#[kani::proof]
fn bug_array_of_struct_held() {
    let hs = [H { p: &V }];
    let v = unsafe { *hs[0].p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_closure_captured_ptr() {
    let p: *const u32 = &ARR[0];
    let f = move || unsafe { *p.add(1) };
    assert!(f() == 2);
}
#[kani::proof]
fn bug_closure_captured_ptr() {
    let p: *const u32 = &V;
    let f = move || unsafe { *p.add(1) };
    let v = f();
    assert!(v == v);
}

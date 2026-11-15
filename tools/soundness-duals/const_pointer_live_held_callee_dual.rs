// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_field_reborrow_callee_read        -> VERIFICATION:- SUCCESSFUL
//   bug_field_reborrow_callee_read         -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_elem_reborrow_callee_read         -> VERIFICATION:- SUCCESSFUL
//   bug_elem_reborrow_callee_read          -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_elem_reborrow_callee_load  -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_elem_reborrow_callee_load   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_mut_field_reborrow_callee_write   -> VERIFICATION:- SUCCESSFUL
//   bug_mut_field_reborrow_callee_write    -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_field_addr_callee_read            -> VERIFICATION:- SUCCESSFUL
//   bug_field_addr_callee_read             -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_whole_reborrow_callee_read        -> VERIFICATION:- SUCCESSFUL
//   bug_whole_reborrow_callee_read         -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//
// A reborrow or a place address past a static, made from a pointer reached
// from a constant pointer, and used ONLY inside a callee (round-3 review of
// fix/chc-atomic-as-ptr-live, beside const_pointer_live_held_dual.rs). Kani
// checks a projected reborrow `&(*p).b` / `&(*p)[1]` where the reference is
// used, not where it is made, so the CHC lane bounds it at its uses too;
// these rows are the uses a callee makes: a read, a write, an atomic load and
// a raw read, beside a whole reborrow `&*p.add(1)`, which Kani checks on
// creation.
#![allow(dead_code, static_mut_refs)]
use std::sync::atomic::{AtomicU32, Ordering};

static V: u32 = 7;
static ARR: [u32; 2] = [1, 2];
static A: AtomicU32 = AtomicU32::new(5);
static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static mut MV: u32 = 7;
static mut MARR: [u32; 2] = [1, 2];

#[repr(C)]
struct S2 {
    a: u32,
    b: u32,
}

#[inline(never)]
fn rd(r: &u32) -> u32 {
    *r
}
#[inline(never)]
fn wr(r: &mut u32) {
    *r = 9;
}
#[inline(never)]
fn ld(a: &AtomicU32) -> u32 {
    a.load(Ordering::SeqCst)
}
#[inline(never)]
fn rdp(p: *const u32) -> u32 {
    unsafe { *p }
}

#[kani::proof]
fn safe_field_reborrow_callee_read() {
    let p = &ARR as *const [u32; 2] as *const S2;
    let r = unsafe { &(*p).b };
    assert!(rd(r) == 2);
}
#[kani::proof]
fn bug_field_reborrow_callee_read() {
    let p = &V as *const u32 as *const S2;
    let r = unsafe { &(*p).b };
    let v = rd(r);
    assert!(v == v);
}
#[kani::proof]
fn safe_elem_reborrow_callee_read() {
    let p = &ARR[0] as *const u32 as *const [u32; 2];
    let r = unsafe { &(*p)[1] };
    assert!(rd(r) == 2);
}
#[kani::proof]
fn bug_elem_reborrow_callee_read() {
    let p = &V as *const u32 as *const [u32; 2];
    let r = unsafe { &(*p)[1] };
    let v = rd(r);
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_elem_reborrow_callee_load() {
    let p = &AP[0] as *const AtomicU32 as *const [AtomicU32; 2];
    let r = unsafe { &(*p)[1] };
    assert!(ld(r) == 2);
}
#[kani::proof]
fn bug_atomic_elem_reborrow_callee_load() {
    let p = &A as *const AtomicU32 as *const [AtomicU32; 2];
    let r = unsafe { &(*p)[1] };
    let v = ld(r);
    assert!(v == v);
}
#[kani::proof]
fn safe_mut_field_reborrow_callee_write() {
    let p = unsafe { std::ptr::addr_of_mut!(MARR) } as *mut S2;
    let r = unsafe { &mut (*p).b };
    wr(r);
    assert!(unsafe { MARR[1] } == 9);
}
#[kani::proof]
fn bug_mut_field_reborrow_callee_write() {
    let p = unsafe { std::ptr::addr_of_mut!(MV) } as *mut S2;
    let r = unsafe { &mut (*p).b };
    wr(r);
}
#[kani::proof]
fn safe_field_addr_callee_read() {
    let p = &ARR as *const [u32; 2] as *const S2;
    let q = unsafe { std::ptr::addr_of!((*p).b) };
    assert!(rdp(q) == 2);
}
#[kani::proof]
fn bug_field_addr_callee_read() {
    let p = &V as *const u32 as *const S2;
    let q = unsafe { std::ptr::addr_of!((*p).b) };
    let v = rdp(q);
    assert!(v == v);
}
#[kani::proof]
fn safe_whole_reborrow_callee_read() {
    let p: *const u32 = &ARR[0];
    let r = unsafe { &*p.add(1) };
    assert!(rd(r) == 2);
}
#[kani::proof]
fn bug_whole_reborrow_callee_read() {
    let p: *const u32 = &V;
    let r = unsafe { &*p.add(1) };
    let v = rd(r);
    assert!(v == v);
}

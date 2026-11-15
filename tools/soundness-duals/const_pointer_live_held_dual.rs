// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_struct_held_add1_read               -> VERIFICATION:- SUCCESSFUL
//   bug_struct_held_add1_read                -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_struct_field_copy_then_add          -> VERIFICATION:- SUCCESSFUL
//   bug_struct_field_copy_then_add           -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_struct_held_moved_read              -> VERIFICATION:- SUCCESSFUL
//   bug_struct_held_moved_read               -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_tuple_held_add1_read                -> VERIFICATION:- SUCCESSFUL
//   bug_tuple_held_add1_read                 -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_struct_reassigned_field_read        -> VERIFICATION:- SUCCESSFUL
//   bug_struct_reassigned_field_read         -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_struct_held_atomic_load             -> VERIFICATION:- SUCCESSFUL
//   bug_struct_held_atomic_load              -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_struct_held_atomic_store            -> VERIFICATION:- SUCCESSFUL
//   bug_struct_held_atomic_store             -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_tuple_atomic_ptr_add1_store         -> VERIFICATION:- SUCCESSFUL
//   bug_tuple_atomic_ptr_add1_store          -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_transmute_ref_read                  -> VERIFICATION:- SUCCESSFUL
//   bug_transmute_ref_read                   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_transmute_atomic_ref_load           -> VERIFICATION:- SUCCESSFUL
//   bug_transmute_atomic_ref_load            -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_array_cast_elem_load         -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_array_cast_elem_load          -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_array_cast_elem_store        -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_array_cast_elem_store         -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_struct_cast_field_fetch_add  -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_struct_cast_field_fetch_add   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_field_reborrow_read                 -> VERIFICATION:- SUCCESSFUL
//   bug_field_reborrow_read                  -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_ptr_to_ptr_add1_read                -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_to_ptr_add1_read                 -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_ptr_to_mut_ptr_reassigned_read      -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_to_mut_ptr_reassigned_read       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_nonnull_as_ref_read                 -> VERIFICATION:- SUCCESSFUL
//   bug_nonnull_as_ref_read                  -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_slice_from_raw_parts_read           -> VERIFICATION:- SUCCESSFUL
//   bug_slice_from_raw_parts_read            -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_count_zeroed_reborrow_unused        -> VERIFICATION:- SUCCESSFUL
//   bug_count_bumped_reborrow_unused         -> VERIFICATION:- FAILED (dereference failure: pointer invalid)
//
// Accesses through a pointer into a static, reached from a constant pointer
// in the shapes the round-2 global-object bound did not reach (round-3 review
// of fix/chc-atomic-as-ptr-live, critical and medium findings): a pointer
// held in a struct or tuple field, a reference made by transmute, a projected
// reborrow `(*p)[1]` / `(*p).y` of an atomic past the static, a pointer read
// back through a shared reference to it, `NonNull::new_unchecked(..).as_ref()`,
// a slice made by `from_raw_parts`, and a field reborrow read. Each bug_ row
// is one past the static; each safe_ twin is the same shape inside a larger
// static. Rows built on `const R: &u32 = &ARR[1]` are left out: corpus-rev
// Kani 0.67.0 mis-models a constant reference into a static at a nonzero
// offset (round-3 review, oracle caveat).
#![allow(dead_code, static_mut_refs)]
use std::ptr::NonNull;
use std::sync::atomic::{AtomicU32, Ordering};

static V: u32 = 7;
static ARR: [u32; 2] = [1, 2];
static A: AtomicU32 = AtomicU32::new(5);
static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];

struct H {
    p: *const u32,
}
struct HA {
    p: *const AtomicU32,
}
#[repr(C)]
struct S2 {
    a: u32,
    b: u32,
}
#[repr(C)]
struct PA {
    x: AtomicU32,
    y: AtomicU32,
}

fn zero(k: &mut usize) {
    *k = 0;
}
fn bump(k: &mut usize) {
    *k += 1;
}

// --- a pointer held in a struct or tuple field ---
#[kani::proof]
fn safe_struct_held_add1_read() {
    let h = H { p: &ARR[0] };
    assert!(unsafe { *h.p.add(1) } == 2);
}
#[kani::proof]
fn bug_struct_held_add1_read() {
    let h = H { p: &V };
    let v = unsafe { *h.p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_field_copy_then_add() {
    let h = H { p: &ARR[0] };
    let q = h.p;
    assert!(unsafe { *q.add(1) } == 2);
}
#[kani::proof]
fn bug_struct_field_copy_then_add() {
    let h = H { p: &V };
    let q = h.p;
    let v = unsafe { *q.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_held_moved_read() {
    let p: *const u32 = &ARR[0];
    let h = H { p: unsafe { p.add(1) } };
    assert!(unsafe { *h.p } == 2);
}
#[kani::proof]
fn bug_struct_held_moved_read() {
    let p: *const u32 = &V;
    let h = H { p: unsafe { p.add(1) } };
    let v = unsafe { *h.p };
    assert!(v == v);
}
#[kani::proof]
fn safe_tuple_held_add1_read() {
    let t: (*const u32, u8) = (&ARR[0], 0);
    assert!(unsafe { *t.0.add(1) } == 2);
}
#[kani::proof]
fn bug_tuple_held_add1_read() {
    let t: (*const u32, u8) = (&V, 0);
    let v = unsafe { *t.0.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_reassigned_field_read() {
    let mut h = H { p: &V };
    h.p = &ARR[0];
    assert!(unsafe { *h.p.add(1) } == 2);
}
#[kani::proof]
fn bug_struct_reassigned_field_read() {
    let mut h = H { p: &ARR[0] };
    h.p = &V;
    let v = unsafe { *h.p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_held_atomic_load() {
    let h = HA { p: &AP[0] };
    let v = unsafe { (*h.p.add(1)).load(Ordering::SeqCst) };
    assert!(v == 2);
}
#[kani::proof]
fn bug_struct_held_atomic_load() {
    let h = HA { p: &A };
    let v = unsafe { (*h.p.add(1)).load(Ordering::SeqCst) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_held_atomic_store() {
    let h = HA { p: &AP[0] };
    unsafe { (*h.p.add(1)).store(9, Ordering::SeqCst) };
    assert!(AP[1].load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_struct_held_atomic_store() {
    let h = HA { p: &A };
    unsafe { (*h.p.add(1)).store(9, Ordering::SeqCst) };
}
#[kani::proof]
fn safe_tuple_atomic_ptr_add1_store() {
    let t = (&AP[0] as *const AtomicU32, 0u8);
    unsafe { (*t.0.add(1)).store(9, Ordering::SeqCst) };
    assert!(AP[1].load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_tuple_atomic_ptr_add1_store() {
    let t = (&A as *const AtomicU32, 0u8);
    unsafe { (*t.0.add(1)).store(9, Ordering::SeqCst) };
}

// --- a reference made by transmute ---
#[kani::proof]
fn safe_transmute_ref_read() {
    let p: *const u32 = &ARR[0];
    let r: &u32 = unsafe { std::mem::transmute(p.add(1)) };
    assert!(*r == 2);
}
#[kani::proof]
fn bug_transmute_ref_read() {
    let p: *const u32 = &V;
    let r: &u32 = unsafe { std::mem::transmute(p.add(1)) };
    assert!(*r == *r);
}
#[kani::proof]
fn safe_transmute_atomic_ref_load() {
    let p = &AP[0] as *const AtomicU32;
    let r: &AtomicU32 = unsafe { std::mem::transmute(p.add(1)) };
    assert!(r.load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn bug_transmute_atomic_ref_load() {
    let p = &A as *const AtomicU32;
    let r: &AtomicU32 = unsafe { std::mem::transmute(p.add(1)) };
    let v = r.load(Ordering::SeqCst);
    assert!(v == v);
}

// --- a projected reborrow of an atomic past the static ---
#[kani::proof]
fn safe_atomic_array_cast_elem_load() {
    let p = &AP[0] as *const AtomicU32 as *const [AtomicU32; 2];
    assert!(unsafe { (*p)[1].load(Ordering::SeqCst) } == 2);
}
#[kani::proof]
fn bug_atomic_array_cast_elem_load() {
    let p = &A as *const AtomicU32 as *const [AtomicU32; 2];
    let v = unsafe { (*p)[1].load(Ordering::SeqCst) };
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_array_cast_elem_store() {
    let p = &AP[0] as *const AtomicU32 as *const [AtomicU32; 2];
    unsafe { (*p)[1].store(9, Ordering::SeqCst) };
    assert!(AP[1].load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_atomic_array_cast_elem_store() {
    let p = &A as *const AtomicU32 as *const [AtomicU32; 2];
    unsafe { (*p)[1].store(9, Ordering::SeqCst) };
}
#[kani::proof]
fn safe_atomic_struct_cast_field_fetch_add() {
    let p = &AP as *const [AtomicU32; 2] as *const PA;
    unsafe { (*p).y.fetch_add(1, Ordering::SeqCst) };
    assert!(AP[1].load(Ordering::SeqCst) == 3);
}
#[kani::proof]
fn bug_atomic_struct_cast_field_fetch_add() {
    let p = &A as *const AtomicU32 as *const PA;
    unsafe { (*p).y.fetch_add(1, Ordering::SeqCst) };
}
#[kani::proof]
fn safe_field_reborrow_read() {
    let p = &ARR as *const [u32; 2] as *const S2;
    let r: &u32 = unsafe { &(*p).b };
    assert!(*r == 2);
}
#[kani::proof]
fn bug_field_reborrow_read() {
    let p = &V as *const u32 as *const S2;
    let r: &u32 = unsafe { &(*p).b };
    assert!(*r == *r);
}

// --- a pointer read back through a reference, a NonNull, a slice ---
#[kani::proof]
fn safe_ptr_to_ptr_add1_read() {
    let p: *const u32 = &ARR[0];
    let pp = &p;
    assert!(unsafe { *(*pp).add(1) } == 2);
}
#[kani::proof]
fn bug_ptr_to_ptr_add1_read() {
    let p: *const u32 = &V;
    let pp = &p;
    let v = unsafe { *(*pp).add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_ptr_to_mut_ptr_reassigned_read() {
    let mut p: *const u32 = &V;
    let pp = &mut p;
    *pp = &ARR[0];
    assert!(unsafe { *(*pp).add(1) } == 2);
}
#[kani::proof]
fn bug_ptr_to_mut_ptr_reassigned_read() {
    let mut p: *const u32 = &ARR[0];
    let pp = &mut p;
    *pp = &V;
    let v = unsafe { *(*pp).add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_nonnull_as_ref_read() {
    let p: *const u32 = &ARR[0];
    let n = unsafe { NonNull::new_unchecked(p.add(1) as *mut u32) };
    assert!(unsafe { *n.as_ref() } == 2);
}
#[kani::proof]
fn bug_nonnull_as_ref_read() {
    let p: *const u32 = &V;
    let n = unsafe { NonNull::new_unchecked(p.add(1) as *mut u32) };
    let v = unsafe { *n.as_ref() };
    assert!(v == v);
}
#[kani::proof]
fn safe_slice_from_raw_parts_read() {
    let s = unsafe { std::slice::from_raw_parts(&ARR[0] as *const u32, 2) };
    assert!(s[1] == 2);
}
#[kani::proof]
fn bug_slice_from_raw_parts_read() {
    let s = unsafe { std::slice::from_raw_parts(&V as *const u32, 2) };
    let v = s[1];
    assert!(v == v);
}

// --- a count a callee writes (the bound is symbolic, not folded) ---
#[kani::proof]
fn safe_count_zeroed_reborrow_unused() {
    let mut k: usize = 1;
    zero(&mut k);
    let p = &A as *const AtomicU32;
    let _q = unsafe { &*p.add(k) };
}
#[kani::proof]
fn bug_count_bumped_reborrow_unused() {
    let mut k: usize = 0;
    bump(&mut k);
    let p = &A as *const AtomicU32;
    let _q = unsafe { &*p.add(k) };
}

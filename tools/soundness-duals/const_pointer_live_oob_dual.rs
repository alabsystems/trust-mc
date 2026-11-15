// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_ref_static_raw_add0_read                  -> VERIFICATION:- SUCCESSFUL
//   bug_ref_static_raw_add1_read                   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_const_static_reborrow_read                -> VERIFICATION:- SUCCESSFUL
//   bug_const_static_reborrow_oob_read             -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_cast_add0_read                     -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_cast_add1_read                      -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_array_ptr_add1_load                -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ptr_add1_load                       -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_atomic_array_ptr_add1_store               -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ptr_add1_store                      -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_atomic_store_then_cast_add0_read          -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_store_then_cast_add1_read           -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_addr_of_static_add0_read                  -> VERIFICATION:- SUCCESSFUL
//   bug_addr_of_static_add1_read                   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_reborrow_static_wrapping_round_trip_read  -> VERIFICATION:- SUCCESSFUL
//   bug_reborrow_static_wrapping_add1_read         -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   bug_static_wrapping_sub1_read                  -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_array_static_add1_read                    -> VERIFICATION:- SUCCESSFUL
//   bug_array_static_add2_read                     -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_array_elem_reborrow_add1_read             -> VERIFICATION:- SUCCESSFUL
//   bug_array_elem_reborrow_add1_read              -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_array_choice_index_read                   -> VERIFICATION:- SUCCESSFUL
//   bug_array_choice_index_read                    -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   bug_array_symbolic_index_read                  -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_static_last_byte                          -> VERIFICATION:- SUCCESSFUL
//   bug_static_byte_past_end                       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_array_u32x2_read_as_u64                   -> VERIFICATION:- SUCCESSFUL
//   bug_static_u32_read_as_u64                     -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_struct_field_a_add1                       -> VERIFICATION:- SUCCESSFUL
//   bug_struct_field_b_add1                        -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_promoted_reborrow_read                    -> VERIFICATION:- SUCCESSFUL
//   bug_promoted_reborrow_add1_read                -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_mut_static_add0_write                     -> VERIFICATION:- SUCCESSFUL
//   bug_mut_static_add1_write                      -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   bug_mut_static_reborrow_add1_write             -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_mut_array_add1_write                      -> VERIFICATION:- SUCCESSFUL
//   bug_mut_array_add2_write                       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_reborrow_ref_in_bounds_unused             -> VERIFICATION:- SUCCESSFUL
//   bug_reborrow_ref_out_of_bounds_unused          -> VERIFICATION:- FAILED (dereference failure: pointer invalid)
//   safe_reborrow_ref_u32_read                     -> VERIFICATION:- SUCCESSFUL
//   bug_reborrow_ref_u32_read                      -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_atomic_as_ptr_add0_read                   -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_as_ptr_add1_read                    -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   bug_const_int_ptr_reborrow_read                -> VERIFICATION:- FAILED (dereference failure: invalid integer address)
//   bug_const_dangling_reborrow_read               -> VERIFICATION:- FAILED (dereference failure: invalid integer address)
//   safe_ptr_read_add0                             -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_read_add1                              -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_read_volatile_add0                        -> VERIFICATION:- SUCCESSFUL
//   bug_read_volatile_add1                         -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_read_unaligned_add0                       -> VERIFICATION:- SUCCESSFUL
//   bug_read_unaligned_add1                        -> VERIFICATION:- FAILED (memcpy source region readable)
//   safe_write_volatile_add0                       -> VERIFICATION:- SUCCESSFUL
//   bug_write_volatile_add1                        -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_ptr_write_add0                            -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_write_add1                             -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_from_ptr_add0_load                 -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_from_ptr_add1_load                  -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_addr_of_deref_add0_read                   -> VERIFICATION:- SUCCESSFUL
//   bug_addr_of_deref_add1_read                    -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//
// WHY THIS FILE EXISTS. A pointer reached through a constant pointer into a
// static or a constant allocation (`let p: *const u32 = &V;` is
// `_1 = &raw const (*_2)` with `_2 = const {&V}`) and then moved
// (`p.add(1)`) reaches its dereference with an opaque obj_id lane, and
// `heap_access_checks` bounds an access only when that lane folds to a
// constant. On main several out-of-bounds rows below failed by accident: the
// use-after-scope check read `_2`'s StorageDead as the death of the pointee
// and staged a constant-false obligation, which also failed SAFE rows. When
// the round-0 commit d866ef143 removed that false obligation, six of them
// became clean CHC proofs (round-2 review of fix/chc-atomic-as-ptr-live);
// others (`addr_of!(V).add(1)`, a promoted constant, a byte past a static, a
// constant integer address, `read_volatile` past a static) proved clean on
// main too. The global-object lane of the provenance walk now states the real
// bound: the access must lie inside the static's or the constant allocation's
// bytes, and no access through a constant integer address is valid.
#![allow(dead_code, static_mut_refs)]
use std::ptr::{NonNull, addr_of, addr_of_mut};
use std::sync::atomic::{AtomicU32, Ordering};

static V: u32 = 7;
static ARR: [u32; 2] = [1, 2];
static A: AtomicU32 = AtomicU32::new(5);
static AP: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
static mut M: u32 = 5;
static mut MA: [u32; 2] = [1, 2];
#[repr(C)]
struct S2 {
    a: u32,
    b: u32,
}
static S: S2 = S2 { a: 1, b: 2 };
const P_INT: *const u32 = 0x1000 as *const u32;
const P_DANGLING: *const u32 = NonNull::<u32>::dangling().as_ptr();

// --- the six rows round 0 turned into clean proofs ---

#[kani::proof]
fn safe_ref_static_raw_add0_read() {
    let p: *const u32 = &V;
    let v = unsafe { *p.add(0) };
    assert!(v == 7);
}
#[kani::proof]
fn bug_ref_static_raw_add1_read() {
    let p: *const u32 = &V;
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_const_static_reborrow_read() {
    let p: *const u32 = &V;
    let q: *const u32 = unsafe { addr_of!(*p) };
    assert!(unsafe { *q } == 7);
}
#[kani::proof]
fn bug_const_static_reborrow_oob_read() {
    let p: *const u32 = &V;
    let q: *const u32 = unsafe { addr_of!(*p).add(1) };
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_cast_add0_read() {
    let p = &A as *const AtomicU32 as *const u32;
    let v = unsafe { *p.add(0) };
    assert!(v == 5);
}
#[kani::proof]
fn bug_atomic_cast_add1_read() {
    let p = &A as *const AtomicU32 as *const u32;
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_array_ptr_add1_load() {
    let p = &AP[0] as *const AtomicU32;
    let q = unsafe { &*p.add(1) };
    assert!(q.load(Ordering::SeqCst) == 2);
}
#[kani::proof]
fn bug_atomic_ptr_add1_load() {
    let p = &A as *const AtomicU32;
    let q = unsafe { &*p.add(1) };
    assert!(q.load(Ordering::SeqCst) == q.load(Ordering::SeqCst));
}
#[kani::proof]
fn safe_atomic_array_ptr_add1_store() {
    let p = &AP[0] as *const AtomicU32;
    let q = unsafe { &*p.add(1) };
    q.store(3, Ordering::SeqCst);
    assert!(AP[1].load(Ordering::SeqCst) == 3);
}
#[kani::proof]
fn bug_atomic_ptr_add1_store() {
    let p = &A as *const AtomicU32;
    let q = unsafe { &*p.add(1) };
    q.store(3, Ordering::SeqCst);
}
#[kani::proof]
fn safe_atomic_store_then_cast_add0_read() {
    let p = &A as *const AtomicU32 as *const u32;
    A.store(9, Ordering::SeqCst);
    let v = unsafe { *p.add(0) };
    assert!(v == 9);
}
#[kani::proof]
fn bug_atomic_store_then_cast_add1_read() {
    let p = &A as *const AtomicU32 as *const u32;
    A.store(9, Ordering::SeqCst);
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}

// --- the same bound, other shapes ---

#[kani::proof]
fn safe_addr_of_static_add0_read() {
    let p = addr_of!(V);
    let v = unsafe { *p.add(0) };
    assert!(v == 7);
}
#[kani::proof]
fn bug_addr_of_static_add1_read() {
    let p = addr_of!(V);
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_reborrow_static_wrapping_round_trip_read() {
    let p: *const u32 = &V;
    let q = unsafe { addr_of!(*p) }.wrapping_add(1).wrapping_sub(1);
    assert!(unsafe { *q } == 7);
}
#[kani::proof]
fn bug_reborrow_static_wrapping_add1_read() {
    let p: *const u32 = &V;
    let q = unsafe { addr_of!(*p) }.wrapping_add(1);
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn bug_static_wrapping_sub1_read() {
    let p: *const u32 = &V;
    let q = p.wrapping_sub(1);
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn safe_array_static_add1_read() {
    let p = addr_of!(ARR) as *const u32;
    let v = unsafe { *p.add(1) };
    assert!(v == 2);
}
#[kani::proof]
fn bug_array_static_add2_read() {
    let p = addr_of!(ARR) as *const u32;
    let v = unsafe { *p.add(2) };
    assert!(v == v);
}
#[kani::proof]
fn safe_array_elem_reborrow_add1_read() {
    let p: *const u32 = &ARR[0];
    let q = unsafe { addr_of!(*p).add(1) };
    assert!(unsafe { *q } == 2);
}
#[kani::proof]
fn bug_array_elem_reborrow_add1_read() {
    let p: *const u32 = &ARR[1];
    let q = unsafe { addr_of!(*p).add(1) };
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn safe_array_choice_index_read() {
    let c: bool = kani::any();
    let i: usize = if c { 1 } else { 0 };
    let p = addr_of!(ARR) as *const u32;
    let v = unsafe { *p.add(i) };
    assert!(v == 1 || v == 2);
}
#[kani::proof]
fn bug_array_choice_index_read() {
    let c: bool = kani::any();
    let i: usize = if c { 2 } else { 0 };
    let p = addr_of!(ARR) as *const u32;
    let v = unsafe { *p.add(i) };
    assert!(v == v);
}
#[kani::proof]
fn bug_array_symbolic_index_read() {
    let i: usize = kani::any();
    kani::assume(i < 3);
    let p = addr_of!(ARR) as *const u32;
    let v = unsafe { *p.add(i) };
    assert!(v == v);
}
#[kani::proof]
fn safe_static_last_byte() {
    let p: *const u32 = &V;
    let v = unsafe { *(p as *const u8).add(3) };
    assert!(v == 0);
}
#[kani::proof]
fn bug_static_byte_past_end() {
    let p: *const u32 = &V;
    let v = unsafe { *(p as *const u8).add(4) };
    assert!(v == v);
}
#[kani::proof]
fn safe_array_u32x2_read_as_u64() {
    let p: *const [u32; 2] = &ARR;
    let v = unsafe { std::ptr::read_unaligned(p as *const u64) };
    assert!(v == v);
}
#[kani::proof]
fn bug_static_u32_read_as_u64() {
    let p: *const u32 = &V;
    let v = unsafe { *(p as *const u64) };
    assert!(v == v);
}
#[kani::proof]
fn safe_struct_field_a_add1() {
    let p: *const u32 = &S.a;
    let v = unsafe { *p.add(1) };
    assert!(v == 2);
}
#[kani::proof]
fn bug_struct_field_b_add1() {
    let p: *const u32 = &S.b;
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn safe_promoted_reborrow_read() {
    let p: *const u32 = &5;
    let q = unsafe { addr_of!(*p) };
    assert!(unsafe { *q } == 5);
}
#[kani::proof]
fn bug_promoted_reborrow_add1_read() {
    let p: *const u32 = &5;
    let q = unsafe { addr_of!(*p).add(1) };
    let v = unsafe { *q };
    assert!(v == v);
}
#[kani::proof]
fn safe_mut_static_add0_write() {
    let p = addr_of_mut!(M);
    unsafe { *p.add(0) = 3 };
    assert!(unsafe { M } == 3);
}
#[kani::proof]
fn bug_mut_static_add1_write() {
    let p = addr_of_mut!(M);
    unsafe { *p.add(1) = 3 };
}
#[kani::proof]
fn bug_mut_static_reborrow_add1_write() {
    let p = addr_of_mut!(M);
    let q = unsafe { addr_of_mut!(*p).add(1) };
    unsafe { *q = 3 };
}
#[kani::proof]
fn safe_mut_array_add1_write() {
    let p = addr_of_mut!(MA) as *mut u32;
    unsafe { *p.add(1) = 3 };
    assert!(unsafe { MA[1] } == 3);
}
#[kani::proof]
fn bug_mut_array_add2_write() {
    let p = addr_of_mut!(MA) as *mut u32;
    unsafe { *p.add(2) = 3 };
}
#[kani::proof]
fn safe_reborrow_ref_in_bounds_unused() {
    let p = &AP[0] as *const AtomicU32;
    let _q = unsafe { &*p.add(1) };
}
#[kani::proof]
fn bug_reborrow_ref_out_of_bounds_unused() {
    let p = &A as *const AtomicU32;
    let _q = unsafe { &*p.add(1) };
}
#[kani::proof]
fn safe_reborrow_ref_u32_read() {
    let p: *const u32 = &ARR[0];
    let q: &u32 = unsafe { &*p.add(1) };
    assert!(*q == 2);
}
#[kani::proof]
fn bug_reborrow_ref_u32_read() {
    let p: *const u32 = &V;
    let q: &u32 = unsafe { &*p.add(1) };
    assert!(*q == *q);
}
#[kani::proof]
fn safe_atomic_as_ptr_add0_read() {
    let p = A.as_ptr();
    let v = unsafe { *p.add(0) };
    assert!(v == 5);
}
#[kani::proof]
fn bug_atomic_as_ptr_add1_read() {
    let p = A.as_ptr();
    let v = unsafe { *p.add(1) };
    assert!(v == v);
}
#[kani::proof]
fn bug_const_int_ptr_reborrow_read() {
    let p: *const u32 = unsafe { addr_of!(*P_INT) };
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_const_dangling_reborrow_read() {
    let p: *const u32 = unsafe { addr_of!(*P_DANGLING) };
    let v = unsafe { *p };
    assert!(v == v);
}

// --- through the standard library's pointer calls ---

#[kani::proof]
fn safe_ptr_read_add0() {
    let p: *const u32 = &V;
    assert!(unsafe { std::ptr::read(p.add(0)) } == 7);
}
#[kani::proof]
fn bug_ptr_read_add1() {
    let p: *const u32 = &V;
    let v = unsafe { std::ptr::read(p.add(1)) };
    assert!(v == v);
}
#[kani::proof]
fn safe_read_volatile_add0() {
    let p: *const u32 = &V;
    assert!(unsafe { std::ptr::read_volatile(p.add(0)) } == 7);
}
#[kani::proof]
fn bug_read_volatile_add1() {
    let p: *const u32 = &V;
    let v = unsafe { std::ptr::read_volatile(p.add(1)) };
    assert!(v == v);
}
#[kani::proof]
fn safe_read_unaligned_add0() {
    let p: *const u32 = &V;
    let v = unsafe { std::ptr::read_unaligned(p.add(0)) };
    assert!(v == v);
}
#[kani::proof]
fn bug_read_unaligned_add1() {
    let p: *const u32 = &V;
    let v = unsafe { std::ptr::read_unaligned(p.add(1)) };
    assert!(v == v);
}
#[kani::proof]
fn safe_write_volatile_add0() {
    let p = addr_of_mut!(M);
    unsafe { std::ptr::write_volatile(p.add(0), 3) };
    assert!(unsafe { M } == 3);
}
#[kani::proof]
fn bug_write_volatile_add1() {
    let p = addr_of_mut!(M);
    unsafe { std::ptr::write_volatile(p.add(1), 3) };
}
#[kani::proof]
fn safe_ptr_write_add0() {
    let p = addr_of_mut!(M);
    unsafe { std::ptr::write(p.add(0), 3) };
    assert!(unsafe { M } == 3);
}
#[kani::proof]
fn bug_ptr_write_add1() {
    let p = addr_of_mut!(M);
    unsafe { std::ptr::write(p.add(1), 3) };
}
#[kani::proof]
fn safe_atomic_from_ptr_add0_load() {
    let p = A.as_ptr();
    let a = unsafe { AtomicU32::from_ptr(p.add(0)) };
    assert!(a.load(Ordering::SeqCst) == 5);
}
#[kani::proof]
fn bug_atomic_from_ptr_add1_load() {
    let p = A.as_ptr();
    let a = unsafe { AtomicU32::from_ptr(p.add(1)) };
    assert!(a.load(Ordering::SeqCst) == a.load(Ordering::SeqCst));
}
#[kani::proof]
fn safe_addr_of_deref_add0_read() {
    let p = addr_of!(V);
    let q = unsafe { addr_of!(*p.add(0)) };
    assert!(unsafe { *q } == 7);
}
#[kani::proof]
fn bug_addr_of_deref_add1_read() {
    let p = addr_of!(V);
    let q = unsafe { addr_of!(*p.add(1)) };
    let v = unsafe { *q };
    assert!(v == v);
}

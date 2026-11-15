// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_ref_static_wrap_zero_read      -> VERIFICATION:- SUCCESSFUL
//   bug_ref_static_wrap_2p32_read       -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_addr_of_static_wrap_zero_read  -> VERIFICATION:- SUCCESSFUL
//   bug_addr_of_static_wrap_2p32_read   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_cast_wrap_zero_read     -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_cast_wrap_2p32_read      -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_atomic_ptr_wrap_zero_load      -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_ptr_wrap_2p32_load       -> VERIFICATION:- FAILED (dereference failure: pointer invalid; dereference failure: pointer outside object bounds)
//   safe_ref_static_wrap_sub_zero_read  -> VERIFICATION:- SUCCESSFUL
//   bug_ref_static_wrap_sub_2p32_read   -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_static_mut_wrap_zero_write     -> VERIFICATION:- SUCCESSFUL
//   bug_static_mut_wrap_2p32_write      -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//   safe_ref_static_with_addr_same_read -> VERIFICATION:- SUCCESSFUL
//   bug_ref_static_with_addr_2p32_read  -> VERIFICATION:- FAILED (dereference failure: pointer outside object bounds)
//
// An access through a constant pointer to a static after a wrapping step of
// exactly 2^32 bytes. The step moves the address's obj_id lane and leaves its
// low 32 offset bits inside the static, so a bound that reads only the offset
// passes it. The count is symbolic (kani::any() assumed equal), so the bound
// does not fold to a constant. On the CHC lane main dd0d949a9 proves six of
// the seven bug_ rows here (the static mut write fails closed); the
// global-object bound now checks the lane
// (codegen_stmt_rvalue_offset_const_object.rs, object_span_checks).

use std::ptr::addr_of;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

static V: u32 = 5;
static A: AtomicU32 = AtomicU32::new(5);
static mut M: [u8; 4] = [1, 2, 3, 4];

fn step_2p32() -> usize {
    let k: usize = kani::any();
    kani::assume(k == 1usize << 32);
    k
}
fn step_zero() -> usize {
    let k: usize = kani::any();
    kani::assume(k == 0);
    k
}

#[kani::proof]
fn safe_ref_static_wrap_zero_read() {
    let p: *const u32 = &V;
    let k = step_zero();
    assert!(unsafe { *p.wrapping_byte_add(k) } == 5);
}
#[kani::proof]
fn bug_ref_static_wrap_2p32_read() {
    let p: *const u32 = &V;
    let k = step_2p32();
    let v = unsafe { *p.wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_addr_of_static_wrap_zero_read() {
    let p: *const u32 = addr_of!(V);
    let k = step_zero();
    assert!(unsafe { *p.wrapping_byte_add(k) } == 5);
}
#[kani::proof]
fn bug_addr_of_static_wrap_2p32_read() {
    let p: *const u32 = addr_of!(V);
    let k = step_2p32();
    let v = unsafe { *p.wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_atomic_cast_wrap_zero_read() {
    A.store(7, SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    let k = step_zero();
    assert!(unsafe { *p.wrapping_byte_add(k) } == 7);
}
#[kani::proof]
fn bug_atomic_cast_wrap_2p32_read() {
    A.store(7, SeqCst);
    let p = &A as *const AtomicU32 as *const u32;
    let k = step_2p32();
    let v = unsafe { *p.wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_atomic_ptr_wrap_zero_load() {
    let p = &A as *const AtomicU32;
    let k = step_zero();
    let r = unsafe { &*p.wrapping_byte_add(k) };
    assert!(r.load(SeqCst) == 5);
}
#[kani::proof]
fn bug_atomic_ptr_wrap_2p32_load() {
    let p = &A as *const AtomicU32;
    let k = step_2p32();
    let r = unsafe { &*p.wrapping_byte_add(k) };
    let v = r.load(SeqCst);
    assert!(v == v);
}

#[kani::proof]
fn safe_ref_static_wrap_sub_zero_read() {
    let p: *const u32 = &V;
    let k = step_zero();
    assert!(unsafe { *p.wrapping_byte_sub(k) } == 5);
}
#[kani::proof]
fn bug_ref_static_wrap_sub_2p32_read() {
    let p: *const u32 = &V;
    let k = step_2p32();
    let v = unsafe { *p.wrapping_byte_sub(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_static_mut_wrap_zero_write() {
    let p = unsafe { std::ptr::addr_of_mut!(M) } as *mut u8;
    let k = step_zero();
    unsafe { *p.wrapping_byte_add(k) = 9 };
    assert!(unsafe { M[0] } == 9);
}
#[kani::proof]
fn bug_static_mut_wrap_2p32_write() {
    let p = unsafe { std::ptr::addr_of_mut!(M) } as *mut u8;
    let k = step_2p32();
    unsafe { *p.wrapping_byte_add(k) = 9 };
}

#[kani::proof]
fn safe_ref_static_with_addr_same_read() {
    let p: *const u32 = &V;
    let q = p.with_addr(p.addr() + step_zero());
    assert!(unsafe { *q } == 5);
}
#[kani::proof]
fn bug_ref_static_with_addr_2p32_read() {
    let p: *const u32 = &V;
    let q = p.with_addr(p.addr().wrapping_add(step_2p32()));
    let v = unsafe { *q };
    assert!(v == v);
}

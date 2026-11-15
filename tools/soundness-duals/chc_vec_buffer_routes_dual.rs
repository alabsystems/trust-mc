// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: routes round 10's Vec-buffer rule
// (heap/vec_buffer_access.rs) did not see, and the direction it did not
// cover (third review of round 10 of fix/chc-false-certificates, 2026-10-15,
// r3_vecbuf.rs v05, v06, v10, the same on main f5dfb8d48):
// - a reference made from the buffer pointer before the `Vec` changed
//   (`&*p.add(1)`, `slice::from_raw_parts(p, n)`): the rule saw accesses
//   through raw-pointer locals only;
// - a change through a `*mut Vec` taken before the accessor: the rule saw
//   changes rooted at the `Vec`'s own aliases only;
// - a write through the buffer pointer followed by a read of the `Vec`'s own
//   model (`*p = 5; v[0]`): the stubs never see the write.
// Each is a missed bug or a certified false counterexample on main. Accesses
// through references whose definition chain reaches a buffer accessor, every
// mutable handle of the `Vec` whenever it was taken, and a model read after a
// write through the buffer now fail the harness closed; a write then a raw read
// of the same cell is exact.

use std::ptr;

#[kani::proof]
fn bug_ref_from_raw_after_indexmut() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_ptr();
    let r: &u8 = unsafe { &*p.add(1) };
    v[1] = 9;
    assert!(*r == 2);
}

#[kani::proof]
fn safe_ref_from_raw_after_indexmut() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_ptr();
    let r: &u8 = unsafe { &*p.add(1) };
    v[1] = 9;
    assert!(*r == 9);
}

#[kani::proof]
fn bug_from_raw_parts_after_indexmut() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_ptr();
    let s: &[u8] = unsafe { std::slice::from_raw_parts(p, 3) };
    v[1] = 9;
    assert!(s[1] == 2);
}

#[kani::proof]
fn safe_from_raw_parts_after_indexmut() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_ptr();
    let s: &[u8] = unsafe { std::slice::from_raw_parts(p, 3) };
    v[1] = 9;
    assert!(s[1] == 9);
}

#[kani::proof]
fn bug_mutation_through_raw_vec_ptr() {
    let mut v = vec![1u8, 2, 3];
    let vp: *mut Vec<u8> = &mut v;
    let p = v.as_ptr();
    unsafe { (&mut *vp)[1] = 9 };
    let x = unsafe { *p.add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_mutation_through_raw_vec_ptr() {
    let mut v = vec![1u8, 2, 3];
    let vp: *mut Vec<u8> = &mut v;
    let p = v.as_ptr();
    unsafe { (&mut *vp)[1] = 9 };
    let x = unsafe { *p.add(1) };
    assert!(x == 9);
}

#[kani::proof]
fn safe_store_then_len() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { *p = 5 };
    assert!(v.len() == 2);
}

#[kani::proof]
fn bug_store_then_index() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { *p = 5 };
    assert!(v[0] == 1);
}

#[kani::proof]
fn safe_store_then_raw_read() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { *p = 5 };
    let y = unsafe { *p };
    assert!(y == 5);
}

#[kani::proof]
fn bug_store_then_raw_read() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { *p = 5 };
    let y = unsafe { *p };
    assert!(y == 1 && v.len() == 2);
}

#[kani::proof]
fn bug_write_then_iter_sum() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { ptr::write(p.add(1), 9) };
    let s: u32 = v.iter().sum();
    assert!(s == 3);
}

#[kani::proof]
fn bug_mut_ref_from_raw_after_indexmut() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_mut_ptr();
    let r: &mut u8 = unsafe { &mut *p.add(1) };
    v[1] = 9;
    assert!(*r == 2);
}

#[kani::proof]
fn bug_from_raw_parts_mut_write_then_index() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_mut_ptr();
    let s: &mut [u8] = unsafe { std::slice::from_raw_parts_mut(p, 3) };
    s[1] = 9;
    assert!(v[1] == 2);
}

#[kani::proof]
fn bug_handle_in_struct_before_accessor() {
    struct H<'a> {
        v: &'a mut Vec<u8>,
    }
    let mut v = vec![1u8, 2, 3];
    let vp: *mut Vec<u8> = &mut v;
    let p = unsafe { (*vp).as_ptr() };
    let h = H { v: unsafe { &mut *vp } };
    h.v[1] = 9;
    let x = unsafe { *p.add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_read_then_len_then_read() {
    let v = vec![1u8, 2, 3];
    let p = v.as_ptr();
    let n = v.len();
    let x = unsafe { *p.add(2) };
    assert!(x == 3 && n == 3);
}

#[kani::proof]
fn bug_swap_through_raw_handle() {
    let mut v = vec![1u8, 2, 3];
    let mut w = vec![7u8, 7, 7];
    let vp: *mut Vec<u8> = &mut v;
    let p = v.as_ptr();
    unsafe { std::mem::swap(&mut *vp, &mut w) };
    drop(w);
    let x = unsafe { *p };
    assert!(x == x);
}

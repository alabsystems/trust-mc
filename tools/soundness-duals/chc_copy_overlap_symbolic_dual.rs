// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: `copy_nonoverlapping`'s non-overlap precondition was
// checked only when both pointers' object ids const-folded. Round 10 of
// fix/chc-false-certificates encoded a one-element integer copy it could not
// resolve as the typed store `*dst = *src`, so a copy of a value onto itself
// through an `FnMut` capture, a raw parameter of a callee or a `Vec`'s buffer
// was proved where Kani reports "memcpy src/dst overlap" (third review of
// round 10, 2026-10-15, r3_overlap.rs o01, o05, o08, o10, r3_copy.rs c01; o05
// the same on main f5dfb8d48). The disjointness obligation is now emitted over
// symbolic object ids too: the two byte ranges are disjoint or lie in
// different objects. The `safe_` rows check copies between distinct objects
// and disjoint ranges of one, and the legal-overlap `copy`.

use std::ptr;

#[inline(never)]
fn cp(s: *const u32, d: *mut u32) {
    unsafe { ptr::copy_nonoverlapping(s, d, 1) }
}

fn self_copy_param(p: *mut u32) {
    unsafe { ptr::copy_nonoverlapping(p as *const u32, p, 1) }
}

#[repr(C)]
struct P {
    a: u32,
    b: u32,
}

#[kani::proof]
fn bug_self_copy_fnmut() {
    let mut x: u32 = 1;
    let d = &mut x as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(d, d, 1) };
    f();
}

#[kani::proof]
fn safe_copy_fnmut() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let s = &mut x as *mut u32;
    let d = &mut y as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(s, d, 1) };
    f();
    assert!(y == 1);
}

#[kani::proof]
fn bug_self_copy_vec_buffer() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p, p, 1) };
}

#[kani::proof]
fn bug_self_copy_u8_fnmut() {
    let mut x: u8 = 1;
    let d = &mut x as *mut u8;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(d as *const u8, d, 1) };
    f();
}

#[kani::proof]
fn bug_self_copy_raw_param_fnonce() {
    let mut x: u32 = 1;
    let p = &mut x as *mut u32;
    let f = move || self_copy_param(p);
    f();
}

#[kani::proof]
fn bug_self_copy_field_fnmut() {
    let mut p = P { a: 1, b: 2 };
    let d = &mut p.b as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(d, d, 1) };
    f();
}

#[kani::proof]
fn safe_two_vec_buffers() {
    let a = vec![1u32, 2];
    let mut b = vec![0u32, 0];
    unsafe { ptr::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr(), 2) };
    assert!(b[0] == 1 && b[1] == 2);
}

#[kani::proof]
fn safe_vec_buffer_to_stack() {
    let v = vec![7u32, 8];
    let mut out = 0u32;
    unsafe { ptr::copy_nonoverlapping(v.as_ptr(), &mut out, 1) };
    assert!(out == 7);
}

#[kani::proof]
fn safe_stack_to_vec_buffer() {
    let mut v = vec![7u32, 8];
    let x = 5u32;
    unsafe { ptr::copy_nonoverlapping(&x, v.as_mut_ptr().add(1), 1) };
    let y = unsafe { *v.as_ptr().add(1) };
    assert!(y == 5);
}

#[kani::proof]
fn bug_overlapping_halves_of_vec() {
    let mut v = vec![1u32, 2, 3, 4];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p as *const u32, p.add(1), 2) };
}

#[kani::proof]
fn safe_disjoint_halves_of_vec() {
    let mut v = vec![1u32, 2, 3, 4];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p as *const u32, p.add(2), 2) };
    let y = unsafe { *p.add(3) };
    assert!(y == 2);
}

#[kani::proof]
fn safe_two_boxes() {
    let a = Box::new(3u32);
    let mut b = Box::new(0u32);
    unsafe { ptr::copy_nonoverlapping(&*a as *const u32, &mut *b as *mut u32, 1) };
    assert!(*b == 3);
}

#[kani::proof]
fn safe_noinline_distinct() {
    let x = 1u32;
    let mut y = 2u32;
    cp(&x, &mut y);
    assert!(y == 1);
}

#[kani::proof]
fn bug_symbolic_index_may_overlap() {
    let mut a = [1u32, 2, 3, 4];
    let i: usize = kani::any();
    let j: usize = kani::any();
    kani::assume(i < 4 && j < 4);
    let p = a.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p.add(i) as *const u32, p.add(j), 1) };
}

#[kani::proof]
fn safe_symbolic_index_disjoint() {
    let mut a = [1u32, 2, 3, 4];
    let i: usize = kani::any();
    kani::assume(i < 2);
    let p = a.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p.add(i) as *const u32, p.add(i + 2), 1) };
    assert!(a[i + 2] == a[i]);
}

#[kani::proof]
fn safe_fnmut_distinct_captures() {
    let mut x: u32 = 1;
    let mut y: u32 = 2;
    let s = &mut x as *mut u32;
    let d = &mut y as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(s, d, 1) };
    f();
    assert!(y == 1);
}

#[kani::proof]
fn bug_vec_buffer_self_copy_u8() {
    let mut v = vec![1u8, 2];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p as *const u8, p, 1) };
}

#[kani::proof]
fn safe_vec_buffer_copy_within_disjoint_u8() {
    let mut v = vec![1u8, 2, 3];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy_nonoverlapping(p as *const u8, p.add(2), 1) };
    let y = unsafe { *p.add(2) };
    assert!(y == 1);
}

#[kani::proof]
fn safe_box_into_raw_distinct() {
    let p = Box::into_raw(Box::new(1u32));
    let q = Box::into_raw(Box::new(2u32));
    unsafe { ptr::copy_nonoverlapping(p, q, 1) };
    let v = unsafe { *q };
    unsafe { drop(Box::from_raw(p)) };
    unsafe { drop(Box::from_raw(q)) };
    assert!(v == 1);
}

#[kani::proof]
fn safe_copy_legal_overlap() {
    let mut v = vec![1u32, 2, 3];
    let p = v.as_mut_ptr();
    unsafe { ptr::copy(p as *const u32, p.add(1), 2) };
    let y = unsafe { *p.add(2) };
    assert!(y == 2);
}

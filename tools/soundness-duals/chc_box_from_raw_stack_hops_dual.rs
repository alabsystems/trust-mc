// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: `Box::from_raw` of a pointer into a stack local
// (undefined behavior Kani does not report) reached through a tuple field, a
// struct field or `Option::unwrap`. The rule that fails such a harness closed
// (heap/stack_address.rs `book_box_from_raw_of_stack_pointer`) followed only
// single definitions by copies, casts, borrows, `as_ptr` and in-bounds steps,
// so these hops ended its walk; the slice `as_mut_ptr` stub gives the pointer
// no address of its own, the box hop drops the points-to metadata, and the
// read through the box read a memory cell at an unconstrained address: each
// safe row below was a certified false counterexample on main f5dfb8d48 and on
// round 9 of fix/chc-false-certificates (second review of round 9, 2026-10-15,
// probes r2_boxstack.rs t01, t02, t04, t08, t09, t11, r2_boxsrc.rs s01; the
// BMC lane is exact on t01 and t02). The walk now follows those hops, and the
// encoder's own `ref_targets` metadata decides too: a pointer it takes to a
// local's own storage points into that local whatever route it took. The safe
// rows fail closed (known-red false failures); the bug rows lose main's
// certificate, which came from the same unconstrained read. The controls
// (a path join, an array of pointers, the hop without a box, a heap pointer
// through a tuple) keep main's proofs.

struct W {
    p: *mut u8,
}

#[kani::proof]
fn safe_box_over_stack_pointer_via_tuple() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn bug_box_over_stack_pointer_via_tuple() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 8);
}

#[kani::proof]
fn safe_box_over_stack_pointer_via_struct() {
    let mut a = [7u8; 16];
    let w = W { p: a.as_mut_ptr() };
    let b: Box<u8> = unsafe { Box::from_raw(w.p) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn bug_box_over_stack_pointer_via_struct() {
    let mut a = [7u8; 16];
    let w = W { p: a.as_mut_ptr() };
    let b: Box<u8> = unsafe { Box::from_raw(w.p) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 8);
}

#[kani::proof]
fn safe_box_over_stack_pointer_via_option() {
    let mut a = [7u8; 16];
    let q = Some(a.as_mut_ptr()).unwrap();
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn safe_box_over_stack_scalar_via_tuple() {
    let mut x: u32 = 7;
    let w = (&mut x as *mut u32,);
    let b: Box<u32> = unsafe { Box::from_raw(w.0) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn bug_box_over_stack_scalar_via_tuple() {
    let mut x: u32 = 7;
    let w = (&mut x as *mut u32,);
    let b: Box<u32> = unsafe { Box::from_raw(w.0) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 8);
}

#[kani::proof]
fn safe_box_over_stack_pointer_deref_box() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    let v = *b;
    std::mem::forget(b);
    assert!(v == 7);
}

#[kani::proof]
fn safe_box_over_stack_pointer_write_then_read() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    a[0] = 9;
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 9);
}

#[kani::proof]
fn bug_box_over_stack_pointer_write_then_read() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    a[0] = 9;
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn safe_control_path_join() {
    let mut a = [7u8; 16];
    let c: bool = kani::any();
    let q = if c { a.as_mut_ptr() } else { unsafe { a.as_mut_ptr().add(1) } };
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn safe_control_array_of_pointers() {
    let mut a = [7u8; 16];
    let ps = [a.as_mut_ptr()];
    let b: Box<u8> = unsafe { Box::from_raw(ps[0]) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn safe_control_tuple_without_box() {
    let mut a = [7u8; 16];
    let w = (a.as_mut_ptr(),);
    assert!(unsafe { *w.0 } == 7);
}

#[kani::proof]
fn safe_control_heap_pointer_via_tuple() {
    let h = Box::into_raw(Box::new([7u8; 16])) as *mut u8;
    let w = (h,);
    let b: Box<u8> = unsafe { Box::from_raw(w.0) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

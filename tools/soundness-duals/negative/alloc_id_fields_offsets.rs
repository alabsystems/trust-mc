// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: addresses and values of distinct fields, array elements and
// objects — on the heap (`Box`, `Rc`) and on the stack — compared by pointer
// equality, by integer offset, by `offset_from` and by `add`.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12) around
// 80e385adc (Box::new stores its payload) and ebf198615 (address-taken stack
// objects are disjoint from heap objects and each other): two fields of one
// object must keep their offset, two objects must never share a byte.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::rc::Rc;

#[repr(C)]
struct S {
    a: u8,
    b: u8,
}

#[repr(C)]
struct T {
    x: u32,
    y: u32,
}

#[kani::proof]
fn box_fields_addrs_differ_safe() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    assert!(&s.a as *const u8 != &s.b as *const u8);
}

#[kani::proof]
fn box_fields_addrs_differ_must_fail() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    assert!(&s.a as *const u8 == &s.b as *const u8);
}

#[kani::proof]
fn box_fields_offset_safe() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    assert!((&s.b as *const u8 as usize) == (&s.a as *const u8 as usize) + 1);
}

#[kani::proof]
fn box_fields_offset_must_fail() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    assert!((&s.b as *const u8 as usize) == (&s.a as *const u8 as usize) + 2);
}

#[kani::proof]
fn box_fields_values_safe() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let pa: &u8 = &s.a;
    let pb: &u8 = &s.b;
    assert!(*pa == 1 && *pb == 2);
}

#[kani::proof]
fn box_fields_values_must_fail() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let pa: &u8 = &s.a;
    assert!(*pa == 2);
}

#[kani::proof]
fn box_u32_fields_offset_safe() {
    let t: Box<T> = Box::new(T { x: 1, y: 2 });
    let dx = &t.x as *const u32 as usize;
    let dy = &t.y as *const u32 as usize;
    assert!(dy - dx == 4 && t.y == 2);
}

#[kani::proof]
fn box_u32_fields_offset_must_fail() {
    let t: Box<T> = Box::new(T { x: 1, y: 2 });
    let dx = &t.x as *const u32 as usize;
    let dy = &t.y as *const u32 as usize;
    assert!(dy - dx == 8);
}

#[kani::proof]
fn stack_fields_differ_safe() {
    let s = S { a: 1, b: 2 };
    assert!(!std::ptr::eq(&s.a, &s.b) && *(&s.a) != *(&s.b));
}

#[kani::proof]
fn stack_fields_differ_must_fail() {
    let s = S { a: 1, b: 2 };
    assert!(std::ptr::eq(&s.a, &s.b));
}

#[kani::proof]
fn array_elem_addrs_safe() {
    let a = [1u8, 2];
    assert!(&a[1] as *const u8 as usize == &a[0] as *const u8 as usize + 1);
}

#[kani::proof]
fn array_elem_addrs_must_fail() {
    let a = [1u8, 2];
    assert!(std::ptr::eq(&a[0], &a[1]));
}

#[kani::proof]
fn two_boxes_addrs_differ_safe() {
    let b1: Box<u8> = Box::new(1);
    let b2: Box<u8> = Box::new(1);
    assert!(!std::ptr::eq(&*b1, &*b2));
}

#[kani::proof]
fn two_boxes_addrs_differ_must_fail() {
    let b1: Box<u8> = Box::new(1);
    let b2: Box<u8> = Box::new(1);
    assert!(std::ptr::eq(&*b1, &*b2));
}

#[kani::proof]
fn stack_vs_box_addrs_differ_safe() {
    let x = 1u8;
    let b: Box<u8> = Box::new(1);
    assert!(!std::ptr::eq(&x, &*b));
}

#[kani::proof]
fn stack_vs_box_addrs_differ_must_fail() {
    let x = 1u8;
    let b: Box<u8> = Box::new(1);
    assert!(std::ptr::eq(&x, &*b));
}

#[kani::proof]
fn box_field_write_then_read_safe() {
    let mut s: Box<S> = Box::new(S { a: 1, b: 2 });
    s.a = 5;
    assert!(s.b == 2 && s.a == 5);
}

#[kani::proof]
fn box_field_write_then_read_must_fail() {
    let mut s: Box<S> = Box::new(S { a: 1, b: 2 });
    s.a = 5;
    assert!(s.b == 5);
}

#[kani::proof]
fn box_field_write_through_ref_safe() {
    let mut s: Box<S> = Box::new(S { a: 1, b: 2 });
    {
        let pb: &mut u8 = &mut s.b;
        *pb = 9;
    }
    assert!(s.a == 1 && s.b == 9);
}

#[kani::proof]
fn box_field_write_through_ref_must_fail() {
    let mut s: Box<S> = Box::new(S { a: 1, b: 2 });
    {
        let pb: &mut u8 = &mut s.b;
        *pb = 9;
    }
    assert!(s.a == 9);
}

#[kani::proof]
fn box_offset_from_safe() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let d = unsafe { (&s.b as *const u8).offset_from(&s.a as *const u8) };
    assert!(d == 1);
}

#[kani::proof]
fn box_offset_from_must_fail() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let d = unsafe { (&s.b as *const u8).offset_from(&s.a as *const u8) };
    assert!(d == 0);
}

#[kani::proof]
fn box_add_reaches_field_safe() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let v = unsafe { *(&s.a as *const u8).add(1) };
    assert!(v == 2);
}

#[kani::proof]
fn box_add_reaches_field_must_fail() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let v = unsafe { *(&s.a as *const u8).add(1) };
    assert!(v == 1);
}

#[kani::proof]
fn rc_fields_differ_safe() {
    let r: Rc<S> = Rc::new(S { a: 1, b: 2 });
    assert!(r.a != r.b && r.a == 1);
}

#[kani::proof]
fn rc_fields_differ_must_fail() {
    let r: Rc<S> = Rc::new(S { a: 1, b: 2 });
    assert!(r.a == r.b);
}

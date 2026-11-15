// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: `copy_nonoverlapping::<T>(src, dst, 1)` into a field
// place the copy lane cannot reach exactly. The fourth review's chain-less copy
// refusal requires the destination pointer's definition chain to reach its ref
// target, and a field at a non-zero offset (`&mut p.b`), a field of a union
// (the lane's offset-0 rule read struct layouts only), and a reference
// captured by an `FnMut` closure and read through its `&mut self` have none:
// the copy took the demoting fallback where main and Kani prove the program
// (second review of round 9 of fix/chc-false-certificates, 2026-10-15, probes
// r2_copy.rs c09, c13, c16, c17, c18). Main proved the field-`b` rows by
// dropping the target's projection, which also wrote `a` and certified their
// safe twins falsely. A one-element copy of an integer is now the typed store
// `*dst = *src` it is, and a union field starts at byte 0.

use std::ptr;

#[repr(C)]
#[derive(Clone, Copy)]
struct Pair {
    a: u32,
    b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
union U32 {
    x: u32,
    h: [u16; 2],
}

fn put_b(p: &mut Pair, v: u32) {
    unsafe { ptr::copy_nonoverlapping(&v as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof]
fn safe_copy_into_union_field() {
    let mut u = U32 { x: 0x0102_0304 };
    let src: u16 = 0xAAAA;
    unsafe { ptr::copy_nonoverlapping(&src as *const u16, &mut u.x as *mut u32 as *mut u16, 1) };
    assert!(unsafe { u.x } == 0x0102_AAAA);
}

#[kani::proof]
fn bug_copy_into_union_field() {
    let mut u = U32 { x: 0x0102_0304 };
    let src: u16 = 0xAAAA;
    unsafe { ptr::copy_nonoverlapping(&src as *const u16, &mut u.x as *mut u32 as *mut u16, 1) };
    assert!(unsafe { u.x } == 0x0102_0304);
}

#[kani::proof]
fn safe_copy_into_field_b_through_param() {
    let mut p = Pair { a: 1, b: 2 };
    put_b(&mut p, 5);
    assert!(p.a == 1 && p.b == 5);
}

#[kani::proof]
fn bug_copy_into_field_b_through_param() {
    let mut p = Pair { a: 1, b: 2 };
    put_b(&mut p, 5);
    assert!(p.a == 5);
}

#[kani::proof]
fn safe_copy_into_field_b_direct() {
    let mut p = Pair { a: 1, b: 2 };
    let src: u32 = 7;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
    assert!(p.a == 1 && p.b == 7);
}

#[kani::proof]
fn bug_copy_into_field_b_direct() {
    let mut p = Pair { a: 1, b: 2 };
    let src: u32 = 7;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
    assert!(p.b == 2);
}

#[kani::proof]
fn safe_copy_through_fnmut_capture() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p.a;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, d as *mut u32, 1) };
        f();
    }
    assert!(p.a == 5 && p.b == 2);
}

#[kani::proof]
fn bug_copy_through_fnmut_capture() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p.a;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, d as *mut u32, 1) };
        f();
    }
    assert!(p.a == 1);
}

#[kani::proof]
fn safe_copy_through_fnmut_capture_field_a() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, &mut d.a as *mut u32, 1) };
        f();
    }
    assert!(p.a == 5 && p.b == 2);
}

#[kani::proof]
fn bug_copy_through_fnmut_capture_field_a() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, &mut d.a as *mut u32, 1) };
        f();
    }
    assert!(p.a == 1);
}

#[kani::proof]
fn safe_copy_through_fnmut_capture_field_b() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, &mut d.b as *mut u32, 1) };
        f();
    }
    assert!(p.a == 1 && p.b == 5);
}

#[kani::proof]
fn bug_copy_through_fnmut_capture_field_b() {
    let mut p = Pair { a: 1, b: 2 };
    let v: u32 = 5;
    {
        let d = &mut p;
        let mut f = move || unsafe { ptr::copy_nonoverlapping(&v as *const u32, &mut d.b as *mut u32, 1) };
        f();
    }
    assert!(p.b == 2);
}

#[kani::proof]
fn safe_copy_into_tuple_field0() {
    let mut t = (1u32, 2u32);
    let src: u32 = 9;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut t.0 as *mut u32, 1) };
    assert!(t.0 == 9 && t.1 == 2);
}

#[kani::proof]
fn bug_copy_into_tuple_field0() {
    let mut t = (1u32, 2u32);
    let src: u32 = 9;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut t.0 as *mut u32, 1) };
    assert!(t.1 == 9);
}

// A symbolic source value through a field-`b` copy: the store is the value.
#[kani::proof]
fn bug_copy_symbolic_into_field_b() {
    let mut p = Pair { a: 1, b: 2 };
    let src: u32 = kani::any();
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
    assert!(p.b != 7);
}

// Two elements into a field at a non-zero offset run past the struct.
#[kani::proof]
fn bug_copy_two_into_field_b_overflows() {
    let mut p = Pair { a: 1, b: 2 };
    let src = [5u32, 6];
    unsafe { ptr::copy_nonoverlapping(src.as_ptr(), &mut p.b as *mut u32, 2) };
}

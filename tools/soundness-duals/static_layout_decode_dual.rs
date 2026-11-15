// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- struct and tuple statics whose fields rustc reorders,
//! arrays of them, and their fields read through pointers (a nested field's
//! address, an element pointer, a pointer loaded out of another value).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   bug_flat_reordered                       -> FAILED ('assertion failed: SP.x == 10')
//!   safe_flat_reordered                      -> SUCCESSFUL
//!   bug_nested_direct                        -> FAILED ('assertion failed: OO.inner.c == 1')
//!   safe_nested_direct                       -> SUCCESSFUL
//!   bug_nested_mut_direct                    -> FAILED ('assertion failed: unsafe { MO.inner.c } == 1')
//!   safe_nested_mut_direct                   -> SUCCESSFUL
//!   bug_nested_field_addr                    -> FAILED ('assertion failed: unsafe { *p } == 4')
//!   safe_nested_field_addr                   -> SUCCESSFUL
//!   bug_arr_reordered_direct                 -> FAILED ('assertion failed: AT[1].b == 3')
//!   safe_arr_reordered_direct                -> SUCCESSFUL
//!   bug_arr_struct_field_sym                 -> FAILED ('assertion failed: v == 10')
//!   safe_arr_struct_field_sym                -> SUCCESSFUL
//!   bug_arr_struct_elem_store_field_read     -> FAILED ('assertion failed: v == 30')
//!   safe_arr_struct_elem_store_field_read    -> SUCCESSFUL
//!   bug_loaded_nested_field                  -> FAILED ('assertion failed: unsafe { (*h.p).inner.b } == 6')
//!   safe_loaded_nested_field                 -> SUCCESSFUL
//!   bug_loaded_nested_whole                  -> FAILED ('assertion failed: s.a == 7')
//!   safe_loaded_nested_whole                 -> SUCCESSFUL
//!   bug_loaded_elem_ptr_field                -> FAILED ('assertion failed: unsafe { (*q.add(1)).b } == 3')
//!   safe_loaded_elem_ptr_field               -> SUCCESSFUL
//!   bug_loaded_tuple_field                   -> FAILED ('assertion failed: unsafe { (*h.p).1 } == 8')
//!   safe_loaded_tuple_field                  -> SUCCESSFUL
//!   bug_enum_payload_via_ref                 -> FAILED ('assertion failed: *v == 6')
//!   safe_enum_payload_via_ref                -> SUCCESSFUL
//!   bug_enum_payload_after_store_direct      -> FAILED ('assertion failed: *v == 6')
//!   safe_enum_payload_after_store_direct     -> SUCCESSFUL
//!   bug_enum_payload_after_store_carried     -> FAILED ('assertion failed: *v == 6')
//!   safe_enum_payload_after_store_carried    -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main c22e1022e and on the round-7 branch). The
//! CHC static decoder read a datatype's fields in declaration order at
//! sort-width offsets, and an array's elements at the element sort's width.
//! `repr(Rust)` reorders fields (`P { x: u8, y: u32 }` is laid out `y@0, x@4`),
//! so every such static started from a wrong value: `assert!(SP.x == 10)`
//! verified SUCCESSFUL (a missed bug) and the safe twins were certified
//! Genuine. This is the root cause of `safe_nested_field_addr` (review of
//! fix/chc-lost-writes round 7, finding 3). Separately, the static's memory
//! image seeded no field of an array element (the element value is a
//! flattened bitvector), so a field read through an element pointer
//! (`(*p.add(i)).y`) selected a free value, certified Genuine on both bundles.
//!
//! FIX (fix/chc-lost-writes round 8): the initializer is read by its real
//! layout (decl/codegen_decl_static_layout.rs): each field at its ABI offset,
//! each element at its stride. The image is seeded and written under the same
//! decomposition (`static_image_fields`), which now also covers tuples and the
//! fields of array elements. The enum payload rows are the exception: an enum's
//! variants are not decomposed, so a payload read through a pointer the
//! encoder cannot resolve to the static's place records
//! `static_memory_read_unseeded_view` (SoundHavoc).

#![allow(unused, static_mut_refs)]
use std::ptr::addr_of;

struct P {
    x: u8,
    y: u32,
}
static SP: P = P { x: 1, y: 10 };

#[kani::proof]
fn bug_flat_reordered() {
    assert!(SP.x == 10);
}

#[kani::proof]
fn safe_flat_reordered() {
    assert!(SP.x == 1 && SP.y == 10);
}

struct Inner {
    b: u16,
    c: u32,
}
struct Outer {
    a: u8,
    inner: Inner,
}
static OO: Outer = Outer { a: 1, inner: Inner { b: 2, c: 3 } };
static mut MO: Outer = Outer { a: 1, inner: Inner { b: 2, c: 3 } };

#[kani::proof]
fn bug_nested_direct() {
    assert!(OO.inner.c == 1);
}

#[kani::proof]
fn safe_nested_direct() {
    assert!(OO.inner.c == 3 && OO.a == 1 && OO.inner.b == 2);
}

#[kani::proof]
fn bug_nested_mut_direct() {
    assert!(unsafe { MO.inner.c } == 1);
}

#[kani::proof]
fn safe_nested_mut_direct() {
    assert!(unsafe { MO.inner.c } == 3 && unsafe { MO.a } == 1);
}

#[kani::proof]
fn bug_nested_field_addr() {
    let p = addr_of!(OO.inner.c);
    assert!(unsafe { *p } == 4);
}

#[kani::proof]
fn safe_nested_field_addr() {
    let p = addr_of!(OO.inner.c);
    assert!(unsafe { *p } == 3);
}

#[derive(Clone, Copy)]
struct T3 {
    a: u8,
    b: u32,
    c: u8,
}
static AT: [T3; 2] = [T3 { a: 1, b: 10, c: 2 }, T3 { a: 3, b: 30, c: 4 }];

#[kani::proof]
fn bug_arr_reordered_direct() {
    assert!(AT[1].b == 3);
}

#[kani::proof]
fn safe_arr_reordered_direct() {
    assert!(AT[1].a == 3 && AT[1].b == 30 && AT[1].c == 4 && AT[0].c == 2);
}

#[derive(Clone, Copy)]
struct Q {
    x: u8,
    y: u32,
}
static AQ: [Q; 2] = [Q { x: 1, y: 10 }, Q { x: 2, y: 20 }];
static mut AM: [Q; 2] = [Q { x: 1, y: 10 }, Q { x: 2, y: 20 }];

#[kani::proof]
fn bug_arr_struct_field_sym() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let p = addr_of!(AQ) as *const Q;
    let v = unsafe { (*p.add(i)).y };
    assert!(v == 10);
}

#[kani::proof]
fn safe_arr_struct_field_sym() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let p = addr_of!(AQ) as *const Q;
    let v = unsafe { (*p.add(i)).y };
    assert!(v == 10 || v == 20);
}

#[kani::proof]
fn bug_arr_struct_elem_store_field_read() {
    unsafe { AM[0] = Q { x: 3, y: 30 }; }
    let i: usize = kani::any();
    kani::assume(i < 2);
    let p = unsafe { addr_of!(AM) } as *const Q;
    let v = unsafe { (*p.add(i)).y };
    assert!(v == 30);
}

#[kani::proof]
fn safe_arr_struct_elem_store_field_read() {
    unsafe { AM[0] = Q { x: 3, y: 30 }; }
    let i: usize = kani::any();
    kani::assume(i < 2);
    let p = unsafe { addr_of!(AM) } as *const Q;
    let v = unsafe { (*p.add(i)).y };
    assert!(v == 30 || v == 20);
}

// Fields read through a pointer loaded out of another value.
#[derive(Clone, Copy)]
struct S {
    a: u32,
    b: u32,
}
#[derive(Clone, Copy)]
struct O2 {
    x: u32,
    inner: S,
}
static GO: O2 = O2 { x: 5, inner: S { a: 6, b: 7 } };
static GAS: [S; 2] = [S { a: 1, b: 2 }, S { a: 3, b: 4 }];
static GT: (u8, u32) = (8, 9);
struct H<T> {
    p: *const T,
    n: u8,
}

#[kani::proof]
fn bug_loaded_nested_field() {
    let h = H { p: addr_of!(GO), n: 1 };
    assert!(unsafe { (*h.p).inner.b } == 6);
}

#[kani::proof]
fn safe_loaded_nested_field() {
    let h = H { p: addr_of!(GO), n: 1 };
    assert!(unsafe { (*h.p).inner.b } == 7);
}

#[kani::proof]
fn bug_loaded_nested_whole() {
    let h = H { p: addr_of!(GO), n: 1 };
    let s = unsafe { (*h.p).inner };
    assert!(s.a == 7);
}

#[kani::proof]
fn safe_loaded_nested_whole() {
    let h = H { p: addr_of!(GO), n: 1 };
    let s = unsafe { (*h.p).inner };
    assert!(s.a == 6 && s.b == 7);
}

#[kani::proof]
fn bug_loaded_elem_ptr_field() {
    let h = H { p: addr_of!(GAS), n: 1 };
    let q = h.p as *const S;
    assert!(unsafe { (*q.add(1)).b } == 3);
}

#[kani::proof]
fn safe_loaded_elem_ptr_field() {
    let h = H { p: addr_of!(GAS), n: 1 };
    let q = h.p as *const S;
    assert!(unsafe { (*q.add(1)).b } == 4);
}

#[kani::proof]
fn bug_loaded_tuple_field() {
    let h = H { p: addr_of!(GT), n: 1 };
    assert!(unsafe { (*h.p).1 } == 8);
}

#[kani::proof]
fn safe_loaded_tuple_field() {
    let h = H { p: addr_of!(GT), n: 1 };
    assert!(unsafe { (*h.p).1 } == 9 && unsafe { (*h.p).0 } == 8);
}

// An enum's variants are not decomposed in the image. A payload read through a
// borrow chain of the static's own place resolves to its state variable: an
// enum initializer with a payload is not decoded (the harness is demoted as
// `static_init_incomplete`), and after a store the state variable is exact.
// Through a pointer loaded out of a struct field it reads the image: fail
// closed.
static EO: Option<u32> = Some(5);
static mut ES: Option<u32> = None;
static mut ET: Option<u32> = None;

#[kani::proof]
fn bug_enum_payload_via_ref() {
    let p = addr_of!(EO);
    if let Some(v) = unsafe { &*p } {
        assert!(*v == 6);
    }
}

#[kani::proof]
fn safe_enum_payload_via_ref() {
    let p = addr_of!(EO);
    if let Some(v) = unsafe { &*p } {
        assert!(*v == 5);
    }
}

#[kani::proof]
fn bug_enum_payload_after_store_direct() {
    unsafe { ES = Some(5); }
    let p = unsafe { addr_of!(ES) };
    if let Some(v) = unsafe { &*p } {
        assert!(*v == 6);
    }
}

#[kani::proof]
fn safe_enum_payload_after_store_direct() {
    unsafe { ES = Some(5); }
    let p = unsafe { addr_of!(ES) };
    if let Some(v) = unsafe { &*p } {
        assert!(*v == 5);
    }
}

struct EHolder {
    p: *const Option<u32>,
    n: u8,
}

#[kani::proof]
fn bug_enum_payload_after_store_carried() {
    unsafe { ET = Some(5); }
    let h = EHolder { p: unsafe { addr_of!(ET) }, n: 1 };
    if let Some(v) = unsafe { &*h.p } {
        assert!(*v == 6);
    }
}

#[kani::proof]
fn safe_enum_payload_after_store_carried() {
    unsafe { ET = Some(5); }
    let h = EHolder { p: unsafe { addr_of!(ET) }, n: 1 };
    if let Some(v) = unsafe { &*h.p } {
        assert!(*v == 5);
    }
}

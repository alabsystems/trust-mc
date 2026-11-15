// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A flattened `Option<*mut T>` carries the POINTER, not the pointee.
//
// The BMC lane's flattened-Option encoding (codegen_assign_flatten.rs) reads a
// `Some(p)` payload through `get_value_through_ref`, which also dereferences a
// RAW pointer, and sizes the None base by the pointee (`value_payload_width`).
// Measured 2026-09-14 on the frozen dev-cli lane (bundle built from 0f62a10e0):
//  * `bug_some_rawptr_distinct_eq` — `Some(&mut a) == Some(&mut b)` with equal
//    pointees — was PROVED: a missed bug (Kani FAILS it);
//  * `safe_some_rawptr_roundtrip` compared the pointee 10, zero-extended, with
//    the pointer and FAILED certified Genuine;
//  * `safe_some_null_rawptr` dereferenced the null payload and FAILED Genuine.
//
// Oracles: `safe_*` MUST be SUCCESSFUL; `bug_*` MUST FAIL.

#[kani::proof]
fn bug_some_rawptr_distinct_eq() {
    let mut a: i32 = 10;
    let mut b: i32 = 10;
    let p: *mut i32 = &mut a;
    let q: *mut i32 = &mut b;
    let x: Option<*mut i32> = Some(p);
    let y: Option<*mut i32> = Some(q);
    assert!(x == y); // p != q: Kani FAILED
}

#[kani::proof]
fn bug_some_rawptr_distinct_match() {
    let mut a: i32 = 10;
    let mut b: i32 = 10;
    let p: *mut i32 = &mut a;
    let q: *mut i32 = &mut b;
    let x: Option<*mut i32> = Some(p);
    if let Some(r) = x {
        assert!(r == q); // r == p != q: Kani FAILED
    }
}

#[kani::proof]
fn safe_some_rawptr_roundtrip() {
    let mut a: i32 = 10;
    let p: *mut i32 = &mut a;
    let x: Option<*mut i32> = Some(p);
    match x {
        Some(r) => assert!(r == p),
        None => unreachable!(),
    }
}

#[kani::proof]
fn safe_some_null_rawptr() {
    let n: *mut i32 = core::ptr::null_mut();
    let x: Option<*mut i32> = Some(n);
    assert!(x.is_some());
}

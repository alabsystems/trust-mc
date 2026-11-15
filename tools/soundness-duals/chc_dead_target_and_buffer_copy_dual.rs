// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: two holes the self-review of round 10 of
// fix/chc-false-certificates found while probing the typed-store lowering of
// one-element copies, the same on main f5dfb8d48 (2026-10-15).
// - A copy through `Vec::as_mut_ptr`'s pointer: the chain walk read the call
//   as an identity hop (its path contains "mut_ptr") and the ref target named
//   the Vec local, so the copy lane spliced the bytes into the Vec handle while
//   `v[0]` kept its old value: `bug_copy_into_vec_buffer_then_index` a clean
//   proof, `safe_copy_into_vec_buffer_then_index` a certified false
//   counterexample. The raw-pointer method test now reads the module path, and
//   the copy lane refuses a collection or smart-pointer local as the target of
//   a pointer to something else.
// - A store, a `ptr::write` or a copy through a raw pointer to a local whose
//   storage is dead: the load side failed such a dereference since #762, the
//   store side wrote the dead local's register (clean proofs where Kani reports
//   a dangling write). It now fails as the load does.
// The safe rows below the bug rows check that the new store check does not
// fire on a pointer re-pointed at a live local, a local of a loop body, or a
// pointer that outlives only a reborrow's scope.

use std::ptr;

#[kani::proof]
fn bug_copy_into_vec_buffer_then_index() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    let x: u32 = 9;
    unsafe { ptr::copy_nonoverlapping(&x, p, 1) };
    assert!(v[0] == 1);
}

#[kani::proof]
fn safe_copy_into_vec_buffer_then_index() {
    let mut v = vec![1u32, 2];
    let p = v.as_mut_ptr();
    let x: u32 = 9;
    unsafe { ptr::copy_nonoverlapping(&x, p, 1) };
    assert!(v[0] == 9 && v[1] == 2);
}

#[kani::proof]
fn bug_store_through_pointer_to_dead_local() {
    let p: *mut u32;
    {
        let mut z: u32 = 0;
        p = &mut z;
    }
    unsafe { *p = 1 };
}

#[kani::proof]
fn bug_copy_through_pointer_to_dead_local() {
    let p: *mut u32;
    {
        let mut z: u32 = 0;
        p = &mut z;
    }
    let x: u32 = 1;
    unsafe { ptr::copy_nonoverlapping(&x, p, 1) };
}

#[kani::proof]
fn bug_write_through_pointer_to_dead_local() {
    let p: *mut u32;
    {
        let mut z: u32 = 0;
        p = &mut z;
    }
    unsafe { ptr::write(p, 1) };
}

#[kani::proof]
fn bug_read_through_pointer_to_dead_local() {
    let p: *const u32;
    {
        let z: u32 = 0;
        p = &z;
    }
    let v = unsafe { *p };
    assert!(v == v);
}

#[kani::proof]
fn safe_store_through_repointed_pointer() {
    let mut a: u32 = 5;
    let mut p: *mut u32 = &mut a;
    {
        let mut z: u32 = 0;
        p = &mut z;
        unsafe { *p = 1 };
        assert!(z == 1);
    }
    p = &mut a;
    unsafe { *p = 2 };
    assert!(a == 2);
}

#[kani::proof]
fn safe_copy_through_repointed_pointer() {
    let mut a: u32 = 5;
    let mut p: *mut u32 = &mut a;
    {
        let mut z: u32 = 0;
        p = &mut z;
        unsafe { ptr::copy_nonoverlapping(&7u32, p, 1) };
        assert!(z == 7);
    }
    p = &mut a;
    unsafe { ptr::copy_nonoverlapping(&9u32, p, 1) };
    assert!(a == 9);
}

#[kani::proof]
#[kani::unwind(4)]
fn safe_store_through_pointer_to_loop_local() {
    let mut s = 0u32;
    for i in 0..3u32 {
        let mut z: u32 = 0;
        let p = &mut z as *mut u32;
        unsafe { *p = i };
        s += z;
    }
    assert!(s == 3);
}

#[kani::proof]
fn safe_store_after_reborrow_scope() {
    struct S {
        x: u32,
    }
    let mut s = S { x: 0 };
    let q: *mut u32;
    {
        let r = &mut s;
        q = &mut r.x;
    }
    unsafe { *q = 4 };
    assert!(s.x == 4);
}

#[kani::proof]
fn safe_store_through_pointer_from_helper() {
    fn id(p: *mut u32) -> *mut u32 {
        p
    }
    let mut a: u32 = 1;
    let p = {
        let t = &mut a as *mut u32;
        id(t)
    };
    unsafe { *p = 3 };
    assert!(a == 3);
}

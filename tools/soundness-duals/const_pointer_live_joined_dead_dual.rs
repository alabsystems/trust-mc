// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own memory-safety check):
//   safe_joined_static_or_live_local          -> VERIFICATION:- SUCCESSFUL
//   bug_joined_static_or_dead_local           -> VERIFICATION:- FAILED (dereference failure: dead object)
//   bug_joined_dead_local_or_static           -> VERIFICATION:- FAILED (dereference failure: dead object)
//   bug_reassigned_static_then_dead_local     -> VERIFICATION:- FAILED (dereference failure: dead object)
//   bug_dead_local_then_maybe_static          -> VERIFICATION:- FAILED (dereference failure: dead object)
//   safe_joined_atomic_static_or_live_local   -> VERIFICATION:- SUCCESSFUL
//   bug_joined_atomic_static_or_dead_local    -> VERIFICATION:- FAILED (dereference failure: dead object; dereference failure: pointer invalid)
//   bug_joined_atomic_dead_local_or_static    -> VERIFICATION:- FAILED (dereference failure: dead object; dereference failure: pointer invalid)
//   safe_atomic_static_then_live_local_store  -> VERIFICATION:- SUCCESSFUL
//   bug_atomic_static_then_dead_local_store   -> VERIFICATION:- FAILED (dereference failure: dead object; dereference failure: pointer invalid)
//
// WHY THIS FILE EXISTS. A pointer joined from a static's address on one path
// and a scoped local's on another must not be read after the local dies. The
// u32 shapes fail closed; the atomic one proved clean on the CHC lane on
// every bundle (round-2 review of fix/chc-atomic-as-ptr-live): the reborrow
// `&(*p)` behind `(*p).load()` resolved one producer's referent through its
// `ref_targets` edge (the static, which never dies), and the joined-pointer
// walk that decides the other path ran only for a pointer with no edge.
#![allow(dead_code, static_mut_refs, unused_assignments)]
use std::sync::atomic::{AtomicU32, Ordering};

static V: u32 = 7;
static A: AtomicU32 = AtomicU32::new(5);

#[kani::proof]
fn safe_joined_static_or_live_local() {
    let c: bool = kani::any();
    let x: u32 = 3;
    let p: *const u32 = if c { &V } else { &x };
    let v = unsafe { *p };
    assert!(v == 7 || v == 3);
}
#[kani::proof]
fn bug_joined_static_or_dead_local() {
    let c: bool = kani::any();
    let p: *const u32;
    if c {
        p = &V;
    } else {
        let x: u32 = 3;
        p = &x;
    }
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_joined_dead_local_or_static() {
    let c: bool = kani::any();
    let p: *const u32;
    if c {
        let x: u32 = 3;
        p = &x;
    } else {
        p = &V;
    }
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_reassigned_static_then_dead_local() {
    let mut p: *const u32 = &V;
    {
        let x: u32 = 3;
        p = &x;
    }
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn bug_dead_local_then_maybe_static() {
    let c: bool = kani::any();
    let mut p: *const u32;
    {
        let x: u32 = 3;
        p = &x;
    }
    if c {
        p = &V;
    }
    let v = unsafe { *p };
    assert!(v == v);
}
#[kani::proof]
fn safe_joined_atomic_static_or_live_local() {
    let c: bool = kani::any();
    let x = AtomicU32::new(3);
    let p: *const AtomicU32 = if c { &A } else { &x };
    let v = unsafe { (*p).load(Ordering::SeqCst) };
    assert!(v == 5 || v == 3);
}
#[kani::proof]
fn bug_joined_atomic_static_or_dead_local() {
    let c: bool = kani::any();
    let p: *const AtomicU32;
    if c {
        p = &A;
    } else {
        let x = AtomicU32::new(3);
        p = &x;
    }
    let v = unsafe { (*p).load(Ordering::SeqCst) };
    assert!(v == v);
}
#[kani::proof]
fn bug_joined_atomic_dead_local_or_static() {
    let c: bool = kani::any();
    let p: *const AtomicU32;
    if c {
        let x = AtomicU32::new(3);
        p = &x;
    } else {
        p = &A;
    }
    let v = unsafe { (*p).load(Ordering::SeqCst) };
    assert!(v == v);
}
#[kani::proof]
fn safe_atomic_static_then_live_local_store() {
    let x = AtomicU32::new(3);
    let mut p: *const AtomicU32 = &A;
    if kani::any() {
        p = &x;
    }
    unsafe { (*p).store(9, Ordering::SeqCst) };
    assert!(A.load(Ordering::SeqCst) == 9 || x.load(Ordering::SeqCst) == 9);
}
#[kani::proof]
fn bug_atomic_static_then_dead_local_store() {
    let mut p: *const AtomicU32 = &A;
    {
        let x = AtomicU32::new(3);
        if kani::any() {
            p = &x;
        }
    }
    unsafe { (*p).store(9, Ordering::SeqCst) };
}

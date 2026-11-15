// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_* -> VERIFICATION:- SUCCESSFUL
//   bug_*  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS (design trust-mc-reds-final §3, Rule A, test A2).
// The Trust standard library declares
// `Atomic<T: AtomicPrimitive> { v: UnsafeCell<T::Storage> }`, so the type of
// an atomic's one field is an associated-type projection of the ADT's own
// parameter. Read through a shallow substitution (only a top-level `Param`
// replaced), it stays `UnsafeCell<<T as AtomicPrimitive>::Storage>`: an
// `Alias` with a parameter inside, which the sort translation cannot read and
// which every rustc query that normalizes panics on. A field's type must be
// instantiated at the ADT's own arguments and normalized
// (`shared::mono_ty::field_ty`), or refused.
//
// Local atomics, one read-modify-write each: an integer `fetch_add`, a `bool`
// `swap`, and a pointer `compare_exchange`. Every harness has nondeterministic
// input, so a vacuous encoding cannot pass the bug twins.

use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, Ordering};

#[kani::proof]
fn safe_fetch_add() {
    let v: u32 = kani::any();
    kani::assume(v < 1000);
    let a = AtomicU32::new(v);
    let old = a.fetch_add(3, Ordering::SeqCst);
    assert!(old == v);
    assert!(a.load(Ordering::SeqCst) == v + 3);
}

#[kani::proof]
fn bug_fetch_add() {
    let v: u32 = kani::any();
    kani::assume(v < 1000);
    let a = AtomicU32::new(v);
    a.fetch_add(3, Ordering::SeqCst);
    assert!(a.load(Ordering::SeqCst) == v);
}

#[kani::proof]
fn safe_bool_swap() {
    let b0: bool = kani::any();
    let b = AtomicBool::new(b0);
    let old = b.swap(!b0, Ordering::SeqCst);
    assert!(old == b0);
    assert!(b.load(Ordering::SeqCst) == !b0);
}

#[kani::proof]
fn bug_bool_swap() {
    let b0: bool = kani::any();
    let b = AtomicBool::new(b0);
    b.swap(!b0, Ordering::SeqCst);
    assert!(b.load(Ordering::SeqCst) == b0);
}

#[kani::proof]
fn safe_ptr_cas() {
    let mut x: u32 = kani::any();
    let mut y: u32 = 7;
    let px: *mut u32 = &mut x;
    let py: *mut u32 = &mut y;
    let p = AtomicPtr::new(px);
    let r = p.compare_exchange(px, py, Ordering::SeqCst, Ordering::SeqCst);
    assert!(r == Ok(px));
    assert!(p.load(Ordering::SeqCst) == py);
}

#[kani::proof]
fn bug_ptr_cas() {
    let mut x: u32 = kani::any();
    let mut y: u32 = 7;
    let px: *mut u32 = &mut x;
    let py: *mut u32 = &mut y;
    let p = AtomicPtr::new(px);
    let _ = p.compare_exchange(px, py, Ordering::SeqCst, Ordering::SeqCst);
    assert!(p.load(Ordering::SeqCst) == px);
}

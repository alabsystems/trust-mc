// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: Some harnesses (1/4) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// NOTE: check_atomicptr_cmpxchg_basic gained PROOF at ay 8a4a9bcc2.
// Test AtomicPtr compare_exchange with pointer-sort (BV64) encoding.
// Part of #3492: AtomicPtr pointer provenance operations.
//
// NOTE: load-after-compare_exchange (store chain propagation through
// repr(transparent) memory) is a separate limitation — not tested here.

use std::sync::atomic::{AtomicPtr, Ordering};

/// Basic AtomicPtr compare_exchange: expected matches, swap succeeds.
#[kani::proof]
fn check_atomicptr_cmpxchg_basic() {
    let mut val: i32 = 42;
    let ptr: *mut i32 = &mut val;
    let atom = AtomicPtr::new(ptr);
    let result =
        atom.compare_exchange(ptr, core::ptr::null_mut(), Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_ok());
}

/// AtomicPtr compare_exchange Result is_ok extraction + unwrap.
#[kani::proof]
fn check_atomicptr_cmpxchg_is_ok() {
    let mut val: i32 = 10;
    let ptr: *mut i32 = &mut val;
    let atom = AtomicPtr::new(ptr);
    let result =
        atom.compare_exchange(ptr, core::ptr::null_mut(), Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_ok());
    let old = result.unwrap();
    assert!(old == ptr);
}

/// AtomicPtr compare_exchange failure path: expected does not match current.
/// Uses kani::any() to choose between matching and non-matching expected,
/// verifying both Ok and Err paths symbolically. (#3501)
#[kani::proof]
fn check_atomicptr_cmpxchg_symbolic_path() {
    let mut val_a: i32 = 1;
    let mut val_b: i32 = 2;
    let ptr_a: *mut i32 = &mut val_a;
    let ptr_b: *mut i32 = &mut val_b;

    let atom = AtomicPtr::new(ptr_a);
    let use_matching: bool = kani::any();

    let expected = if use_matching { ptr_a } else { ptr_b };
    let result =
        atom.compare_exchange(expected, core::ptr::null_mut(), Ordering::SeqCst, Ordering::SeqCst);

    if use_matching {
        assert!(result.is_ok());
    } else {
        // When expected != current, compare_exchange must fail
        assert!(result.is_err());
    }
}

/// AtomicPtr compare_exchange Err variant: unwrap_err returns the current value.
/// Validates the Err payload, not just is_err(). (#3501)
#[kani::proof]
fn check_atomicptr_cmpxchg_err_payload() {
    let mut val_a: i32 = 1;
    let mut val_b: i32 = 2;
    let ptr_a: *mut i32 = &mut val_a;
    let ptr_b: *mut i32 = &mut val_b;

    let atom = AtomicPtr::new(ptr_a);
    // expected (ptr_b) != current (ptr_a), so this must fail
    let result =
        atom.compare_exchange(ptr_b, core::ptr::null_mut(), Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    let current = result.unwrap_err();
    assert!(current == ptr_a);
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Diagnostic harness: CAS Result PartialEq encoding gap.
//
// Root cause investigation: compare_exchange Err path + PartialEq::eq (`==`)
// produces Genuine CTREX. The bug is:
// - CAS-specific (non-CAS Result PartialEq works)
// - Err-variant specific (Ok path always passes)
// - Type-independent (affects u8, u16, bool)
// - MIR-shape dependent (same code can pass in different compilation units)
// - Decomposed checks work (is_err + unwrap_err + scalar eq)
//
// Affects: compare_exchange_failure.rs (2 Kani regression harnesses)
// Part of #3768
//
// kani-expect: PROOF
// kani-expect: check_cmpxchg_u8_ne_ok=UNKNOWN
// NOTE: 1 harness(es) demoted PROOF→UNKNOWN by false proof defense (ay#8578).

use std::sync::atomic::{AtomicU8, Ordering};

/// Pure Result<u8, u8> Err comparison — no atomics.
#[kani::proof]
fn check_pure_result_u8_err_eq() {
    let r: Result<u8, u8> = Err(0u8);
    assert!(r == Err(0u8));
}

/// Pure Result<u8, u8> Ok comparison — no atomics.
#[kani::proof]
fn check_pure_result_u8_ok_eq() {
    let r: Result<u8, u8> = Ok(42u8);
    assert!(r == Ok(42u8));
}

/// CAS failure path with AtomicU8 — matches compare_exchange_failure.rs.
#[kani::proof]
fn check_cmpxchg_u8_err_eq() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Err(0));
}

/// CAS success path with AtomicU8.
#[kani::proof]
fn check_cmpxchg_u8_ok_eq() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(0));
}

/// Decomposed CAS failure: test is_err + unwrap_err separately.
#[kani::proof]
fn check_cmpxchg_u8_decomposed() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert!(result.unwrap_err() == 0);
}

/// CAS failure with let-bound Err (not inline temporary).
#[kani::proof]
fn check_cmpxchg_u8_err_let_bound() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst);
    let expected: Result<u8, u8> = Err(0);
    assert!(result == expected);
}

/// CAS failure: pattern match instead of PartialEq.
#[kani::proof]
fn check_cmpxchg_u8_err_match() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst);
    match result {
        Err(v) => assert!(v == 0),
        Ok(_) => panic!("should be Err"),
    }
}

/// CAS failure with != Ok instead of == Err.
#[kani::proof]
fn check_cmpxchg_u8_ne_ok() {
    let a = AtomicU8::new(0);
    let result = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result != Ok(0));
}

/// Non-atomic Result<u8,u8> from a function (not CAS).
#[kani::proof]
fn check_fn_result_u8_err_eq() {
    fn make_err() -> Result<u8, u8> {
        Err(0)
    }
    let result = make_err();
    assert!(result == Err(0));
}

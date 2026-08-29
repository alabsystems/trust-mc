// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Diagnostic harness: CAS Result PartialEq across multiple atomic types.
//
// Verifies that the flattened enum field decomposition (Part of #3963) works
// for AtomicU8, AtomicU16, AtomicU32, AtomicBool, and AtomicI8 — not just
// the originally-fixed AtomicU8 case.
//
// kani-expect: check_cas_u16_err_eq=PROOF
// kani-expect: check_cas_u16_ok_eq=PROOF
// kani-expect: check_cas_u32_err_eq=PROOF
// kani-expect: check_cas_u32_ok_eq=PROOF
// kani-expect: check_cas_bool_err_eq=PROOF
// kani-expect: check_cas_bool_ok_eq=PROOF
// kani-expect: check_cas_i8_err_eq=PROOF
// kani-expect: check_cas_i8_ok_eq=PROOF

use std::sync::atomic::{AtomicBool, AtomicI8, AtomicU16, AtomicU32, Ordering};

// --- AtomicU16 ---

#[kani::proof]
fn check_cas_u16_err_eq() {
    let a = AtomicU16::new(100);
    let result = a.compare_exchange(200, 300, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Err(100));
}

#[kani::proof]
fn check_cas_u16_ok_eq() {
    let a = AtomicU16::new(100);
    let result = a.compare_exchange(100, 200, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(100));
}

// --- AtomicU32 ---

#[kani::proof]
fn check_cas_u32_err_eq() {
    let a = AtomicU32::new(1000);
    let result = a.compare_exchange(2000, 3000, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Err(1000));
}

#[kani::proof]
fn check_cas_u32_ok_eq() {
    let a = AtomicU32::new(1000);
    let result = a.compare_exchange(1000, 2000, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(1000));
}

// --- AtomicBool ---

#[kani::proof]
fn check_cas_bool_err_eq() {
    let a = AtomicBool::new(true);
    let result = a.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Err(true));
}

#[kani::proof]
fn check_cas_bool_ok_eq() {
    let a = AtomicBool::new(true);
    let result = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(true));
}

// --- AtomicI8 (signed) ---

#[kani::proof]
fn check_cas_i8_err_eq() {
    let a = AtomicI8::new(-1);
    let result = a.compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Err(-1));
}

#[kani::proof]
fn check_cas_i8_ok_eq() {
    let a = AtomicI8::new(-1);
    let result = a.compare_exchange(-1, 0, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result == Ok(-1));
}

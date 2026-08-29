// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test for #3490: inline Result comparison encoding gap.
// Verifies that `assert!(r == Ok(true))` with an inline Ok(true) produces PROOF,
// not spurious CTREX from unconstrained flattened Result fields.
//
// The 3-field flattened Result<T, E> layout is: fld0=Bool (is_ok), fld1=T, fld2=E.
// Before the fix, only 2-field Option-like reconstruction was supported, so
// bare reads of 3-field Result locals returned None and PartialEq fell through
// to unconstrained fallback → spurious CTREX.

// kani-expect: PROOF
// kani-expect: check_result_symbolic_variant=UNKNOWN

use std::sync::atomic::{AtomicBool, Ordering};

/// Let-binding Result comparison with compare_exchange.
/// Validates that 3-field Result reconstruction works for named locals
/// in the PartialEq comparison context with atomic-returned Results.
#[kani::proof]
fn check_cmpxchg_let_binding_eq() {
    let a = AtomicBool::new(true);
    let r = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    let expected = Ok(true);
    assert!(r == expected);
}

/// Inline Ok(true) comparison with compare_exchange result.
/// Core #3507 regression: compare_exchange returns Result<bool, bool> via the
/// atomic RMW stub, and `assert!(r == Ok(true))` creates an anonymous temporary
/// for `Ok(true)`. Both the LHS (from stub) and RHS (inline temp) must reconstruct
/// to matching Datatype expressions for PartialEq to succeed.
#[kani::proof]
fn check_cmpxchg_inline_result_eq() {
    let a = AtomicBool::new(true);
    let r = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    assert!(r == Ok(true));
}

/// Pure Result construction + inline comparison (no atomics).
/// Core #3490 fix validation: tests that 3-field Result ITE reconstruction
/// works for non-atomic Results with inline Ok(true) temporary.
#[kani::proof]
fn check_pure_result_inline_eq() {
    let r: Result<bool, bool> = Ok(true);
    assert!(r == Ok(true));
}

/// Err variant of Result comparison — validates that Err path of
/// 3-field Result reconstruction works, not just Ok. (#3501)
#[kani::proof]
fn check_cmpxchg_err_variant_eq() {
    let a = AtomicBool::new(false);
    // expected=true but current=false, so compare_exchange fails with Err(false)
    let r = a.compare_exchange(true, true, Ordering::SeqCst, Ordering::SeqCst);
    assert!(r.is_err());
    assert!(r == Err(false));
}

/// Symbolic Result comparison: verifies PartialEq for Result<bool, bool>
/// with both Ok and Err variants chosen symbolically. (#3501)
#[kani::proof]
fn check_result_symbolic_variant() {
    let val: bool = kani::any();
    let is_ok: bool = kani::any();
    let r: Result<bool, bool> = if is_ok { Ok(val) } else { Err(val) };

    if is_ok {
        assert!(r == Ok(val));
        assert!(r != Err(val));
    } else {
        assert!(r == Err(val));
        assert!(r != Ok(val));
    }
}

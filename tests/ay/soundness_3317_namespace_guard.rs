// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Soundness test for #3317: namespace guards on string-dispatch matching.
//!
//! Verifies that user functions whose names contain substrings matching Kani
//! internal functions (e.g., "any_raw_internal") are NOT misrouted to Kani
//! model handlers. Before the #3317 fix, this function would be dispatched
//! to `KaniModel::Any`, replacing its return value with an unconstrained
//! symbolic value and producing a false PROOF.

/// User function with "any_raw_internal" substring in its name.
/// Must return its actual value (42), not be replaced by a symbolic value.
fn check_any_raw_internal_state() -> u32 {
    42
}

#[kani::proof]
fn test_namespace_guard_any_raw_internal() {
    let result = check_any_raw_internal_state();
    // If the namespace guard is missing, this function gets routed to
    // KaniModel::Any and `result` becomes an unconstrained symbolic u32.
    // The assert would PROOF vacuously (symbolic can be anything).
    // With the guard, the function returns 42 deterministically.
    assert!(result == 42);
}

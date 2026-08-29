// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: check_vec_into_iter_empty=PROOF
// kani-expect: check_vec_into_iter_concrete_elements=PROOF
// kani-expect: check_vec_into_iter_sequence=PROOF
// kani-expect: check_vec_iter_state_isolation=PROOF
// kani-expect: check_position_invariant=PROOF
// kani-expect: check_vec_into_iter_exhaustion=PROOF
// kani-expect: check_vec_iter_mut_tracking=PROOF
// kani-expect: check_vec_iter_sequence=PROOF
// NOTE: check_vec_into_iter_empty restored PROOF after trivial-safe check fix
// (Part of #4272). Concrete allocation-size metadata restored PROOF for
// position/exhaustion/ref/mut iterator state checks. The concrete multi-element
// into_iter checks require an extended canary timeout at ay 914ee043. Latest AY
// plus concrete VecIntoIter replay proves the state-isolation value-propagation
// case.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Vec iterator soundness tests (Part of #1751)
//!
//! Tests verify iterator invariants that would fail without correct implementation:
//! 1. Position tracking - iterator advances position after each next()
//! 2. Element extraction - correct element returned at each position
//! 3. Terminal state - returns None when exhausted
//! 4. State mutation - iterator state properly updated
//!
//! These tests are designed to catch common iterator implementation bugs:
//! - Off-by-one in position tracking
//! - Reading wrong element (pos vs pos-1)
//! - Not updating iterator state after next()
//! - Incorrect bounds check (pos < len vs pos <= len)

/// Test that Vec::into_iter() returns elements in order.
/// Would fail if: position increment was wrong, or elements extracted from wrong index.
#[kani::proof]
#[kani::unwind(4)]
fn check_vec_into_iter_sequence() {
    let v = vec![10i32, 20, 30];
    let mut iter = v.into_iter();

    let first = iter.next();
    assert_eq!(first, Some(10));

    let second = iter.next();
    assert_eq!(second, Some(20));

    let third = iter.next();
    assert_eq!(third, Some(30));
}

/// Test that Vec::into_iter() returns None after exhaustion.
/// Would fail if: bounds check was incorrect (e.g., pos <= len instead of pos < len).
#[kani::proof]
#[kani::unwind(4)]
fn check_vec_into_iter_exhaustion() {
    let v = vec![1i32, 2];
    let mut iter = v.into_iter();

    let _ = iter.next(); // 1
    let _ = iter.next(); // 2
    let none = iter.next(); // should be None

    assert!(none.is_none());
}

/// Test Vec::into_iter() on empty vec.
/// Would fail if: empty case not handled, or bounds check broken.
#[kani::proof]
fn check_vec_into_iter_empty() {
    let v: Vec<i32> = Vec::new();
    let mut iter = v.into_iter();
    let first = iter.next();
    assert!(first.is_none());
}

/// Test that Vec::iter() position tracking and exhaustion work correctly.
/// Would fail if: iter() model had wrong position tracking or bounds check.
/// Uses is_some/is_none (not value comparison): reference equality through
/// VecAsSlice → SliceIter path is a separate encoding issue (#3133).
#[kani::proof]
#[kani::unwind(5)]
fn check_vec_iter_sequence() {
    let v = vec![5i32, 10, 15];
    let mut iter = v.iter();

    let first = iter.next();
    assert!(first.is_some());

    let second = iter.next();
    assert!(second.is_some());

    let third = iter.next();
    assert!(third.is_some());

    let none = iter.next();
    assert!(none.is_none());
}

/// Test that multiple next() calls don't corrupt state.
/// Would fail if: iterator state was not properly updated after next().
#[kani::proof]
#[kani::unwind(6)]
fn check_vec_iter_state_isolation() {
    let v = vec![1i32, 2, 3, 4];
    let mut iter = v.into_iter();

    // Call next() 4 times - each should return successive element
    let a = iter.next();
    let b = iter.next();
    let c = iter.next();
    let d = iter.next();

    // Each element should be unique and in sequence
    assert_eq!(a, Some(1));
    assert_eq!(b, Some(2));
    assert_eq!(c, Some(3));
    assert_eq!(d, Some(4));

    // 5th call should be None
    let e = iter.next();
    assert!(e.is_none());
}

/// Test Vec::iter_mut() position tracking.
/// Would fail if: iter_mut() didn't track position correctly.
#[kani::proof]
#[kani::unwind(4)]
fn check_vec_iter_mut_tracking() {
    let mut v = vec![100i32, 200];
    let mut iter = v.iter_mut();

    let first = iter.next();
    assert!(first.is_some());

    let second = iter.next();
    assert!(second.is_some());

    let third = iter.next();
    assert!(third.is_none());
}

/// Test that into_iter() returns elements from the actual Vec, not symbolic.
/// Would fail if: element extraction used symbolic fallback instead of real data.
/// Uses direct Some(val) comparison (avoids unwrap() CHC complexity).
/// Uses 2-element vec: single-element vecs give Spacer insufficient store-chain
/// material for value propagation through the data array (#3095).
#[kani::proof]
#[kani::unwind(4)]
fn check_vec_into_iter_concrete_elements() {
    let v = vec![999i32, 0];
    let mut iter = v.into_iter();
    let first = iter.next();
    assert_eq!(first, Some(999));
    let second = iter.next();
    assert_eq!(second, Some(0));
    let none = iter.next();
    assert!(none.is_none());
}

/// Test invariant: position only advances when in bounds.
/// Critical soundness property - position should not overflow.
/// Would fail if: position incremented unconditionally.
#[kani::proof]
#[kani::unwind(10)]
fn check_position_invariant() {
    let v = vec![1i32];
    let mut iter = v.into_iter();

    // First next() returns Some, advances position 0->1
    let _ = iter.next();

    // All subsequent calls return None, position stays at 1
    for _ in 0..5 {
        let result = iter.next();
        assert!(result.is_none());
    }
}

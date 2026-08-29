// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: check_hashmap_iter_count=PROOF
// kani-expect: check_hashset_iter_count=PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Iterator membership invariant tests (Part of #1751)
//!
//! These tests verify that iterator implementations correctly enforce the
//! membership invariant: iterated keys must be members of the underlying collection.
//!
//! Without the membership invariant assertions in iter.rs:276-277 (HashMap) and
//! iter.rs:382-383 (HashSet), these tests would fail because:
//! - The symbolic `keys` array could contain keys not present in the collection
//! - The verifier could find counterexamples with impossible states
//!
//! The invariants assert:
//! - HashMap: forall i < len: map[keys[i]] is Some
//! - HashSet: forall i < len: set[keys[i]] = true

use std::collections::{HashMap, HashSet};

/// Test HashMap iterator membership: iterated keys must exist in map.
/// Would fail without invariant: solver could pick keys[0] not in map.
#[kani::proof]
#[kani::unwind(3)]
fn check_hashmap_iter_membership() {
    let mut map = HashMap::new();
    map.insert(10i32, 100i32);
    map.insert(20, 200);

    // Iterate and verify each key exists in map
    for (k, v) in map.into_iter() {
        // If membership invariant holds, this must succeed
        // Without invariant, k could be any symbolic value
        assert!(k == 10 || k == 20);
        assert!((k == 10 && v == 100) || (k == 20 && v == 200));
    }
}

/// Test HashSet iterator membership: iterated elements must be set members.
/// Would fail without invariant: solver could pick keys[0] not in set.
#[kani::proof]
#[kani::unwind(3)]
fn check_hashset_iter_membership() {
    let mut set = HashSet::new();
    set.insert(1i32);
    set.insert(2);

    // Iterate and verify each element was inserted
    for elem in set.into_iter() {
        // If membership invariant holds, this must succeed
        // Without invariant, elem could be any symbolic value
        assert!(elem == 1 || elem == 2);
    }
}

/// Test that HashMap iteration produces exactly the inserted key-value pairs.
/// This is stronger than membership - tests that values match keys.
#[kani::proof]
#[kani::unwind(2)]
fn check_hashmap_iter_value_binding() {
    let mut map = HashMap::new();
    map.insert(42i32, 99i32);

    let mut iter = map.into_iter();
    if let Some((k, v)) = iter.next() {
        // Key must be 42 (only key inserted)
        assert_eq!(k, 42);
        // Value must be 99 (the value for key 42)
        assert_eq!(v, 99);
    }
}

/// Test that single-element HashSet iteration returns that element.
#[kani::proof]
#[kani::unwind(2)]
fn check_hashset_iter_single_element() {
    let mut set = HashSet::new();
    set.insert(777i32);

    let mut iter = set.into_iter();
    let elem = iter.next();
    assert!(elem.is_some());
    assert_eq!(elem.unwrap(), 777);
}

/// Test HashMap iteration count matches insertion count.
/// Would fail without invariant: iteration could return more than inserted.
#[kani::proof]
#[kani::unwind(4)]
fn check_hashmap_iter_count() {
    let mut map = HashMap::new();
    map.insert(1i32, 10i32);
    map.insert(2, 20);

    let mut count = 0;
    for _ in map.into_iter() {
        count += 1;
    }
    assert!(count == 2);
}

/// Test HashSet iteration count matches insertion count.
#[kani::proof]
#[kani::unwind(4)]
fn check_hashset_iter_count() {
    let mut set = HashSet::new();
    set.insert(100i32);
    set.insert(200);

    let mut count = 0;
    for _ in set.into_iter() {
        count += 1;
    }
    assert!(count == 2);
}

/// Negative test: verify iterator does NOT return non-members.
/// This tests the membership invariant from the other direction.
#[kani::proof]
#[kani::unwind(3)]
fn check_hashset_iter_no_phantom_elements() {
    let mut set = HashSet::new();
    set.insert(5i32);
    // Note: 6 is NOT inserted

    for elem in set.into_iter() {
        // If we iterate any element, it MUST be 5
        // This would fail without invariant since keys[0] could be 6
        assert!(elem == 5);
    }
}

/// Test that HashMap iterator respects the key-value association.
/// Without membership invariant, map[keys[i]] could return wrong value.
#[kani::proof]
#[kani::unwind(3)]
fn check_hashmap_iter_key_value_consistency() {
    let mut map = HashMap::new();
    map.insert(1i32, 100i32);
    map.insert(2, 200);

    for (k, v) in map.into_iter() {
        // The value must correspond to the key
        let expected_v = if k == 1 { 100 } else if k == 2 { 200 } else { -1 };
        assert_eq!(v, expected_v);
    }
}

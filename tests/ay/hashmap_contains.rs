// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// NOTE: Most harnesses (6/7) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
// kani-flags: --ay-chc-track=mem
//
//! Phase 5 test: HashMap contains_key verification.
//!
//! This test verifies the contains_key semantics of HashMap with symbolic keys.
//! The property is simple but requires reasoning about HashMap state that
//! CBMC cannot handle efficiently with symbolic keys.
//!
//! Part of #471, #16 (Phase 5: BigInt/HashMap Verification)
//!
//! Phase 5 completion criteria (Test 4)
//!
//! ## Required Flags
//!
//! ```bash
//! target/release/trust_mc-driver -Z unstable-options --backend=ay --ay-chc tests/ay/hashmap_contains.rs
//! ```
//!
//! The `--ay-chc` flag enables CHC mode which intercepts HashMap operations via MIR stubbing.
//!
//! ## Success Criteria
//!
//! - trust_mc: Proves in <30s
//! - Kani/CBMC: Fails (OOM or timeout)

use std::collections::HashMap;

/// Verify contains_key returns true after insert.
///
/// This is the fundamental HashMap invariant: after inserting a key,
/// that key must be contained in the map.
///
/// **CBMC expected**: State explosion with symbolic key.
/// **trust_mc expected**: VERIFIED via functional HashMap model.
#[kani::proof]
fn verify_contains_after_insert() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    assert!(!map.contains_key(&k)); // Before insert
    map.insert(k, v);
    assert!(map.contains_key(&k)); // After insert
}

/// Verify contains_key returns false for non-inserted keys.
///
/// Tests the negative case: a key that was never inserted should
/// not be contained in the map.
#[kani::proof]
fn verify_not_contains_without_insert() {
    let map: HashMap<u32, u32> = HashMap::new();
    let k: u32 = kani::any();

    // Fresh map should not contain any key
    assert!(!map.contains_key(&k));
}

/// Verify contains_key is selective - insert k1, check k2.
///
/// Inserting one key should not cause other keys to be contained.
#[kani::proof]
fn verify_contains_selective() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v: u32 = kani::any();

    // Assume keys are different
    kani::assume(k1 != k2);

    map.insert(k1, v);

    // Property: inserting k1 makes k1 contained, but not k2
    assert!(map.contains_key(&k1));
    assert!(!map.contains_key(&k2));
}

/// Verify remove makes contains_key return false.
///
/// After removing a key, contains_key should return false for that key.
#[kani::proof]
fn verify_not_contains_after_remove() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    map.insert(k, v);
    assert!(map.contains_key(&k));

    map.remove(&k);
    assert!(!map.contains_key(&k));
}

/// Verify remove is selective - removing k1 doesn't affect k2.
#[kani::proof]
fn verify_remove_selective() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v: u32 = kani::any();

    kani::assume(k1 != k2);

    map.insert(k1, v);
    map.insert(k2, v);

    assert!(map.contains_key(&k1));
    assert!(map.contains_key(&k2));

    map.remove(&k1);

    // Property: removing k1 doesn't affect k2
    assert!(!map.contains_key(&k1));
    assert!(map.contains_key(&k2));
}

/// Verify is_empty semantics.
///
/// Empty map should be empty, map with one element should not be empty.
#[kani::proof]
fn verify_is_empty() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    assert!(map.is_empty());

    map.insert(k, v);
    assert!(!map.is_empty());

    map.remove(&k);
    assert!(map.is_empty());
}

/// Verify clear removes all keys.
#[kani::proof]
fn verify_clear() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v: u32 = kani::any();

    kani::assume(k1 != k2);

    map.insert(k1, v);
    map.insert(k2, v);

    assert!(!map.is_empty());
    assert!(map.contains_key(&k1));
    assert!(map.contains_key(&k2));

    map.clear();

    assert!(map.is_empty());
    assert!(!map.contains_key(&k1));
    assert!(!map.contains_key(&k2));
}

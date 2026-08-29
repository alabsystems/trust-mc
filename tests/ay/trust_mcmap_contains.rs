// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// kani-flags: --unstable=symbolic-collections
//
//! Phase 5 test: trust_mcMap verification-friendly HashMap.
//!
//! This test uses kani::hashmap::trust_mcMap instead of std::collections::HashMap.
//! trust_mcMap provides the same interface but uses marker functions that CHC codegen
//! can intercept, avoiding the hashbrown MIR inlining problem.
//!
//! Part of #788: HashMap verification via SMT Array theory.
//!
//! ## Required Flags
//!
//! ```bash
//! target/release/trust_mc-driver -Z unstable-options --backend=ay --ay-chc tests/ay/trust_mcmap_contains.rs
//! ```
//!
//! The `--ay-chc` flag is required to enable CHC mode which intercepts trust_mcMap operations.
//!
//! ## Success Criteria
//!
//! - trust_mc: Proves in <30s using SMT Array model
//! - No hashbrown internal calls (trust_mcMap doesn't use hashbrown)

extern crate kani;
use kani::hashmap::trust_mcMap;

/// Verify contains_key returns true after insert.
///
/// This is the fundamental map invariant: after inserting a key,
/// that key must be contained in the map.
#[kani::proof]
fn verify_trust_mcmap_contains_after_insert() {
    let mut map: trust_mcMap<u32, u32> = trust_mcMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    assert!(!map.contains_key(&k)); // Before insert
    map.insert(k, v);
    assert!(map.contains_key(&k)); // After insert
}

/// Verify contains_key returns false for non-inserted keys.
#[kani::proof]
fn verify_trust_mcmap_not_contains_without_insert() {
    let map: trust_mcMap<u32, u32> = trust_mcMap::new();
    let k: u32 = kani::any();

    // Fresh map should not contain any key
    assert!(!map.contains_key(&k));
}

/// Verify contains_key is selective - insert k1, check k2.
#[kani::proof]
fn verify_trust_mcmap_contains_selective() {
    let mut map: trust_mcMap<u32, u32> = trust_mcMap::new();
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
#[kani::proof]
fn verify_trust_mcmap_not_contains_after_remove() {
    let mut map: trust_mcMap<u32, u32> = trust_mcMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    map.insert(k, v);
    assert!(map.contains_key(&k));

    map.remove(&k);
    assert!(!map.contains_key(&k));
}

/// Verify remove is selective - removing k1 doesn't affect k2.
#[kani::proof]
fn verify_trust_mcmap_remove_selective() {
    let mut map: trust_mcMap<u32, u32> = trust_mcMap::new();
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

/// Verify trust_mcMap into_iter works (Part of #1812).
///
/// This test verifies the trust_mcMapIntoIter stub is intercepted.
#[kani::proof]
fn verify_trust_mcmap_into_iter_basic() {
    let mut map: trust_mcMap<u32, u32> = trust_mcMap::new();
    let k: u32 = kani::any();
    let v: u32 = kani::any();

    map.insert(k, v);

    // into_iter creates trust_mcMapIntoIter which CHC codegen models
    let mut iter = map.into_iter();

    // First call to next should return Some when map is non-empty
    // The actual key/value returned is symbolic (iterator state is modeled)
    let _first = iter.next();
}

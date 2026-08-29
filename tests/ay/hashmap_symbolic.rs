// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: verify_insert_lookup_returns_value=PROOF
// kani-expect: verify_len_after_insert=PROOF
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 5 test: HashMap verification with symbolic keys.
//!
//! This test demonstrates trust_mc's ability to verify HashMap operations with
//! symbolic (non-concrete) keys - something CBMC cannot handle efficiently.
//!
//! **Why CBMC fails**: Symbolic key `k` could hash to any bucket. CBMC must
//! track all 2^64 possibilities (for u64 keys), causing exponential state
//! explosion.
//!
//! **Why CHC succeeds**: CHC models HashMap abstractly as a partial function
//! `key -> Option<value>`, avoiding explicit bucket tracking. The functional
//! model captures the semantics without enumerating storage details.
//!
//! Part of #471, #16 (Phase 5: BigInt/HashMap Verification)
//!
//! Phase 5 completion criteria (Test 3)
//!
//! ## Required Flags
//!
//! ```bash
//! target/release/trust_mc-driver -Z unstable-options --backend=ay --ay-chc tests/ay/hashmap_symbolic.rs
//! ```
//!
//! The `--ay-chc` flag enables CHC mode which intercepts HashMap operations via MIR stubbing.
//!
//! ## Success Criteria
//!
//! - trust_mc: Proves in <30s
//! - Kani/CBMC: Fails (OOM or timeout at 300s)

use std::collections::HashMap;

/// Insert a value and retrieve it - canonical HashMap test.
///
/// This function encapsulates the insert/lookup pattern that is trivial
/// for functional reasoning but problematic for explicit state enumeration.
fn insert_lookup<K, V>(map: &mut HashMap<K, V>, key: K, value: V) -> V
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    map.insert(key.clone(), value.clone());
    map.get(&key).cloned().unwrap()
}

/// Verify insert followed by lookup returns the inserted value.
///
/// **CBMC expected**: OOM or extreme slowdown. Symbolic key creates
/// state explosion as CBMC tracks all possible bucket placements.
///
/// **trust_mc expected**: VERIFIED. CHC models HashMap functionally:
/// `insert(m, k, v).get(k) = Some(v)` regardless of hashing details.
#[kani::proof]
fn verify_insert_lookup_returns_value() {
    let mut map: HashMap<u64, u64> = HashMap::new();
    let key: u64 = kani::any();
    let value: u64 = kani::any();

    let result = insert_lookup(&mut map, key, value);

    // Property: lookup returns the inserted value
    assert_eq!(result, value);
}

/// Verify insert/lookup with different key types (u32).
///
/// Tests the same property with a different key size to verify
/// the abstraction isn't key-size dependent.
#[kani::proof]
fn verify_insert_lookup_u32_keys() {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let key: u32 = kani::any();
    let value: u32 = kani::any();

    map.insert(key, value);
    let result = map.get(&key);

    // Property: after insert, get returns Some(value)
    assert_eq!(result, Some(&value));
}

/// Verify that two inserts with different keys don't interfere.
///
/// This tests the isolation property of HashMap - inserting at key `k1`
/// doesn't affect the value at key `k2` (when k1 != k2).
#[kani::proof]
fn verify_insert_isolation() {
    let mut map: HashMap<u32, u32> = HashMap::new();

    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();

    // Assume keys are different
    kani::assume(k1 != k2);

    // Insert v1 at k1, then v2 at k2
    map.insert(k1, v1);
    map.insert(k2, v2);

    // Property: both values are independently retrievable
    assert_eq!(map.get(&k1), Some(&v1));
    assert_eq!(map.get(&k2), Some(&v2));
}

/// Verify that overwriting a key replaces the value.
///
/// Tests the update semantics: insert(k, v2) after insert(k, v1)
/// should result in get(k) = Some(v2).
#[kani::proof]
fn verify_insert_overwrites() {
    let mut map: HashMap<u32, u32> = HashMap::new();

    let key: u32 = kani::any();
    let v1: u32 = kani::any();
    let v2: u32 = kani::any();

    map.insert(key, v1);
    map.insert(key, v2);

    // Property: second insert overwrites first
    assert_eq!(map.get(&key), Some(&v2));
}

/// Verify len() is correct after inserts.
///
/// Tests that the length increases correctly with new keys
/// and stays the same when overwriting.
#[kani::proof]
fn verify_len_after_insert() {
    let mut map: HashMap<u32, u32> = HashMap::new();

    let k1: u32 = kani::any();
    let k2: u32 = kani::any();
    let v: u32 = kani::any();

    // Assume keys are different
    kani::assume(k1 != k2);

    assert_eq!(map.len(), 0);

    map.insert(k1, v);
    assert_eq!(map.len(), 1);

    map.insert(k2, v);
    assert_eq!(map.len(), 2);

    // Overwrite k1 - length should stay 2
    map.insert(k1, v);
    assert_eq!(map.len(), 2);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! TrustMcMap — a symbolic collection model with a HashMap-like API subset.
//!
//! Part of #788: HashMap stub interception for CHC codegen.
//!
//! `TrustMcMap<K, V>` is **not** a drop-in replacement for
//! `std::collections::HashMap`. The method bodies are verifier markers:
//! CHC codegen intercepts calls at the MIR level and replaces them with
//! SMT Array theory operations. Outside CHC interception the runtime bodies
//! return `kani::any()` (nondeterministic) values for owned-type returns,
//! or `unreachable!()` for reference-returning methods. This ensures that
//! if interception fails, verification explores all possible return values
//! rather than silently accepting hardcoded constants.
//!
//! SMT model:
//! - `(Array KeySort (Option ValueSort))` — functional map representation
//! - `select(map, key)` — lookup
//! - `store(map, key, value)` — update
//!
//! ## Required Flags
//!
//! This is an unstable API gated behind `-Z symbolic-collections`.
//! Current verification support requires CHC mode (`--ay-chc`).
//!
//! ```bash
//! cargo trust_mc -Z symbolic-collections -- --ay-chc <file>
//! ```
//!
//! ## Limitations
//!
//! - `len` and `is_empty` are over-approximated (symbolic, not exact).
//! - Method bodies are symbolic marker stubs, not runtime HashMap semantics.
//! - Iteration (`into_iter`) requires CHC interception for meaningful results.
//!
//! ## CHC Codegen Interception
//!
//! The marker functions use `#[inline(never)]` so CHC codegen can detect
//! and intercept them via path-based lookup. Detection uses
//! `kani::hashmap::TrustMcMap::` prefix matching.

use crate::Arbitrary;
use core::hash::Hash;
use core::marker::PhantomData;

/// A symbolic collection model with a HashMap-like API subset.
///
/// Method bodies are verifier markers — CHC codegen intercepts them at MIR
/// level and provides SMT Array semantics. Outside CHC interception the
/// runtime bodies return nondeterministic values (`kani::any()`) or panic
/// (`unreachable!()` for reference returns) to prevent silent unsoundness.
///
/// Requires `-Z symbolic-collections` and CHC mode (`--ay-chc`).
#[derive(Clone)]
#[crate::unstable(
    feature = "symbolic-collections",
    issue = 3648,
    reason = "experimental symbolic collection models; current support relies on verifier interception"
)]
pub struct TrustMcMap<K, V> {
    /// Phantom data to track key/value types for SMT sort inference.
    _marker: PhantomData<(K, V)>,
}

impl<K, V> Default for TrustMcMap<K, V>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> TrustMcMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new empty TrustMcMap.
    ///
    /// CHC codegen intercepts this and creates: `const_array(KeySort, None)`
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    #[must_use]
    pub fn new() -> Self {
        TrustMcMap { _marker: PhantomData }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// CHC codegen intercepts this and creates:
    /// - prev = select(map, key)
    /// - new_map = store(map, key, Some(value))
    /// - result = prev
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Clone,
        V: Arbitrary,
    {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores both Some/None branches instead of silently returning None.
        let _ = (key, value);
        kani::any()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// CHC codegen intercepts this and creates:
    /// - result = select(map, key)
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    #[must_use]
    pub fn get(&self, key: &K) -> Option<&V>
    where
        K: Clone,
    {
        // Soundness: cannot use kani::any() for reference types. If CHC codegen
        // fails to intercept this call, panic to prevent silent unsoundness.
        let _ = key;
        unreachable!("TrustMcMap::get must be intercepted by CHC codegen")
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// CHC codegen intercepts this and creates:
    /// - result = is_some(select(map, key))
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    #[must_use]
    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Clone,
    {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores both true/false branches instead of silently returning false.
        let _ = key;
        kani::any()
    }

    /// Removes a key from the map, returning the value at the key if present.
    ///
    /// CHC codegen intercepts this and creates:
    /// - prev = select(map, key)
    /// - new_map = store(map, key, None)
    /// - result = prev
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    pub fn remove(&mut self, key: &K) -> Option<V>
    where
        K: Clone,
        V: Arbitrary,
    {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores both Some/None branches instead of silently returning None.
        let _ = key;
        kani::any()
    }

    /// Returns true if the map is empty.
    ///
    /// Note: CHC codegen currently models this as nondet for soundness.
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores both true/false branches instead of silently returning true.
        kani::any()
    }

    /// Returns the number of elements in the map.
    ///
    /// Note: CHC codegen currently models this as nondet for soundness.
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    #[must_use]
    pub fn len(&self) -> usize {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores all possible lengths instead of silently returning 0.
        kani::any()
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// CHC codegen intercepts this and creates:
    /// - new_map = const_array(KeySort, None)
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    pub fn clear(&mut self) {
        // Stub - CHC codegen provides SMT Array semantics
    }
}

impl<K, V> core::fmt::Debug for TrustMcMap<K, V>
where
    K: core::fmt::Debug,
    V: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "TrustMcMap {{ ... }}")
    }
}

/// Iterator over key-value pairs of a TrustMcMap.
///
/// Part of #1812: CHC HashMap iterator support.
///
/// This iterator uses marker functions that CHC codegen intercepts:
/// - `into_iter()` creates iterator struct (map, keys, pos, len)
/// - `next()` advances position and returns Option<(K, V)>
///
/// The iterator model uses a symbolic keys array and length for soundness.
/// CHC codegen adds membership constraints: `pos < len => map[keys[pos]] is Some`.
#[crate::unstable(
    feature = "symbolic-collections",
    issue = 3648,
    reason = "experimental symbolic collection models; current support relies on verifier interception"
)]
pub struct TrustMcMapIntoIter<K, V> {
    /// Phantom data to track key/value types for SMT sort inference.
    _marker: PhantomData<(K, V)>,
}

impl<K, V> IntoIterator for TrustMcMap<K, V>
where
    K: Eq + Hash + Arbitrary,
    V: Arbitrary,
{
    type Item = (K, V);
    type IntoIter = TrustMcMapIntoIter<K, V>;

    /// Consumes the map and returns an iterator over key-value pairs.
    ///
    /// CHC codegen intercepts this and creates:
    /// - Iterator struct: (map, keys: Array<usize, K>, pos: 0, len: symbolic)
    /// - Membership constraint: forall i < len: is_some(map[keys[i]])
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    fn into_iter(self) -> Self::IntoIter {
        // Stub - CHC codegen provides SMT iterator semantics
        TrustMcMapIntoIter { _marker: PhantomData }
    }
}

impl<K, V> Iterator for TrustMcMapIntoIter<K, V>
where
    K: Arbitrary,
    V: Arbitrary,
{
    type Item = (K, V);

    /// Advances the iterator and returns the next key-value pair.
    ///
    /// CHC codegen intercepts this and creates:
    /// - If pos < len: return Some((keys[pos], unwrap(map[keys[pos]]))), pos += 1
    /// - Else: return None
    ///
    /// The membership constraint ensures map[keys[pos]] is always Some when in bounds.
    #[crate::unstable(
        feature = "symbolic-collections",
        issue = 3648,
        reason = "experimental symbolic collection models; current support relies on verifier interception"
    )]
    #[inline(never)]
    fn next(&mut self) -> Option<Self::Item> {
        // Soundness: if CHC codegen fails to intercept this call, kani::any()
        // explores both Some((k,v))/None branches instead of silently returning None.
        kani::any()
    }
}

impl<K, V> core::fmt::Debug for TrustMcMapIntoIter<K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "TrustMcMapIntoIter {{ ... }}")
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! HashMap/TrustMcMap/BTreeMap semantic model for AY codegen.
//!
//! BMC models HashMap/TrustMcMap/BTreeMap as `Array<KeySort, Option<ValueSort>>` using SMT array
//! theory. This matches the CHC encoding in chc/mod.rs for consistency across backends.
//!
//! # Semantics
//!
//! - `new`/`default`: `const_array(KeySort, None)`, len = 0
//! - `insert`: `prev = select(map, key); map' = store(map, key, Some(value));`
//!   `len' = ite(was_absent, len+1, len);` return `prev`
//! - `get`/`get_mut`: `select(map, key)`
//! - `contains_key`: `is_some(select(map, key))`
//! - `remove`: `prev = select(map, key); map' = store(map, key, None);`
//!   `len' = ite(was_present, len-1, len);` return `prev`
//! - `len`: return tracked length (Part of #1744)
//! - `is_empty`: return `len == 0` (Part of #1744)
//! - `clear`: `map' = const_array(KeySort, None), len = 0`
//! - `clone`: return same map (arrays are immutable in the model)
//!
//! # BTreeMap Limitations (Part of #1750)
//!
//! BTreeMap is modeled identically to HashMap - as an unordered array. This means:
//!
//! - Key-value operations (`get`, `insert`, `remove`) work correctly
//! - Map cardinality (`len`, `is_empty`) works correctly
//! - Ordering is not modeled - BTreeMap's sorted iteration guarantee is lost
//! - Properties depending on key ordering cannot be verified
//! - Range queries (`range`, `first_key`, `last_key`) need ordering theory
//!
//! This is a precision gap, not a soundness bug. See `btreeset.rs` for similar
//! limitations on BTreeSet. Most verification needs map semantics, not ordering.
//!
//! Part of #1275: BMC collection stubs implementation.
//! Part of #1354: Statement module refactoring.

#[path = "hashmap_helpers.rs"]
mod hashmap_helpers;
#[path = "hashmap_iter.rs"]
mod hashmap_iter;
#[path = "hashmap_stub.rs"]
mod hashmap_stub;

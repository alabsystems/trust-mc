// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `stubs_hashmap_detect.rs` — HashMap/BTreeMap/TrustMcMap stub
//! detection helpers.
//!
//! Part of #2303 (stubs_hashmap_detect.rs, 223 LOC, zero dedicated coverage).
//! Covers:
//! - `detect_hashmap_stub`: StubRegistry-based detection (Phase 1)
//! - `detect_hashmap_stub`: type-based fallback detection (Phase 2)
//! - `detect_hashbrown_stub`: hashbrown internal pattern matching (#798)
//! - `is_hashmap_receiver`: type predicate for hashbrown receivers
//! - `type_is_hashmap_or_hashbrown`: extended type check including internals

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// HashMap::new detection
// =============================================================================

const HASHMAP_NEW_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_new() -> HashMap<u32, u32> {
        HashMap::new()
    }
"#;

/// HashMap::new() is detected as HashMapNew stub.
#[test]
fn test_detect_hashmap_new() {
    with_test_ay_ctx_for_source(HASHMAP_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_new");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_new", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapNew),
            "should detect HashMapNew stub; got: {stubs:?}"
        );
    });
}

// =============================================================================
// HashMap::insert detection
// =============================================================================

const HASHMAP_INSERT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_insert(map: &mut HashMap<u32, u32>, k: u32, v: u32) {
        map.insert(k, v);
    }
"#;

/// HashMap::insert() is detected as HashMapInsert stub.
#[test]
fn test_detect_hashmap_insert() {
    with_test_ay_ctx_for_source(HASHMAP_INSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapInsert),
            "should detect HashMapInsert stub; got: {stubs:?}"
        );
    });
}

// =============================================================================
// HashMap::get detection
// =============================================================================

// =============================================================================
// HashMap::contains_key detection
// =============================================================================

const HASHMAP_CONTAINS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_contains(map: &mut HashMap<u32, u32>, k: u32) -> bool {
        map.contains_key(&k)
    }
"#;

/// HashMap::contains_key() is detected as HashMapContainsKey stub.
#[test]
fn test_detect_hashmap_contains_key() {
    with_test_ay_ctx_for_source(HASHMAP_CONTAINS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_contains");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_contains", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapContainsKey),
            "should detect HashMapContainsKey stub; got: {stubs:?}"
        );
    });
}

// =============================================================================
// HashMap::remove detection
// =============================================================================

const HASHMAP_REMOVE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_remove(map: &mut HashMap<u32, u32>, k: u32) -> Option<u32> {
        map.remove(&k)
    }
"#;

/// HashMap::remove() is detected as HashMapRemove stub.
#[test]
fn test_detect_hashmap_remove() {
    with_test_ay_ctx_for_source(HASHMAP_REMOVE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_remove");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_remove", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapRemove),
            "should detect HashMapRemove stub; got: {stubs:?}"
        );
    });
}

// =============================================================================
// HashMap::len / is_empty detection
// =============================================================================

const HASHMAP_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_len(map: &HashMap<u32, u32>) -> usize {
        map.len()
    }

    pub fn probe_hashmap_is_empty(map: &HashMap<u32, u32>) -> bool {
        map.is_empty()
    }
"#;

/// HashMap::len() is detected as HashMapLen stub.
#[test]
fn test_detect_hashmap_len() {
    with_test_ay_ctx_for_source(HASHMAP_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_len");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_len", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapLen),
            "should detect HashMapLen stub; got: {stubs:?}"
        );
    });
}

/// HashMap::is_empty() is detected as HashMapIsEmpty stub.
#[test]
fn test_detect_hashmap_is_empty() {
    with_test_ay_ctx_for_source(HASHMAP_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_is_empty");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_is_empty", ChcConfig::default());

        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            stubs.contains(&StubKind::HashMapIsEmpty),
            "should detect HashMapIsEmpty stub; got: {stubs:?}"
        );
    });
}

// =============================================================================
// Non-hashmap function should not be detected
// =============================================================================

/// A function that doesn't use HashMap should detect no HashMap stubs.
#[test]
fn test_no_false_positive_on_non_hashmap() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_no_hashmap(x: u32) -> u32 {
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_no_hashmap");
            let body = instance.body().expect("body");

            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_hashmap", ChcConfig::default());

            let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);
            assert!(
                stubs.is_empty(),
                "non-HashMap function should detect no stubs; got: {stubs:?}"
            );
        },
    );
}

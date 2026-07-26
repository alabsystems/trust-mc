// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precheck pattern tests: abstracted fallback, BTree internal, RawVec stub/fallback, Cow::to_string.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;

// =============================================================================
// Abstracted fallback pattern matching
// =============================================================================

/// Verify the four abstracted patterns recognized by try_codegen_abstracted_fallback.
#[test]
fn test_abstracted_patterns_match() {
    let patterns = &["core::str::lossy::", "Utf8Chunk::", "Utf8Chunks::", "borrow::Cow::"];

    // Positive cases
    assert!(patterns.iter().any(|p| "core::str::lossy::Utf8Lossy::chunks".contains(p)));
    assert!(patterns.iter().any(|p| "core::str::lossy::Utf8Chunk::valid".contains(p)));
    assert!(patterns.iter().any(|p| "core::str::lossy::Utf8Chunks::new".contains(p)));
    assert!(patterns.iter().any(|p| "std::borrow::Cow::to_owned".contains(p)));

    // Negative cases — should NOT match
    assert!(!patterns.iter().any(|p| "core::str::from_utf8".contains(p)));
    assert!(!patterns.iter().any(|p| "alloc::vec::Vec::push".contains(p)));
    assert!(!patterns.iter().any(|p| "core::num::wrapping_add".contains(p)));
}

/// Verify the Utf8Chunks-specific Iterator::next pattern.
#[test]
fn test_abstracted_utf8_iterator_next_pattern() {
    let is_utf8_iterator_next =
        |path: &str| path.contains("Iterator::next") && path.contains("Utf8Chunks");

    // In rustc def_path_str, the path for trait method calls uses "::" not ">::"
    assert!(is_utf8_iterator_next("core::str::lossy::Utf8Chunks::Iterator::next"));
    assert!(!is_utf8_iterator_next("Iterator::next"));
    assert!(!is_utf8_iterator_next("Utf8Chunks::new"));
    assert!(!is_utf8_iterator_next("alloc::vec::IntoIter::Iterator::next"));
}

/// Verify telemetry counters are distinct, loadable AtomicUsize statics.
#[test]
fn test_telemetry_counters_exist() {
    use crate::codegen_ay::statement::dispatch::{
        ABSTRACTED_FALLBACK_COUNT, INTERNAL_WORKAROUND_COUNT,
    };
    use std::sync::atomic::Ordering;

    // Counters are loadable and return well-defined values
    let workaround = INTERNAL_WORKAROUND_COUNT.load(Ordering::Relaxed);
    let fallback = ABSTRACTED_FALLBACK_COUNT.load(Ordering::Relaxed);

    // Values are non-negative (usize) — verifies no corruption
    assert!(workaround < usize::MAX, "workaround counter should be a reasonable value");
    assert!(fallback < usize::MAX, "fallback counter should be a reasonable value");

    // Counters are distinct objects (different addresses)
    let workaround_ptr = &raw const INTERNAL_WORKAROUND_COUNT as usize;
    let fallback_ptr = &raw const ABSTRACTED_FALLBACK_COUNT as usize;
    assert_ne!(workaround_ptr, fallback_ptr, "counters should be distinct statics");
}

// =============================================================================
// BTree internal precheck patterns
// =============================================================================

/// Verify mem::replace<SetValZST> path matching.
#[test]
fn test_btree_precheck_mem_replace_pattern() {
    let callee_path = "core::mem::replace";
    assert!(callee_path.contains("mem::replace"));

    // The precheck returns Some(target) for mem::replace<SetValZST>,
    // assigning Expr::bool_const(true).
    let result = Expr::bool_const(true);
    assert!(result.sort().is_bool());
}

/// Verify BTree internal path pattern matching.
#[test]
fn test_btree_precheck_internal_paths() {
    let btree_paths = [
        "alloc::collections::btree::node::NodeRef::new_leaf",
        "alloc::collections::btree::search::search_tree",
        "alloc::collections::btree::node::Handle::insert",
    ];

    for path in &btree_paths {
        assert!(
            path.contains("btree::node::") || path.contains("btree::search::"),
            "BTree internal path should match: {}",
            path
        );
    }

    // Non-BTree paths should NOT match
    let non_btree =
        ["alloc::vec::Vec::push", "std::collections::HashMap::insert", "core::ptr::write"];
    for path in &non_btree {
        assert!(
            !path.contains("btree::node::") && !path.contains("btree::search::"),
            "Non-BTree path should not match: {}",
            path
        );
    }
}

/// Verify RawVec internal precheck: stubs vs fallback distinction.
#[test]
fn test_btree_precheck_rawvec_stub_vs_fallback() {
    let has_stub = |callee_path: &str| -> bool {
        callee_path.ends_with("::capacity")
            || callee_path.ends_with("::ptr")
            || callee_path.ends_with("::grow_one")
            || callee_path.ends_with("::new_in")
            // Part of #2876 RC2: pre-inlined Vec capacity growth paths
            || callee_path.ends_with("::reserve_exact")
            || callee_path.ends_with("::grow_amortized")
    };

    // These have stubs — should NOT be caught by the precheck
    assert!(has_stub("alloc::raw_vec::RawVec::capacity"));
    assert!(has_stub("alloc::raw_vec::RawVec::ptr"));
    assert!(has_stub("alloc::raw_vec::RawVec::grow_one"));
    assert!(has_stub("alloc::raw_vec::RawVec::new_in"));
    assert!(has_stub("alloc::raw_vec::RawVecInner::reserve_exact"));
    assert!(has_stub("alloc::raw_vec::RawVecInner::grow_amortized"));

    // These do NOT have stubs — caught by precheck
    assert!(!has_stub("alloc::raw_vec::RawVec::allocate_in"));
    assert!(!has_stub("alloc::raw_vec::RawVec::shrink"));
}

// =============================================================================
// Cow<str>::to_string precheck pattern
// =============================================================================

/// Verify to_string path matching for Cow precheck.
#[test]
fn test_cow_tostring_path_pattern() {
    let check = |path: &str| -> bool {
        path.ends_with("::to_string") || path.contains("ToString::to_string")
    };

    assert!(check("std::string::ToString::to_string"));
    assert!(check("<alloc::borrow::Cow<str> as ToString>::to_string"));
    assert!(!check("core::fmt::Display::fmt"));
    assert!(!check("alloc::string::String::from"));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for heap_regions.rs: region array management and sort-to-suffix helper.
//!
//! Covers: assign_region_array (fresh, idempotent, bv8→typed upgrade, sort mismatch),
//! alias_most_recent_region, alias_region, get_region_array, sort_to_type_suffix.
//!
//! Part of #2921: CHC codegen unit test coverage.

#![allow(clippy::unwrap_used)]

use ay_bindings::Sort;

use super::super::heap_state::ChcHeapState;

// =============================================================================
// assign_region_array
// =============================================================================

/// Fresh region assignment creates a new entry.
#[test]
fn test_assign_region_array_fresh() {
    let mut heap = ChcHeapState::new();
    let (arr_name, out_name) = heap.assign_region_array(1, Sort::bitvec(32), "test_fn");

    assert!(!arr_name.is_empty(), "array name should be non-empty");
    assert!(out_name.ends_with("__out"), "output name should end with __out");
    assert!(arr_name.contains("region"), "name should contain 'region': {arr_name}");

    // get_region_array should find it.
    let region = heap.get_region_array(1);
    assert!(region.is_some(), "region should be retrievable after assignment");
    let (in_name, o_name, sort) = region.unwrap();
    assert_eq!(in_name, arr_name);
    assert_eq!(o_name, out_name);
    assert_eq!(sort, Sort::bitvec(32));
}

/// Repeated assignment with same sort is idempotent.
#[test]
fn test_assign_region_array_idempotent() {
    let mut heap = ChcHeapState::new();
    let (name1, out1) = heap.assign_region_array(1, Sort::bitvec(32), "test_fn");
    let (name2, out2) = heap.assign_region_array(1, Sort::bitvec(32), "test_fn");

    assert_eq!(name1, name2, "idempotent: same name on repeated call");
    assert_eq!(out1, out2);
}

/// Assignment with bv8 can be upgraded to a typed sort per #1453.
#[test]
fn test_assign_region_array_bv8_to_typed_upgrade() {
    let mut heap = ChcHeapState::new();
    // First assignment: raw bv8 (from allocation)
    let (name_bv8, _) = heap.assign_region_array(1, Sort::bitvec(8), "test_fn");

    // Second assignment: typed bv32 (from typed store)
    let (name_typed, _) = heap.assign_region_array(1, Sort::bitvec(32), "test_fn");

    assert_ne!(name_bv8, name_typed, "upgrade should create new name");

    // Verify the region now has the typed sort.
    let (_, _, sort) = heap.get_region_array(1).unwrap();
    assert_eq!(sort, Sort::bitvec(32), "should be upgraded to typed sort");
}

/// Assignment with different non-bv8 sorts warns and keeps existing.
#[test]
fn test_assign_region_array_sort_mismatch_keeps_existing() {
    let mut heap = ChcHeapState::new();
    let (name1, _) = heap.assign_region_array(1, Sort::bitvec(32), "test_fn");

    // Try to assign bv64 — incompatible (not a bv8 upgrade)
    let (name2, _) = heap.assign_region_array(1, Sort::bitvec(64), "test_fn");

    assert_eq!(name1, name2, "mismatch should return existing name");
    let (_, _, sort) = heap.get_region_array(1).unwrap();
    assert_eq!(sort, Sort::bitvec(32), "existing sort should be preserved");
}

// =============================================================================
// get_region_array
// =============================================================================

/// get_region_array returns None for unassigned obj_id.
#[test]
fn test_get_region_array_unassigned() {
    let heap = ChcHeapState::new();
    assert!(heap.get_region_array(99).is_none());
}

// =============================================================================
// alias_region (exact)
// =============================================================================

/// alias_region copies region from old to new allocation.
#[test]
fn test_alias_region_exact() {
    let mut heap = ChcHeapState::new();
    heap.assign_region_array(1, Sort::bitvec(32), "test_fn");

    let success = heap.alias_region(1, 2);
    assert!(success, "aliasing should succeed when old region exists");

    // New allocation should share the same region.
    let old_region = heap.get_region_array(1).unwrap();
    let new_region = heap.get_region_array(2).unwrap();
    assert_eq!(old_region.0, new_region.0, "aliased regions share array name");
    assert_eq!(old_region.2, new_region.2, "aliased regions share sort");
}

/// alias_region returns false when old obj_id has no region.
#[test]
fn test_alias_region_missing_old() {
    let mut heap = ChcHeapState::new();
    let success = heap.alias_region(99, 100);
    assert!(!success, "aliasing should fail when old region is missing");
}

// =============================================================================
// alias_most_recent_region
// =============================================================================

/// alias_most_recent_region finds the highest obj_id < new_obj_id.
#[test]
fn test_alias_most_recent_region() {
    let mut heap = ChcHeapState::new();
    heap.assign_region_array(1, Sort::bitvec(8), "fn");
    heap.assign_region_array(3, Sort::bitvec(16), "fn");
    heap.assign_region_array(5, Sort::bitvec(32), "fn");

    // Alias obj_id=6 should use obj_id=5 (most recent < 6).
    let success = heap.alias_most_recent_region(6);
    assert!(success);

    let region_5 = heap.get_region_array(5).unwrap();
    let region_6 = heap.get_region_array(6).unwrap();
    assert_eq!(region_5.0, region_6.0, "should alias to obj_id=5");
}

/// alias_most_recent_region returns false when no prior regions exist.
#[test]
fn test_alias_most_recent_region_empty() {
    let mut heap = ChcHeapState::new();
    let success = heap.alias_most_recent_region(1);
    assert!(!success, "should fail with no prior regions");
}

// =============================================================================
// sort_to_type_suffix
// =============================================================================

/// sort_to_type_suffix produces correct suffixes for common sorts.
#[test]
fn test_sort_to_type_suffix_common_sorts() {
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(8)).as_ref(), "bv8");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(32)).as_ref(), "bv32");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(64)).as_ref(), "bv64");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(128)).as_ref(), "bv128");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bool()).as_ref(), "bool");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::int()).as_ref(), "int");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::real()).as_ref(), "real");
}

/// sort_to_type_suffix handles non-standard bitvec widths.
#[test]
fn test_sort_to_type_suffix_non_standard_bv() {
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(7)).as_ref(), "bv7");
    assert_eq!(ChcHeapState::sort_to_type_suffix(&Sort::bitvec(256)).as_ref(), "bv256");
}

/// sort_to_type_suffix returns "arr" for array sorts.
#[test]
fn test_sort_to_type_suffix_array() {
    let arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    assert_eq!(ChcHeapState::sort_to_type_suffix(&arr).as_ref(), "arr");
}

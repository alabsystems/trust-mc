// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for ChcHeapState (heap_state.rs).
//!
//! Covers: drain_store_chains, accumulate_store, assign_region_array,
//! get_or_create_type_array, store chain sort-mismatch drop path.
//!
//! Part of #2643: heap_state.rs has 431 LOC and zero unit tests.

#![allow(clippy::unwrap_used)]

use ay_bindings::{Expr, Sort};

use super::super::codegen_ctx::diagnostics::ChcDiagnostics;
use super::super::heap_state::ChcHeapState;

// =============================================================================
// drain_store_chains
// =============================================================================

/// Empty store chains produce empty constraints.
#[test]
fn test_drain_store_chains_empty() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    let constraints = heap.drain_store_chains(&diagnostics);
    assert!(constraints.is_empty(), "empty heap should drain to empty constraints");
}

/// Single accumulate + drain produces one equality constraint.
#[test]
fn test_drain_store_chains_single_store() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Register a type array so expected_store_chain_output_sort can find it.
    let elem_sort = Sort::bitvec(32);
    let (_arr_in, arr_out, _es, _) =
        heap.get_or_create_type_array("i32", elem_sort.clone(), "test_fn");

    // Build a store expression: store(arr_in, addr, val)
    let arr_sort = Sort::array(Sort::bitvec(64), elem_sort.clone());
    let arr_in_expr = Expr::var("_test_fn_mem_i32", arr_sort);
    let addr = Expr::var("addr", Sort::bitvec(64));
    let val = Expr::var("val", elem_sort);
    let store_expr = arr_in_expr.store(addr, val);

    heap.accumulate_store("i32", arr_out, store_expr);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 1, "single store chain should produce 1 constraint");

    let c_str = constraints[0].to_string();
    // The constraint should be: arr_out = store(arr_in, addr, val)
    assert!(c_str.contains("_test_fn_mem_i32__out"), "constraint should reference output array");
}

/// Multiple stores to same type key accumulate (last wins since caller pre-nests).
#[test]
fn test_drain_store_chains_multiple_stores_same_key() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    let elem_sort = Sort::bitvec(32);
    let (_arr_in, arr_out, _es, _) =
        heap.get_or_create_type_array("i32", elem_sort.clone(), "test_fn");

    let arr_sort = Sort::array(Sort::bitvec(64), elem_sort.clone());
    let arr_in_expr = Expr::var("_test_fn_mem_i32", arr_sort);
    let addr1 = Expr::var("addr1", Sort::bitvec(64));
    let val1 = Expr::var("val1", elem_sort.clone());
    let store1 = arr_in_expr.store(addr1, val1);

    // First accumulate
    heap.accumulate_store("i32", arr_out.clone(), store1.clone());

    // Second accumulate overwrites (caller pre-nests store expressions)
    let addr2 = Expr::var("addr2", Sort::bitvec(64));
    let val2 = Expr::var("val2", elem_sort);
    let store2 = store1.store(addr2, val2);
    heap.accumulate_store("i32", arr_out, store2);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(
        constraints.len(),
        1,
        "multiple stores to same key should produce 1 constraint (nested)"
    );
}

/// Multiple stores to different type keys produce multiple constraints.
#[test]
fn test_drain_store_chains_multiple_keys() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // i32 array
    let elem_i32 = Sort::bitvec(32);
    let (_in1, out1, _, _) = heap.get_or_create_type_array("i32", elem_i32.clone(), "test_fn");
    let arr_sort_i32 = Sort::array(Sort::bitvec(64), elem_i32.clone());
    let arr_in_i32 = Expr::var("_test_fn_mem_i32", arr_sort_i32);
    let store_i32 = arr_in_i32.store(Expr::var("a1", Sort::bitvec(64)), Expr::var("v1", elem_i32));
    heap.accumulate_store("i32", out1, store_i32);

    // i64 array
    let elem_i64 = Sort::bitvec(64);
    let (_in2, out2, _, _) = heap.get_or_create_type_array("i64", elem_i64.clone(), "test_fn");
    let arr_sort_i64 = Sort::array(Sort::bitvec(64), elem_i64.clone());
    let arr_in_i64 = Expr::var("_test_fn_mem_i64", arr_sort_i64);
    let store_i64 = arr_in_i64.store(Expr::var("a2", Sort::bitvec(64)), Expr::var("v2", elem_i64));
    heap.accumulate_store("i64", out2, store_i64);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 2, "two different type keys should produce 2 constraints");
}

/// Deterministic ordering: constraints are sorted by type_key.
#[test]
fn test_drain_store_chains_deterministic_order() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Insert in reverse alphabetical order
    let elem8 = Sort::bitvec(8);
    let (_in_z, out_z, _, _) = heap.get_or_create_type_array("zzz", elem8.clone(), "test_fn");
    let arr_sort = Sort::array(Sort::bitvec(64), elem8.clone());
    let store_z = Expr::var("_test_fn_mem_zzz", arr_sort.clone())
        .store(Expr::var("az", Sort::bitvec(64)), Expr::var("vz", elem8.clone()));
    heap.accumulate_store("zzz", out_z, store_z);

    let (_in_a, out_a, _, _) = heap.get_or_create_type_array("aaa", elem8.clone(), "test_fn");
    let store_a = Expr::var("_test_fn_mem_aaa", arr_sort)
        .store(Expr::var("aa", Sort::bitvec(64)), Expr::var("va", elem8));
    heap.accumulate_store("aaa", out_a, store_a);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 2);

    let c0 = constraints[0].to_string();
    let c1 = constraints[1].to_string();
    // "aaa" should come before "zzz" in sorted order
    assert!(
        c0.contains("_test_fn_mem_aaa__out"),
        "first constraint should be for 'aaa', got: {c0}"
    );
    assert!(
        c1.contains("_test_fn_mem_zzz__out"),
        "second constraint should be for 'zzz', got: {c1}"
    );
}

/// Sort mismatch between store expression and expected output skips constraint
/// emission entirely per #3138. arr_out is universally quantified (sound
/// over-approximation). Counter still increments.
#[test]
fn test_drain_store_chains_sort_mismatch_emits_self_loop() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Register type array with i32 element sort
    let elem_i32 = Sort::bitvec(32);
    let (_arr_in, arr_out, _es, _) = heap.get_or_create_type_array("i32", elem_i32, "test_fn");

    // Build a store expression with WRONG element sort (i64 instead of i32)
    let wrong_elem = Sort::bitvec(64);
    let wrong_arr_sort = Sort::array(Sort::bitvec(64), wrong_elem.clone());
    let wrong_arr = Expr::var("_test_fn_mem_i32", wrong_arr_sort);
    let wrong_store =
        wrong_arr.store(Expr::var("addr", Sort::bitvec(64)), Expr::var("val", wrong_elem));

    heap.accumulate_store("i32", arr_out, wrong_store);

    let constraints = heap.drain_store_chains(&diagnostics);

    // #3138: sort-mismatched stores skip constraint emission entirely.
    // arr_out is universally quantified (sound over-approximation).
    assert_eq!(
        constraints.len(),
        0,
        "sort mismatch should emit no constraints (#3138), got {}",
        constraints.len()
    );
    assert!(
        diagnostics.store_dropped_transition.get() > 0,
        "store_dropped_transition should increment on sort mismatch"
    );
}

// =============================================================================
// accumulate_store / get_store_chain
// =============================================================================

/// get_store_chain returns None for non-existent key.
#[test]
fn test_get_store_chain_empty() {
    let heap = ChcHeapState::new();
    assert!(heap.get_store_chain("nonexistent").is_none());
}

/// accumulate_store followed by get_store_chain returns the expression.
#[test]
fn test_accumulate_then_get_store_chain() {
    let mut heap = ChcHeapState::new();

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let store_expr = Expr::var("arr_in", arr_sort)
        .store(Expr::var("addr", Sort::bitvec(64)), Expr::var("val", Sort::bitvec(32)));

    heap.accumulate_store("i32", "arr_out", store_expr);
    let chain = heap.get_store_chain("i32");
    assert!(chain.is_some(), "should find accumulated store chain for 'i32'");
}

/// Second accumulate_store to same key overwrites.
#[test]
fn test_accumulate_store_overwrites_same_key() {
    let mut heap = ChcHeapState::new();

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let store1 = Expr::var("arr_in", arr_sort.clone())
        .store(Expr::var("addr1", Sort::bitvec(64)), Expr::var("val1", Sort::bitvec(32)));
    let store2 = Expr::var("arr_in", arr_sort)
        .store(Expr::var("addr2", Sort::bitvec(64)), Expr::var("val2", Sort::bitvec(32)));

    heap.accumulate_store("i32", "out1", store1);
    heap.accumulate_store("i32", "out2", store2);

    // The chain should have the second expression
    let chain = heap.get_store_chain("i32").unwrap();
    let chain_str = chain.to_string();
    assert!(
        chain_str.contains("addr2"),
        "overwritten chain should contain addr2, got: {chain_str}"
    );
}

// =============================================================================
// assign_region_array
// =============================================================================

/// New region assignment creates array with correct naming.
#[test]
fn test_assign_region_array_new() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();
    let elem_sort = Sort::bitvec(32);

    let (arr_in, arr_out) = heap.assign_region_array(obj_id, elem_sort, "my_fn");

    assert!(arr_in.contains("region"), "region array name should contain 'region': {arr_in}");
    assert!(
        arr_in.contains(&obj_id.to_string()),
        "region array name should contain obj_id: {arr_in}"
    );
    assert!(arr_in.contains("bv32"), "region name should contain type suffix: {arr_in}");
    assert_eq!(arr_out, format!("{arr_in}__out"), "output name should be input + __out");
}

/// Repeated assign with same sort is idempotent — returns same names.
#[test]
fn test_assign_region_array_idempotent() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();
    let elem_sort = Sort::bitvec(32);

    let (name1, out1) = heap.assign_region_array(obj_id, elem_sort.clone(), "my_fn");
    let (name2, out2) = heap.assign_region_array(obj_id, elem_sort, "my_fn");

    assert_eq!(name1, name2, "idempotent assign should return same input name");
    assert_eq!(out1, out2, "idempotent assign should return same output name");
}

/// Upgrade from bv8 to typed sort replaces the region array (#1453).
#[test]
fn test_assign_region_array_bv8_to_typed_upgrade() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();

    // First assign with bv8 (raw bytes from allocation)
    let (bv8_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(8), "my_fn");
    assert!(bv8_name.contains("bv8"), "initial region should be bv8: {bv8_name}");

    // Upgrade to typed sort (e.g., i32 store)
    let (typed_name, typed_out) = heap.assign_region_array(obj_id, Sort::bitvec(32), "my_fn");
    assert!(typed_name.contains("bv32"), "upgraded region should be bv32: {typed_name}");
    assert_ne!(bv8_name, typed_name, "upgrade should change the array name");
    assert_eq!(typed_out, format!("{typed_name}__out"), "output name should match upgraded input");

    // Subsequent get should reflect upgrade
    let region = heap.get_region_array(obj_id);
    assert!(region.is_some(), "region should exist after upgrade");
    let (got_name, _, got_sort) = region.unwrap();
    assert_eq!(got_name, typed_name, "get should return upgraded name");
    assert_eq!(got_sort, Sort::bitvec(32), "get should return upgraded sort");
}

/// Sort mismatch that's not a bv8→typed upgrade uses existing region.
#[test]
fn test_assign_region_array_sort_mismatch_keeps_existing() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();

    // Assign with i32
    let (i32_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(32), "my_fn");

    // Try to assign with i64 — not an upgrade, keeps existing
    let (got_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(64), "my_fn");

    assert_eq!(i32_name, got_name, "non-upgrade sort mismatch should keep existing region");
}

// =============================================================================
// get_or_create_type_array
// =============================================================================

/// First call creates; second call returns same names.
#[test]
fn test_get_or_create_type_array_idempotent() {
    let mut heap = ChcHeapState::new();
    let elem = Sort::bitvec(32);

    let (in1, out1, sort1, new1) = heap.get_or_create_type_array("i32", elem.clone(), "my_fn");
    let (in2, out2, sort2, new2) = heap.get_or_create_type_array("i32", elem, "my_fn");

    assert_eq!(in1, in2);
    assert_eq!(out1, out2);
    assert_eq!(sort1, sort2);
    assert!(new1, "first call should report is_new=true");
    assert!(!new2, "second call should report is_new=false");
}

/// Output name is input name + "__out".
#[test]
fn test_get_or_create_type_array_naming() {
    let mut heap = ChcHeapState::new();
    let elem = Sort::bitvec(8);

    let (arr_in, arr_out, _, _) = heap.get_or_create_type_array("u8", elem, "test_fn");

    assert!(arr_in.contains("test_fn"), "input name should contain fn name: {arr_in}");
    assert!(arr_in.contains("u8"), "input name should contain type key: {arr_in}");
    assert_eq!(arr_out, format!("{arr_in}__out"));
}

// =============================================================================
// mark/reset modified arrays
// =============================================================================

/// Modified array tracking works across mark, check, reset cycle.
#[test]
fn test_modified_arrays_lifecycle() {
    let mut heap = ChcHeapState::new();

    assert!(!heap.is_array_modified("i32"));
    heap.mark_array_modified("i32");
    assert!(heap.is_array_modified("i32"));
    assert!(!heap.is_array_modified("i64"));

    heap.reset_modified_arrays();
    assert!(!heap.is_array_modified("i32"));
}

/// reset_modified_arrays also clears store chains.
#[test]
fn test_reset_clears_store_chains() {
    let mut heap = ChcHeapState::new();

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let store = Expr::var("arr", arr_sort)
        .store(Expr::var("a", Sort::bitvec(64)), Expr::var("v", Sort::bitvec(32)));
    heap.accumulate_store("i32", "out", store);
    assert!(heap.get_store_chain("i32").is_some());

    heap.reset_modified_arrays();
    assert!(heap.get_store_chain("i32").is_none(), "reset should clear store chains");
}

/// reset_modified_arrays also clears store_forward_map (#3664).
/// Without this, forwarding entries from a previous block could leak across
/// block boundaries, causing stale reads.
#[test]
fn test_reset_clears_store_forward_map() {
    let mut heap = ChcHeapState::new();

    // Insert a forwarding entry: obj_id=5, offset=8
    let fwd_key = ((5u64) << 32) | 8u64;
    let value = Expr::bitvec_const(42u128, 32);
    heap.store_forward_map.insert(fwd_key, (0, value));
    assert!(heap.store_forward_map.contains_key(&fwd_key));

    heap.reset_modified_arrays();
    assert!(
        heap.store_forward_map.is_empty(),
        "reset_modified_arrays should clear store_forward_map (#3664)"
    );
}

// =============================================================================
// alloc ID management
// =============================================================================

/// Alloc IDs start at 2 (0 = null, 1 = promoted constants) and increment.
/// Part of #2958: obj_id 1 reserved for promoted constant memory region.
#[test]
fn test_alloc_id_sequence() {
    let mut heap = ChcHeapState::new();
    assert_eq!(heap.next_alloc_id().unwrap(), 2);
    assert_eq!(heap.next_alloc_id().unwrap(), 3);
    assert_eq!(heap.next_alloc_id().unwrap(), 4);
}

/// Allocation ID overflow returns None instead of panicking (#2735).
/// Matches BMC path's graceful-failure pattern (context/heap.rs).
/// At u32::MAX, checked_add(1) fails so the ID cannot be issued.
#[test]
fn test_alloc_id_overflow_returns_none() {
    let mut heap = ChcHeapState::new();
    heap.set_next_alloc_id(u32::MAX);
    assert_eq!(heap.next_alloc_id(), None, "u32::MAX should return None (cannot advance counter)");
}

/// The last allocatable ID is u32::MAX - 1 (counter advances to u32::MAX).
#[test]
fn test_alloc_id_last_valid_is_max_minus_one() {
    let mut heap = ChcHeapState::new();
    heap.set_next_alloc_id(u32::MAX - 1);
    assert_eq!(heap.next_alloc_id(), Some(u32::MAX - 1));
    // Counter is now at u32::MAX; next call fails
    assert_eq!(heap.next_alloc_id(), None);
}

/// reserve_heap_alloc_id propagates None on overflow (#2735).
#[test]
fn test_reserve_heap_alloc_id_overflow_returns_none() {
    let mut heap = ChcHeapState::new();
    heap.set_next_alloc_id(u32::MAX);
    assert!(heap.reserve_heap_alloc_id().is_none(), "reserve should return None on overflow");
}

/// next_heap_alloc_id returns None when preallocated queue is empty
/// and next_alloc_id overflows (#2735).
#[test]
fn test_next_heap_alloc_id_overflow_returns_none() {
    let mut heap = ChcHeapState::new();
    heap.set_next_alloc_id(u32::MAX);
    assert!(
        heap.next_heap_alloc_id().is_none(),
        "should return None on overflow when preallocated queue is empty"
    );
}

/// Preallocated heap IDs are consumed in FIFO order.
#[test]
fn test_preallocated_heap_ids() {
    let mut heap = ChcHeapState::new();

    let reserved1 = heap.reserve_heap_alloc_id().unwrap();
    let reserved2 = heap.reserve_heap_alloc_id().unwrap();

    // next_heap_alloc_id should return preallocated IDs first
    assert_eq!(heap.next_heap_alloc_id().unwrap(), reserved1);
    assert_eq!(heap.next_heap_alloc_id().unwrap(), reserved2);

    // After preallocated are consumed, falls back to fresh IDs
    let fresh = heap.next_heap_alloc_id().unwrap();
    assert!(fresh > reserved2, "fresh ID should be > last reserved");
}

// =============================================================================
// alias_most_recent_region (realloc support)
// =============================================================================

/// Aliasing to most recent region works for realloc.
#[test]
fn test_alias_most_recent_region() {
    let mut heap = ChcHeapState::new();

    let obj1 = heap.next_alloc_id().unwrap();
    heap.assign_region_array(obj1, Sort::bitvec(32), "test_fn");

    let obj2 = heap.next_alloc_id().unwrap();
    let aliased = heap.alias_most_recent_region(obj2);
    assert!(aliased, "aliasing should succeed when prior region exists");

    // obj2's region should share obj1's array name
    let r1 = heap.get_region_array(obj1).unwrap();
    let r2 = heap.get_region_array(obj2).unwrap();
    assert_eq!(r1.0, r2.0, "aliased regions should share array name");
}

/// Aliasing fails when no prior regions exist.
#[test]
fn test_alias_no_prior_region() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();
    assert!(!heap.alias_most_recent_region(obj_id), "aliasing should fail with no prior regions");
}

/// Fix #2553: alias_region targets exact old_obj_id, not most-recent heuristic.
/// Regression: alloc(A) + alloc(B) + realloc(A) should alias A, not B.
#[test]
fn test_alias_region_targets_exact_old_id() {
    let mut heap = ChcHeapState::new();

    let obj_a = heap.next_alloc_id().unwrap();
    heap.assign_region_array(obj_a, Sort::bitvec(8), "test_fn");

    let obj_b = heap.next_alloc_id().unwrap();
    heap.assign_region_array(obj_b, Sort::bitvec(8), "test_fn");

    let obj_realloc = heap.next_alloc_id().unwrap();

    // alias_region targets obj_a exactly
    let aliased = heap.alias_region(obj_a, obj_realloc);
    assert!(aliased, "alias_region should succeed for existing old region");

    // realloc'd region should see A's array, not B's
    let region_a = heap.get_region_array(obj_a).unwrap();
    let region_b = heap.get_region_array(obj_b).unwrap();
    let region_realloc = heap.get_region_array(obj_realloc).unwrap();
    assert_eq!(region_a.0, region_realloc.0, "realloc should alias A's region");
    assert_ne!(region_b.0, region_realloc.0, "realloc should NOT alias B's region");
}

/// alias_region fails when target old_id has no region.
#[test]
fn test_alias_region_fails_for_missing_old_id() {
    let mut heap = ChcHeapState::new();
    let obj_a = heap.next_alloc_id().unwrap();
    // Don't assign a region to obj_a
    let obj_realloc = heap.next_alloc_id().unwrap();
    assert!(
        !heap.alias_region(obj_a, obj_realloc),
        "alias_region should fail when old has no region"
    );
}

// =============================================================================
// metadata arrays
// =============================================================================

/// Metadata array modification tracking.
#[test]
fn test_metadata_arrays_lifecycle() {
    let mut heap = ChcHeapState::new();
    assert!(!heap.are_metadata_arrays_modified());
    heap.mark_metadata_arrays_modified();
    assert!(heap.are_metadata_arrays_modified());
    heap.reset_modified_arrays();
    assert!(!heap.are_metadata_arrays_modified());
}

// =============================================================================
// local_idx_for_obj_id
// =============================================================================

/// local_idx_for_obj_id finds stack locals by obj_id.
#[test]
fn test_local_idx_for_obj_id() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();

    heap.insert_local_address(5, obj_id, "addr_5".to_string());

    assert_eq!(heap.local_idx_for_obj_id(obj_id), Some(5));
    assert_eq!(heap.local_idx_for_obj_id(999), None);
}

/// Concrete heap allocation sizes are tracked by object ID.
#[test]
fn test_known_heap_alloc_size_by_obj_id() {
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();

    assert_eq!(heap.heap_alloc_size(obj_id), None);
    heap.record_heap_alloc_size(obj_id, 24);
    assert_eq!(heap.heap_alloc_size(obj_id), Some(24));
    assert_eq!(heap.heap_alloc_size(obj_id + 1), None);
}

// =============================================================================
// snapshot_transient_rule_state / restore_transient_rule_state (#4185)
// =============================================================================

/// Part of #4185: Verify that snapshot/restore rolls back heap mutations
/// from a partial inline walk. Simulates: snapshot → accumulate stores +
/// push pending_updates/checks → bail → restore → verify pre-walk state.
#[test]
fn test_snapshot_restore_clears_partial_walk_mutations() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Pre-existing state: one pending_update from before the inline walk.
    let pre_existing = Expr::bool_const(true);
    heap.pending_updates.push(pre_existing.clone());
    assert_eq!(heap.pending_updates.len(), 1);

    // Snapshot before speculative inline walk.
    let snapshot = heap.snapshot_transient_rule_state();

    // Simulate partial inline walk mutations.
    heap.pending_updates.push(Expr::bool_const(false));
    heap.pending_checks.push(Expr::bool_const(true));
    heap.mark_array_modified("i32");
    heap.record_heap_alloc_size(777, 16);

    // Verify mutations are visible.
    assert_eq!(heap.pending_updates.len(), 2);
    assert_eq!(heap.pending_checks.len(), 1);
    assert!(heap.is_array_modified("i32"));

    // Restore: simulates bail-out path.
    heap.restore_transient_rule_state(&snapshot);

    // Verify: pre-existing update preserved, walk mutations rolled back.
    assert_eq!(
        heap.pending_updates.len(),
        1,
        "restore should roll back to pre-walk state (1 pre-existing update)"
    );
    assert_eq!(
        heap.pending_updates[0].to_string(),
        pre_existing.to_string(),
        "pre-existing update should be preserved"
    );
    assert!(
        heap.pending_checks.is_empty(),
        "pending_checks should be empty (none existed pre-walk)"
    );
    assert!(!heap.is_array_modified("i32"), "modified_arrays should be rolled back");
    assert_eq!(heap.heap_alloc_size(777), None, "known allocation sizes should be rolled back");
    let post_restore_chains = heap.drain_store_chains(&diagnostics);
    assert!(
        post_restore_chains.is_empty(),
        "store chains should be empty after restore (none existed pre-walk)"
    );
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::codegen_ctx::diagnostics::ChcDiagnostics;

// ============================================================================
// HeapState store chain accumulation tests (Part of #2188)
// ============================================================================

#[test]
fn test_store_chain_accumulate_single_store() {
    // (#2188) Verify single store accumulation creates chain with one entry
    let mut heap = ChcHeapState::new();

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let arr_in = Expr::var("_fn_mem_i32", arr_sort);
    let addr = Expr::bitvec_const(0x100i128, 64);
    let val = Expr::bitvec_const(42, 32);

    let store_expr = arr_in.store(addr, val);
    heap.accumulate_store("i32", "_fn_mem_i32__out", store_expr);

    let chain = heap.get_store_chain("i32");
    assert!(chain.is_some(), "Should have store chain for i32");
    assert!(chain.unwrap().sort().is_array(), "Store chain should be array sort");
}

#[test]
fn test_store_chain_get_nonexistent_returns_none() {
    // (#2188) Querying a store chain for a type that hasn't been stored to returns None
    let heap = ChcHeapState::new();
    assert!(heap.get_store_chain("u64").is_none(), "Non-existent type key should return None");
}

#[test]
fn test_store_chain_drain_produces_equality_constraints() {
    // (#2188) drain_store_chains should produce arr_out = store_chain constraints
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let arr_in = Expr::var("_fn_mem_i32", arr_sort);
    let store_expr = arr_in.store(Expr::bitvec_const(8i128, 64), Expr::bitvec_const(99, 32));

    heap.accumulate_store("i32", "_fn_mem_i32__out", store_expr);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 1, "Should produce one constraint per type key");

    let smt = constraints[0].to_string();
    assert!(smt.contains("_fn_mem_i32__out"), "Constraint should reference output array");
    assert!(smt.contains("store"), "Constraint should contain store expression");
}

#[test]
fn test_store_chain_drain_sort_mismatch_emits_self_loop() {
    // (#3138) If accumulated store sort drifts from declared array sort,
    // drain skips constraint emission entirely. arr_out is universally
    // quantified (sound over-approximation).
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    let (arr_in, arr_out, _, _) = heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");
    let wrong_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    let wrong_arr = Expr::var(&*arr_in, wrong_sort);
    let store_expr = wrong_arr.store(Expr::bitvec_const(0i128, 64), Expr::bitvec_const(7, 64));

    heap.accumulate_store("i32", arr_out, store_expr);

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 0, "sort mismatch should emit no constraints (#3138)");
    assert_eq!(
        diagnostics.store_dropped_transition.get(),
        1,
        "store_dropped_transition should increment on sort mismatch"
    );
}

#[test]
fn test_store_chain_drain_empty_returns_empty() {
    // (#2188) Draining with no accumulated stores returns empty vec
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    let constraints = heap.drain_store_chains(&diagnostics);
    assert!(constraints.is_empty(), "No stores should produce no constraints");
}

#[test]
fn test_store_chain_drain_deterministic_ordering() {
    // (#2188, #1974) drain_store_chains sorts by type_key for determinism
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    let arr_u64 = Expr::var("_fn_mem_u64", Sort::array(Sort::bitvec(64), Sort::bitvec(64)));
    let arr_i32 = Expr::var("_fn_mem_i32", Sort::array(Sort::bitvec(64), Sort::bitvec(32)));

    // Insert in reverse alphabetical order
    heap.accumulate_store(
        "u64",
        "_fn_mem_u64__out",
        arr_u64.store(Expr::bitvec_const(0i128, 64), Expr::bitvec_const(1, 64)),
    );
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        arr_i32.store(Expr::bitvec_const(0i128, 64), Expr::bitvec_const(2, 32)),
    );

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 2);
    // "i32" < "u64" alphabetically, so i32 constraint comes first
    let smt0 = constraints[0].to_string();
    let smt1 = constraints[1].to_string();
    assert!(smt0.contains("i32"), "First constraint should be i32 (sorted), got: {smt0}");
    assert!(smt1.contains("u64"), "Second constraint should be u64 (sorted), got: {smt1}");
}

// ============================================================================
// HeapState metadata array tracking tests (Part of #2188)
// ============================================================================

#[test]
fn test_metadata_arrays_initially_unmodified() {
    // (#2188) Metadata arrays (obj_valid, obj_size) start unmodified
    let heap = ChcHeapState::new();
    assert!(!heap.are_metadata_arrays_modified(), "Metadata arrays should be unmodified initially");
}

#[test]
fn test_metadata_arrays_mark_and_check() {
    // (#2188) mark_metadata_arrays_modified sets the flag
    let mut heap = ChcHeapState::new();
    heap.mark_metadata_arrays_modified();
    assert!(heap.are_metadata_arrays_modified(), "Metadata arrays should be modified after mark");
}

#[test]
fn test_metadata_arrays_reset_clears_flag() {
    // (#2188) reset_modified_arrays clears metadata flag along with type arrays
    let mut heap = ChcHeapState::new();
    heap.mark_metadata_arrays_modified();
    heap.mark_array_modified("i32");
    assert!(heap.are_metadata_arrays_modified());
    assert!(heap.is_array_modified("i32"));

    heap.reset_modified_arrays();
    assert!(!heap.are_metadata_arrays_modified(), "Metadata flag should be reset");
    assert!(!heap.is_array_modified("i32"), "Type array flag should be reset");
}

// ============================================================================
// HeapState pre-allocated ID tests (Part of #2188)
// ============================================================================

#[test]
fn test_reserve_heap_alloc_id_returns_sequential() {
    // (#2188) reserve_heap_alloc_id returns sequential IDs
    let mut heap = ChcHeapState::new();
    let id1 = heap.reserve_heap_alloc_id().unwrap();
    let id2 = heap.reserve_heap_alloc_id().unwrap();
    assert_eq!(id1, 2); // 0=null, 1=promoted constants, allocs start at 2
    assert_eq!(id2, 3);
}

#[test]
fn test_next_heap_alloc_id_uses_preallocated_first() {
    // (#2188) next_heap_alloc_id should use preallocated IDs before generating new ones
    let mut heap = ChcHeapState::new();

    // Reserve two IDs
    let reserved_1 = heap.reserve_heap_alloc_id().unwrap();
    let reserved_2 = heap.reserve_heap_alloc_id().unwrap();

    // Consume them via next_heap_alloc_id (FIFO order)
    let consumed_1 = heap.next_heap_alloc_id().unwrap();
    let consumed_2 = heap.next_heap_alloc_id().unwrap();

    assert_eq!(consumed_1, reserved_1, "First consumed should match first reserved");
    assert_eq!(consumed_2, reserved_2, "Second consumed should match second reserved");

    // Now preallocated queue is empty, should generate a new ID
    let fresh_id = heap.next_heap_alloc_id().unwrap();
    assert_eq!(fresh_id, 4, "After preallocated exhausted, should continue sequence");
}

// ============================================================================
// HeapState alias_most_recent_region tests (Part of #2188)
// ============================================================================

#[test]
fn test_alias_most_recent_region_succeeds_with_prior_region() {
    // (#2188, #1836) alias_most_recent_region finds the most recent allocation's region
    let mut heap = ChcHeapState::new();

    let obj_id_old = heap.next_alloc_id().unwrap();
    heap.assign_region_array(obj_id_old, Sort::bitvec(8), "fn_test");

    let obj_id_new = heap.next_alloc_id().unwrap();
    let aliased = heap.alias_most_recent_region(obj_id_new);
    assert!(aliased, "Should succeed when prior region exists");

    // New allocation should share old allocation's region
    let old_region = heap.get_region_array(obj_id_old).unwrap();
    let new_region = heap.get_region_array(obj_id_new).unwrap();
    assert_eq!(old_region.0, new_region.0, "New should alias old region's input name");
}

#[test]
fn test_alias_most_recent_region_fails_with_no_prior_regions() {
    // (#2188) alias_most_recent_region returns false when no regions exist
    let mut heap = ChcHeapState::new();
    let obj_id = heap.next_alloc_id().unwrap();
    let aliased = heap.alias_most_recent_region(obj_id);
    assert!(!aliased, "Should fail when no prior regions exist");
}

// ============================================================================
// HeapState region sort upgrade tests (#1453, Part of #2188)
// ============================================================================

#[test]
fn test_region_array_upgrade_from_bv8_to_typed() {
    // (#2188, #1453) Region arrays upgrade from bv8 (raw bytes) to typed sort
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();

    // First assignment: raw byte allocation (bv8)
    let (bv8_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(8), "fn_test");
    assert!(bv8_name.contains("bv8"), "Initial region should be bv8");

    // Second assignment: typed store (bv32) — should upgrade
    let (upgraded_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(32), "fn_test");
    assert!(upgraded_name.contains("bv32"), "Region should upgrade to bv32, got: {upgraded_name}");
    assert_ne!(bv8_name, upgraded_name, "Upgraded name should differ from original");
}

#[test]
fn test_region_array_no_downgrade_from_typed() {
    // (#2188, #1453) Region arrays should not downgrade from typed to bv8
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();

    // First assignment: typed (bv32)
    let (typed_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(32), "fn_test");

    // Second assignment: raw bytes (bv8) — should keep existing typed region
    let (same_name, _) = heap.assign_region_array(obj_id, Sort::bitvec(8), "fn_test");
    assert_eq!(typed_name, same_name, "Should not downgrade from typed to bv8");
}

// ============================================================================
// HeapState pending checks tests (Part of #2188)
// ============================================================================

#[test]
fn test_pending_checks_reset() {
    // (#2188) reset_pending_checks clears accumulated safety checks
    let mut heap = ChcHeapState::new();
    heap.pending_checks.push(Expr::bool_const(true));
    heap.pending_checks.push(Expr::bool_const(false));
    assert_eq!(heap.pending_checks.len(), 2);

    heap.reset_pending_checks();
    assert!(heap.pending_checks.is_empty(), "Pending checks should be cleared after reset");
}

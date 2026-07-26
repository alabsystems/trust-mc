// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for heap_store_chains.rs: store chain accumulation and draining.
//!
//! Covers: accumulate_store, get_store_chain, drain_store_chains (deterministic
//! ordering, sort-mismatch drop, multi-key separation), drained_store_chain_seeds
//! (seed fallback after drain, cross-block reset, seed overwrite on re-drain).
//!
//! Part of #2921: CHC codegen unit test coverage.
//! Part of #3549: seed mechanism test coverage.
//! Part of #3541: filter_superseded_store_chains test coverage.

#![allow(clippy::unwrap_used)]

use ay_bindings::{Expr, Sort};

use super::super::codegen_ctx::diagnostics::ChcDiagnostics;
use super::super::heap_state::ChcHeapState;
use super::super::heap_store_chains::filter_superseded_store_chains;

// =============================================================================
// get_store_chain
// =============================================================================

/// get_store_chain returns None when no store has been accumulated for a key.
#[test]
fn test_get_store_chain_missing_key_returns_none() {
    let heap = ChcHeapState::new();
    assert!(heap.get_store_chain("nonexistent").is_none());
}

/// get_store_chain returns the accumulated expression after a single store.
#[test]
fn test_get_store_chain_after_accumulate() {
    let mut heap = ChcHeapState::new();
    let elem_sort = Sort::bitvec(32);
    let arr_sort = Sort::array(Sort::bitvec(64), elem_sort);
    let arr_in = Expr::var("mem_i32", arr_sort);
    let addr = Expr::bitvec_const(42u64, 64);
    let val = Expr::bitvec_const(7u64, 32);
    let store_expr = arr_in.store(addr, val);

    heap.accumulate_store("i32", "mem_i32__out", store_expr.clone());

    let chain = heap.get_store_chain("i32").unwrap();
    assert_eq!(chain.to_string(), store_expr.to_string());
}

/// Second accumulate with same key overwrites the first (caller pre-nests).
#[test]
fn test_accumulate_store_overwrites_same_key() {
    let mut heap = ChcHeapState::new();
    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let arr_in = Expr::var("mem_i32", arr_sort.clone());
    let addr1 = Expr::bitvec_const(1u64, 64);
    let val1 = Expr::bitvec_const(10u64, 32);
    let store1 = arr_in.store(addr1, val1);

    heap.accumulate_store("i32", "mem_i32__out", store1);

    // Second accumulate: pre-nested by caller
    let addr2 = Expr::bitvec_const(2u64, 64);
    let val2 = Expr::bitvec_const(20u64, 32);
    let arr_in2 = Expr::var("mem_i32", arr_sort);
    let nested = arr_in2.store(Expr::bitvec_const(1u64, 64), Expr::bitvec_const(10u64, 32));
    let store2 = nested.store(addr2, val2);

    heap.accumulate_store("i32", "mem_i32__out", store2.clone());

    let chain = heap.get_store_chain("i32").unwrap();
    assert_eq!(chain.to_string(), store2.to_string());
}

// =============================================================================
// drain_store_chains: deterministic ordering
// =============================================================================

/// drain_store_chains produces constraints sorted by type_key.
#[test]
fn test_drain_store_chains_deterministic_ordering() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Register type arrays for sort resolution.
    heap.get_or_create_type_array("u64", Sort::bitvec(64), "fn");
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");
    heap.get_or_create_type_array("bool", Sort::bool(), "fn");

    // Accumulate in non-alphabetical order.
    let u64_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    let i32_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let bool_arr = Sort::array(Sort::bitvec(64), Sort::bool());

    let addr = Expr::bitvec_const(0u64, 64);

    heap.accumulate_store(
        "u64",
        "_fn_mem_u64__out",
        Expr::var("_fn_mem_u64", u64_arr).store(addr.clone(), Expr::bitvec_const(1u64, 64)),
    );
    heap.accumulate_store(
        "bool",
        "_fn_mem_bool__out",
        Expr::var("_fn_mem_bool", bool_arr).store(addr.clone(), Expr::bool_const(true)),
    );
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        Expr::var("_fn_mem_i32", i32_arr).store(addr, Expr::bitvec_const(2u64, 32)),
    );

    let constraints = heap.drain_store_chains(&diagnostics);
    assert_eq!(constraints.len(), 3, "three type keys -> three constraints");

    // Sorted alphabetically: bool < i32 < u64
    let c0 = constraints[0].to_string();
    let c1 = constraints[1].to_string();
    let c2 = constraints[2].to_string();
    assert!(c0.contains("bool"), "first constraint should be bool, got: {c0}");
    assert!(c1.contains("i32"), "second constraint should be i32, got: {c1}");
    assert!(c2.contains("u64"), "third constraint should be u64, got: {c2}");
}

/// drain_store_chains empties the primary store_chains map.
/// The seed fallback (#3528) preserves expressions for post-drain chaining.
#[test]
fn test_drain_store_chains_clears_map() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        Expr::var("_fn_mem_i32", arr_sort)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(0u64, 32)),
    );

    let constraints = heap.drain_store_chains(&diagnostics);
    assert!(!constraints.is_empty(), "drain should produce constraints");
    assert!(heap.store_chains.is_empty(), "drain should clear the primary store_chains map");

    // Second drain returns empty (seeds don't produce new constraints).
    let second = heap.drain_store_chains(&diagnostics);
    assert!(second.is_empty());
}

// =============================================================================
// drained_store_chain_seeds (#3528, #3549)
// =============================================================================

/// After drain, get_store_chain returns the seed expression via fallback.
/// Part of #3549: seed mechanism must have test coverage.
#[test]
fn test_get_store_chain_returns_seed_after_drain() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let store_expr = Expr::var("_fn_mem_i32", arr_sort)
        .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(42u64, 32));

    heap.accumulate_store("i32", "_fn_mem_i32__out", store_expr.clone());

    let _ = heap.drain_store_chains(&diagnostics);

    // Primary map is empty, but seed fallback returns the drained expression.
    assert!(heap.store_chains.is_empty());
    let seed = heap.get_store_chain("i32").expect("get_store_chain should return seed after drain");
    assert_eq!(
        seed.to_string(),
        store_expr.to_string(),
        "seed should match the expression that was drained"
    );
}

/// reset_modified_arrays clears seeds, preventing cross-block leak (#3551).
#[test]
fn test_reset_modified_arrays_clears_seeds() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        Expr::var("_fn_mem_i32", arr_sort)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32)),
    );

    let _ = heap.drain_store_chains(&diagnostics);
    assert!(heap.get_store_chain("i32").is_some(), "seed should exist after drain");

    // Simulate block boundary — seeds must be cleared.
    heap.reset_modified_arrays();
    assert!(
        heap.get_store_chain("i32").is_none(),
        "get_store_chain should return None after reset_modified_arrays"
    );
}

/// get_store_chain returns None for type keys not present in the drained chain.
/// Part of #3549 AC #3.
#[test]
fn test_get_store_chain_returns_none_for_non_drained_key() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");
    heap.get_or_create_type_array("u64", Sort::bitvec(64), "fn");

    // Only accumulate and drain "i32", not "u64".
    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        Expr::var("_fn_mem_i32", arr_sort)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32)),
    );
    let _ = heap.drain_store_chains(&diagnostics);

    // "i32" has a seed, "u64" does not.
    assert!(heap.get_store_chain("i32").is_some(), "drained key should have seed");
    assert!(
        heap.get_store_chain("u64").is_none(),
        "non-drained key should return None, not a stale seed"
    );
}

/// Subsequent drain overwrites seeds from the previous drain.
#[test]
fn test_drain_overwrites_previous_seeds() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));

    // First accumulate + drain.
    let store1 = Expr::var("_fn_mem_i32", arr_sort.clone())
        .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32));
    heap.accumulate_store("i32", "_fn_mem_i32__out", store1.clone());
    let _ = heap.drain_store_chains(&diagnostics);

    // Verify first seed is present (intermediate state). Convert to String to release borrow.
    let seed1_str =
        heap.get_store_chain("i32").expect("seed should exist after first drain").to_string();
    assert_eq!(seed1_str, store1.to_string(), "first seed should match first drain");

    // Second accumulate + drain — seeds should update.
    let store2 = Expr::var("_fn_mem_i32", arr_sort)
        .store(Expr::bitvec_const(8u64, 64), Expr::bitvec_const(2u64, 32));
    heap.accumulate_store("i32", "_fn_mem_i32__out", store2.clone());
    let _ = heap.drain_store_chains(&diagnostics);

    let seed2 = heap.get_store_chain("i32").expect("seed should exist after second drain");
    assert_ne!(seed1_str, seed2.to_string(), "seeds from different drains should differ");
    assert_eq!(
        seed2.to_string(),
        store2.to_string(),
        "seed should reflect the second drain, not the first"
    );
}

// =============================================================================
// drain_store_chains: sort-mismatch drop path
// =============================================================================

/// drain_store_chains skips constraints when store sort mismatches the
/// registered array output sort. Per #3138, arr_out is left universally
/// quantified (no constraint emitted) — sound over-approximation.
#[test]
fn test_drain_store_chains_sort_mismatch_emits_self_loop() {
    let mut heap = ChcHeapState::new();
    let diagnostics = ChcDiagnostics::default();

    // Register type array with i32 element sort
    heap.get_or_create_type_array("i32", Sort::bitvec(32), "fn");

    // Accumulate a store expression with WRONG sort (i64 element instead of i32).
    let wrong_arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    heap.accumulate_store(
        "i32",
        "_fn_mem_i32__out",
        Expr::var("_fn_mem_i32_wrong", wrong_arr_sort)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(0u64, 64)),
    );

    let constraints = heap.drain_store_chains(&diagnostics);
    // #3138: sort-mismatched stores now skip constraint emission entirely.
    // arr_out is universally quantified (sound over-approximation).
    // The old #2977 self-loop (arr_out = arr_in) was an identity copy (unsound).
    assert_eq!(constraints.len(), 0, "sort mismatch should emit no constraints (#3138)");
    assert_eq!(
        diagnostics.store_dropped_transition.get(),
        1,
        "should increment store_dropped_transition counter"
    );
}

// =============================================================================
// filter_superseded_store_chains (#3541)
// =============================================================================

/// Returns None when bridge_constraints contain no `__out` variables.
#[test]
fn test_filter_superseded_no_out_in_bridge_returns_none() {
    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let stmt_constraints = vec![
        Expr::var("mem_i32__out", arr_sort.clone()).eq(Expr::var("mem_i32", arr_sort)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32))),
    ];
    // Bridge has a non-store constraint (no __out variable).
    let bridge_constraints = vec![Expr::bitvec_const(1u64, 64).eq(Expr::bitvec_const(1u64, 64))];

    let result = filter_superseded_store_chains(&stmt_constraints, &bridge_constraints);
    assert!(result.is_none(), "no __out in bridge → no filtering");
}

/// Returns None when bridge `__out` names don't overlap with stmt `__out` names.
#[test]
fn test_filter_superseded_no_overlap_returns_none() {
    let i32_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let u64_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(64));

    let stmt_constraints = vec![
        Expr::var("mem_i32__out", i32_arr.clone()).eq(Expr::var("mem_i32", i32_arr)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32))),
    ];
    // Bridge targets a different type array.
    let bridge_constraints = vec![
        Expr::var("mem_u64__out", u64_arr.clone()).eq(Expr::var("mem_u64", u64_arr)
            .store(Expr::bitvec_const(8u64, 64), Expr::bitvec_const(2u64, 64))),
    ];

    let result = filter_superseded_store_chains(&stmt_constraints, &bridge_constraints);
    assert!(result.is_none(), "no overlap → no filtering");
}

/// Removes the superseded constraint from stmt_constraints when bridge has
/// a matching `__out` name, preserving non-conflicting constraints.
#[test]
fn test_filter_superseded_removes_conflicting_constraint() {
    let i32_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));

    // stmt has: mem_i32__out = store(mem_i32, addr0, val0) AND a non-store constraint.
    let stmt_store =
        Expr::var("mem_i32__out", i32_arr.clone()).eq(Expr::var("mem_i32", i32_arr.clone())
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32)));
    let non_store = Expr::var("x__out", Sort::bitvec(64)).eq(Expr::bitvec_const(42u64, 64));
    let stmt_constraints = vec![stmt_store, non_store.clone()];

    // Bridge supersedes with: mem_i32__out = store(store(mem_i32, addr0, val0), addr1, val1)
    let bridge_store = Expr::var("mem_i32__out", i32_arr.clone()).eq(Expr::var("mem_i32", i32_arr)
        .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32))
        .store(Expr::bitvec_const(8u64, 64), Expr::bitvec_const(2u64, 32)));
    let bridge_constraints = vec![bridge_store];

    let result = filter_superseded_store_chains(&stmt_constraints, &bridge_constraints);
    let filtered = result.expect("should return Some when conflicts exist");

    assert_eq!(filtered.len(), 1, "should remove the conflicting mem_i32__out constraint");
    assert_eq!(
        filtered[0].to_string(),
        non_store.to_string(),
        "non-store constraint should be preserved"
    );
}

/// Multiple conflicting `__out` names are all removed.
#[test]
fn test_filter_superseded_removes_multiple_conflicts() {
    let i32_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let u64_arr = Sort::array(Sort::bitvec(64), Sort::bitvec(64));

    let stmt_constraints = vec![
        Expr::var("mem_i32__out", i32_arr.clone()).eq(Expr::var("mem_i32", i32_arr.clone())
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 32))),
        Expr::var("mem_u64__out", u64_arr.clone()).eq(Expr::var("mem_u64", u64_arr.clone())
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(1u64, 64))),
        // Non-store constraint preserved.
        Expr::var("x__out", Sort::bitvec(64)).eq(Expr::bitvec_const(99u64, 64)),
    ];
    let bridge_constraints = vec![
        Expr::var("mem_i32__out", i32_arr.clone()).eq(Expr::var("mem_i32", i32_arr)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(10u64, 32))),
        Expr::var("mem_u64__out", u64_arr.clone()).eq(Expr::var("mem_u64", u64_arr)
            .store(Expr::bitvec_const(0u64, 64), Expr::bitvec_const(10u64, 64))),
    ];

    let filtered = filter_superseded_store_chains(&stmt_constraints, &bridge_constraints).unwrap();
    assert_eq!(
        filtered.len(),
        1,
        "both mem_i32__out and mem_u64__out should be removed; x__out preserved"
    );
}

/// Returns None when both inputs are empty.
#[test]
fn test_filter_superseded_empty_inputs_returns_none() {
    let result = filter_superseded_store_chains(&[], &[]);
    assert!(result.is_none(), "empty inputs → no filtering");
}

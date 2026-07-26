// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_ctx/clusters.rs — field-cluster sub-structs
//! for ChcCtx data encapsulation.
//!
//! Covers:
//! - StateVarManager: push_state_var_pair, push_state_var_pair_arc,
//!   state_var_index_by_name, output_state_var_index_by_name,
//!   try_state_idx_for_local
//! - LivenessState: constructor and dead_locals_at_entry initialization
//! - FlattenState: (no production methods beyond trivial new())
//!
//! Part of #2921: CHC zero-coverage remediation (clusters.rs: 242 LOC, 0 tests).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use ay_bindings::Sort;
use std::collections::HashSet;
use std::sync::Arc;

use super::super::codegen_ctx::clusters::{LivenessState, StateVarManager};

// =============================================================================
// StateVarManager: push_state_var_pair + name lookups
// =============================================================================

/// Pushing a state var pair makes it retrievable by input name.
#[test]
fn test_state_var_mgr_push_pair_lookup_by_input_name() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("x", "x__out", Sort::bitvec(32));

    assert_eq!(mgr.state_var_index_by_name("x"), Some(0));
}

/// Pushing a state var pair makes it retrievable by output name.
#[test]
fn test_state_var_mgr_push_pair_lookup_by_output_name() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("y", "y__out", Sort::bitvec(64));

    assert_eq!(mgr.output_state_var_index_by_name("y__out"), Some(0));
}

/// Multiple pushes assign sequential indices.
#[test]
fn test_state_var_mgr_sequential_indices() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("a", "a__out", Sort::bitvec(32));
    mgr.push_state_var_pair("b", "b__out", Sort::bitvec(64));
    mgr.push_state_var_pair("c", "c__out", Sort::bool());

    assert_eq!(mgr.state_var_index_by_name("a"), Some(0));
    assert_eq!(mgr.state_var_index_by_name("b"), Some(1));
    assert_eq!(mgr.state_var_index_by_name("c"), Some(2));
    assert_eq!(mgr.output_state_var_index_by_name("a__out"), Some(0));
    assert_eq!(mgr.output_state_var_index_by_name("b__out"), Some(1));
    assert_eq!(mgr.output_state_var_index_by_name("c__out"), Some(2));
}

/// Input and output name lookups return None for non-existent names.
#[test]
fn test_state_var_mgr_lookup_missing_returns_none() {
    let mgr = StateVarManager::new();

    assert_eq!(mgr.state_var_index_by_name("nonexistent"), None);
    assert_eq!(mgr.output_state_var_index_by_name("nonexistent"), None);
}

/// state_vars and output_state_vars vectors maintain corresponding entries.
#[test]
fn test_state_var_mgr_vectors_consistent() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("x", "x__out", Sort::bitvec(32));

    assert_eq!(mgr.state_vars.len(), 1);
    assert_eq!(mgr.output_state_vars.len(), 1);
    assert_eq!(&*mgr.state_vars[0].0, "x");
    assert_eq!(&*mgr.output_state_vars[0].0, "x__out");
    assert_eq!(mgr.state_vars[0].1, Sort::bitvec(32));
    assert_eq!(mgr.output_state_vars[0].1, Sort::bitvec(32));
}

// =============================================================================
// StateVarManager: push_state_var_pair_arc (Arc<str> path)
// =============================================================================

/// push_state_var_pair_arc inserts the name into the index via shared Arc.
#[test]
fn test_state_var_mgr_push_pair_arc_lookup() {
    let mut mgr = StateVarManager::new();
    let name: Arc<str> = Arc::from("heap_region_0");
    mgr.push_state_var_pair_arc(name, "heap_region_0__out", Sort::bitvec(8));

    assert_eq!(mgr.state_var_index_by_name("heap_region_0"), Some(0));
    assert_eq!(mgr.output_state_var_index_by_name("heap_region_0__out"), Some(0));
}

/// push_state_var_pair_arc stores the String conversion in state_vars.
#[test]
fn test_state_var_mgr_push_pair_arc_stores_string_in_vec() {
    let mut mgr = StateVarManager::new();
    let name: Arc<str> = Arc::from("obj_valid");
    mgr.push_state_var_pair_arc(name, "obj_valid__out", Sort::bool());

    assert_eq!(&*mgr.state_vars[0].0, "obj_valid");
    assert_eq!(&*mgr.output_state_vars[0].0, "obj_valid__out");
}

/// Mixing push_state_var_pair and push_state_var_pair_arc produces correct indices.
#[test]
fn test_state_var_mgr_mixed_push_methods() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("a", "a__out", Sort::bitvec(32));
    mgr.push_state_var_pair_arc(Arc::from("b"), "b__out", Sort::bitvec(64));
    mgr.push_state_var_pair("c", "c__out", Sort::bool());

    assert_eq!(mgr.state_var_index_by_name("a"), Some(0));
    assert_eq!(mgr.state_var_index_by_name("b"), Some(1));
    assert_eq!(mgr.state_var_index_by_name("c"), Some(2));
    assert_eq!(mgr.state_vars.len(), 3);
}

// =============================================================================
// StateVarManager: try_state_idx_for_local
// =============================================================================

/// try_state_idx_for_local returns None when no mapping exists.
#[test]
fn test_state_var_mgr_try_state_idx_for_local_missing() {
    let mgr = StateVarManager::new();
    assert_eq!(mgr.try_state_idx_for_local(0), None);
    assert_eq!(mgr.try_state_idx_for_local(42), None);
}

/// try_state_idx_for_local returns the mapped index after insertion.
#[test]
fn test_state_var_mgr_try_state_idx_for_local_after_insert() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("local_0", "local_0__out", Sort::bitvec(32));
    mgr.local_to_state_idx.insert(0, 0);

    assert_eq!(mgr.try_state_idx_for_local(0), Some(0));
    assert_eq!(mgr.try_state_idx_for_local(1), None);
}

/// Multiple local mappings coexist correctly.
#[test]
fn test_state_var_mgr_multiple_local_mappings() {
    let mut mgr = StateVarManager::new();
    mgr.push_state_var_pair("v0", "v0__out", Sort::bitvec(32));
    mgr.push_state_var_pair("v1", "v1__out", Sort::bitvec(64));
    mgr.local_to_state_idx.insert(3, 0); // MIR local 3 -> state var 0
    mgr.local_to_state_idx.insert(7, 1); // MIR local 7 -> state var 1

    assert_eq!(mgr.try_state_idx_for_local(3), Some(0));
    assert_eq!(mgr.try_state_idx_for_local(7), Some(1));
    assert_eq!(mgr.try_state_idx_for_local(0), None);
}

// =============================================================================
// LivenessState: constructor
// =============================================================================

/// LivenessState::new initializes dead_locals_at_entry and empty dead_locals.
#[test]
fn test_liveness_state_new_initializes_fields() {
    let entry: Vec<HashSet<usize>> =
        vec![HashSet::from([1, 2]), HashSet::from([3]), HashSet::new()];
    let state = LivenessState::new(entry);

    assert_eq!(state.dead_locals_at_entry.len(), 3);
    assert!(state.dead_locals_at_entry[0].contains(&1));
    assert!(state.dead_locals_at_entry[0].contains(&2));
    assert!(state.dead_locals_at_entry[1].contains(&3));
    assert!(state.dead_locals_at_entry[2].is_empty());
    assert!(state.dead_locals.is_empty(), "dead_locals should start empty");
}

// FlattenState: no production methods beyond trivial new().
// test_flatten_state_field_interactions deleted per #2312 — only exercised
// HashSet/HashMap insert/get on public fields, not production logic.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_ctx/types.rs — helper types used by CHC codegen.
//!
//! Covers:
//! - ChcDebugMode and WideMemMode enum conversions
//! - ChcCollectionLenState: len/cap tracking, modification state, clear
//! - CollectionCallResult: constructors (read_only, mutating, clear, forced_failure, new_collection)
//! - CollectionProjectionKind: equality/clone
//!
//! Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use ay_bindings::{Expr, Sort};

use super::super::codegen_ctx::types::{
    ChcCollectionLenState, ChcDebugMode, CollectionCallResult, CollectionProjectionKind,
    WideMemMode,
};

// =============================================================================
// ChcDebugMode
// =============================================================================

#[test]
fn test_chc_debug_mode_from_bool_true() {
    let mode: ChcDebugMode = true.into();
    assert_eq!(mode, ChcDebugMode::On);
}

#[test]
fn test_chc_debug_mode_from_bool_false() {
    let mode: ChcDebugMode = false.into();
    assert_eq!(mode, ChcDebugMode::Off);
}

#[test]
fn test_chc_debug_mode_equality() {
    assert_eq!(ChcDebugMode::Off, ChcDebugMode::Off);
    assert_eq!(ChcDebugMode::On, ChcDebugMode::On);
    assert_ne!(ChcDebugMode::Off, ChcDebugMode::On);
}

#[test]
fn test_chc_debug_mode_clone_copy() {
    let mode = ChcDebugMode::On;
    let copied = mode;
    let cloned = mode;
    assert_eq!(copied, ChcDebugMode::On);
    assert_eq!(cloned, ChcDebugMode::On);
}

// =============================================================================
// WideMemMode
// =============================================================================

#[test]
fn test_wide_mem_mode_from_bool_true() {
    let mode: WideMemMode = true.into();
    assert_eq!(mode, WideMemMode::On);
}

#[test]
fn test_wide_mem_mode_from_bool_false() {
    let mode: WideMemMode = false.into();
    assert_eq!(mode, WideMemMode::Off);
}

#[test]
fn test_wide_mem_mode_equality() {
    assert_eq!(WideMemMode::Off, WideMemMode::Off);
    assert_eq!(WideMemMode::On, WideMemMode::On);
    assert_ne!(WideMemMode::Off, WideMemMode::On);
}

// =============================================================================
// ChcCollectionLenState
// =============================================================================

#[test]
fn test_collection_len_state_new_is_empty() {
    let state = ChcCollectionLenState::new();
    assert!(state.len_var_names.is_empty());
    assert!(state.modified_len_vars.is_empty());
    assert!(state.cap_var_names.is_empty());
    assert!(state.modified_cap_vars.is_empty());
}

#[test]
fn test_collection_len_state_get_len_var_missing() {
    let state = ChcCollectionLenState::new();
    assert!(state.get_len_var(42).is_none());
}

#[test]
fn test_collection_len_state_get_len_var_present() {
    let mut state = ChcCollectionLenState::new();
    state.len_var_names.insert(3, std::sync::Arc::from("hashmap_len_local_3"));

    let result = state.get_len_var(3);
    let expected: std::sync::Arc<str> = "hashmap_len_local_3".into();
    assert_eq!(result, Some(&expected));
}

#[test]
fn test_collection_len_state_get_cap_var_missing() {
    let state = ChcCollectionLenState::new();
    assert!(state.get_cap_var(1).is_none());
}

#[test]
fn test_collection_len_state_get_cap_var_present() {
    let mut state = ChcCollectionLenState::new();
    state.cap_var_names.insert(1, std::sync::Arc::from("vec_cap_local_1"));

    let result = state.get_cap_var(1);
    let expected: std::sync::Arc<str> = "vec_cap_local_1".into();
    assert_eq!(result, Some(&expected));
}

#[test]
fn test_collection_len_state_mark_len_modified() {
    let mut state = ChcCollectionLenState::new();
    assert!(!state.modified_len_vars.contains("len_x"));

    state.mark_len_modified("len_x");
    assert!(state.modified_len_vars.contains("len_x"));
    assert!(!state.modified_len_vars.contains("len_y"));
}

#[test]
fn test_collection_len_state_mark_len_modified_idempotent() {
    let mut state = ChcCollectionLenState::new();
    state.mark_len_modified("len_x");
    state.mark_len_modified("len_x"); // second call should not duplicate
    assert_eq!(state.modified_len_vars.len(), 1);
}

#[test]
fn test_collection_len_state_mark_cap_modified() {
    let mut state = ChcCollectionLenState::new();
    assert!(!state.modified_cap_vars.contains("cap_x"));

    state.mark_cap_modified("cap_x");
    assert!(state.modified_cap_vars.contains("cap_x"));
    assert!(!state.modified_cap_vars.contains("cap_y"));
}

#[test]
fn test_collection_len_state_mark_cap_modified_idempotent() {
    let mut state = ChcCollectionLenState::new();
    state.mark_cap_modified("cap_x");
    state.mark_cap_modified("cap_x");
    assert_eq!(state.modified_cap_vars.len(), 1);
}

#[test]
fn test_collection_len_state_clear_modified() {
    let mut state = ChcCollectionLenState::new();
    state.len_var_names.insert(1, std::sync::Arc::from("len_1"));
    state.cap_var_names.insert(1, std::sync::Arc::from("cap_1"));
    state.mark_len_modified("len_1");
    state.mark_cap_modified("cap_1");

    assert!(state.modified_len_vars.contains("len_1"));
    assert!(state.modified_cap_vars.contains("cap_1"));

    state.clear_modified();

    assert!(!state.modified_len_vars.contains("len_1"));
    assert!(!state.modified_cap_vars.contains("cap_1"));
    // Var names should be preserved after clear_modified
    let expected_len: std::sync::Arc<str> = "len_1".into();
    let expected_cap: std::sync::Arc<str> = "cap_1".into();
    assert_eq!(state.get_len_var(1), Some(&expected_len));
    assert_eq!(state.get_cap_var(1), Some(&expected_cap));
}

// =============================================================================
// CollectionCallResult constructors
// =============================================================================

#[test]
fn test_collection_call_result_read_only() {
    let val = Expr::bitvec_const(42u64, 32);
    let result = CollectionCallResult::read_only(val);

    assert!(result.map_update.is_none(), "read_only should not have map_update");
    assert!(result.result.is_some(), "read_only should have result");
    assert!(result.len_update.is_none(), "read_only should not have len_update");
    assert!(result.constraints.is_empty(), "read_only should have no constraints");
}

#[test]
fn test_collection_call_result_new_collection_with_len() {
    let val = Expr::const_array(Sort::bitvec(32), Expr::bool_const(false));
    let len = Expr::bitvec_const(0u64, 64);
    let result = CollectionCallResult::new_collection(val, Some(len));

    assert!(result.map_update.is_none(), "new_collection should not have map_update");
    assert!(result.result.is_some(), "new_collection should have result");
    assert!(result.len_update.is_some(), "new_collection should have len_update when provided");
    assert!(result.constraints.is_empty(), "new_collection should have no constraints");
}

#[test]
fn test_collection_call_result_new_collection_without_len() {
    let val = Expr::const_array(Sort::bitvec(32), Expr::bool_const(false));
    let result = CollectionCallResult::new_collection(val, None);

    assert!(result.len_update.is_none(), "new_collection without len should have no len_update");
}

#[test]
fn test_collection_call_result_mutating() {
    let map = Expr::var("new_map", Sort::array(Sort::bitvec(32), Sort::bool()));
    let val = Expr::bool_const(true);
    let len = Expr::bitvec_const(1u64, 64);
    let result = CollectionCallResult::mutating(map, val, Some(len));

    assert!(result.map_update.is_some(), "mutating should have map_update");
    assert!(result.result.is_some(), "mutating should have result");
    assert!(result.len_update.is_some(), "mutating should have len_update");
    assert!(result.constraints.is_empty(), "mutating should have no constraints");
}

#[test]
fn test_collection_call_result_clear() {
    let empty_map = Expr::const_array(Sort::bitvec(32), Expr::bool_const(false));
    let zero_len = Expr::bitvec_const(0u64, 64);
    let result = CollectionCallResult::clear(empty_map, Some(zero_len));

    assert!(result.map_update.is_some(), "clear should have map_update");
    assert!(result.result.is_none(), "clear should not have result");
    assert!(result.len_update.is_some(), "clear should have len_update");
    assert!(result.constraints.is_empty(), "clear should have no constraints");
}

#[test]
fn test_collection_call_result_forced_failure() {
    let result = CollectionCallResult::forced_failure();

    assert!(result.map_update.is_none(), "forced_failure should not have map_update");
    assert!(result.result.is_none(), "forced_failure should not have result");
    assert!(result.len_update.is_none(), "forced_failure should not have len_update");
    assert!(
        result.constraints.is_empty(),
        "forced_failure should not encode fail-closed semantics via constraints"
    );
    assert!(result.force_error, "forced_failure should request fail-closed error emission");
}

// =============================================================================
// CollectionProjectionKind
// =============================================================================

#[test]
fn test_collection_projection_kind_equality() {
    assert_eq!(CollectionProjectionKind::Vec, CollectionProjectionKind::Vec);
    assert_eq!(CollectionProjectionKind::VecIntoIter, CollectionProjectionKind::VecIntoIter);
    assert_eq!(
        CollectionProjectionKind::HashMapIntoIter,
        CollectionProjectionKind::HashMapIntoIter
    );
    assert_eq!(
        CollectionProjectionKind::HashSetIntoIter,
        CollectionProjectionKind::HashSetIntoIter
    );
    assert_ne!(CollectionProjectionKind::Vec, CollectionProjectionKind::VecIntoIter);
    assert_ne!(
        CollectionProjectionKind::HashMapIntoIter,
        CollectionProjectionKind::HashSetIntoIter
    );
}

#[test]
fn test_collection_projection_kind_clone_copy() {
    let kind = CollectionProjectionKind::Vec;
    let copied = kind;
    let cloned = kind;
    assert_eq!(copied, CollectionProjectionKind::Vec);
    assert_eq!(cloned, CollectionProjectionKind::Vec);
}

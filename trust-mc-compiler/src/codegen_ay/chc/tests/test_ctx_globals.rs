// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_ctx/globals.rs — global statics, counters,
//! and thread-local accumulators used by CHC codegen.
//!
//! Covers:
//! - chc_fresh_name: generates unique prefixed names
//! - declare_pending_var: creates an Expr and registers VarDecl
//! - take_undef_counter / UNDEF_COUNTER reset
//! - TYPE_SORT_FALLBACK via ChcDiagnostics (per-ctx counter)
//! - UNHANDLED_CALL via ChcDiagnostics (per-ctx counter)
//! - CHC_FALLBACK_COUNTS: per-function fallback map
//! - PENDING_FRESH_VAR_DECLS: thread-local accumulator
//!
//! Part of #2921: CHC zero-coverage remediation.
//! Part of #2906: counter registry consolidation (Mutex elimination).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use ay_bindings::Sort;

use super::super::codegen_ctx::globals::{
    PENDING_FRESH_VAR_DECLS, PendingFreshVarDeclsPanicGuard, UNDEF_COUNTER, chc_fresh_name,
    declare_pending_var, get_chc_fallback_counts, set_chc_fallback_count_for_fn,
    set_chc_fallback_count_for_test, take_chc_fallback_counts, take_undef_counter,
};

// =============================================================================
// chc_fresh_name
// =============================================================================

#[test]
fn test_chc_fresh_name_has_prefix_and_counter() {
    let name = chc_fresh_name("test_var");
    assert!(name.starts_with("test_var_"), "name should start with prefix: {name}");
    // Verify it contains a numeric suffix after the underscore
    let suffix = name.strip_prefix("test_var_").unwrap();
    assert!(suffix.parse::<u64>().is_ok(), "suffix should be numeric: {suffix}");
}

#[test]
fn test_chc_fresh_name_increments_counter() {
    let name1 = chc_fresh_name("seq");
    let name2 = chc_fresh_name("seq");

    let n1: u64 = name1.strip_prefix("seq_").unwrap().parse().unwrap();
    let n2: u64 = name2.strip_prefix("seq_").unwrap().parse().unwrap();

    assert!(n2 > n1, "counter should monotonically increase: {name1} -> {name2}");
}

#[test]
fn test_chc_fresh_name_empty_prefix() {
    let name = chc_fresh_name("");
    assert!(name.starts_with('_'), "empty prefix should still produce _N: {name}");
}

// =============================================================================
// declare_pending_var
// =============================================================================

#[test]
fn test_declare_pending_var_creates_expr_with_correct_sort() {
    // Clear thread-local state first
    PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow_mut().clear());

    let name = chc_fresh_name("dpv_test");
    let sort = Sort::bitvec(32);
    let expr = declare_pending_var(name.clone(), sort);

    assert_eq!(expr.sort().bitvec_width(), Some(32));
    assert!(
        matches!(expr.value(), ay_bindings::ExprValue::Var { name: n } if *n == name),
        "expr should be a Var with matching name"
    );
}

#[test]
fn test_declare_pending_var_registers_var_decl() {
    PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow_mut().clear());

    let name = chc_fresh_name("dpv_reg");
    let sort = Sort::bool();
    let _expr = declare_pending_var(name.clone(), sort);

    let pending = PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow().clone());
    assert_eq!(pending.len(), 1, "should have registered one VarDecl");
    assert_eq!(&*pending[0].name, name.as_str());
}

#[test]
fn test_declare_pending_var_multiple_accumulate() {
    PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow_mut().clear());

    let _e1 = declare_pending_var(chc_fresh_name("a"), Sort::bitvec(8));
    let _e2 = declare_pending_var(chc_fresh_name("b"), Sort::bitvec(16));
    let _e3 = declare_pending_var(chc_fresh_name("c"), Sort::bool());

    let pending = PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow().clone());
    assert_eq!(pending.len(), 3, "should have accumulated 3 VarDecls");
}

// =============================================================================
// UNDEF_COUNTER
// =============================================================================

#[test]
fn test_take_undef_counter_resets_to_zero() {
    // Force a known counter state
    let _ = chc_fresh_name("undef_test");
    let prev = take_undef_counter();
    assert!(prev > 0, "counter should have been incremented");

    let after = UNDEF_COUNTER.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(after, 0, "take should reset counter to zero");
}

// =============================================================================
// TYPE_SORT_FALLBACK via ChcDiagnostics (Part of #2906)
// =============================================================================

/// Per-ctx type_sort_fallback counter uses CellCounter semantics.
/// No Mutex needed — each test gets its own ChcDiagnostics instance.
#[test]
fn test_type_sort_fallback_diagnostics_increment() {
    use super::super::codegen_ctx::ChcDiagnostics;
    use super::super::codegen_ctx::diagnostics::CellCounter;

    let diag = ChcDiagnostics::default();
    assert_eq!(diag.type_sort_fallback.get(), 0, "default should be 0");

    diag.type_sort_fallback.inc();
    diag.type_sort_fallback.inc();
    assert_eq!(diag.type_sort_fallback.get(), 2, "after two incs, should be 2");
}

/// Per-ctx type_sort_fallback default resets via Default::default().
#[test]
fn test_type_sort_fallback_diagnostics_fresh_is_zero() {
    use super::super::codegen_ctx::ChcDiagnostics;

    let diag1 = ChcDiagnostics::default();
    diag1.type_sort_fallback.set(42);

    // New instance starts fresh — no cross-context leakage.
    let diag2 = ChcDiagnostics::default();
    assert_eq!(diag2.type_sort_fallback.get(), 0, "new instance should start at zero");
}

// =============================================================================
// UNHANDLED_CALL_COUNT via ChcDiagnostics (Part of #2906)
// =============================================================================

/// Per-ctx unhandled_call counter via ChcDiagnostics (Part of #2906).
#[test]
fn test_unhandled_call_count_set_get_take() {
    use super::super::codegen_ctx::ChcDiagnostics;
    use super::super::codegen_ctx::diagnostics::CellCounter;

    let diag = ChcDiagnostics::default();
    assert_eq!(diag.unhandled_call.get(), 0, "default should be 0");

    diag.unhandled_call.inc();
    diag.unhandled_call.inc();
    assert_eq!(diag.unhandled_call.get(), 2, "after two incs, should be 2");
}

// =============================================================================
// CHC_FALLBACK_COUNTS (per-function map) — still uses global BTreeMap
// No Mutex<()> needed: set_chc_fallback_count_for_fn overwrites per function
// name, and test-unique names prevent cross-test interference (Part of #2906).
// =============================================================================

#[test]
fn test_chc_fallback_counts_set_and_get() {
    // Unique names prevent cross-test interference without needing Mutex<()>.
    set_chc_fallback_count_for_fn("__test_set_get_a", 3);
    set_chc_fallback_count_for_fn("__test_set_get_b", 7);

    let counts = get_chc_fallback_counts();
    assert_eq!(counts.get("__test_set_get_a"), Some(&3));
    assert_eq!(counts.get("__test_set_get_b"), Some(&7));
}

#[test]
fn test_chc_fallback_counts_zero_removes_entry() {
    set_chc_fallback_count_for_fn("__test_zero_removes", 5);
    assert_eq!(get_chc_fallback_counts().get("__test_zero_removes"), Some(&5));

    set_chc_fallback_count_for_fn("__test_zero_removes", 0);
    assert!(
        !get_chc_fallback_counts().contains_key("__test_zero_removes"),
        "zero count should remove the entry"
    );
}

#[test]
fn test_chc_fallback_counts_take_returns_entries() {
    set_chc_fallback_count_for_test("__test_take_entry", 10);
    let taken = take_chc_fallback_counts();

    // Verify our entry was included in the taken map.
    assert_eq!(taken.get("__test_take_entry"), Some(&10));
    // Note: we do NOT assert the map is empty after take — parallel tests
    // may have inserted entries between take and get (Part of #2906).
}

#[test]
fn test_chc_fallback_counts_update_existing_entry() {
    set_chc_fallback_count_for_fn("__test_update", 2);
    set_chc_fallback_count_for_fn("__test_update", 8);

    let counts = get_chc_fallback_counts();
    assert_eq!(counts.get("__test_update"), Some(&8), "should overwrite with new value");
}

// =============================================================================
// PENDING_FRESH_VAR_DECLS panic-leak detection (#2950)
// =============================================================================

/// The unwind guard used by `translate_inner()` must clear pending declarations
/// if translation panics before the success-path drain.
#[test]
fn test_pending_fresh_var_decls_guard_clears_on_panic() {
    // Clear thread-local state
    PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow_mut().clear());

    // Simulate translate_inner(): arm guard, push vars, then panic before drain.
    let result = std::panic::catch_unwind(|| {
        let _guard = PendingFreshVarDeclsPanicGuard::arm();
        let _e1 = declare_pending_var(chc_fresh_name("leak_a"), Sort::bitvec(8));
        let _e2 = declare_pending_var(chc_fresh_name("leak_b"), Sort::bitvec(16));
        // Simulate a panic before translate_inner() reaches its success-path drain.
        panic!("simulated panic during CHC translation");
    });
    assert!(result.is_err(), "should have caught the panic");

    // Guard clears pending vars on unwind so the next translation starts clean.
    let leaked_count = PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow().len());
    assert_eq!(leaked_count, 0, "PENDING_FRESH_VAR_DECLS should be empty after panic unwind guard");
}

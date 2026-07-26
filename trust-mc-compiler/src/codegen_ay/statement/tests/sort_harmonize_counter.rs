// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for sort_harmonize fresh-var fallback counter (#3366).
//!
//! Verifies that the `SORT_HARMONIZE_FRESH_VAR_COUNT` global atomic counter
//! correctly increments on each of the three fresh-var fallback paths in
//! `sort_harmonize.rs`, and does NOT increment on successful conversions.

use super::*;

/// Serializes access to SORT_HARMONIZE_FRESH_VAR_COUNT across tests.
///
/// Any test that reads or drains the global sort_harmonize counter must hold
/// this lock to prevent concurrent threads from draining/incrementing between
/// before/after reads.
static SORT_HARMONIZE_COUNTER_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Part of #3366: Datatype→BitVec conversion with Int-leaf struct triggers
/// fresh-var fallback and increments sort_harmonize counter.
///
/// When flatten_datatype_to_bitvec fails (Int fields can't flatten to BV),
/// convert_expr_to_sort creates a fresh unconstrained symbolic variable and
/// increments the counter.
#[test]
fn test_sort_harmonize_fresh_var_counter_datatype_to_bitvec_fallback() {
    let _lock =
        SORT_HARMONIZE_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    // Drain any prior counter state from other tests.
    take_sort_harmonize_fresh_var_count();

    // Struct with Int field — flatten_datatype_to_bitvec returns None for Int leaves.
    let dt_sort = struct_sort("IntLeafStruct", [("value", Sort::int()), ("extra", Sort::int())]);
    let dt_expr = Expr::var("int_leaf", dt_sort);

    let converted = StatementCodegen::convert_expr_to_sort(dt_expr, &Sort::bitvec(64), None);

    // Should produce a fresh symbolic BV variable (not the original Datatype expr).
    assert!(
        converted.sort().is_bitvec(),
        "fallback should produce BitVec sort, got {:?}",
        converted.sort()
    );
    assert!(
        matches!(converted.value(), ExprValue::Var { name } if name.starts_with("dt_to_bv_phi_")),
        "expected fresh symbolic var dt_to_bv_phi_*, got {:?}",
        converted.value()
    );

    let count = take_sort_harmonize_fresh_var_count();
    assert_eq!(count, 1, "Datatype→BitVec fallback should increment counter once");
}

/// Part of #3366: BitVec→Datatype conversion with narrow BV triggers
/// fresh-var fallback and increments sort_harmonize counter.
///
/// When unflatten_bitvec_to_datatype fails (BV too narrow for struct),
/// convert_expr_to_sort creates a fresh unconstrained symbolic variable.
#[test]
fn test_sort_harmonize_fresh_var_counter_bitvec_to_datatype_fallback() {
    let _lock =
        SORT_HARMONIZE_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    take_sort_harmonize_fresh_var_count();

    // Target Datatype needs 64 bits but source BV is only 8 — unflatten will fail.
    let target_sort = struct_sort("WideStruct", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);
    let bv_expr = Expr::bitvec_const(0u64, 8);

    let converted = StatementCodegen::convert_expr_to_sort(bv_expr, &target_sort, None);

    // Should produce a fresh symbolic Datatype variable.
    assert!(
        converted.sort().datatype_name().is_some(),
        "fallback should produce Datatype sort, got {:?}",
        converted.sort()
    );
    assert!(
        matches!(converted.value(), ExprValue::Var { name } if name.starts_with("bv_to_dt_phi_")),
        "expected fresh symbolic var bv_to_dt_phi_*, got {:?}",
        converted.value()
    );

    let count = take_sort_harmonize_fresh_var_count();
    assert_eq!(count, 1, "BitVec→Datatype fallback should increment counter once");
}

/// Part of #3366: catch-all sort mismatch triggers fresh-var fallback
/// and increments sort_harmonize counter.
///
/// When no specific conversion arm matches (e.g., non-BigInt Datatype→Int),
/// the catch-all creates a fresh unconstrained symbolic variable.
#[test]
fn test_sort_harmonize_fresh_var_counter_catchall_mismatch() {
    let _lock =
        SORT_HARMONIZE_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    take_sort_harmonize_fresh_var_count();

    // Non-BigInt multi-field struct → Int: no specific conversion arm matches.
    let dt_sort = struct_sort("PlainStruct", [("a", Sort::bitvec(32)), ("b", Sort::bitvec(32))]);
    let dt_expr = Expr::var("plain", dt_sort);

    let converted = StatementCodegen::convert_expr_to_sort(dt_expr, &Sort::int(), None);

    // Should produce a fresh symbolic Int variable.
    assert!(
        converted.sort().is_int(),
        "fallback should produce Int sort, got {:?}",
        converted.sort()
    );
    assert!(
        matches!(converted.value(), ExprValue::Var { name } if name.starts_with("sort_mismatch_phi_")),
        "expected fresh symbolic var sort_mismatch_phi_*, got {:?}",
        converted.value()
    );

    let count = take_sort_harmonize_fresh_var_count();
    assert_eq!(count, 1, "catch-all fallback should increment counter once");
}

/// Part of #3366: successful sort conversion does NOT increment the counter.
///
/// Verifies that the counter only fires on actual fallback paths, not on
/// legitimate conversions (BitVec→Int, Int→BitVec, etc.).
#[test]
fn test_sort_harmonize_fresh_var_counter_no_increment_on_success() {
    let _lock =
        SORT_HARMONIZE_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    take_sort_harmonize_fresh_var_count();

    // These conversions all succeed without fresh-var fallback.
    let _ =
        StatementCodegen::convert_expr_to_sort(Expr::bitvec_const(42u64, 32), &Sort::int(), None);
    let _ = StatementCodegen::convert_expr_to_sort(
        Expr::var("x", Sort::int()),
        &Sort::bitvec(32),
        None,
    );
    let _ = StatementCodegen::convert_expr_to_sort(
        Expr::var("flag", Sort::bool()),
        &Sort::bitvec(8),
        None,
    );
    let _ = StatementCodegen::convert_expr_to_sort(
        Expr::var("status", Sort::bitvec(8)),
        &Sort::bool(),
        None,
    );

    let count = take_sort_harmonize_fresh_var_count();
    assert_eq!(count, 0, "successful conversions should not increment counter");
}

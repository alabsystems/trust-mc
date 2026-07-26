// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_coroutine_state.rs` — pure-function CoroutineState
//! expression construction and coercion helpers.
//!
//! Part of #4127.
//!
//! Covers:
//! - `try_construct_coroutine_state_expr`: ITE-based yield-or-complete construction
//! - `try_construct_coroutine_state_variant_expr`: single-variant construction
//! - `coerce_coroutine_result_to_sort`: sort coercion across BV/Bool/Datatype
//! - Negative: non-Datatype sorts must return None
//! - Edge: single-constructor Datatypes (Yielded-only, Complete-only)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::codegen_call_coroutine::test_wrappers::{
    test_coerce_coroutine_result_to_sort, test_try_construct_coroutine_state_complete_expr,
    test_try_construct_coroutine_state_expr, test_try_construct_coroutine_state_yielded_expr,
};
use ay_bindings::{Expr, ExprValue, Sort};
use trust_mc_codegen_types::names::enum_sort;

/// Build a CoroutineState<i32, i32> Datatype sort with Yielded and Complete
/// constructors, each carrying a single BV32 payload field.
fn coroutine_state_sort_bv32() -> Sort {
    enum_sort(
        "CoroutineState_i32_i32",
        vec![
            ("Yielded", vec![("yield_val", Sort::bitvec(32))]),
            ("Complete", vec![("complete_val", Sort::bitvec(32))]),
        ],
    )
}

/// Build a CoroutineState<(), i32> sort — Yielded payload is ZST (Bool placeholder).
fn coroutine_state_sort_yield_zst() -> Sort {
    enum_sort(
        "CoroutineState_unit_i32",
        vec![
            ("Yielded", vec![("yield_val", Sort::bool())]),
            ("Complete", vec![("complete_val", Sort::bitvec(32))]),
        ],
    )
}

/// Build a CoroutineState with only a Yielded constructor (no Complete).
fn coroutine_state_sort_yielded_only() -> Sort {
    enum_sort(
        "CoroutineState_yielded_only",
        vec![("Yielded", vec![("yield_val", Sort::bitvec(32))])],
    )
}

/// Build a CoroutineState with only a Complete constructor (no Yielded).
fn coroutine_state_sort_complete_only() -> Sort {
    enum_sort(
        "CoroutineState_complete_only",
        vec![("Complete", vec![("complete_val", Sort::bitvec(32))])],
    )
}

// =========================================================================
// try_construct_coroutine_state_expr tests
// =========================================================================

#[test]
fn test_construct_coroutine_state_both_branches_produces_ite() {
    let sort = coroutine_state_sort_bv32();
    let result = test_try_construct_coroutine_state_expr(&sort, false, false, true);
    let expr = result.expect("should produce an expression for a 2-constructor Datatype");

    // The result should be an ITE choosing between Yielded and Complete.
    assert!(
        matches!(expr.value(), ExprValue::Ite { .. }),
        "two-constructor CoroutineState with allow_complete=true should produce ITE, got: {:?}",
        expr.value()
    );
    assert_eq!(
        expr.sort(),
        &sort,
        "constructed expression sort should match the CoroutineState sort"
    );
}

#[test]
fn test_construct_coroutine_state_yielded_only_no_ite() {
    let sort = coroutine_state_sort_bv32();
    let result = test_try_construct_coroutine_state_expr(&sort, false, false, false);
    let expr = result.expect("should produce an expression with allow_complete=false");

    // With allow_complete_branch=false, should produce just Yielded, not ITE.
    assert!(
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, .. }
            if constructor_name.contains("Yielded") || constructor_name.contains("ield")
        ),
        "allow_complete=false should produce DatatypeConstructor(Yielded), got: {:?}",
        expr.value()
    );
}

#[test]
fn test_construct_coroutine_state_non_datatype_returns_none() {
    let bv_sort = Sort::bitvec(64);
    let result = test_try_construct_coroutine_state_expr(&bv_sort, false, false, true);
    assert!(result.is_none(), "non-Datatype sort should return None");
}

#[test]
fn test_construct_coroutine_state_bool_sort_returns_none() {
    let bool_sort = Sort::bool();
    let result = test_try_construct_coroutine_state_expr(&bool_sort, false, false, true);
    assert!(result.is_none(), "Bool sort should return None (not a Datatype)");
}

#[test]
fn test_construct_coroutine_state_single_yielded_constructor() {
    let sort = coroutine_state_sort_yielded_only();
    let result = test_try_construct_coroutine_state_expr(&sort, false, false, true);
    let expr = result.expect("single Yielded constructor should produce an expression");

    // With only Yielded available, should produce DatatypeConstructor directly.
    assert!(
        matches!(expr.value(), ExprValue::DatatypeConstructor { .. }),
        "single-constructor sort should produce DatatypeConstructor, got: {:?}",
        expr.value()
    );
}

#[test]
fn test_construct_coroutine_state_single_complete_constructor() {
    let sort = coroutine_state_sort_complete_only();
    let result = test_try_construct_coroutine_state_expr(&sort, false, false, true);
    let expr = result.expect("single Complete constructor should produce an expression");

    assert!(
        matches!(
            expr.value(),
            ExprValue::DatatypeConstructor { constructor_name, .. }
            if constructor_name.contains("Complete") || constructor_name.contains("omplete")
        ),
        "single Complete constructor should produce DatatypeConstructor(Complete), got: {:?}",
        expr.value()
    );
}

#[test]
fn test_construct_coroutine_state_yield_zst_payload_is_bool_true() {
    let sort = coroutine_state_sort_yield_zst();
    let result = test_try_construct_coroutine_state_yielded_expr(&sort, true, false);
    let expr = result.expect("Yielded variant with ZST payload should produce an expression");

    // When yield_is_zst=true and field sort is Bool, the payload should be
    // `true` (not a fresh symbolic variable).
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value() {
        assert_eq!(args.len(), 1, "Yielded should have exactly one field");
        assert!(
            matches!(args[0].value(), ExprValue::BoolConst(true)),
            "ZST yield payload should be `true`, got: {:?}",
            args[0].value()
        );
    } else {
        panic!("expected DatatypeConstructor for Yielded, got: {:?}", expr.value());
    }
}

// =========================================================================
// try_construct_coroutine_state_variant_expr tests
// =========================================================================

#[test]
fn test_construct_yielded_variant_produces_yielded_constructor() {
    let sort = coroutine_state_sort_bv32();
    let result = test_try_construct_coroutine_state_yielded_expr(&sort, false, false);
    let expr = result.expect("Yielded variant should produce an expression");

    if let ExprValue::DatatypeConstructor { constructor_name, args, .. } = expr.value() {
        assert!(
            constructor_name.contains("Yielded") || constructor_name.contains("ield"),
            "constructor should be Yielded, got: {constructor_name}"
        );
        assert_eq!(args.len(), 1, "Yielded should have one payload field");
        assert_eq!(args[0].sort(), &Sort::bitvec(32), "Yielded payload should be BV32");
    } else {
        panic!("expected DatatypeConstructor, got: {:?}", expr.value());
    }
}

#[test]
fn test_construct_complete_variant_produces_complete_constructor() {
    let sort = coroutine_state_sort_bv32();
    let result = test_try_construct_coroutine_state_complete_expr(&sort, false, false);
    let expr = result.expect("Complete variant should produce an expression");

    if let ExprValue::DatatypeConstructor { constructor_name, args, .. } = expr.value() {
        assert!(
            constructor_name.contains("Complete") || constructor_name.contains("omplete"),
            "constructor should be Complete, got: {constructor_name}"
        );
        assert_eq!(args.len(), 1, "Complete should have one payload field");
        assert_eq!(args[0].sort(), &Sort::bitvec(32), "Complete payload should be BV32");
    } else {
        panic!("expected DatatypeConstructor, got: {:?}", expr.value());
    }
}

#[test]
fn test_construct_yielded_variant_missing_returns_none() {
    // Sort with only Complete constructor — asking for Yielded should return None.
    let sort = coroutine_state_sort_complete_only();
    let result = test_try_construct_coroutine_state_yielded_expr(&sort, false, false);
    assert!(
        result.is_none(),
        "requesting Yielded variant from Complete-only sort should return None"
    );
}

#[test]
fn test_construct_complete_variant_missing_returns_none() {
    // Sort with only Yielded constructor — asking for Complete should return None.
    let sort = coroutine_state_sort_yielded_only();
    let result = test_try_construct_coroutine_state_complete_expr(&sort, false, false);
    assert!(
        result.is_none(),
        "requesting Complete variant from Yielded-only sort should return None"
    );
}

// =========================================================================
// coerce_coroutine_result_to_sort tests
// =========================================================================

#[test]
fn test_coerce_same_sort_returns_identity() {
    let bv32 = Sort::bitvec(32);
    let expr = Expr::bitvec_const(42u64, 32);
    let result = test_coerce_coroutine_result_to_sort(expr.clone(), &bv32);
    let coerced = result.expect("same-sort coercion should succeed");
    assert_eq!(coerced.sort(), &bv32, "coerced sort should match target");
}

#[test]
fn test_coerce_bool_to_bitvec_produces_ite() {
    let bv8 = Sort::bitvec(8);
    let bool_expr = Expr::bool_const(true);
    let result = test_coerce_coroutine_result_to_sort(bool_expr, &bv8);
    let coerced = result.expect("bool-to-bv8 coercion should succeed");

    assert_eq!(coerced.sort(), &bv8, "coerced expression sort should be BV8");
    // The coercion produces ITE(true, bv8(1), bv8(0)).
    assert!(
        matches!(coerced.value(), ExprValue::Ite { .. }),
        "bool-to-bitvec coercion should produce ITE, got: {:?}",
        coerced.value()
    );
}

#[test]
fn test_coerce_bitvec_to_bool_produces_ne_zero() {
    let bool_sort = Sort::bool();
    let bv_expr = Expr::bitvec_const(1u64, 8);
    let result = test_coerce_coroutine_result_to_sort(bv_expr, &bool_sort);
    let coerced = result.expect("bv8-to-bool coercion should succeed");

    assert_eq!(coerced.sort(), &bool_sort, "coerced expression sort should be Bool");
}

#[test]
fn test_coerce_narrow_bitvec_to_wider_bitvec() {
    let bv64 = Sort::bitvec(64);
    let narrow_expr = Expr::bitvec_const(255u64, 8);
    let result = test_coerce_coroutine_result_to_sort(narrow_expr, &bv64);
    let coerced = result.expect("bv8-to-bv64 coercion should succeed");

    assert_eq!(coerced.sort(), &bv64, "coerced expression sort should be BV64");
}

#[test]
fn test_coerce_wider_bitvec_to_narrow_bitvec() {
    let bv8 = Sort::bitvec(8);
    let wide_expr = Expr::bitvec_const(1024u64, 64);
    let result = test_coerce_coroutine_result_to_sort(wide_expr, &bv8);
    let coerced = result.expect("bv64-to-bv8 coercion should succeed");

    assert_eq!(coerced.sort(), &bv8, "coerced expression sort should be BV8");
}

#[test]
fn test_coerce_array_sort_returns_none() {
    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let bv_expr = Expr::bitvec_const(0u64, 32);
    let result = test_coerce_coroutine_result_to_sort(bv_expr, &arr_sort);
    assert!(result.is_none(), "bitvec-to-array coercion should return None (unsupported)");
}

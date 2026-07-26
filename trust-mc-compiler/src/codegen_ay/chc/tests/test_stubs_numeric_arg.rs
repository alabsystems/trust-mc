// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `stubs_numeric_arg.rs` — `NumericArgKind` sort acceptance,
//! coercion, and metadata methods.
//!
//! Part of #2921 (untested production file coverage).
//! Part of #2302 (cross-repo quality patterns).
//!
//! Covers:
//! - `accept_or_coerce`: sort matching and Int→Real coercion
//! - `label`, `fallback_prefix`, `fallback_sort`: metadata accessors

#![allow(clippy::unwrap_used)]

use super::super::stubs_numeric_arg::NumericArgKind;
use ay_bindings::Expr;

// =============================================================================
// NumericArgKind::BigInt — accept_or_coerce
// =============================================================================

#[test]
fn test_bigint_accepts_int_sort() {
    let expr = Expr::int_const(42);
    let result = NumericArgKind::BigInt.accept_or_coerce(&expr);
    assert!(result.is_some(), "BigInt should accept Int sort");
    assert!(result.unwrap().sort().is_int());
}

#[test]
fn test_bigint_rejects_real_sort() {
    let expr = Expr::real_const(3);
    let result = NumericArgKind::BigInt.accept_or_coerce(&expr);
    assert!(result.is_none(), "BigInt should reject Real sort");
}

#[test]
fn test_bigint_rejects_bitvec_sort() {
    let expr = Expr::bitvec_const(42u64, 32);
    let result = NumericArgKind::BigInt.accept_or_coerce(&expr);
    assert!(result.is_none(), "BigInt should reject BV sort");
}

#[test]
fn test_bigint_rejects_bool_sort() {
    let expr = Expr::bool_const(true);
    let result = NumericArgKind::BigInt.accept_or_coerce(&expr);
    assert!(result.is_none(), "BigInt should reject Bool sort");
}

// =============================================================================
// NumericArgKind::BigRational — accept_or_coerce
// =============================================================================

#[test]
fn test_bigrational_accepts_real_sort() {
    let expr = Expr::real_const(22);
    let result = NumericArgKind::BigRational.accept_or_coerce(&expr);
    assert!(result.is_some(), "BigRational should accept Real sort");
    assert!(result.unwrap().sort().is_real());
}

#[test]
fn test_bigrational_coerces_int_to_real() {
    let expr = Expr::int_const(42);
    let result = NumericArgKind::BigRational.accept_or_coerce(&expr);
    assert!(result.is_some(), "BigRational should coerce Int to Real");
    let coerced = result.unwrap();
    assert!(coerced.sort().is_real(), "coerced result should be Real sort");
}

#[test]
fn test_bigrational_rejects_bitvec_sort() {
    let expr = Expr::bitvec_const(42u64, 64);
    let result = NumericArgKind::BigRational.accept_or_coerce(&expr);
    assert!(result.is_none(), "BigRational should reject BV sort");
}

#[test]
fn test_bigrational_rejects_bool_sort() {
    let expr = Expr::bool_const(false);
    let result = NumericArgKind::BigRational.accept_or_coerce(&expr);
    assert!(result.is_none(), "BigRational should reject Bool sort");
}

// =============================================================================
// Metadata accessors
// =============================================================================

#[test]
fn test_bigint_label() {
    assert_eq!(NumericArgKind::BigInt.label(), "BigInt");
}

#[test]
fn test_bigrational_label() {
    assert_eq!(NumericArgKind::BigRational.label(), "BigRational");
}

#[test]
fn test_bigint_fallback_prefix() {
    assert_eq!(NumericArgKind::BigInt.fallback_prefix(), "bigint_arg");
}

#[test]
fn test_bigrational_fallback_prefix() {
    assert_eq!(NumericArgKind::BigRational.fallback_prefix(), "bigrational_arg");
}

#[test]
fn test_bigint_fallback_sort() {
    let sort = NumericArgKind::BigInt.fallback_sort();
    assert!(sort.is_int(), "BigInt fallback should be Int sort");
}

#[test]
fn test_bigrational_fallback_sort() {
    let sort = NumericArgKind::BigRational.fallback_sort();
    assert!(sort.is_real(), "BigRational fallback should be Real sort");
}

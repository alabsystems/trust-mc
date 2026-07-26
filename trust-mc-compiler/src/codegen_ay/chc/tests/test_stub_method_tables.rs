// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for stub_method_tables.rs: static method-to-stub mapping tables.
//!
//! Covers: lookup_method_stub correctness, table ordering (binary search
//! correctness), boundary methods, missing methods, full BigInt + BigRational
//! table coverage.
//!
//! Part of #2921: CHC codegen unit test coverage.

#![allow(clippy::unwrap_used)]

use super::super::stub_method_tables::{
    BIGINT_METHOD_STUBS, BIGRATIONAL_METHOD_STUBS, lookup_method_stub,
};
use crate::codegen_ay::stubs::StubKind;

// =============================================================================
// Table ordering (binary search correctness)
// =============================================================================

/// BigInt method table is sorted alphabetically (required for binary search).
#[test]
fn test_bigint_table_sorted() {
    for window in BIGINT_METHOD_STUBS.windows(2) {
        assert!(
            window[0].method < window[1].method,
            "BIGINT_METHOD_STUBS not sorted: {:?} >= {:?}",
            window[0].method,
            window[1].method
        );
    }
}

/// BigRational method table is sorted alphabetically.
#[test]
fn test_bigrational_table_sorted() {
    for window in BIGRATIONAL_METHOD_STUBS.windows(2) {
        assert!(
            window[0].method < window[1].method,
            "BIGRATIONAL_METHOD_STUBS not sorted: {:?} >= {:?}",
            window[0].method,
            window[1].method
        );
    }
}

// =============================================================================
// lookup_method_stub: BigInt table
// =============================================================================

/// Lookup known BigInt methods returns correct StubKind.
#[test]
fn test_bigint_lookup_known_methods() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "add"), Some(StubKind::BigIntAdd));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "sub"), Some(StubKind::BigIntSub));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "mul"), Some(StubKind::BigIntMul));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "div"), Some(StubKind::BigIntDiv));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "rem"), Some(StubKind::BigIntRem));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "abs"), Some(StubKind::BigIntAbs));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "zero"), Some(StubKind::BigIntZero));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "one"), Some(StubKind::BigIntOne));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "clone"), Some(StubKind::BigIntClone));
}

/// First and last entries are reachable (boundary check for binary search).
#[test]
fn test_bigint_lookup_boundaries() {
    // First entry: "abs"
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "abs"), Some(StubKind::BigIntAbs));
    // Last entry: "zero"
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "zero"), Some(StubKind::BigIntZero));
}

/// BigInt comparison methods are all present.
#[test]
fn test_bigint_lookup_comparison_methods() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "eq"), Some(StubKind::BigIntEq));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "lt"), Some(StubKind::BigIntLt));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "le"), Some(StubKind::BigIntLe));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "gt"), Some(StubKind::BigIntGt));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "ge"), Some(StubKind::BigIntGe));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "cmp"), Some(StubKind::BigIntCmp));
    assert_eq!(
        lookup_method_stub(BIGINT_METHOD_STUBS, "partial_cmp"),
        Some(StubKind::BigIntPartialCmp)
    );
}

/// BigInt shift operations are present.
#[test]
fn test_bigint_lookup_shift_methods() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "shl"), Some(StubKind::BigIntShl));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "shr"), Some(StubKind::BigIntShr));
    assert_eq!(
        lookup_method_stub(BIGINT_METHOD_STUBS, "shl_assign"),
        Some(StubKind::BigIntShlAssign)
    );
    assert_eq!(
        lookup_method_stub(BIGINT_METHOD_STUBS, "shr_assign"),
        Some(StubKind::BigIntShrAssign)
    );
}

// =============================================================================
// lookup_method_stub: BigRational table
// =============================================================================

/// Lookup known BigRational methods returns correct StubKind.
#[test]
fn test_bigrational_lookup_known_methods() {
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "add"), Some(StubKind::BigRationalAdd));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "sub"), Some(StubKind::BigRationalSub));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "mul"), Some(StubKind::BigRationalMul));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "div"), Some(StubKind::BigRationalDiv));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "new"), Some(StubKind::BigRationalNew));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "neg"), Some(StubKind::BigRationalNeg));
    assert_eq!(
        lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "clone"),
        Some(StubKind::BigRationalClone)
    );
}

/// BigRational comparison methods are present.
#[test]
fn test_bigrational_lookup_comparison_methods() {
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "eq"), Some(StubKind::BigRationalEq));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "lt"), Some(StubKind::BigRationalLt));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "le"), Some(StubKind::BigRationalLe));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "gt"), Some(StubKind::BigRationalGt));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "ge"), Some(StubKind::BigRationalGe));
}

// =============================================================================
// lookup_method_stub: missing/unknown methods
// =============================================================================

/// Unknown method returns None.
#[test]
fn test_lookup_unknown_method_returns_none() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "nonexistent"), None);
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "nonexistent"), None);
}

/// Empty string returns None.
#[test]
fn test_lookup_empty_method_returns_none() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, ""), None);
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, ""), None);
}

/// Method present in BigInt but not BigRational returns None for BigRational.
#[test]
fn test_lookup_cross_table_miss() {
    // "abs" is BigInt-only
    assert!(lookup_method_stub(BIGINT_METHOD_STUBS, "abs").is_some());
    assert!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "abs").is_none());

    // "new" is BigRational-only
    assert!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "new").is_some());
    assert!(lookup_method_stub(BIGINT_METHOD_STUBS, "new").is_none());
}

// =============================================================================
// Table completeness
// =============================================================================

/// BigInt table has all expected entries (no accidental deletions).
#[test]
fn test_bigint_table_size() {
    assert_eq!(BIGINT_METHOD_STUBS.len(), 32, "BigInt method table should have 32 entries");
}

/// BigRational table has all expected entries.
#[test]
fn test_bigrational_table_size() {
    assert_eq!(
        BIGRATIONAL_METHOD_STUBS.len(),
        17,
        "BigRational method table should have 17 entries"
    );
}

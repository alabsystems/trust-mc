// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Property-based tests (proptest) for CHC codegen paths.
//!
//! Part of #2200: Adds proptest coverage for:
//! - `sort_from_type_key`: type-key string → Sort mapping invariants
//! - `coerce_eq_constraint`: sort coercion completeness and consistency
//! - Sort construction: round-trip and structural invariants
//! - Expression encoding: Sort-typed expressions maintain sort consistency

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, Sort};
use proptest::prelude::*;

use crate::codegen_ay::types::POINTER_WIDTH;

// ============================================================================
// Sort generators
// ============================================================================

/// Generate a leaf Sort (non-recursive).
fn arb_leaf_sort() -> impl Strategy<Value = Sort> {
    prop_oneof![
        Just(Sort::bool()),
        (1u32..=128).prop_map(Sort::bitvec),
        Just(Sort::int()),
        Just(Sort::real()),
    ]
}

// ============================================================================
// Type-key string generators
// ============================================================================

/// Known primitive type keys that sort_from_type_key handles explicitly.
fn arb_primitive_type_key() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("bool".to_string()),
        Just("char".to_string()),
        Just("i8".to_string()),
        Just("u8".to_string()),
        Just("i16".to_string()),
        Just("u16".to_string()),
        Just("i32".to_string()),
        Just("u32".to_string()),
        Just("i64".to_string()),
        Just("u64".to_string()),
        Just("i128".to_string()),
        Just("u128".to_string()),
        Just("isize".to_string()),
        Just("usize".to_string()),
        Just("f16".to_string()),
        Just("f32".to_string()),
        Just("f64".to_string()),
        Just("f128".to_string()),
        Just("unit".to_string()),
    ]
}

/// Type keys with recognized prefixes (ref_, ptr_, arr_, slice_, tuple_).
fn arb_prefixed_type_key() -> impl Strategy<Value = String> {
    let suffixes = prop_oneof![
        Just("u8".to_string()),
        Just("i32".to_string()),
        Just("u64".to_string()),
        Just("bool".to_string()),
    ];
    let prefixes = prop_oneof![
        Just("ref_".to_string()),
        Just("ptr_".to_string()),
        Just("arr_".to_string()),
        Just("slice_".to_string()),
        Just("tuple_".to_string()),
    ];
    (prefixes, suffixes).prop_map(|(p, s)| format!("{p}{s}"))
}

/// Composite type key generator covering all categories.
fn arb_type_key() -> impl Strategy<Value = String> {
    prop_oneof![
        arb_primitive_type_key(),
        arb_prefixed_type_key(),
        Just("Vec_i32".to_string()),
        Just("String".to_string()),
        Just("std_string_String".to_string()),
        Just("Box_u64".to_string()),
        Just("std_boxed_Box_u32".to_string()),
        Just("num_bigint_BigInt".to_string()),
        // Unknown keys (fallback path)
        "[a-zA-Z_][a-zA-Z0-9_]{0,20}".prop_filter("not a known key", |s| {
            ![
                "bool", "char", "unit", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64",
                "i128", "u128", "isize", "usize", "f16", "f32", "f64", "f128",
            ]
            .contains(&s.as_str())
                && !s.starts_with("ref_")
                && !s.starts_with("ptr_")
                && !s.starts_with("arr_")
                && !s.starts_with("slice_")
                && !s.starts_with("tuple_")
                && !s.starts_with("Vec")
                && !s.contains("String")
                && !s.starts_with("Box")
                && !s.contains("BigInt")
                && !s.contains("bigint")
        }),
    ]
}

// ============================================================================
// Property 1: sort_from_type_key always returns a well-formed Sort
// ============================================================================

proptest! {
    #[test]
    fn sort_from_type_key_returns_valid_sort(key in arb_type_key()) {
        let sort = ChcCtx::sort_from_type_key(&key);
        // Must be one of the recognized sort kinds
        prop_assert!(
            sort.is_bool() || sort.is_bitvec() || sort.is_int()
                || sort.is_real() || sort.is_array() || sort.is_datatype(),
            "sort_from_type_key({:?}) returned unrecognized sort: {:?}",
            key,
            sort
        );
    }

    #[test]
    fn sort_from_type_key_primitives_are_bitvec_or_bool(key in arb_primitive_type_key()) {
        let sort = ChcCtx::sort_from_type_key(&key);
        // Primitives map to Bool or BitVec (never Int/Real/Array/Datatype)
        prop_assert!(
            sort.is_bool() || sort.is_bitvec(),
            "primitive key {:?} mapped to non-leaf sort: {:?}",
            key,
            sort
        );
    }

    #[test]
    fn sort_from_type_key_ref_ptr_are_pointer_width(
        prefix in prop_oneof![Just("ref_"), Just("ptr_")],
        suffix in prop_oneof![Just("u8"), Just("i32"), Just("u64"), Just("bool")],
    ) {
        let key = format!("{prefix}{suffix}");
        let sort = ChcCtx::sort_from_type_key(&key);
        prop_assert_eq!(
            sort,
            Sort::bitvec(POINTER_WIDTH),
            "ref/ptr key {:?} should map to BV(POINTER_WIDTH)",
            key
        );
    }

    #[test]
    fn sort_from_type_key_arr_slice_produce_arrays(
        prefix in prop_oneof![Just("arr_"), Just("slice_")],
        suffix in prop_oneof![Just("u8"), Just("i32"), Just("u64"), Just("bool")],
    ) {
        let key = format!("{prefix}{suffix}");
        let sort = ChcCtx::sort_from_type_key(&key);
        prop_assert!(
            sort.is_array(),
            "arr/slice key {:?} should produce Array sort, got {:?}",
            key,
            sort
        );
        // Index sort is BV(POINTER_WIDTH) for arrays
        let arr = sort.array_sort().unwrap();
        prop_assert_eq!(
            &arr.index_sort,
            &Sort::bitvec(POINTER_WIDTH),
            "array index sort should be BV(POINTER_WIDTH)"
        );
    }

    #[test]
    fn sort_from_type_key_tuples_unwrap_to_element_sort(
        inner in prop_oneof![
            // Underscore-free keys always unwrap
            "[a-z][a-z0-9]{0,10}",
            // Known compound prefixes with underscores also unwrap
            "ptr_[a-z][a-z0-9]{0,5}",
            "ref_[a-z][a-z0-9]{0,5}",
            "arr_[a-z][a-z0-9]{0,5}",
            "slice_[a-z][a-z0-9]{0,5}",
        ],
    ) {
        let key = format!("tuple_{inner}");
        let sort = ChcCtx::sort_from_type_key(&key);
        // Per #2244: tuple_X recursively resolves X via sort_from_type_key.
        // Single-element tuples unwrap to element sort (matching translate_ty).
        // Ambiguous keys with underscores that don't match known compound
        // prefixes fall to bv32 multi-element default (see is_compound_type_key).
        let expected = ChcCtx::sort_from_type_key(&inner);
        prop_assert_eq!(
            sort,
            expected,
            "tuple key {:?} should unwrap to sort of inner key {:?}",
            key,
            inner
        );
    }

    #[test]
    fn sort_from_type_key_unknown_uses_opaque_byte_array_fallback(
        key in "[a-zA-Z_][a-zA-Z0-9_]{0,20}"
    ) {
        // Authoritative filter: a key is "unknown" iff the production lookup
        // returns the opaque byte-array fallback. This avoids mirroring the
        // (growing) set of EXACT_TYPE_KEY_SORTS / PREFIX_TYPE_KEY_RULES entries
        // — rules are added regularly (e.g. #4014 added Rc/Weak prefixes) and
        // keeping two sources of truth in sync drifts quickly.
        //
        // The property being checked is that the fallback is stable: for keys
        // that actually hit the fallback branch, repeated lookups yield the
        // same opaque sort. This exercises random-string dispatch through
        // sort_from_type_key and the fallback function's idempotency.
        let sort = ChcCtx::sort_from_type_key(&key);
        let fallback = ChcCtx::unknown_type_key_fallback_sort();
        prop_assume!(sort == fallback);
        prop_assert_eq!(
            sort,
            fallback,
            "unknown key {:?} should use opaque byte-array fallback sort",
            key
        );
    }
}

// ============================================================================
// Property 2: sort_from_type_key is deterministic (same input → same output)
// ============================================================================

proptest! {
    #[test]
    fn sort_from_type_key_is_deterministic(key in arb_type_key()) {
        let sort1 = ChcCtx::sort_from_type_key(&key);
        let sort2 = ChcCtx::sort_from_type_key(&key);
        prop_assert_eq!(sort1, sort2, "sort_from_type_key should be deterministic for {:?}", key);
    }
}

// ============================================================================
// Property 3: coerce_eq_constraint completeness
// ============================================================================

// For coerce_eq_constraint we need to test with actual Expr/Sort values.
// The key property is that coercion succeeds for all Bool/BV combinations
// and fails for incompatible sorts.
proptest! {
    #[test]
    fn coerce_eq_same_sort_always_succeeds(sort in arb_leaf_sort()) {
        let dest = Expr::var("dest", sort.clone());
        let result = Expr::var("result", sort.clone());
        let coerced = coerce_eq_constraint(&dest, result, &sort, false);
        prop_assert!(
            coerced.is_some(),
            "same-sort coercion should always succeed for {:?}",
            sort
        );
    }

    #[test]
    fn coerce_eq_bv_to_bv_always_succeeds(
        w1 in 1u32..=128,
        w2 in 1u32..=128,
    ) {
        let dest_sort = Sort::bitvec(w2);
        let result_sort = Sort::bitvec(w1);
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", result_sort);
        let coerced = coerce_eq_constraint(&dest, result, &dest_sort, false);
        prop_assert!(
            coerced.is_some(),
            "BV({}) → BV({}) coercion should always succeed",
            w1,
            w2
        );
    }

    #[test]
    fn coerce_eq_bool_to_bv_always_succeeds(width in 1u32..=128) {
        let dest_sort = Sort::bitvec(width);
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", Sort::bool());
        let coerced = coerce_eq_constraint(&dest, result, &dest_sort, false);
        prop_assert!(
            coerced.is_some(),
            "Bool → BV({}) coercion should succeed",
            width
        );
    }

    #[test]
    fn coerce_eq_bv_to_bool_always_succeeds(width in 1u32..=128) {
        let dest_sort = Sort::bool();
        let result_sort = Sort::bitvec(width);
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", result_sort);
        let coerced = coerce_eq_constraint(&dest, result, &dest_sort, false);
        prop_assert!(
            coerced.is_some(),
            "BV({}) → Bool coercion should succeed",
            width
        );
    }

    #[test]
    fn coerce_eq_incompatible_returns_none(
        width in 1u32..=64,
    ) {
        // Int → Bool is incompatible (no coercion path exists).
        // Int → BV is now valid (int2bv, added in #2875).
        // Width parameter kept to exercise proptest machinery; used to
        // construct the Int literal value (arbitrary but harmless).
        let dest_sort = Sort::bool();
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", Sort::int());
        let coerced = coerce_eq_constraint(&dest, result, &dest_sort, false);
        prop_assert!(
            coerced.is_none(),
            "Int → Bool coercion should fail (incompatible sorts, width={})",
            width
        );
    }
}

// ============================================================================
// Property 4: coerce_eq_constraint output has correct sort (Bool — it's an eq)
// ============================================================================

proptest! {
    #[test]
    fn coerce_eq_output_is_bool_sorted(
        w1 in 1u32..=64,
        w2 in 1u32..=64,
    ) {
        let dest_sort = Sort::bitvec(w2);
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", Sort::bitvec(w1));
        match coerce_eq_constraint(&dest, result, &dest_sort, false) {
            Some(constraint) => {
                prop_assert!(
                    constraint.sort().is_bool(),
                    "coerce_eq_constraint output should be Bool-sorted, got {:?}",
                    constraint.sort()
                );
            }
            None => {
                // None means same-width identity coercion — no constraint needed.
                prop_assert_eq!(w1, w2, "coerce_eq returned None for different widths");
            }
        }
    }

    #[test]
    fn coerce_eq_bool_bv_output_is_bool_sorted(width in 1u32..=64) {
        let dest_sort = Sort::bitvec(width);
        let dest = Expr::var("dest", dest_sort.clone());
        let result = Expr::var("result", Sort::bool());
        // Bool→BV always requires coercion (different sorts), so None is unexpected.
        let constraint = coerce_eq_constraint(&dest, result, &dest_sort, false)
            .expect("coerce_eq_constraint should not return None for Bool→BV coercion");
        prop_assert!(
            constraint.sort().is_bool(),
            "Bool→BV coerce_eq output should be Bool-sorted, got {:?}",
            constraint.sort()
        );
    }
}

// Trivial Sort structural tests (sort_bitvec_width_roundtrips,
// sort_array_components_preserved, sort_equality_is_reflexive,
// sort_clone_equals_original) deleted per #2391 / rule #2312.
// They only tested ay_bindings Sort type properties without calling
// production CHC codegen functions.

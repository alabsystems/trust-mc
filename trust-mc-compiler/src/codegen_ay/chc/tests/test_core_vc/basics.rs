// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_primitive_cmp_method_classification() {
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord::cmp"), Some("cmp"));
    assert_eq!(
        ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::partial_cmp"),
        Some("partial_cmp")
    );
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::lt"), Some("lt"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::le"), Some("le"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::gt"), Some("gt"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::ge"), Some("ge"));

    // Guard regression: `std::cmp::...::lt` must not be classified as `cmp`.
    assert_ne!(ChcCtx::primitive_cmp_method("std::cmp::PartialOrd::lt"), Some("cmp"));

    // BigInt comparators are handled by dedicated BigInt stubs.
    assert_eq!(ChcCtx::primitive_cmp_method("num_bigint::BigInt::cmp"), None);
}

#[test]
fn test_step_unchecked_method_classification() {
    assert_eq!(
        ChcCtx::step_unchecked_method("<usize as std::iter::Step>::forward_unchecked"),
        Some(true)
    );
    assert_eq!(ChcCtx::step_unchecked_method("core::iter::Step::backward_unchecked"), Some(false));
    assert_eq!(ChcCtx::step_unchecked_method("std::cmp::PartialOrd::lt"), None);
}

// Deleted: test_frame_condition_generation_logic — #2312, tested AY Expr.eq/not, not production frame codegen.

#[test]
#[allow(clippy::useless_conversion)] // usize.into() needed for Local type
fn test_nondet_fallback_marks_plain_local() {
    let lhs = Place { local: 0usize.into(), projection: vec![] };
    let mut modified = HashSet::new();

    let did_mark = ChcCtx::mark_modified_for_unsupported_rvalue(&lhs, &mut modified);

    assert!(did_mark);
    assert!(modified.contains(&0));
}

#[test]
#[allow(clippy::useless_conversion)] // usize.into() needed for Local type
fn test_nondet_fallback_marks_projected_place_root() {
    // #767: Projected places should mark the root local as modified
    // e.g., `*_1 = <unsupported>` marks _1 (whole aggregate becomes nondet)
    // This test uses Deref projection; same applies to Field and other projections.
    let lhs = Place { local: 1usize.into(), projection: vec![ProjectionElem::Deref] };
    let mut modified = HashSet::new();

    let did_mark = ChcCtx::mark_modified_for_unsupported_rvalue(&lhs, &mut modified);

    assert!(did_mark);
    assert!(modified.contains(&1));
}

#[test]
fn test_sort_short_name_bool() {
    let sort = Sort::bool();
    assert_eq!(names::sort_short_name(&sort), "bool");
}

#[test]
fn test_sort_short_name_bitvec() {
    assert_eq!(names::sort_short_name(&Sort::bitvec(32)), "bv32");
    assert_eq!(names::sort_short_name(&Sort::bitvec(64)), "bv64");
}

#[test]
fn test_sort_short_name_int() {
    assert_eq!(names::sort_short_name(&Sort::int()), "int");
}

#[test]
fn test_tuple_sort_name() {
    let fields = vec![("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bool())];
    assert_eq!(ChcCtx::tuple_sort_name(&fields), "Tuple_bv32_bool");
}

#[test]
fn test_tuple_sort_name_single_field() {
    let fields = vec![("fld_0", Sort::int())];
    assert_eq!(ChcCtx::tuple_sort_name(&fields), "Tuple_int");
}

#[test]
fn test_tuple_sort_name_three_fields() {
    let fields =
        vec![("fld_0", Sort::bitvec(8)), ("fld_1", Sort::bitvec(16)), ("fld_2", Sort::bitvec(32))];
    assert_eq!(ChcCtx::tuple_sort_name(&fields), "Tuple_bv8_bv16_bv32");
}

#[test]
fn test_tuple_sort_name_empty() {
    // Edge case: empty tuple (unit type)
    let fields: Vec<(&str, Sort)> = vec![];
    assert_eq!(ChcCtx::tuple_sort_name(&fields), "Tuple");
}

#[test]
fn test_sort_short_name_real() {
    // Real sort should return "real"
    let sort = Sort::real();
    assert_eq!(names::sort_short_name(&sort), "real");
}

#[test]
fn test_sort_short_name_array() {
    // Array sorts now include index and element sort names to avoid collisions (#822)
    let array_sort = Sort::array(Sort::int(), Sort::bool());
    assert_eq!(names::sort_short_name(&array_sort), "arr_int_bool");

    // Different array types should have different names
    let array_sort2 = Sort::array(Sort::int(), Sort::int());
    assert_eq!(names::sort_short_name(&array_sort2), "arr_int_int");

    // Nested arrays should work up to depth limit
    let nested = Sort::array(Sort::int(), Sort::array(Sort::bool(), Sort::int()));
    assert_eq!(names::sort_short_name(&nested), "arr_int_arr_bool_int");
}

// Deleted: test_assert_error_rule_encoding, test_assert_bitvector_condition_to_bool,
// test_assert_int_condition_to_bool, test_entry_rule_structure
// Reason: #2312 — tested AY Expr/Rule/RelationApp library constructors, not production codegen.

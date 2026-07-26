// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for chc/memory_type_key_tables.rs.
// Covers: EXACT_TYPE_KEY_SORTS sort invariant, exact key → sort mapping,
// PREFIX_TYPE_KEY_RULES match predicates, and prefix rule sort construction.
// Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::memory_type_key_tables::{EXACT_TYPE_KEY_SORTS, PREFIX_TYPE_KEY_RULES};
use crate::codegen_ay::types::POINTER_WIDTH;

// =============================================================================
// EXACT_TYPE_KEY_SORTS — sort order invariant (binary search correctness)
// =============================================================================

#[test]
fn test_exact_table_is_sorted_by_key() {
    for window in EXACT_TYPE_KEY_SORTS.windows(2) {
        assert!(
            window[0].0 < window[1].0,
            "EXACT_TYPE_KEY_SORTS is not sorted: {:?} should precede {:?} (byte order)",
            window[0].0,
            window[1].0
        );
    }
}

#[test]
fn test_exact_table_has_no_duplicate_keys() {
    let mut seen = std::collections::HashSet::new();
    for (key, _) in EXACT_TYPE_KEY_SORTS {
        assert!(seen.insert(*key), "duplicate key in EXACT_TYPE_KEY_SORTS: {key}");
    }
}

// =============================================================================
// EXACT_TYPE_KEY_SORTS — primitive integer sorts
// =============================================================================

#[test]
fn test_exact_table_i8_produces_bv8() {
    let entry = EXACT_TYPE_KEY_SORTS.iter().find(|(k, _)| *k == "i8");
    assert!(entry.is_some(), "i8 should be in exact table");
    let sort = (entry.unwrap().1)();
    assert!(sort.is_bitvec());
    assert_eq!(sort.bitvec_width(), Some(8));
}

#[test]
fn test_exact_table_i16_produces_bv16() {
    let sort = exact_sort("i16");
    assert_eq!(sort.bitvec_width(), Some(16));
}

#[test]
fn test_exact_table_i32_produces_bv32() {
    let sort = exact_sort("i32");
    assert_eq!(sort.bitvec_width(), Some(32));
}

#[test]
fn test_exact_table_i64_produces_bv64() {
    let sort = exact_sort("i64");
    assert_eq!(sort.bitvec_width(), Some(64));
}

#[test]
fn test_exact_table_i128_produces_bv128() {
    let sort = exact_sort("i128");
    assert_eq!(sort.bitvec_width(), Some(128));
}

#[test]
fn test_exact_table_u8_produces_bv8() {
    let sort = exact_sort("u8");
    assert_eq!(sort.bitvec_width(), Some(8));
}

#[test]
fn test_exact_table_u32_produces_bv32() {
    let sort = exact_sort("u32");
    assert_eq!(sort.bitvec_width(), Some(32));
}

#[test]
fn test_exact_table_u64_produces_bv64() {
    let sort = exact_sort("u64");
    assert_eq!(sort.bitvec_width(), Some(64));
}

#[test]
fn test_exact_table_u128_produces_bv128() {
    let sort = exact_sort("u128");
    assert_eq!(sort.bitvec_width(), Some(128));
}

#[test]
fn test_exact_table_usize_produces_pointer_width_bv() {
    let sort = exact_sort("usize");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_exact_table_isize_produces_pointer_width_bv() {
    let sort = exact_sort("isize");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// EXACT_TYPE_KEY_SORTS — bool, char, floats, unit
// =============================================================================

#[test]
fn test_exact_table_bool_produces_bool_sort() {
    let sort = exact_sort("bool");
    assert!(sort.is_bool());
}

#[test]
fn test_exact_table_char_produces_bv32() {
    let sort = exact_sort("char");
    assert_eq!(sort.bitvec_width(), Some(32));
}

#[test]
fn test_exact_table_f32_produces_bv32() {
    let sort = exact_sort("f32");
    assert_eq!(sort.bitvec_width(), Some(32));
}

#[test]
fn test_exact_table_f64_produces_bv64() {
    let sort = exact_sort("f64");
    assert_eq!(sort.bitvec_width(), Some(64));
}

#[test]
fn test_exact_table_unit_produces_bool_sort() {
    let sort = exact_sort("unit");
    assert!(sort.is_bool());
}

// =============================================================================
// EXACT_TYPE_KEY_SORTS — allocator/infra types
// =============================================================================

#[test]
fn test_exact_table_layout_produces_bv128() {
    let sort = exact_sort("Layout");
    assert_eq!(sort.bitvec_width(), Some(128));
}

#[test]
fn test_exact_table_alignment_produces_pointer_width() {
    let sort = exact_sort("Alignment");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_exact_table_alloc_error_produces_bool() {
    let sort = exact_sort("AllocError");
    assert!(sort.is_bool());
}

#[test]
fn test_exact_table_global_produces_bool() {
    let sort = exact_sort("Global");
    assert!(sort.is_bool());
}

#[test]
fn test_exact_table_infallible_produces_bool() {
    let sort = exact_sort("Infallible");
    assert!(sort.is_bool());
}

// Part of #3521: ControlFlow removed from EXACT_TYPE_KEY_SORTS — now a proper Datatype.
#[test]
fn test_exact_table_control_flow_removed() {
    let result = EXACT_TYPE_KEY_SORTS.binary_search_by_key(&"ControlFlow", |(k, _)| *k);
    assert!(result.is_err(), "ControlFlow should no longer be in EXACT_TYPE_KEY_SORTS");
}

// =============================================================================
// EXACT_TYPE_KEY_SORTS — binary search correctness
// =============================================================================

#[test]
fn test_exact_table_binary_search_finds_all_keys() {
    for (key, ctor) in EXACT_TYPE_KEY_SORTS {
        let result = EXACT_TYPE_KEY_SORTS.binary_search_by_key(key, |(k, _)| *k);
        assert!(result.is_ok(), "binary search should find key '{key}'");
        // Verify the found entry produces the same sort
        let idx = result.unwrap();
        let found_sort = (EXACT_TYPE_KEY_SORTS[idx].1)();
        let expected_sort = ctor();
        assert_eq!(
            found_sort.to_string(),
            expected_sort.to_string(),
            "binary search for '{key}' returned wrong entry"
        );
    }
}

#[test]
fn test_exact_table_binary_search_misses_absent_key() {
    let result = EXACT_TYPE_KEY_SORTS.binary_search_by_key(&"nonexistent_key_xyz", |(k, _)| *k);
    assert!(result.is_err(), "absent key should not be found");
}

// =============================================================================
// PREFIX_TYPE_KEY_RULES — match predicate coverage
// =============================================================================

#[test]
fn test_prefix_rule_ref_ptr_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[0];
    assert!((rule.matches)("ref_u32"));
    assert!((rule.matches)("ptr_i64"));
    assert!(!(rule.matches)("u32"));
    assert!(!(rule.matches)("arr_u8"));
}

#[test]
fn test_prefix_rule_ref_ptr_produces_pointer_width() {
    let rule = &PREFIX_TYPE_KEY_RULES[0];
    let sort = (rule.sort)("ref_u32");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_prefix_rule_dyn_metadata_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[3];
    assert!((rule.matches)("DynMetadata_SomeTrait"));
    assert!((rule.matches)("DynMetadata"));
    assert!(!(rule.matches)("Dynamic_Trait"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_dyn_metadata_produces_pointer_width() {
    let rule = &PREFIX_TYPE_KEY_RULES[3];
    let sort = (rule.sort)("DynMetadata_SomeTrait");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_prefix_rule_arr_slice_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[4];
    assert!((rule.matches)("arr_i32"));
    assert!((rule.matches)("slice_u8"));
    assert!(!(rule.matches)("Vec_u8"));
}

#[test]
fn test_prefix_rule_arr_produces_array_sort() {
    let rule = &PREFIX_TYPE_KEY_RULES[4];
    let sort = (rule.sort)("arr_i32");
    assert!(sort.is_array(), "arr_i32 should produce an array sort");
    let arr = sort.array_sort().unwrap();
    assert_eq!(arr.index_sort.bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(arr.element_sort.bitvec_width(), Some(32));
}

#[test]
fn test_prefix_rule_arr_empty_suffix_uses_bv32_default() {
    let rule = &PREFIX_TYPE_KEY_RULES[4];
    let sort = (rule.sort)("arr_");
    assert!(sort.is_array());
    let arr = sort.array_sort().unwrap();
    assert_eq!(arr.element_sort.bitvec_width(), Some(32));
}

#[test]
fn test_prefix_rule_tuple_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[5];
    assert!((rule.matches)("tuple_u32"));
    assert!((rule.matches)("tuple_ptr_u8"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_bigint_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[6];
    assert!((rule.matches)("BigInt"));
    assert!((rule.matches)("some_bigint_type"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_bigint_produces_int_sort() {
    let rule = &PREFIX_TYPE_KEY_RULES[6];
    let sort = (rule.sort)("BigInt");
    assert!(sort.is_int(), "BigInt should produce Int sort");
}

#[test]
fn test_prefix_rule_vec_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[7];
    assert!((rule.matches)("Vec_u32"));
    assert!((rule.matches)("std_vec_Vec_i8"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_vec_produces_datatype() {
    let rule = &PREFIX_TYPE_KEY_RULES[7];
    let sort = (rule.sort)("Vec_u32");
    assert!(sort.is_datatype(), "Vec_u32 should produce a datatype sort");
    let name = sort.datatype_name().unwrap_or("");
    assert!(name.contains("Vec"), "Vec sort name should contain 'Vec', got: {name}");
}

#[test]
fn test_prefix_rule_string_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[8];
    assert!((rule.matches)("String"));
    assert!((rule.matches)("std_string_String"));
    assert!(!(rule.matches)("str"));
}

#[test]
fn test_prefix_rule_string_produces_rust_string_datatype() {
    let rule = &PREFIX_TYPE_KEY_RULES[8];
    let sort = (rule.sort)("String");
    assert!(sort.is_datatype());
    assert_eq!(sort.datatype_name(), Some("RustString"));
}

#[test]
fn test_prefix_rule_box_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[9];
    assert!((rule.matches)("Box_u32"));
    assert!((rule.matches)("std_boxed_Box_i8"));
    assert!(!(rule.matches)("Vec_u8"));
}

#[test]
fn test_prefix_rule_box_produces_pointer_width() {
    let rule = &PREFIX_TYPE_KEY_RULES[9];
    let sort = (rule.sort)("Box_u32");
    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
}

#[test]
fn test_prefix_rule_nonnull_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[10];
    assert!((rule.matches)("NonNull_u8"));
    assert!((rule.matches)("std_ptr_NonNull_i32"));
    assert!(!(rule.matches)("Box_u8"));
}

#[test]
fn test_prefix_rule_phantom_data_matches() {
    // Part of #4124: indices shifted +4 after W5:4352 added Rc/Weak/RcInner/WeakInner
    // at positions 12-15.
    let rule = &PREFIX_TYPE_KEY_RULES[19];
    assert!((rule.matches)("PhantomData_u32"));
    assert!((rule.matches)("std_marker_PhantomData_i8"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_phantom_data_produces_bool() {
    let rule = &PREFIX_TYPE_KEY_RULES[19];
    let sort = (rule.sort)("PhantomData_u32");
    assert!(sort.is_bool());
}

#[test]
fn test_prefix_rule_rawvec_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[20];
    assert!((rule.matches)("RawVec_u8"));
    assert!((rule.matches)("raw_vec_RawVec_i32"));
    assert!(!(rule.matches)("Vec_u8"));
}

#[test]
fn test_prefix_rule_rawvec_produces_datatype() {
    let rule = &PREFIX_TYPE_KEY_RULES[20];
    let sort = (rule.sort)("RawVec_u8");
    assert!(sort.is_datatype());
    assert_eq!(sort.datatype_name(), Some("RawVec"));
}

#[test]
fn test_prefix_rule_range_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[22];
    assert!((rule.matches)("std_ops_Range_usize"));
    assert!((rule.matches)("Range_i32"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_range_produces_struct_with_start_end() {
    let rule = &PREFIX_TYPE_KEY_RULES[22];
    let sort = (rule.sort)("Range_usize");
    assert!(sort.is_datatype());
    let name = sort.datatype_name().unwrap_or("");
    assert!(name.contains("Range"), "Range sort name should contain 'Range', got: {name}");
}

#[test]
fn test_prefix_rule_option_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[23];
    assert!((rule.matches)("Option_u32"));
    assert!((rule.matches)("std_option_Option_i8"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_option_produces_enum_sort() {
    let rule = &PREFIX_TYPE_KEY_RULES[23];
    let sort = (rule.sort)("Option_u32");
    assert!(sort.is_datatype());
    let name = sort.datatype_name().unwrap_or("");
    assert!(name.contains("Option"), "Option sort name should contain 'Option', got: {name}");
}

#[test]
fn test_prefix_rule_closure_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[26];
    assert!((rule.matches)("ty_Closure_abc"));
    assert!(!(rule.matches)("Closure_abc"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_closure_produces_bool() {
    let rule = &PREFIX_TYPE_KEY_RULES[26];
    let sort = (rule.sort)("ty_Closure_abc");
    assert!(sort.is_bool());
}

#[test]
fn test_prefix_rule_str_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[27];
    assert!((rule.matches)("ty_RigidTy_Str"));
    assert!(!(rule.matches)("String"));
}

#[test]
fn test_prefix_rule_str_produces_slice_datatype() {
    let rule = &PREFIX_TYPE_KEY_RULES[27];
    let sort = (rule.sort)("ty_RigidTy_Str");
    assert!(sort.is_datatype());
}

#[test]
fn test_prefix_rule_dynamic_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[28];
    assert!((rule.matches)("ty_Dynamic_Trait"));
    assert!(!(rule.matches)("Dynamic_Trait"));
    assert!(!(rule.matches)("u32"));
}

#[test]
fn test_prefix_rule_dynamic_produces_dyn_datatype() {
    let rule = &PREFIX_TYPE_KEY_RULES[28];
    let sort = (rule.sort)("ty_Dynamic_Trait");
    assert!(sort.is_datatype());
}

#[test]
fn test_prefix_rule_polymorphic_iter_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[32];
    assert!((rule.matches)("std_array_iter_iter_inner_PolymorphicIter_u8"));
    assert!((rule.matches)("PolymorphicIter"));
    assert!(!(rule.matches)("IntoIter_u8"));
}

#[test]
fn test_prefix_rule_polymorphic_iter_produces_double_pointer_width() {
    let rule = &PREFIX_TYPE_KEY_RULES[32];
    let sort = (rule.sort)("PolymorphicIter");
    assert_eq!(sort.bitvec_width(), Some(2 * POINTER_WIDTH));
}

// =============================================================================
// PREFIX_TYPE_KEY_RULES — no duplicate match semantics (first-match-wins order)
// =============================================================================

#[test]
fn test_prefix_rules_count() {
    // Guard against silent rule additions/removals
    assert_eq!(
        PREFIX_TYPE_KEY_RULES.len(),
        40,
        "expected 40 prefix rules (update test if rules were intentionally added/removed)"
    );
}

// =============================================================================
// Part of #3669: type-key table gap tests
// =============================================================================

#[test]
fn test_exact_table_index_range_produces_datatype() {
    let sort = exact_sort("std_ops_index_range_IndexRange");
    assert!(sort.is_datatype(), "IndexRange should produce a datatype sort");
    assert_eq!(sort.datatype_name(), Some("IndexRange"));
}

#[test]
fn test_prefix_rule_std_array_into_iter_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[31];
    assert!((rule.matches)("std_array_IntoIter_NonCopyWrapper"));
    assert!((rule.matches)("std_array_IntoIter_u32"));
    assert!(!(rule.matches)("std_vec_IntoIter_u32"));
}

#[test]
fn test_prefix_rule_std_array_into_iter_produces_double_pointer_width() {
    let rule = &PREFIX_TYPE_KEY_RULES[31];
    let sort = (rule.sort)("std_array_IntoIter_NonCopyWrapper");
    assert_eq!(sort.bitvec_width(), Some(2 * POINTER_WIDTH));
}

#[test]
fn test_prefix_rule_maybe_uninit_matches() {
    let rule = &PREFIX_TYPE_KEY_RULES[38];
    assert!((rule.matches)("std_mem_MaybeUninit_NonCopyWrapper"));
    assert!((rule.matches)("std_mem_MaybeUninit_u32"));
    assert!(!(rule.matches)("MaybeUninit_u32"));
}

#[test]
fn test_prefix_rule_maybe_uninit_transparent_unwrap() {
    use super::super::ChcCtx;
    let sort = ChcCtx::sort_from_type_key("std_mem_MaybeUninit_u32");
    assert_eq!(sort.bitvec_width(), Some(32), "MaybeUninit<u32> should unwrap to bv32");
}

#[test]
fn test_prefix_rule_maybe_uninit_recursive_from_slice() {
    use super::super::ChcCtx;
    let sort = ChcCtx::sort_from_type_key("slice_std_mem_MaybeUninit_u8");
    assert!(sort.is_array(), "slice of MaybeUninit<u8> should produce array sort");
    let arr = sort.array_sort().unwrap();
    assert_eq!(
        arr.element_sort.bitvec_width(),
        Some(8),
        "element should be bv8 via MaybeUninit unwrap"
    );
}

// =============================================================================
// Part of #3738 D4: semantic Result prefix-rule assertions (no hard-coded indices)
// =============================================================================

#[test]
fn test_prefix_rule_result_matches_only_try_reserve_error() {
    // Iterate rules semantically — do not rely on array index.
    let try_reserve_key = "std_result_Result_unit_std_collections_TryReserveError";
    let generic_result_key = "std_result_Result_u32_u8";

    let matches_try_reserve = PREFIX_TYPE_KEY_RULES.iter().any(|r| (r.matches)(try_reserve_key));
    assert!(matches_try_reserve, "some prefix rule must match the TryReserveError Result key");

    // Note: generic Result keys like "std_result_Result_u32_u8" now match the
    // custom ADT catch-all rule (#4225) which matches any key containing `_`
    // followed by uppercase. The specific TryReserveError rule has higher
    // precedence (earlier index), so it still wins for TryReserveError variants.
    // Verify that the TryReserveError-specific rule comes BEFORE the catch-all.
    let try_reserve_idx = PREFIX_TYPE_KEY_RULES
        .iter()
        .position(|r| (r.matches)(try_reserve_key))
        .expect("TryReserveError rule");
    let generic_idx = PREFIX_TYPE_KEY_RULES.iter().position(|r| (r.matches)(generic_result_key));
    if let Some(gen_idx) = generic_idx {
        assert!(
            try_reserve_idx < gen_idx,
            "TryReserveError rule (idx {try_reserve_idx}) must precede generic match (idx {gen_idx})"
        );
    }
}

#[test]
fn test_prefix_rule_result_try_reserve_produces_bv128() {
    let key = "std_result_Result_unit_std_collections_TryReserveError";
    let rule = PREFIX_TYPE_KEY_RULES
        .iter()
        .find(|r| (r.matches)(key))
        .expect("TryReserveError Result key must match a prefix rule");
    let sort = (rule.sort)(key);
    assert_eq!(sort.bitvec_width(), Some(128), "TryReserveError Result should produce BV128");
}

// =============================================================================
// Helpers
// =============================================================================

fn exact_sort(key: &str) -> ay_bindings::Sort {
    let entry = EXACT_TYPE_KEY_SORTS
        .iter()
        .find(|(k, _)| *k == key)
        .unwrap_or_else(|| panic!("key '{key}' not found in EXACT_TYPE_KEY_SORTS"));
    (entry.1)()
}

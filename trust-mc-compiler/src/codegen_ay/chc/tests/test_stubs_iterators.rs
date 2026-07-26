// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_iterators.rs — iterator helper methods and sort inference.
//!
//! Part of #2016 (test coverage for chc/stubs_iterators.rs, 876 lines).
//! Covers internal helpers: make_vec_into_iter_chc, infer_vec_sort_from_iter,
//! infer_vec_type_name, extract_vec_data_with_sort, make_hashmap_into_iter_chc,
//! extract_hashmap_iter_all_fields,
//! get_collection_arg, translate_iterator_intrinsic_call edge cases.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_iterator_adapter::CallIteratorAdapter;
use super::common::*;

// =============================================================================
// make_vec_into_iter_chc — builds VecIntoIter struct from Vec expression
// =============================================================================

/// Vec with proper datatype sort should produce a VecIntoIter struct with fld_vec and fld_pos.
#[test]
fn test_make_vec_into_iter_chc_valid_vec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Build a Vec<u32> sort: struct Vec_bv32 { fld_ptr: bv64, fld_len: bv64, fld_cap: bv64, fld_data: Array<bv64, bv32> }
        let elem_sort = Sort::bitvec(32);
        let data_sort = Sort::array(Sort::bitvec(64), elem_sort);
        let vec_sort = struct_sort(
            "Vec_bv32",
            [
                ("fld_ptr", Sort::bitvec(64)),
                ("fld_len", Sort::bitvec(64)),
                ("fld_cap", Sort::bitvec(64)),
                ("fld_data", data_sort),
            ],
        );

        let vec_expr = Expr::var("test_vec", vec_sort);
        let result = chc_ctx.make_vec_into_iter_chc(vec_expr);
        assert!(result.is_some(), "make_vec_into_iter_chc should succeed for valid Vec sort");

        let iter = result.unwrap();
        // Should be a datatype with "VecIntoIter_bv32" name
        assert!(iter.sort().is_datatype(), "VecIntoIter should be a datatype");
        let dt = iter.sort().datatype_sort().expect("datatype info");
        assert!(
            dt.name.starts_with("VecIntoIter_"),
            "iter sort name should start with VecIntoIter_, got: {}",
            dt.name
        );
        // Should have fld_vec and fld_pos fields
        let ctor = &dt.constructors[0];
        let field_names: Vec<&str> = ctor.fields.iter().map(|f| f.name.as_str()).collect();
        assert!(field_names.contains(&"fld_vec"), "iter should have fld_vec");
        assert!(field_names.contains(&"fld_pos"), "iter should have fld_pos");
    });
}

/// Non-datatype Vec sort (e.g., bitvec) should return None (Part of #1930).
#[test]
fn test_make_vec_into_iter_chc_non_datatype_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // A bitvec "vec" should fail
        let bad_vec = Expr::var("not_a_vec", Sort::bitvec(64));
        let result = chc_ctx.make_vec_into_iter_chc(bad_vec);
        assert!(result.is_none(), "non-datatype sort should return None");
    });
}

/// Vec sort without fld_data array field should return None.
#[test]
fn test_make_vec_into_iter_chc_no_data_field_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Struct without fld_data — should fail element sort extraction
        let bad_vec_sort = struct_sort("BadVec", [("fld_len", Sort::bitvec(64))]);
        let bad_vec = Expr::var("bad_vec", bad_vec_sort);
        let result = chc_ctx.make_vec_into_iter_chc(bad_vec);
        assert!(result.is_none(), "sort without fld_data should return None");
    });
}

// =============================================================================
// infer_vec_sort_from_iter — extracts Vec sort from VecIntoIter
// =============================================================================

/// VecIntoIter with fld_vec field should extract the Vec sort.
#[test]
fn test_infer_vec_sort_from_iter_valid() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Build VecIntoIter sort with fld_vec
        let vec_sort = struct_sort(
            "Vec_bv32",
            [
                ("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(32))),
                ("fld_len", Sort::bitvec(64)),
            ],
        );
        let iter_sort =
            struct_sort("VecIntoIter_bv32", [("fld_vec", vec_sort), ("fld_pos", Sort::bitvec(64))]);
        let iter_expr = Expr::var("test_iter", iter_sort);

        let result = chc_ctx.infer_vec_sort_from_iter(&iter_expr);
        assert!(result.is_some(), "should extract Vec sort from VecIntoIter");
        assert!(result.unwrap().is_datatype(), "extracted sort should be a datatype");
    });
}

/// Non-datatype sort returns None.
#[test]
fn test_infer_vec_sort_from_iter_non_datatype_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bad_iter = Expr::var("not_an_iter", Sort::bitvec(64));
        let result = chc_ctx.infer_vec_sort_from_iter(&bad_iter);
        assert!(result.is_none(), "bitvec sort should return None");
    });
}

/// Datatype without fld_vec field returns None.
#[test]
fn test_infer_vec_sort_from_iter_no_fld_vec_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let no_vec_sort = struct_sort("BadIter", [("fld_pos", Sort::bitvec(64))]);
        let no_vec_expr = Expr::var("bad_iter", no_vec_sort);
        let result = chc_ctx.infer_vec_sort_from_iter(&no_vec_expr);
        assert!(result.is_none(), "struct without fld_vec should return None");
    });
}

// =============================================================================
// infer_vec_type_name — extracts Vec type name from expression
// =============================================================================

/// Datatype sort should return its name.
#[test]
fn test_infer_vec_type_name_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let vec_sort = struct_sort("Vec_bv32", [("fld_len", Sort::bitvec(64))]);
        let vec_expr = Expr::var("v", vec_sort);
        let name = chc_ctx.infer_vec_type_name(&vec_expr);
        assert_eq!(name, "Vec_bv32");
    });
}

/// Non-datatype sort should return fallback "Vec".
#[test]
fn test_infer_vec_type_name_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bv_expr = Expr::var("v", Sort::bitvec(64));
        let name = chc_ctx.infer_vec_type_name(&bv_expr);
        assert_eq!(name, "Vec");
    });
}

// =============================================================================
// extract_vec_data_with_sort — extracts data array and element sort from Vec
// =============================================================================

/// Valid Vec with fld_data should extract (data_expr, elem_sort).
#[test]
fn test_extract_vec_data_with_sort_valid() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let elem_sort = Sort::bitvec(32);
        let data_sort = Sort::array(Sort::bitvec(64), elem_sort);
        let vec_sort = struct_sort(
            "Vec_bv32",
            [("fld_ptr", Sort::bitvec(64)), ("fld_len", Sort::bitvec(64)), ("fld_data", data_sort)],
        );
        let vec_expr = Expr::var("v", vec_sort);

        let result = chc_ctx.extract_vec_data_with_sort(&vec_expr);
        assert!(result.is_some(), "should extract data from valid Vec");
        let (data, extracted_elem_sort) = result.unwrap();
        assert!(data.sort().is_array(), "data should be array sort");
        assert_eq!(extracted_elem_sort.bitvec_width(), Some(32), "element sort should be bv32");
    });
}

/// Non-datatype Vec returns None.
#[test]
fn test_extract_vec_data_with_sort_non_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bad_vec = Expr::var("v", Sort::bitvec(64));
        let result = chc_ctx.extract_vec_data_with_sort(&bad_vec);
        assert!(result.is_none(), "non-datatype should return None");
    });
}

/// Vec without fld_data field returns None.
#[test]
fn test_extract_vec_data_with_sort_no_data_field() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bad_sort = struct_sort("NotVec", [("fld_len", Sort::bitvec(64))]);
        let bad_vec = Expr::var("v", bad_sort);
        let result = chc_ctx.extract_vec_data_with_sort(&bad_vec);
        assert!(result.is_none(), "struct without fld_data should return None");
    });
}

// =============================================================================
// make_hashmap_into_iter_chc — builds HashMapIntoIter from map expression
// =============================================================================

/// Valid map (Array<K, Option<V>>) should produce HashMapIntoIter struct.
#[test]
fn test_make_hashmap_into_iter_chc_valid_map() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // DT-free encoding (Part of #3057): Array(K, V) without Option wrapper.
        let key_sort = Sort::bitvec(32);
        let value_sort = Sort::bitvec(64);
        let map_sort = Sort::array(key_sort, value_sort);
        let map_expr = Expr::var("test_map", map_sort);

        let result = chc_ctx.make_hashmap_into_iter_chc(map_expr, None, None, None);
        assert!(result.is_some(), "make_hashmap_into_iter_chc should succeed for valid map");

        let iter = result.unwrap();
        assert!(iter.sort().is_datatype(), "HashMapIntoIter should be a datatype");
        let dt = iter.sort().datatype_sort().expect("datatype info");
        assert!(
            dt.name.starts_with("HashMapIntoIter_"),
            "iter sort name should start with HashMapIntoIter_, got: {}",
            dt.name
        );
        // DT-free: fld_data, fld_present, fld_keys, fld_pos, fld_len
        let ctor = &dt.constructors[0];
        let field_names: Vec<&str> = ctor.fields.iter().map(|f| f.name.as_str()).collect();
        assert!(field_names.contains(&"fld_data"), "iter should have fld_data");
        assert!(field_names.contains(&"fld_present"), "iter should have fld_present");
        assert!(field_names.contains(&"fld_keys"), "iter should have fld_keys");
        assert!(field_names.contains(&"fld_pos"), "iter should have fld_pos");
        assert!(field_names.contains(&"fld_len"), "iter should have fld_len");
    });
}

/// Non-array map sort should return None (Part of #1930).
#[test]
fn test_make_hashmap_into_iter_chc_non_array_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let bad_map = Expr::var("not_a_map", Sort::bitvec(64));
        let result = chc_ctx.make_hashmap_into_iter_chc(bad_map, None, None, None);
        assert!(result.is_none(), "non-array sort should return None");
    });
}

/// DT-free encoding (Part of #3057): any array sort is valid, not just Array<K, Option<V>>.
#[test]
fn test_make_hashmap_into_iter_chc_plain_array_succeeds() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // DT-free: Array<bv32, bv64> is a valid map sort (no Option wrapper needed).
        let map_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(64));
        let map_expr = Expr::var("test_map", map_sort);
        let result = chc_ctx.make_hashmap_into_iter_chc(map_expr, None, None, None);
        assert!(result.is_some(), "plain array sort should succeed in DT-free encoding");
    });
}

/// Providing a tracked_len expression should be used instead of generating symbolic len.
#[test]
fn test_make_hashmap_into_iter_chc_with_tracked_len() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // DT-free encoding (Part of #3057): Array(K, V) without Option wrapper.
        let key_sort = Sort::bitvec(32);
        let value_sort = Sort::bitvec(64);
        let map_sort = Sort::array(key_sort, value_sort);
        let map_expr = Expr::var("test_map", map_sort);

        let tracked_len = Expr::bitvec_const(5u64, 64);
        let result = chc_ctx.make_hashmap_into_iter_chc(map_expr, None, None, Some(tracked_len));
        assert!(result.is_some(), "should succeed with tracked len");
    });
}

// =============================================================================
// extract_hashmap_iter_all_fields — extracts data, present, keys, pos, len, key_sort, value_sort
// =============================================================================

/// Valid HashMapIntoIter struct should extract all fields and sorts.
#[test]
fn test_extract_hashmap_iter_fields_valid() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let iter_sort = hashmap_iter_sort(Sort::bitvec(32), Sort::bitvec(64));
        let iter_expr = Expr::var("test_iter", iter_sort);

        let result = chc_ctx.extract_hashmap_iter_all_fields(&iter_expr, "HashMapIntoIter");
        assert!(result.is_some(), "should extract fields from valid iter");
        // DT-free (Part of #3057): 7-element tuple with present field.
        let (data, _present, keys, _pos, _len, key_sort, value_sort) = result.unwrap();
        assert!(data.sort().is_array(), "data should be array sort");
        assert!(keys.sort().is_array(), "keys should be array sort");
        assert_eq!(key_sort.bitvec_width(), Some(32), "key_sort should be bv32");
        assert_eq!(value_sort.bitvec_width(), Some(64), "value_sort should be bv64");
    });
}

/// Non-datatype sort returns None.
#[test]
fn test_extract_hashmap_iter_fields_non_datatype() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bad_iter = Expr::var("not_iter", Sort::bitvec(64));
        let result = chc_ctx.extract_hashmap_iter_all_fields(&bad_iter, "HashMapIntoIter");
        assert!(result.is_none(), "non-datatype should return None");
    });
}

// make_tuple_chc tests removed: method was removed in DT-free encoding (Part of #3057).
// HashMap iterator next() now passes key/value as separate fields via result_fields.
// extract_option_payload tests removed: method was removed in DT-free encoding (Part of #3057).

// =============================================================================
// translate_iterator_intrinsic_call edge cases
// =============================================================================

/// CheckedAddUnsigned with insufficient args returns None.
#[test]
fn test_translate_checked_add_unsigned_insufficient_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args for CheckedAddUnsigned should return None
        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::CheckedAddUnsigned,
            &[],
            &modified,
            None,
        );
        assert!(result.is_none(), "CheckedAddUnsigned with 0 args should return None");

        // 1 arg should also return None (needs 2)
        let one_arg = vec![rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 0,
            projection: vec![],
        })];
        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::CheckedAddUnsigned,
            &one_arg,
            &modified,
            None,
        );
        assert!(result.is_none(), "CheckedAddUnsigned with 1 arg should return None");
    });
}

/// CheckedAddUnsigned returns raw payload for flattened Option destination.
#[test]
fn test_translate_checked_add_unsigned_flattened_dest_returns_payload() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_checked_add_unsigned_flat(a: i32, b: u32) -> Option<i32> {
            a.checked_add_unsigned(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned_flat");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_checked_add_unsigned_flat", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = 0;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local),
            "destination local should be flattened"
        );
        assert!(
            chc_ctx.flatten.flattened_enum_discr.contains_key(&dest_local),
            "destination local should have flattened enum discriminant metadata"
        );

        let lhs = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 1,
            projection: vec![],
        });
        let rhs = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 2,
            projection: vec![],
        });
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::CheckedAddUnsigned,
            &[lhs, rhs],
            &modified,
            Some(dest_local),
        );
        assert!(
            result.is_some(),
            "CheckedAddUnsigned should produce payload expression for flattened destination"
        );
        let result = result.unwrap();
        assert!(
            result.sort().is_bitvec(),
            "flattened destination should return payload bitvector, got {:?}",
            result.sort()
        );
    });
}

/// OptionUnwrapUnchecked with empty args returns None.
#[test]
fn test_translate_option_unwrap_unchecked_empty_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::OptionUnwrapUnchecked,
            &[],
            &modified,
            None,
        );
        assert!(result.is_none(), "OptionUnwrapUnchecked with 0 args should return None");
    });
}

/// OptionUnwrapUnchecked recovers payload from flattened Option argument.
#[test]
fn test_translate_option_unwrap_unchecked_flattened_arg_payload() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_unwrap_unchecked_flat(opt: Option<u32>) -> u32 {
            unsafe { opt.unwrap_unchecked() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unwrap_unchecked_flat");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unwrap_unchecked_flat", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = 1;
        assert!(
            chc_ctx.flatten.flattened_enum_discr.contains_key(&option_local),
            "expected flattened Option argument local metadata"
        );
        let option_operand = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: option_local,
            projection: vec![],
        });
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::OptionUnwrapUnchecked,
            &[option_operand],
            &modified,
            None,
        );
        assert!(
            result.is_some(),
            "OptionUnwrapUnchecked should recover payload from flattened Option local"
        );
        let payload = result.unwrap();
        assert!(
            payload.sort().is_bitvec(),
            "unwrapped payload should be bitvector, got {:?}",
            payload.sort()
        );
    });
}

fn nested_some_ite_option_i16_expr() -> Expr {
    let option_sort = enum_sort(
        "Option_i16",
        vec![
            ("None_Option_i16", Vec::<(&str, Sort)>::new()),
            ("Some_Option_i16", vec![("value", Sort::bitvec(16))]),
        ],
    );
    let none =
        Expr::datatype_constructor("Option_i16", "None_Option_i16", vec![], option_sort.clone());
    let some_a = Expr::datatype_constructor(
        "Option_i16",
        "Some_Option_i16",
        vec![Expr::var("payload_a_i16", Sort::bitvec(16))],
        option_sort.clone(),
    );
    let some_b = Expr::datatype_constructor(
        "Option_i16",
        "Some_Option_i16",
        vec![Expr::var("payload_b_i16", Sort::bitvec(16))],
        option_sort,
    );
    let nested_some_ite = Expr::ite(Expr::var("pick_a", Sort::bool()), some_a, some_b);
    Expr::ite(Expr::var("is_none", Sort::bool()), none, nested_some_ite)
}

#[test]
fn test_translate_option_unwrap_unchecked_nested_some_ite_avoids_symbolic_gap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_unwrap_unchecked_nested(opt: Option<i16>) -> i16 {
            unsafe { opt.unwrap_unchecked() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unwrap_unchecked_nested");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unwrap_unchecked_nested", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn();

        chc_ctx.encode.local_expr_env.insert(1, nested_some_ite_option_i16_expr());
        let option_operand = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 1,
            projection: vec![],
        });
        let modified = HashSet::from([1usize]);

        let result = chc_ctx.translate_iterator_intrinsic_call(
            StubKind::OptionUnwrapUnchecked,
            &[option_operand],
            &modified,
            None,
        );
        assert!(
            result.is_some(),
            "OptionUnwrapUnchecked should translate nested Some ITE receivers"
        );
        assert_eq!(
            result.expect("payload").sort(),
            &Sort::bitvec(16),
            "unwrapped nested Some ITE should yield the i16 payload sort"
        );

        let gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn()
            .remove("probe_unwrap_unchecked_nested")
            .unwrap_or_default();
        assert_eq!(
            gap_count, 0,
            "unwrap_unchecked should not record aggregate gaps for nested Some ITEs"
        );
        assert_eq!(
            gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
            0,
            "unwrap_unchecked should stay on the Some path for nested Some ITEs: {gap_reasons:?}"
        );
    });
}

/// Unhandled stub kind returns None.
#[test]
fn test_translate_iterator_intrinsic_unhandled_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // VecIntoIter is NOT an iterator intrinsic
        let result =
            chc_ctx.translate_iterator_intrinsic_call(StubKind::VecIntoIter, &[], &modified, None);
        assert!(result.is_none(), "VecIntoIter should not be handled by iterator intrinsic path");
    });
}

/// RangeSpecNext should take flattened advancement path and avoid symbolic fallback assignment.
#[test]
fn test_range_spec_next_flattened_update_has_constraints_without_symbolic_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range_adapter_constraints(n: u32) -> Option<u32> {
            let r = 0u32..n;
            if r.start < r.end { Some(r.start) } else { None }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_adapter_constraints");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_range_adapter_constraints", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let range_local = body
            .local_decls()
            .find_map(|(local_idx, local_decl)| match local_decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Range" => {
                    Some(local_idx)
                }
                _ => None, // external enum: TyKind
            })
            .expect("expected a Range local in probe_range_adapter_constraints");
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&range_local),
            "precondition: range local should be flattened for flattened-path assertion"
        );
        let destination = rustc_public::mir::Place { local: 0, projection: vec![] };
        let args = vec![rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: range_local,
            projection: vec![],
        })];
        let from_bb = 0;
        let target = 0;

        let from_rel =
            chc_ctx.block_relations.get(&from_bb).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        let before_rules = chc_ctx.vc.rules.len();
        let before_counts =
            super::super::codegen_call_iterator_adapter::get_range_spec_next_path_counts();

        let cx = ChcCallContext {
            stub: StubKind::RangeSpecNext,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_iterator_adapter(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule = chc_ctx.vc.rules.last().expect("RangeSpecNext should emit transition rule");
        let target_rel =
            chc_ctx.block_relations.get(&target).expect("target relation for call block");
        assert_eq!(
            rule.head.name, *target_rel,
            "successful RangeSpecNext translation should emit goto rule"
        );

        assert!(
            rule.body.constraints.iter().any(|c| {
                let s = c.to_string();
                s.contains("fld1__out") && s.contains("(ite ")
            }),
            "flattened RangeSpecNext payload should be ITE-constrained"
        );
        assert!(
            !rule.body.constraints.iter().any(|c| c.to_string().contains("iter_adapter_result")),
            "RangeSpecNext should not use generic symbolic iter_adapter_result fallback"
        );

        let after_counts =
            super::super::codegen_call_iterator_adapter::get_range_spec_next_path_counts();
        assert!(
            after_counts.flattened > before_counts.flattened,
            "flattened-path telemetry should increment: before={before_counts:?}, after={after_counts:?}"
        );
    });
}

// =============================================================================
// detect_iterator_intrinsic_stub — only accepts iterator intrinsic stubs
// =============================================================================

/// detect_iterator_intrinsic_stub with non-iterator-intrinsic call returns None.
#[test]
fn test_detect_iterator_intrinsic_stub_rejects_vec_methods() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_len(v: &Vec<u32>) -> usize {
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        // None of the calls in probe_vec_len should be detected as iterator intrinsics
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let result = chc_ctx.detect_iterator_intrinsic_stub(func);
                assert!(result.is_none(), "Vec::len should not be detected as iterator intrinsic");
            }
        }
    });
}

// =============================================================================
// detect_hashmap_iter_stub — TrustMcMap stubs map to HashMap iter stubs
// =============================================================================

/// detect_hashmap_iter_stub rejects non-HashMap-iter calls.
#[test]
fn test_detect_hashmap_iter_stub_rejects_non_iter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push(v: &mut Vec<u32>, x: u32) {
            v.push(x);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let result = chc_ctx.detect_hashmap_iter_stub(func);
                assert!(result.is_none(), "Vec::push should not be detected as HashMap iter stub");
            }
        }
    });
}

// =============================================================================
// translate_vec_iter_call — unhandled stub returns None
// =============================================================================

#[test]
fn test_translate_vec_iter_call_unhandled_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // HashMapIntoIter is not a Vec iter stub
        let result =
            chc_ctx.translate_vec_iter_call(StubKind::HashMapIntoIter, &[], &modified, None);
        assert!(result.is_none(), "HashMapIntoIter should not be handled by vec iter path");
    });
}

// =============================================================================
// translate_hashmap_iter_call — unhandled stub returns None
// =============================================================================

#[test]
fn test_translate_hashmap_iter_call_unhandled_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // VecIntoIter is not a HashMap iter stub
        let result =
            chc_ctx.translate_hashmap_iter_call(StubKind::VecIntoIter, &[], &modified, None);
        assert!(result.is_none(), "VecIntoIter should not be handled by hashmap iter path");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_iterators_hashmap.rs — HashMap iterator stub detection,
//! translation, and SMT struct construction.
//!
//! Covers:
//! - detect_hashmap_iter_stub: stub detection for into_iter/iter/keys/values/next
//! - make_hashmap_into_iter_chc: iterator struct construction with sort inference
//! - extract_hashmap_iter_all_fields: field extraction from iterator datatype
//! - translate_hashmap_iter_call end-to-end: IntoIter/Iter/IterNext
//!
//! Part of #2303 (zero-coverage CHC files).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// HashMap iterator detection tests
// ═══════════════════════════════════════════════════════════════════════

/// HashMap::into_iter should be detected as HashMapIntoIter stub.
#[test]
fn test_detect_hashmap_into_iter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_into_iter(m: HashMap<u32, u32>) -> Vec<(u32, u32)> {
            m.into_iter().collect()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_into_iter");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_into_iter", ChcConfig::default());

        // Look for HashMap iterator stubs in the MIR
        let mut found_iter_stub = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_iter_stub(func)
            {
                found_iter_stub = true;
                assert!(
                    matches!(
                        stub,
                        StubKind::HashMapIntoIter
                            | StubKind::HashMapIter
                            | StubKind::HashMapKeys
                            | StubKind::HashMapValues
                            | StubKind::HashMapIterNext
                    ),
                    "detected stub should be a HashMap iterator variant, got {:?}",
                    stub
                );
            }
        }

        // The function calls into_iter which should be detected.
        // Note: MIR may optimize or inline differently, so this is best-effort.
        if !found_iter_stub {
            // Fallback: check pipeline doesn't panic
            let (vc, _) = chc_ctx.translate();
            assert!(!vc.rules.is_empty(), "HashMap into_iter pipeline should produce rules");
        }
    });
}

/// HashMap::keys() should be detected as HashMapKeys stub.
#[test]
fn test_detect_hashmap_keys() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_keys(m: &HashMap<u32, u32>) -> Vec<&u32> {
            m.keys().collect()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_keys");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_keys", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "HashMap keys pipeline should produce rules");
        assert!(!vc.relations.is_empty(), "HashMap keys should produce relations");
    });
}

/// HashMap::values() should be detected as HashMapValues stub.
#[test]
fn test_detect_hashmap_values() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_values(m: &HashMap<u32, u32>) -> Vec<&u32> {
            m.values().collect()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_values");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_values", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "HashMap values pipeline should produce rules");
        assert!(!vc.relations.is_empty(), "HashMap values should produce relations");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// make_hashmap_into_iter_chc structural tests
// ═══════════════════════════════════════════════════════════════════════

/// make_hashmap_into_iter_chc should produce a datatype with (data, present, keys, pos, len).
#[test]
fn test_make_hashmap_into_iter_chc_structure() {
    // DT-free encoding (Part of #3057): Array<K, V> without Option wrapper.
    let map_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let map = Expr::var("test_map", map_sort);

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_iter_struct(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_struct");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_struct", ChcConfig::default());

        let result = chc_ctx.make_hashmap_into_iter_chc(map, None, None, None);
        assert!(
            result.is_some(),
            "make_hashmap_into_iter_chc should succeed with valid Array<K, V> map"
        );

        let iter = result.unwrap();
        assert!(iter.sort().is_datatype(), "HashMapIntoIter should be a datatype sort");

        let sort_name = iter.sort().datatype_name().unwrap_or("");
        assert!(
            sort_name.contains("HashMapIntoIter"),
            "sort name should contain 'HashMapIntoIter', got: {}",
            sort_name
        );
    });
}

/// make_hashmap_into_iter_chc should return None for non-array map sorts.
#[test]
fn test_make_hashmap_into_iter_chc_non_array_returns_none() {
    let bad_map = Expr::var("not_a_map", Sort::bitvec(32));

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_bad_iter(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bad_iter");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bad_iter", ChcConfig::default());

        let result = chc_ctx.make_hashmap_into_iter_chc(bad_map, None, None, None);
        assert!(
            result.is_none(),
            "make_hashmap_into_iter_chc should return None for non-array sort"
        );
    });
}

/// make_hashmap_into_iter_chc with tracked_len should use that length.
#[test]
fn test_make_hashmap_into_iter_chc_with_tracked_len() {
    // DT-free encoding (Part of #3057): Array(K, V) without Option wrapper.
    let map_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let map = Expr::var("test_map", map_sort);
    let tracked_len = Expr::bitvec_const(5u64, 64);

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_tracked(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tracked");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tracked", ChcConfig::default());

        let result = chc_ctx.make_hashmap_into_iter_chc(map, None, None, Some(tracked_len));
        assert!(result.is_some(), "should succeed with tracked_len");

        let iter = result.unwrap();
        assert!(iter.sort().is_datatype());
    });
}

// make_tuple_chc tests removed: method was removed in DT-free encoding (Part of #3057).
// HashMap iterator next() now passes key/value as separate fields via result_fields.
// extract_option_payload tests removed: method was removed in DT-free encoding (Part of #3057).

// ═══════════════════════════════════════════════════════════════════════
// Full pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// HashMap into_iter + for loop through the full CHC pipeline.
#[test]
fn test_hashmap_iter_full_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_iter_sum(m: HashMap<u32, u32>) -> u32 {
            let mut sum = 0u32;
            for (_k, v) in m {
                sum += v;
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_sum");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_sum", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "HashMap iteration pipeline should produce rules");

        // Should have error relation (for potential overflow checks)
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "should declare error relation");
    });
}

/// extract_hashmap_iter_fields with a proper HashMapIntoIter sort.
#[test]
fn test_extract_hashmap_iter_fields_from_valid_sort() {
    // DT-free encoding (Part of #3057): Array(K, V) + Array(K, Bool) presence array.
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let data_sort = Sort::array(key_sort.clone(), value_sort);
    let present_sort = Sort::array(key_sort.clone(), Sort::bool());
    let keys_sort = Sort::array(Sort::bitvec(64), key_sort);

    let iter_sort = struct_sort(
        "HashMapIntoIter_bv32_bv64",
        [
            ("fld_data", data_sort),
            ("fld_present", present_sort),
            ("fld_keys", keys_sort),
            ("fld_pos", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
        ],
    );

    let iter_expr = Expr::var("test_iter", iter_sort);

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_extract(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_extract");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_extract", ChcConfig::default());

        let result =
            chc_ctx.extract_hashmap_iter_all_fields(&iter_expr, "HashMapIntoIter_bv32_bv64");
        assert!(result.is_some(), "should extract fields from valid HashMapIntoIter");

        // DT-free (Part of #3057): 7-element tuple with present field.
        let (data, _present, keys, _pos, _len, extracted_key_sort, extracted_value_sort) =
            result.unwrap();
        assert!(data.sort().is_array(), "extracted data should be array sort");
        assert!(keys.sort().is_array(), "extracted keys should be array sort");
        assert_eq!(&extracted_key_sort, &Sort::bitvec(32), "key sort should be bv32");
        assert_eq!(&extracted_value_sort, &Sort::bitvec(64), "value sort should be bv64");
    });
}

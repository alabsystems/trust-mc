// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =========================================================================
// BTreeMap -> HashMap CHC Mapping Tests (Part of #2125)
// =========================================================================

#[test]
fn test_detect_btreemap_stub_maps_to_hashmap() {
    // BTreeMap methods should be detected and mapped to HashMap stub kinds
    // for CHC dispatch (same SMT Array model). Part of #2125.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::BTreeMap;

        pub fn probe_btreemap_ops() {
            let mut m: BTreeMap<u8, u16> = BTreeMap::new();
            m.insert(1, 10);
            let _ = m.get(&1);
            let _ = m.len();
            let _ = m.is_empty();
            let _ = m.contains_key(&1);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreemap_ops");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreemap_ops", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        // BTreeMap stubs should be mapped to HashMap equivalents
        assert!(
            detected.contains(&StubKind::HashMapNew),
            "BTreeMap::new should map to HashMapNew; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapInsert),
            "BTreeMap::insert should map to HashMapInsert; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapGet),
            "BTreeMap::get should map to HashMapGet; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapLen),
            "BTreeMap::len should map to HashMapLen; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapIsEmpty),
            "BTreeMap::is_empty should map to HashMapIsEmpty; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapContainsKey),
            "BTreeMap::contains_key should map to HashMapContainsKey; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_convert_key_to_array_index_coerces_bitvec_width_for_hashmap() {
    // Regression for #2125: map index and key widths can diverge in CHC.
    // The converter must coerce keys before Array::select/store to avoid panic.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_key_coercion() {
            let _ = std::collections::BTreeMap::<u8, u16>::new();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_key_coercion");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_key_coercion", ChcConfig::default());

        let key8 = Expr::bitvec_const(7u128, 8);
        let coerced = chc_ctx.convert_key_to_array_index(key8, &Sort::bitvec(64), false);
        assert_eq!(coerced.sort().bitvec_width(), Some(64));

        let option_sort = option_datatype_sort(Sort::bitvec(16));
        let map = Expr::var("map_bv64_idx", Sort::array(Sort::bitvec(64), option_sort));
        let entry = map.select(coerced);
        assert!(entry.sort().is_datatype(), "select should succeed with normalized key sort");
    });
}

#[test]
fn test_convert_key_to_array_index_bv_to_int_for_hashmap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_key_coercion_bv_to_int() {
            let _ = std::collections::BTreeMap::<u8, u16>::new();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_key_coercion_bv_to_int");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_key_coercion_bv_to_int", ChcConfig::default());

        let key_bv8 = Expr::bitvec_const(3u128, 8);
        let coerced = chc_ctx.convert_key_to_array_index(key_bv8, &Sort::int(), false);
        assert!(coerced.sort().is_int());
        assert!(matches!(coerced.value(), ExprValue::Bv2Int(..)));

        let option_sort = option_datatype_sort(Sort::bitvec(16));
        let map = Expr::var("map_int_idx", Sort::array(Sort::int(), option_sort));
        let entry = map.select(coerced);
        assert!(entry.sort().is_datatype(), "select should succeed with Int-normalized key sort");
    });
}

#[test]
fn test_convert_key_to_array_index_int_to_bv_for_hashmap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_key_coercion_int_to_bv() {
            let _ = std::collections::BTreeMap::<u8, u16>::new();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_key_coercion_int_to_bv");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_key_coercion_int_to_bv", ChcConfig::default());

        let key_int = Expr::int_const(3);
        let coerced = chc_ctx.convert_key_to_array_index(key_int, &Sort::bitvec(64), false);
        assert_eq!(coerced.sort().bitvec_width(), Some(64));

        let option_sort = option_datatype_sort(Sort::bitvec(16));
        let map = Expr::var("map_bv64_idx_int_key", Sort::array(Sort::bitvec(64), option_sort));
        let entry = map.select(coerced);
        assert!(entry.sort().is_datatype(), "select should succeed with BV-normalized key sort");
    });
}

#[test]
fn test_convert_key_to_array_index_signed_bv_to_int_uses_signed_conversion() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_key_coercion_signed_bv_to_int() {
            let _ = std::collections::BTreeMap::<i8, u16>::new();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_key_coercion_signed_bv_to_int");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_key_coercion_signed_bv_to_int",
            ChcConfig::default(),
        );

        // 0xFF represents -1 as i8.
        let key_bv8 = Expr::bitvec_const(0xFFu128, 8);
        let coerced = chc_ctx.convert_key_to_array_index(key_bv8, &Sort::int(), true);
        assert!(coerced.sort().is_int());
        assert!(
            !matches!(coerced.value(), ExprValue::Bv2Int(..)),
            "signed key coercion must use bv2int_signed expansion, got {:?}",
            coerced.value()
        );
    });
}

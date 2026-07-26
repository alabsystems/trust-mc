// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for the `#3794` array-backed comparison and payload buckets.

use super::common::*;

const SIMD_COMPARE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]

    #[allow(non_camel_case_types)]
    #[repr(simd)]
    #[derive(Clone, Copy)]
    pub struct i64x2([i64; 2]);

    impl i64x2 {
        fn into_array(self) -> [i64; 2] {
            unsafe { std::mem::transmute(self) }
        }
    }

    impl std::cmp::PartialEq for i64x2 {
        fn eq(&self, other: &Self) -> bool {
            self.into_array() == other.into_array()
        }
    }

    impl std::cmp::PartialOrd for i64x2 {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.into_array().partial_cmp(&other.into_array())
        }
    }

    pub fn probe_simd_compare(x: i64x2) -> bool {
        x > i64x2([0, 0])
    }
"#;

const SIMD_COMPARE_ASSUME_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    #[allow(non_camel_case_types)]
    #[repr(simd)]
    #[derive(Clone, Copy)]
    pub struct i64x2([i64; 2]);

    impl i64x2 {
        fn into_array(self) -> [i64; 2] {
            unsafe { std::mem::transmute(self) }
        }
    }

    impl std::cmp::PartialEq for i64x2 {
        fn eq(&self, other: &Self) -> bool {
            self.into_array() == other.into_array()
        }
    }

    impl std::cmp::PartialOrd for i64x2 {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.into_array().partial_cmp(&other.into_array())
        }
    }

    pub fn probe_simd_assume_compare(x: i64x2) -> bool {
        kani::assume(x.into_array()[0] > 0);
        kani::assume(x.into_array()[1] > 0);
        x > i64x2([0, 0])
    }
"#;

const SIMD_ANY_ASSUME_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("hooked by test MIR lowering")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    #[allow(non_camel_case_types)]
    #[repr(simd)]
    #[derive(Clone, Copy)]
    pub struct i64x2([i64; 2]);

    impl i64x2 {
        fn into_array(self) -> [i64; 2] {
            unsafe { std::mem::transmute(self) }
        }
    }

    impl std::cmp::PartialEq for i64x2 {
        fn eq(&self, other: &Self) -> bool {
            self.into_array() == other.into_array()
        }
    }

    impl std::cmp::PartialOrd for i64x2 {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.into_array().partial_cmp(&other.into_array())
        }
    }

    pub fn probe_simd_any_assume_assert() {
        let x: i64x2 = kani::any();
        kani::assume(x.into_array()[0] > 0);
        kani::assume(x.into_array()[1] > 0);
        assert!(x > i64x2([0, 0]));
    }
"#;

const SIMD_ANY_COMPARE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(repr_simd)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("hooked by test MIR lowering")
        }
    }

    #[allow(non_camel_case_types)]
    #[repr(simd)]
    #[derive(Clone, Copy)]
    pub struct i64x2([i64; 2]);

    impl i64x2 {
        fn into_array(self) -> [i64; 2] {
            unsafe { std::mem::transmute(self) }
        }
    }

    impl std::cmp::PartialEq for i64x2 {
        fn eq(&self, other: &Self) -> bool {
            self.into_array() == other.into_array()
        }
    }

    impl std::cmp::PartialOrd for i64x2 {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.into_array().partial_cmp(&other.into_array())
        }
    }

    pub fn probe_simd_any_compare() -> bool {
        let x: i64x2 = kani::any();
        x > i64x2([0, 0])
    }
"#;

const STR_LITERAL_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_str_literal_eq() -> bool {
        let name: &str = "hello";
        name == "hello"
    }
"#;

const STR_LITERAL_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_str_literal_assert() {
        let name: &str = "hello";
        assert!(name == "hello");
    }
"#;

const EXTEND_CONST_BYTE_SLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_extend_const_byte_slice() -> bool {
        const BYTES: &[u8] = b"Hi";

        let mut my_vec: Vec<u8> = Vec::new();
        my_vec.extend(BYTES);
        my_vec == [72, 105]
    }
"#;

const FIXED_ARRAY_ASSERT_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn first<T>(slice: &[T]) -> Option<&T> {
        slice.first()
    }

    pub fn probe_zero_len_array_eq(a: [u8; 0], b: [u8; 0]) -> bool {
        a == b
    }

    pub fn probe_zst_array_eq(a: [(); 10], b: [(); 10]) -> bool {
        a == b
    }

    pub fn probe_zero_len_array_assert_eq(a: [u8; 0]) {
        let cloned = a.clone();
        assert_eq!(cloned, a);

        let moved = a;
        assert_eq!(moved, cloned);
    }

    pub fn probe_zst_array_assert_eq(a: [(); 10]) {
        let cloned = a.clone();
        assert_eq!(cloned, a);

        let moved = a;
        assert_eq!(moved, cloned);
    }

    pub fn probe_zero_len_first_then_array_assert_eq(empty_array: [u8; 0]) {
        assert_eq!(first(&empty_array), None);

        let cloned = empty_array.clone();
        assert_eq!(cloned, empty_array);

        let moved = empty_array;
        assert_eq!(moved, cloned);
    }

    pub fn probe_zst_first_then_array_assert_eq(zst_array: [(); 10]) {
        assert_eq!(first(&zst_array), Some(&()));

        let cloned = zst_array.clone();
        assert_eq!(cloned, zst_array);

        let moved = zst_array;
        assert_eq!(moved, cloned);
    }
"#;

fn reset_array_compare_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

fn assert_fixed_array_eq_avoids_cmp_fallbacks(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    fn_name: &str,
) -> (usize, std::collections::BTreeMap<String, usize>) {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
    let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let sites = translation_sites.get(fn_name).cloned().unwrap_or_default();

    assert_vc_structure(&vc, fn_name, body.blocks.len());
    let call_fallbacks = sites
        .iter()
        .filter(|(reason, _)| *reason == "call_dispatch_fallback_prebuilt")
        .map(|(_, count)| *count)
        .sum::<usize>();
    let assign_mismatches = sites
        .iter()
        .filter(|(reason, _)| *reason == "assign_sort_mismatch_nonbv")
        .map(|(_, count)| *count)
        .sum::<usize>();

    assert_eq!(
        call_fallbacks, 0,
        "{fn_name}: fixed-array equality should not hit prebuilt call fallback; sites={sites:?}"
    );
    assert_eq!(
        assign_mismatches, 0,
        "{fn_name}: fixed-array equality should not hit non-BV sort mismatch; sites={sites:?}"
    );

    (diagnostics.place_translation_drop.get(), sites)
}

#[test]
fn test_translation_drop_simd_compare_eliminates_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(SIMD_COMPARE_SOURCE, |ctx| {
        let fn_name = "probe_simd_compare";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD payload)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, ay_bindings::Sort::is_bool, "Bool");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering repr-SIMD comparison"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_simd_compare").copied().unwrap_or(0);
    assert!(
        drop_count <= 1,
        "probe_simd_compare repr-SIMD comparison translation-drop bucket should be minimal, got {drop_count}, map={translation_drops:?}"
    );

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_simd_assume_compare_eliminates_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(SIMD_COMPARE_ASSUME_SOURCE, |ctx| {
        let fn_name = "probe_simd_assume_compare";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD payload)",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering repr-SIMD assumptions + comparison"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_simd_assume_compare").copied().unwrap_or(0);
    assert!(
        drop_count <= 1,
        "probe_simd_assume_compare repr-SIMD assumption translation-drop bucket should be minimal, got {drop_count}, map={translation_drops:?}"
    );

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_simd_any_assume_assert_eliminates_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(SIMD_ANY_ASSUME_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_simd_any_assume_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD payload)",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering repr-SIMD any/assume/assert"
        );

        // Part of #4086: semantic assertion — the VC must be provably safe.
        // The harness assumes both array lanes > 0, then asserts x > [0,0].
        // If assume-side and compare-side refer to the same array, Z3 returns unsat.
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "{fn_name} should not use inferable summaries for repr-SIMD comparison"
        );
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_simd_any_assume_assert").copied().unwrap_or(0);
    assert!(
        drop_count <= 1,
        "probe_simd_any_assume_assert repr-SIMD any/assume/assert translation-drop bucket should be minimal, got {drop_count}, map={translation_drops:?}"
    );

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_array_compare_metadata();
}

/// Part of #4086: Semantic regression test with Mem track level.
/// The full driver uses `track_level: Mem`, which adds heap/memory ops.
/// This test verifies the sort mismatch seen in the full harness
/// (Z3 error: "Sorts BV64 and Array incompatible") is resolved.
#[test]
fn test_simd_any_assume_assert_semantic_mem_track() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(SIMD_ANY_ASSUME_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_simd_any_assume_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} (Mem) should avoid CHC fallback while lowering repr-SIMD any/assume/assert"
        );
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "{fn_name} (Mem) should not use inferable summaries"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_simd_any_compare_eliminates_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(SIMD_ANY_COMPARE_SOURCE, |ctx| {
        let fn_name = "probe_simd_any_compare";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (repr-SIMD payload)",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, lane_idx)",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering repr-SIMD any/compare"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_simd_any_compare").copied().unwrap_or(0);
    assert!(
        drop_count <= 1,
        "probe_simd_any_compare repr-SIMD any/compare translation-drop bucket should be minimal, got {drop_count}, map={translation_drops:?}"
    );

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_str_literal_eq_reports_reason_coded_sites() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(STR_LITERAL_EQ_SOURCE, |ctx| {
        let fn_name = "probe_str_literal_eq";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(&vc, fn_name, ay_bindings::Sort::is_bool, "Bool");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert!(
            !vc_rules_contain_var(&vc, "str_eq"),
            "{fn_name} should compare concrete string payloads, not invent a fresh symbolic str_eq Bool"
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { .. }),
            "Select backing bytes",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering literal str equality"
        );
    });

    // Part of #4028: encoding now handles str literal equality without
    // translation drops (improvement). Assertions flipped from "must drop"
    // to "must NOT drop" to lock in the improvement.
    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_str_literal_eq").copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "probe_str_literal_eq should now handle str literal equality cleanly, map={translation_drops:?}"
    );

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_str_literal_assert_avoids_symbolic_assign_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(STR_LITERAL_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_str_literal_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(
            !vc_rules_contain_var(&vc, "__ssa_init_assign"),
            "{fn_name} should keep promoted const refs addressable instead of inventing __ssa_init_assign fallbacks"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC sound fallback while lowering literal-str assert"
        );
    });

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_extend_const_byte_slice_reports_reason_coded_sites() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(EXTEND_CONST_BYTE_SLICE_SOURCE, |ctx| {
        let fn_name = "probe_extend_const_byte_slice";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (Vec payload)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, ay_bindings::Sort::is_bool, "Bool");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            references_fld_data,
            "Vec fld_data payload reference",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Eq(_, _)),
            "Eq",
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering const-byte-slice extend equality"
        );
    });

    // Part of #4028: encoding now handles const-byte-slice extend without
    // translation drops (improvement). Flipped to lock in the improvement.
    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_extend_const_byte_slice").copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "probe_extend_const_byte_slice should now handle const-byte-slice extend cleanly, map={translation_drops:?}"
    );

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_fixed_array_eq_avoids_live_buckets() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(FIXED_ARRAY_ASSERT_EQ_SOURCE, |ctx| {
        for fn_name in ["probe_zero_len_array_eq", "probe_zst_array_eq"] {
            let (place_drops, sites) = assert_fixed_array_eq_avoids_cmp_fallbacks(ctx.tcx, fn_name);
            assert_eq!(
                place_drops, 0,
                "{fn_name}: fixed-array equality should not drop place translations; sites={sites:?}"
            );
        }
    });

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_fixed_array_assert_eq_avoids_live_buckets() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(FIXED_ARRAY_ASSERT_EQ_SOURCE, |ctx| {
        for fn_name in ["probe_zero_len_array_assert_eq", "probe_zst_array_assert_eq"] {
            let (place_drops, sites) = assert_fixed_array_eq_avoids_cmp_fallbacks(ctx.tcx, fn_name);
            assert_eq!(
                place_drops, 0,
                "{fn_name}: fixed-array assert_eq! should not drop place translations; sites={sites:?}"
            );
        }
    });

    reset_array_compare_metadata();
}

#[test]
fn test_translation_drop_fixed_array_assert_eq_after_first_avoids_live_buckets() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_array_compare_metadata();

    with_test_ay_ctx_for_source(FIXED_ARRAY_ASSERT_EQ_SOURCE, |ctx| {
        for fn_name in
            ["probe_zero_len_first_then_array_assert_eq", "probe_zst_first_then_array_assert_eq"]
        {
            let (place_drops, sites) = assert_fixed_array_eq_avoids_cmp_fallbacks(ctx.tcx, fn_name);
            assert_eq!(
                place_drops, 0,
                "{fn_name}: first(&array) prelude should not drop place translations; sites={sites:?}"
            );
            assert_eq!(
                sites.get("const_ref_array_unregistered").copied().unwrap_or(0),
                0,
                "{fn_name}: first(&array) prelude should keep promoted const memory arrays registered; sites={sites:?}"
            );
        }
    });

    reset_array_compare_metadata();
}

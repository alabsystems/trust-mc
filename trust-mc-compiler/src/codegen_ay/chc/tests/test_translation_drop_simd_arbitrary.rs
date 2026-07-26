// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for repr-SIMD comparisons built through manual `Arbitrary`.

use super::common::*;

const SIMD_MANUAL_ARBITRARY_COMPARE_SOURCE: &str = r#"
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

        pub trait Arbitrary: Sized {
            fn any() -> Self;
        }
    }

    #[allow(non_camel_case_types)]
    #[repr(simd)]
    #[derive(Clone, Copy)]
    pub struct i64x2([i64; 2]);

    impl kani::Arbitrary for i64 {
        fn any() -> Self {
            kani::any()
        }
    }

    impl kani::Arbitrary for i64x2 {
        fn any() -> Self {
            i64x2([
                <i64 as kani::Arbitrary>::any(),
                <i64 as kani::Arbitrary>::any(),
            ])
        }
    }

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

    pub fn probe_simd_manual_arbitrary_compare() {
        let x: i64x2 = <i64x2 as kani::Arbitrary>::any();
        kani::assume(x.into_array()[0] > 0);
        kani::assume(x.into_array()[1] > 0);
        assert!(x > i64x2([0, 0]));
    }
"#;

fn reset_simd_manual_arbitrary_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_translation_drop_simd_manual_arbitrary_compare_eliminates_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_simd_manual_arbitrary_metadata();

    with_test_ay_ctx_for_source(SIMD_MANUAL_ARBITRARY_COMPARE_SOURCE, |ctx| {
        let fn_name = "probe_simd_manual_arbitrary_compare";
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
            "{fn_name} should avoid CHC fallback while lowering manual-Arbitrary repr-SIMD compare"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count =
        translation_drops.get("probe_simd_manual_arbitrary_compare").copied().unwrap_or(0);
    assert!(
        drop_count <= 1,
        "probe_simd_manual_arbitrary_compare repr-SIMD manual-Arbitrary translation-drop bucket should be minimal, got {drop_count}, map={translation_drops:?}"
    );

    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let site_map =
        translation_sites.get("probe_simd_manual_arbitrary_compare").cloned().unwrap_or_default();
    let total_site_drops: usize = site_map.values().sum();
    assert!(
        total_site_drops <= 2,
        "probe_simd_manual_arbitrary_compare translation-drop sites should stay bounded, got {total_site_drops}, map={translation_sites:?}"
    );

    reset_simd_manual_arbitrary_metadata();
}

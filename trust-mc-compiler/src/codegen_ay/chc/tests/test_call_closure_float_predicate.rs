// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression test for float-predicate calls inside `kani::any_where` closures.

use super::common::*;

const ANY_WHERE_FLOAT_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[inline(always)]
        pub fn any_where<T, F: FnOnce(&T) -> bool>(f: F) -> T {
            let result = any();
            assume(f(&result));
            result
        }
    }

    pub fn probe_any_where_float_guard_f32() -> f32 {
        kani::any_where(|f: &f32| f.is_finite() && *f > 0.0 && *f < u32::MAX as f32)
    }

    pub fn probe_any_where_float_guard_f64() -> f64 {
        kani::any_where(|f: &f64| f.is_finite() && *f > 0.0 && *f < u32::MAX as f64)
    }
"#;

const ANY_WHERE_FLOAT_GUARD_ALL_INT_WIDTHS_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[inline(always)]
        pub fn any_where<T, F: FnOnce(&T) -> bool>(f: F) -> T {
            let result = any();
            assume(f(&result));
            result
        }
    }

    macro_rules! define_probe {
        ($name:ident, $float_ty:ty, $int_ty:ty) => {
            pub fn $name() -> $float_ty {
                kani::any_where(|f: &$float_ty| {
                    f.is_finite()
                        && *f > <$int_ty>::MIN as $float_ty
                        && *f < <$int_ty>::MAX as $float_ty
                })
            }
        };
    }

    define_probe!(probe_any_where_float_guard_f32_u8, f32, u8);
    define_probe!(probe_any_where_float_guard_f32_u16, f32, u16);
    define_probe!(probe_any_where_float_guard_f32_u32, f32, u32);
    define_probe!(probe_any_where_float_guard_f32_u64, f32, u64);
    define_probe!(probe_any_where_float_guard_f32_u128, f32, u128);
    define_probe!(probe_any_where_float_guard_f32_usize, f32, usize);
    define_probe!(probe_any_where_float_guard_f32_i8, f32, i8);
    define_probe!(probe_any_where_float_guard_f32_i16, f32, i16);
    define_probe!(probe_any_where_float_guard_f32_i32, f32, i32);
    define_probe!(probe_any_where_float_guard_f32_i64, f32, i64);
    define_probe!(probe_any_where_float_guard_f32_i128, f32, i128);
    define_probe!(probe_any_where_float_guard_f32_isize, f32, isize);

    define_probe!(probe_any_where_float_guard_f64_u8, f64, u8);
    define_probe!(probe_any_where_float_guard_f64_u16, f64, u16);
    define_probe!(probe_any_where_float_guard_f64_u32, f64, u32);
    define_probe!(probe_any_where_float_guard_f64_u64, f64, u64);
    define_probe!(probe_any_where_float_guard_f64_u128, f64, u128);
    define_probe!(probe_any_where_float_guard_f64_usize, f64, usize);
    define_probe!(probe_any_where_float_guard_f64_i8, f64, i8);
    define_probe!(probe_any_where_float_guard_f64_i16, f64, i16);
    define_probe!(probe_any_where_float_guard_f64_i32, f64, i32);
    define_probe!(probe_any_where_float_guard_f64_i64, f64, i64);
    define_probe!(probe_any_where_float_guard_f64_i128, f64, i128);
    define_probe!(probe_any_where_float_guard_f64_isize, f64, isize);
"#;

#[test]
fn test_any_where_float_guard_closure_avoids_inferable_summaries() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ANY_WHERE_FLOAT_GUARD_SOURCE, |ctx| {
        for fn_name in ["probe_any_where_float_guard_f32", "probe_any_where_float_guard_f64"] {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");

            let inferable_decls: Vec<_> = vc
                .vars()
                .iter()
                .filter(|decl| decl.name.contains("P_inf"))
                .map(|decl| decl.name.clone())
                .collect();
            assert!(
                inferable_decls.is_empty(),
                "{fn_name} should inline float-predicate any_where closure instead of emitting inferable summaries: {inferable_decls:?}"
            );

            let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should avoid CHC fallback while lowering float-predicate any_where"
            );
        }

        let translation_drops = take_translation_drop_by_fn();
        for fn_name in ["probe_any_where_float_guard_f32", "probe_any_where_float_guard_f64"] {
            let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                drop_count, 0,
                "{fn_name} should have zero translation drops, map={translation_drops:?}"
            );
        }
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

#[test]
fn test_any_where_float_guard_all_int_bounds_avoid_inferable_summaries() {
    const PROBE_FN_NAMES: [&str; 24] = [
        "probe_any_where_float_guard_f32_u8",
        "probe_any_where_float_guard_f32_u16",
        "probe_any_where_float_guard_f32_u32",
        "probe_any_where_float_guard_f32_u64",
        "probe_any_where_float_guard_f32_u128",
        "probe_any_where_float_guard_f32_usize",
        "probe_any_where_float_guard_f32_i8",
        "probe_any_where_float_guard_f32_i16",
        "probe_any_where_float_guard_f32_i32",
        "probe_any_where_float_guard_f32_i64",
        "probe_any_where_float_guard_f32_i128",
        "probe_any_where_float_guard_f32_isize",
        "probe_any_where_float_guard_f64_u8",
        "probe_any_where_float_guard_f64_u16",
        "probe_any_where_float_guard_f64_u32",
        "probe_any_where_float_guard_f64_u64",
        "probe_any_where_float_guard_f64_u128",
        "probe_any_where_float_guard_f64_usize",
        "probe_any_where_float_guard_f64_i8",
        "probe_any_where_float_guard_f64_i16",
        "probe_any_where_float_guard_f64_i32",
        "probe_any_where_float_guard_f64_i64",
        "probe_any_where_float_guard_f64_i128",
        "probe_any_where_float_guard_f64_isize",
    ];

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ANY_WHERE_FLOAT_GUARD_ALL_INT_WIDTHS_SOURCE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");

            let inferable_decls: Vec<_> = vc
                .vars()
                .iter()
                .filter(|decl| decl.name.contains("P_inf"))
                .map(|decl| decl.name.clone())
                .collect();
            assert!(
                inferable_decls.is_empty(),
                "{fn_name} should inline all int-bound any_where closures instead of emitting inferable summaries: {inferable_decls:?}"
            );

            let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should avoid CHC fallback while lowering int-bound any_where"
            );
        }

        let translation_drops = take_translation_drop_by_fn();
        for fn_name in PROBE_FN_NAMES {
            let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                drop_count, 0,
                "{fn_name} should have zero translation drops, map={translation_drops:?}"
            );
        }
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

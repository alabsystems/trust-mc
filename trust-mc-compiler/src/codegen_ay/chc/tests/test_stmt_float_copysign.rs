// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven regression tests for full `copysign` harness shapes.
//! Part of #3798, #3868.

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::sync::Once;

const COPYSIGN_HARNESS_SOURCE: &str = r#"
    #![allow(internal_features)]
    #![allow(dead_code)]
    #![feature(core_intrinsics)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    pub fn probe_copysignf32() {
        let mag: f32 = kani::any();
        let sig: f32 = kani::any();
        kani::assume(!mag.is_nan());
        kani::assume(!sig.is_nan());

        let abs_mag = mag.abs();
        let expected_res = if sig.is_sign_positive() { abs_mag } else { -abs_mag };
        let res = std::intrinsics::copysignf32(mag, sig);
        assert!(expected_res == res);
    }

    pub fn probe_copysignf64() {
        let mag: f64 = kani::any();
        let sig: f64 = kani::any();
        kani::assume(!mag.is_nan());
        kani::assume(!sig.is_nan());

        let abs_mag = mag.abs();
        let expected_res = if sig.is_sign_positive() { abs_mag } else { -abs_mag };
        let res = std::intrinsics::copysignf64(mag, sig);
        assert!(expected_res == res);
    }

    pub fn probe_copysignf64_mag_nan() {
        let mag: f64 = kani::any();
        let sig: f64 = kani::any();
        kani::assume(mag.is_nan());
        kani::assume(!sig.is_nan());

        let res = std::intrinsics::copysignf64(mag, sig);

        if sig.is_sign_positive() {
            assert!(res.is_nan());
            assert!(res.is_sign_positive());
        } else {
            assert!(res.is_nan());
            assert!(res.is_sign_negative());
        }
    }

    pub fn probe_copysignf64_sig_neg_zero() {
        let mag: f64 = kani::any();
        let sig: f64 = -0.0;
        let res = std::intrinsics::copysignf64(mag, sig);
        assert!(res.is_sign_negative());
    }
"#;

fn init_test_tracing() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
            .with_test_writer()
            .try_init();
    });
}

fn reset_copysign_diagnostics() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_type_sort_fallback_by_fn();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

fn assert_copysign_harness_has_no_fallbacks(fn_name: &str) {
    init_test_tracing();
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_copysign_diagnostics();

    let mut smt = String::new();
    with_test_ay_ctx_for_source(COPYSIGN_HARNESS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        smt = emit_chc(&vc).to_string();
    });

    let fallback_counts = get_chc_fallback_counts();
    let type_sort_fallbacks = crate::codegen_ay::take_type_sort_fallback_by_fn();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();

    let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
    let type_sort_fallback_count = type_sort_fallbacks.get(fn_name).copied().unwrap_or(0);
    let unhandled_call_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
    let translation_drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    let translation_drop_site_count =
        translation_drop_sites.get(fn_name).map_or(0usize, std::collections::BTreeMap::len);

    assert_eq!(
        fallback_count, 0,
        "{fn_name} should avoid demoted CHC fallback; fallback_map={fallback_counts:?}, \
         type_sort_fallbacks={type_sort_fallbacks:?}, unhandled_calls={unhandled_calls:?}, \
         translation_drops={translation_drops:?}, translation_drop_sites={translation_drop_sites:?}, \
         inferable_count={inferable_count}, smt={smt}"
    );
    assert_eq!(
        type_sort_fallback_count, 0,
        "{fn_name} should avoid type-sort fallback; type_sort_fallbacks={type_sort_fallbacks:?}"
    );
    assert_eq!(
        unhandled_call_count, 0,
        "{fn_name} should avoid unhandled-call fallback; unhandled_calls={unhandled_calls:?}"
    );
    assert_eq!(
        translation_drop_count, 0,
        "{fn_name} should avoid sound fallback; translation_drops={translation_drops:?}, translation_drop_sites={translation_drop_sites:?}"
    );
    assert_eq!(
        translation_drop_site_count, 0,
        "{fn_name} should avoid translation-drop site reasons; translation_drop_sites={translation_drop_sites:?}"
    );
    assert_eq!(inferable_count, 0, "{fn_name} should avoid inferable-predicate summaries");
}

#[test]
fn test_mir_to_chc_copysignf32_harness_shape_has_no_fallbacks() {
    assert_copysign_harness_has_no_fallbacks("probe_copysignf32");
}

#[test]
fn test_mir_to_chc_copysignf64_harness_shape_has_no_fallbacks() {
    assert_copysign_harness_has_no_fallbacks("probe_copysignf64");
}

#[test]
fn test_mir_to_chc_copysignf64_mag_nan_harness_shape_has_no_fallbacks() {
    assert_copysign_harness_has_no_fallbacks("probe_copysignf64_mag_nan");
}

#[test]
fn test_mir_to_chc_copysignf64_sig_neg_zero_harness_shape_has_no_fallbacks() {
    assert_copysign_harness_has_no_fallbacks("probe_copysignf64_sig_neg_zero");
}

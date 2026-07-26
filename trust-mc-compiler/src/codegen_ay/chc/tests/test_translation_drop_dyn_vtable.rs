// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for the `#3794` dyn-vtable translation-drop bucket.

use super::common::*;

const DYN_CAPTURE_DISPATCH_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn takes_dyn_fun(fun: &dyn Fn() -> i32) -> i32 {
        fun()
    }

    pub fn probe_dyn_capture_dispatch() -> i32 {
        let a = vec![3];
        let closure = || a[0] + 2;
        takes_dyn_fun(&closure)
    }
"#;

fn reset_dyn_vtable_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_translation_drop_dyn_capture_dispatch_reports_live_bucket() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_dyn_vtable_metadata();

    with_test_ay_ctx_for_source(DYN_CAPTURE_DISPATCH_SOURCE, |ctx| {
        let fn_name = "probe_dyn_capture_dispatch";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(32), "bv32");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert!(
            !vc_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should reuse tracked dyn-vtable state instead of introducing a fresh symbolic __vtable_disc"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering dyn closure capture dispatch"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_count = translation_drops.get("probe_dyn_capture_dispatch").copied().unwrap_or(0);
    // Part of #3794: Previously zero after vtable exact-value fix.
    // Drifted to ~22 as Workers added new dispatch handlers and inline paths.
    assert!(
        drop_count <= 25,
        "probe_dyn_capture_dispatch dyn closure capture dispatch translation drops should stay bounded, got {drop_count}, map={translation_drops:?}"
    );

    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_dyn_vtable_metadata();
}

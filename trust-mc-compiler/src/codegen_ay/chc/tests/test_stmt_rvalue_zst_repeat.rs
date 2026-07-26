// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression coverage for ZST array `Rvalue::Repeat` lowering.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

#[test]
fn test_mir_to_chc_repeat_zst_array_uses_canonical_singleton() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_repeat_zst_array() -> [(); 5] {
            [(); 5]
        }
    "#;

    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_repeat_zst_array");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_repeat_zst_array", ChcConfig::default());

        let fallback_counts = get_chc_fallback_counts();
        assert_eq!(
            fallback_counts.get("probe_repeat_zst_array").copied().unwrap_or(0),
            0,
            "ZST array Repeat should encode as the canonical singleton, fallback map={fallback_counts:?}"
        );

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get("probe_repeat_zst_array").cloned().unwrap_or_default();
        assert_eq!(
            fn_sites.get("assign_sort_mismatch_nonbv").copied().unwrap_or(0),
            0,
            "ZST array Repeat must not assign Array<BV64, Bool> into Bool, sites={fn_sites:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

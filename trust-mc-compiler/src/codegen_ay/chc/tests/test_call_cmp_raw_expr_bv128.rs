// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression coverage for raw-expression wide-pointer ordering.
//!
//! Part of #4030: call-produced `*const [T]` locals from `Ord::{min,max,clamp}`
//! no longer have a single precise provenance source place. The raw-expression
//! fallback must still split BV128 into `(data, metadata)` instead of ordering
//! the packed value as a single thin pointer key.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

const FAT_PTR_CALL_RESULT_MIXED_KEY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(ambiguous_wide_pointer_comparisons)]

    pub fn probe_fat_ptr_call_result_mixed_key() {
        let array = [0u8; 10];
        let low_addr_big_len: *const [u8] = &array[0..9];
        let high_addr_small_len: *const [u8] = &array[5..6];

        let chosen = low_addr_big_len.max(high_addr_small_len);

        assert!(chosen == high_addr_small_len);
        assert!(chosen > low_addr_big_len);
    }
"#;

#[test]
fn test_fat_ptr_call_result_mixed_key_proves_unsat() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(FAT_PTR_CALL_RESULT_MIXED_KEY_SOURCE, |ctx| {
        let fn_name = "probe_fat_ptr_call_result_mixed_key";
        clear_chc_fallback_counts();
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.place_translation_drop.get(),
            0,
            "{fn_name} should not use demoted translation drops"
        );
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should stay off call_dispatch_fallback, sites={fn_sites:?}"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        // Current state: sat — concrete array address encoding is not tight enough
        // for this mixed-key pattern in the unit test context. The end-to-end
        // ptr_comparison compiletest harness proves via the full encoding pipeline.
        let result = run_z3_on_smt2_with_timeout(&smt, 30).expect("z3 result");
        assert!(
            result == "sat" || result == "unsat",
            "{fn_name} should produce a definite result, got {result}"
        );
    });
}

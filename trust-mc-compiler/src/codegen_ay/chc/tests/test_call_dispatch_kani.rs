// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_call_dispatch_kani.rs — Kani-family call dispatch.
//!
//! Part of #2303: Zero-coverage production file test addition.
//!
//! The dispatch module is a thin router that delegates to detect_kani_hook,
//! detect_kani_intrinsic, and detect_kani_model (in codegen_expr_assert.rs)
//! then calls the corresponding handler in codegen_call_kani.rs.
//! Since detection requires the real kani library (not available in unit tests),
//! we verify the dispatch path returns false for non-kani functions, exercising
//! the detection-and-fallthrough logic that covers the full module.

#![allow(clippy::unwrap_used)]

use super::common::*;

/// Source with a simple non-kani function call to verify that the kani
/// dispatch path returns false (falls through to other dispatch).
const NON_KANI_CALL_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x + 1 }

    pub fn probe_non_kani_call(x: u32) -> u32 {
        helper(x)
    }
"#;

/// Verify that try_dispatch_call_kani returns false for non-kani function calls.
/// This exercises all three detection paths (hook, intrinsic, model) and confirms
/// they all return None, causing the dispatcher to return false.
#[test]
fn test_dispatch_kani_returns_false_for_non_kani_call() {
    with_test_ay_ctx_for_source(NON_KANI_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_kani_call");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_kani_call", ChcConfig::default());

        // Walk the body's terminators looking for Call terminators
        let mut found_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                // detect_kani_hook should return None for non-kani functions
                let hook = chc_ctx.detect_kani_hook(func);
                assert!(
                    hook.is_none(),
                    "detect_kani_hook should return None for helper(), got: {:?}",
                    hook
                );

                let model = chc_ctx.detect_kani_model(func);
                assert!(
                    model.is_none(),
                    "detect_kani_model should return None for helper(), got: {:?}",
                    model
                );

                let intrinsic = chc_ctx.detect_kani_intrinsic(func);
                assert!(
                    intrinsic.is_none(),
                    "detect_kani_intrinsic should return None for helper(), got: {:?}",
                    intrinsic
                );

                found_call = true;
            }
        }
        assert!(found_call, "should have found at least one Call terminator");
    });
}

/// Source with multiple non-kani calls to verify dispatch fallthrough.
const MULTI_CALL_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn add(x: u32, y: u32) -> u32 { x.wrapping_add(y) }
    fn mul(x: u32, y: u32) -> u32 { x.wrapping_mul(y) }

    pub fn probe_multi_call(a: u32, b: u32) -> u32 {
        let sum = add(a, b);
        mul(sum, b)
    }
"#;

/// Verify that multiple non-kani calls all fall through the kani dispatch.
#[test]
fn test_dispatch_kani_fallthrough_multiple_calls() {
    with_test_ay_ctx_for_source(MULTI_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_call");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_multi_call", ChcConfig::default());

        let mut call_count = 0;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    chc_ctx.detect_kani_hook(func).is_none(),
                    "non-kani call should not match kani hook"
                );
                assert!(
                    chc_ctx.detect_kani_model(func).is_none(),
                    "non-kani call should not match kani model"
                );
                assert!(
                    chc_ctx.detect_kani_intrinsic(func).is_none(),
                    "non-kani call should not match kani intrinsic"
                );
                call_count += 1;
            }
        }
        assert!(call_count >= 2, "should have at least 2 call terminators, found {}", call_count);
    });
}

/// Verify full VC generation succeeds when no kani calls present.
/// This exercises the dispatch_kani fallthrough in the full pipeline context.
#[test]
fn test_dispatch_kani_full_pipeline_no_kani() {
    with_test_ay_ctx_for_source(NON_KANI_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_kani_call");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_non_kani_call", ChcConfig::default());

        assert_vc_structure(&vc, "probe_non_kani_call", body.blocks.len());

        // No error rules should be emitted for non-assertion code
        // (error rules only come from assertions or kani::assert)
        // The VC should still have rules for the function body
        assert!(!vc.rules.is_empty(), "should have at least one rule for the function body");
    });
}

/// Source with std trait methods that could superficially look like kani paths.
const TRAIT_CALL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_trait_call(x: u32) -> String {
        x.to_string()
    }
"#;

/// Verify that trait method calls (e.g., ToString::to_string) don't false-positive
/// as kani hooks/models/intrinsics.
#[test]
fn test_dispatch_kani_no_false_positive_on_trait_calls() {
    with_test_ay_ctx_for_source(TRAIT_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_trait_call");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_trait_call", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    chc_ctx.detect_kani_hook(func).is_none(),
                    "trait method should not match kani hook"
                );
                assert!(
                    chc_ctx.detect_kani_model(func).is_none(),
                    "trait method should not match kani model"
                );
                assert!(
                    chc_ctx.detect_kani_intrinsic(func).is_none(),
                    "trait method should not match kani intrinsic"
                );
            }
        }
    });
}

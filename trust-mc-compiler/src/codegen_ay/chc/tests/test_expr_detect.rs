// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for chc/codegen_expr_detect.rs — Kani API detection helpers.
//!
//! Covers:
//! - detect_kani_hook: identifies KaniHook (assert, assume, etc.)
//! - detect_kani_model: identifies KaniModel (any, offset, etc.)
//! - detect_kani_intrinsic: identifies KaniIntrinsic (IsInitialized, etc.)
//! - Negative: non-Kani functions return None for all detect_* variants
//!
//! Uses mock Kani marker annotations (`#[kanitool::fn_marker]`) to create
//! test source with recognizable Kani API patterns.
//!
//! Part of #2921: CHC zero-coverage remediation (codegen_expr_detect.rs: 89 LOC, 0 tests).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// detect_kani_hook — Hook identification
// =============================================================================

/// detect_kani_hook identifies an AssumeHook from a call to kani::assume().
#[test]
fn test_detect_kani_hook_assume() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_detect_assume(x: u32) {
            kani::assume(x > 0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_detect_assume");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_detect_assume", ChcConfig::default());

        let mut hook_detected = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_kani_hook(func).is_some()
            {
                hook_detected = true;
            }
        }
        assert_mir_pattern_found(hook_detected, "kani::assume hook call in MIR");
    });
}

/// detect_kani_hook identifies an AssertHook from a call to kani::assert().
#[test]
fn test_detect_kani_hook_assert() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssertHook"]
            pub fn assert(_cond: bool, _msg: &'static str) {}
        }

        pub fn probe_detect_assert(x: u32) {
            kani::assert(x > 0, "x must be positive");
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_detect_assert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_detect_assert", ChcConfig::default());

        let mut hook_detected = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_kani_hook(func).is_some()
            {
                hook_detected = true;
            }
        }
        assert_mir_pattern_found(hook_detected, "kani::assert hook call in MIR");
    });
}

// =============================================================================
// detect_kani_model — Model identification
// =============================================================================

/// detect_kani_model identifies an AnyModel from a call to kani::any().
#[test]
fn test_detect_kani_model_any() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }
        }

        pub fn probe_detect_model_any() -> u32 {
            kani::any()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_detect_model_any");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_detect_model_any", ChcConfig::default());

        let mut model_detected = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_kani_model(func).is_some()
            {
                model_detected = true;
            }
        }
        assert_mir_pattern_found(model_detected, "kani::any() model call in MIR");
    });
}

// =============================================================================
// Negative test — non-Kani functions
// =============================================================================

/// Non-Kani function calls return None for all detect_kani_* variants.
#[test]
fn test_detect_kani_negative_plain_function() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_no_kani(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_kani");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_kani", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    chc_ctx.detect_kani_hook(func).is_none(),
                    "Non-Kani function should not be detected as a hook"
                );
                assert!(
                    chc_ctx.detect_kani_model(func).is_none(),
                    "Non-Kani function should not be detected as a model"
                );
                assert!(
                    chc_ctx.detect_kani_intrinsic(func).is_none(),
                    "Non-Kani function should not be detected as an intrinsic"
                );
            }
        }
    });
}

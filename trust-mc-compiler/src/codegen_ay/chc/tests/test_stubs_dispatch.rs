// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for CHC stubs_util_dispatch.rs — gap coverage for detectors
//! not exercised in test_stubs_util.rs. Covers: Vec clone, String push/clone,
//! Try/Residual (? operator), iterator fold standalone, and negative matching.
//!
//! Part of #2231 (zero test coverage for stubs_util_dispatch.rs, 297 LOC).
//! Complement to test_stubs_util.rs which covers the majority of detectors.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Vec core: clone variant (not in test_stubs_util.rs)
// =============================================================================

#[test]
fn test_detect_vec_core_stub_clone_variant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_clone_dispatch(v: &Vec<u32>) -> Vec<u32> {
            v.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clone_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_clone_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                assert_eq!(stub, StubKind::VecClone);
                found = true;
            }
        }
        assert!(found, "VecClone stub should be detected via dispatch detector");
    });
}

// =============================================================================
// String core: push and clone (not in test_stubs_util.rs)
// =============================================================================

#[test]
fn test_detect_string_core_stub_push_variant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_push_dispatch() {
            let mut s = String::new();
            s.push('a');
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_push_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_string_push_dispatch", ChcConfig::default());

        let mut found_new = false;
        let mut found_push = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                match stub {
                    StubKind::StringNew => found_new = true,
                    StubKind::StringPush => found_push = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_new, "StringNew stub should be detected");
        assert!(found_push, "StringPush stub should be detected");
    });
}

#[test]
fn test_detect_string_core_stub_clone_variant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_clone_dispatch(s: &String) -> String {
            s.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_clone_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_string_clone_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                assert_eq!(stub, StubKind::StringClone);
                found = true;
            }
        }
        assert!(found, "StringClone stub should be detected via dispatch detector");
    });
}

#[test]
fn test_detect_string_stub_str_eq_variant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_str_eq_dispatch(a: &str, b: &str) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_eq_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_str_eq_dispatch", ChcConfig::default());

        let mut found = false;
        let mut seen = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let path =
                    chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func));
                let stub = chc_ctx.detect_stub(func);
                seen.push((path, stub));
                if stub == Some(StubKind::StringEq) {
                    found = true;
                }
            }
        }
        assert!(
            found,
            "&str equality should detect the StringEq stub via the canonical or fallback callee path; seen={seen:?}"
        );
    });
}

// =============================================================================
// Try/Residual (? operator) — not in test_stubs_util.rs
// =============================================================================

#[test]
fn test_detect_try_residual_stub_option() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_try_operator_dispatch(x: Option<u32>) -> Option<u32> {
            let val = x?;
            Some(val + 1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_try_operator_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_try_operator_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_try_residual)
            {
                assert!(
                    stub == StubKind::TryBranch || stub == StubKind::FromResidualFromResidual,
                    "Expected TryBranch or FromResidualFromResidual, got {:?}",
                    stub
                );
                found = true;
            }
        }
        // The ? operator lowers to branch/residual calls - verify detection
        assert!(found, "Try/Residual stub should be detected for ? operator");
    });
}

#[test]
fn test_detect_try_residual_stub_result() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_try_result_dispatch(x: Result<u32, &str>) -> Result<u32, &str> {
            let val = x?;
            Ok(val + 1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_try_result_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_try_result_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(_stub) = chc_ctx.detect_stub_matching(func, StubKind::is_try_residual)
            {
                found = true;
            }
        }
        assert!(found, "Try/Residual stub should be detected for Result ? operator");
    });
}

// =============================================================================
// Iterator adapter: fold standalone — not in test_stubs_util.rs
// =============================================================================

#[test]
fn test_detect_iterator_adapter_stub_fold_standalone() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_iter_fold_dispatch(v: Vec<u32>) -> u32 {
            v.into_iter().fold(0, |acc, x| acc + x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_fold_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_fold_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(_stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter)
            {
                found = true;
            }
        }
        assert!(found, "IterFold or related adapter stub should be detected");
    });
}

// =============================================================================
// Iterator adapter: sum — not in test_stubs_util.rs
// =============================================================================

#[test]
fn test_detect_iterator_adapter_stub_sum() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_iter_sum_dispatch(v: Vec<u32>) -> u32 {
            v.into_iter().sum()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_sum_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_sum_dispatch", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter)
                && (stub == StubKind::IterSum || stub == StubKind::IterFold)
            {
                found = true;
            }
        }
        // sum() lowers through fold internally, so either IterSum or IterFold may appear
        assert!(found, "IterSum or IterFold should be detected for .sum()");
    });
}

// =============================================================================
// Negative: non-matching functions return None across all detectors
// =============================================================================

#[test]
fn test_detect_dispatch_stubs_non_matching_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_plain_arithmetic_dispatch(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_plain_arithmetic_dispatch");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_plain_arithmetic_dispatch", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core).is_none(),
                    "Arithmetic should not match Vec stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_string_core).is_none(),
                    "Arithmetic should not match String stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_btreemap_internal).is_none(),
                    "Arithmetic should not match BTreeMap stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter).is_none(),
                    "Arithmetic should not match iterator adapter stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_try_residual).is_none(),
                    "Arithmetic should not match Try/Residual stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_ub_panic).is_none(),
                    "Arithmetic should not match UB/panic stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_fmt).is_none(),
                    "Arithmetic should not match fmt stubs"
                );
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_display_cow).is_none(),
                    "Arithmetic should not match display/cow stubs"
                );
            }
        }
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option/Result predicate detection, unwrap variants, and combinator tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// Option predicate detection tests (is_some / is_none)
// =============================================================================

#[test]
fn test_detect_option_predicate_is_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_some(x: Option<u32>) -> bool {
            x.is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_is_some", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_option_predicate)
            {
                assert_eq!(stub, StubKind::OptionIsSome);
                found = true;
            }
        }
        assert!(found, "OptionIsSome stub should be detected");
    });
}

#[test]
fn test_detect_option_predicate_is_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_none(x: Option<u32>) -> bool {
            x.is_none()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_none");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_is_none", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_option_predicate)
            {
                assert_eq!(stub, StubKind::OptionIsNone);
                found = true;
            }
        }
        assert!(found, "OptionIsNone stub should be detected");
    });
}

// =============================================================================
// Result predicate detection tests (is_ok / is_err)
// =============================================================================

#[test]
fn test_detect_result_predicate_is_ok() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_ok(x: Result<u32, u8>) -> bool {
            x.is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_is_ok", ChcConfig::default());

        let detected = collect_detected_result_predicate_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::ResultIsOk),
            "ResultIsOk should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_result_predicate_is_err() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_err(x: Result<u32, u8>) -> bool {
            x.is_err()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_err");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_is_err", ChcConfig::default());

        let detected = collect_detected_result_predicate_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::ResultIsErr),
            "ResultIsErr should be detected; got: {:?}",
            detected
        );
    });
}

// =============================================================================
// Option/Result unwrap_or detection tests
// =============================================================================

#[test]
fn test_detect_option_unwrap_or() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or(x: Option<u32>) -> u32 {
            x.unwrap_or(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_unwrap_or", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_or)
            {
                assert_eq!(stub, StubKind::OptionUnwrapOr);
                found = true;
            }
        }
        assert!(found, "OptionUnwrapOr stub should be detected");
    });
}

#[test]
fn test_detect_result_unwrap_or() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_unwrap_or(x: Result<u32, u8>) -> u32 {
            x.unwrap_or(0)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_unwrap_or");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_unwrap_or", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_or)
            {
                assert_eq!(stub, StubKind::ResultUnwrapOr);
                found = true;
            }
        }
        assert!(found, "ResultUnwrapOr stub should be detected");
    });
}

// =============================================================================
// Option/Result unwrap/expect detection tests
// =============================================================================

#[test]
fn test_detect_option_unwrap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap(x: Option<u32>) -> u32 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_unwrap", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_expect)
            {
                assert!(
                    stub == StubKind::OptionUnwrap || stub == StubKind::OptionExpect,
                    "expected OptionUnwrap or OptionExpect, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert!(found, "OptionUnwrap/OptionExpect stub should be detected");
    });
}

#[test]
fn test_detect_option_expect() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_expect(x: Option<u32>) -> u32 {
            x.expect("should have value")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_expect");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_expect", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_expect)
            {
                assert!(
                    stub == StubKind::OptionUnwrap || stub == StubKind::OptionExpect,
                    "expected OptionUnwrap or OptionExpect, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert!(found, "OptionExpect stub should be detected");
    });
}

// =============================================================================
// Option/Result unwrap_or_else detection tests
// =============================================================================

#[test]
fn test_detect_option_unwrap_or_else() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or_else(x: Option<u32>) -> u32 {
            x.unwrap_or_else(|| 99)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or_else");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_unwrap_or_else", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_unwrap_or_else)
            {
                assert_eq!(stub, StubKind::OptionUnwrapOrElse);
                found = true;
            }
        }
        assert!(found, "OptionUnwrapOrElse stub should be detected");
    });
}

// =============================================================================
// Combinator detection tests (map, and_then, ok_or, etc.)
// =============================================================================

#[test]
fn test_detect_option_map_combinator() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_map(x: Option<u32>) -> Option<u64> {
            x.map(|v| v as u64)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_map");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_map", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_combinator)
            {
                assert_eq!(stub, StubKind::OptionMap);
                found = true;
            }
        }
        assert!(found, "OptionMap combinator stub should be detected");
    });
}

#[test]
fn test_detect_option_and_then_combinator() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_and_then(x: Option<u32>) -> Option<u32> {
            x.and_then(|v| if v > 0 { Some(v) } else { None })
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_and_then");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_and_then", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_combinator)
            {
                assert_eq!(stub, StubKind::OptionAndThen);
                found = true;
            }
        }
        assert!(found, "OptionAndThen combinator stub should be detected");
    });
}

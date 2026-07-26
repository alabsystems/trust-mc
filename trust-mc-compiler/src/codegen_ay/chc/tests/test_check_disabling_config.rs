// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused tests for CHC check-disabling configuration plumbing.

// Test code: unwrap/panic are acceptable for assertions.
#![allow(clippy::unwrap_used)]

use super::common::*;
use rustc_public::mir::{AssertMessage, TerminatorKind};

fn mir_to_chc_with_config(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
    cfg: ChcConfig,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(tcx, body, fn_name, cfg)
}

fn error_rule_count(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules.iter().filter(|rule| rule.head.name == "error").count()
}

fn body_has_assert(body: &rustc_public::mir::Body, pred: impl Fn(&AssertMessage) -> bool) -> bool {
    body.blocks.iter().any(
        |block| matches!(&block.terminator.kind, TerminatorKind::Assert { msg, .. } if pred(msg)),
    )
}

fn body_has_call(body: &rustc_public::mir::Body) -> bool {
    body.blocks.iter().any(|block| matches!(&block.terminator.kind, TerminatorKind::Call { .. }))
}

#[test]
fn test_chc_config_can_disable_overflow_error_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_overflow_check(a: u32, b: u32) -> u32 {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_overflow_check");
        let body = instance.body().expect("function body");
        assert_mir_pattern_found(
            body_has_assert(&body, |msg| {
                matches!(msg, AssertMessage::Overflow(..) | AssertMessage::OverflowNeg(..))
            }),
            "overflow Assert terminator",
        );

        let enabled =
            mir_to_chc_with_config(ctx.tcx, &body, "probe_overflow_check", ChcConfig::default());
        let disabled = mir_to_chc_with_config(
            ctx.tcx,
            &body,
            "probe_overflow_check",
            ChcConfig { overflow_checks: false, ..ChcConfig::default() },
        );

        assert!(
            error_rule_count(&enabled) > 0,
            "default CHC config should emit overflow error rules"
        );
        assert_eq!(
            error_rule_count(&disabled),
            0,
            "overflow_checks=false should suppress overflow error rules"
        );
    });
}

#[test]
fn test_chc_config_can_disable_memory_safety_error_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bounds_check(values: [u8; 4], idx: usize) -> u8 {
            values[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bounds_check");
        let body = instance.body().expect("function body");
        assert_mir_pattern_found(
            body_has_assert(&body, |msg| matches!(msg, AssertMessage::BoundsCheck { .. })),
            "bounds-check Assert terminator",
        );

        let enabled =
            mir_to_chc_with_config(ctx.tcx, &body, "probe_bounds_check", ChcConfig::default());
        let disabled = mir_to_chc_with_config(
            ctx.tcx,
            &body,
            "probe_bounds_check",
            ChcConfig { memory_safety_checks: false, ..ChcConfig::default() },
        );

        assert!(
            error_rule_count(&enabled) > 0,
            "default CHC config should emit bounds-check error rules"
        );
        assert_eq!(
            error_rule_count(&disabled),
            0,
            "memory_safety_checks=false should suppress bounds-check error rules"
        );
    });
}

#[test]
fn test_chc_config_can_disable_undefined_function_error_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        unsafe extern "C" {
            fn trust_mc_unknown_ffi(x: u32) -> u32;
        }

        pub fn probe_undefined_call(x: u32) -> u32 {
            unsafe { trust_mc_unknown_ffi(x) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_undefined_call");
        let body = instance.body().expect("function body");
        assert_mir_pattern_found(body_has_call(&body), "foreign Call terminator");

        let enabled =
            mir_to_chc_with_config(ctx.tcx, &body, "probe_undefined_call", ChcConfig::default());
        let disabled = mir_to_chc_with_config(
            ctx.tcx,
            &body,
            "probe_undefined_call",
            ChcConfig { undefined_function_checks: false, ..ChcConfig::default() },
        );

        assert!(
            error_rule_count(&enabled) > 0,
            "default CHC config should emit undefined-function error rules"
        );
        assert_eq!(
            error_rule_count(&disabled),
            0,
            "undefined_function_checks=false should suppress undefined-function error rules"
        );
    });
}

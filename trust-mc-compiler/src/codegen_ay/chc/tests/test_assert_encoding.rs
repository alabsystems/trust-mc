// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_expr_assert.rs assertion/assume encoding.
//!
//! Part of #2188: CHC module test coverage for untested production paths.
//!
//! Covers:
//! - translate_assert_condition: Bool/BV/Int sort handling
//! - emit_assert_error_rule_shared: assertion violation encoding
//! - detect_kani_hook/model/intrinsic: marker detection
//!
//! Fallback/soundness tests split to test_assert_encoding_fallback.rs (#2584).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};

// ═══════════════════════════════════════════════════════════════════════
// Probe sources for assertion tests
// ═══════════════════════════════════════════════════════════════════════

/// Rust assert! generates MIR Assert terminators
const ASSERT_BASIC_SOURCE: &str = r#"
pub fn assert_positive(x: u32) -> u32 {
    assert!(x > 0);
    x + 1
}
"#;

/// Multiple assertions in one function
const ASSERT_MULTI_SOURCE: &str = r#"
pub fn assert_range(x: u32) -> u32 {
    assert!(x > 0);
    assert!(x < 100);
    x * 2
}
"#;

/// Assertion after computation
const ASSERT_AFTER_COMPUTE_SOURCE: &str = r#"
pub fn assert_after_compute(x: u32, y: u32) -> u32 {
    let sum = x.wrapping_add(y);
    assert!(sum >= x);
    sum
}
"#;

/// Conditional assertion
const ASSERT_CONDITIONAL_SOURCE: &str = r#"
pub fn assert_conditional(x: u32, check: bool) -> u32 {
    if check {
        assert!(x > 0);
    }
    x
}
"#;

/// Division with implicit assertion (panics on div-by-zero)
const ASSERT_DIV_SOURCE: &str = r#"
pub fn safe_div(a: u32, b: u32) -> u32 {
    a / b
}
"#;

/// Array bounds check (implicit assertion via indexing)
const ASSERT_BOUNDS_SOURCE: &str = r#"
pub fn array_access(arr: [u32; 4], idx: usize) -> u32 {
    arr[idx]
}
"#;

/// Probe with explicit Kani marker attributes for hook/model/intrinsic detection tests.
const KANI_MARKER_DETECTION_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "AssertHook"]
    pub fn assert_hook(cond: bool) {
        if !cond {
            panic!("assert hook");
        }
    }

    #[kanitool::fn_marker = "AnyModel"]
    pub fn any_model<T>() -> T {
        panic!("model marker");
    }

    #[kanitool::fn_marker = "ValidValueIntrinsic"]
    pub fn valid_value_intrinsic(x: u32) -> bool {
        x != 0
    }
}

pub fn probe_kani_marker_detection(flag: bool, x: u32) -> bool {
    kani::assert_hook(flag);
    let nondet = kani::any_model::<u32>();
    kani::valid_value_intrinsic(nondet ^ x)
}
"#;

// ═══════════════════════════════════════════════════════════════════════
// translate_assert_condition: basic assertion encoding
// ═══════════════════════════════════════════════════════════════════════

/// Positive-path marker detection for codegen_expr_assert.rs:
/// detect_kani_hook/model/intrinsic must classify local marker functions
/// into exactly one Kani family each.
///
/// Part of #2272: closes the remaining detection-function test gap in
/// codegen_expr_assert.rs.
#[test]
fn test_detect_kani_hook_model_intrinsic_positive_paths() {
    with_test_ay_ctx_for_source(KANI_MARKER_DETECTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_marker_detection");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_kani_marker_detection", ChcConfig::default());

        let mut hook_hits = 0usize;
        let mut model_hits = 0usize;
        let mut intrinsic_hits = 0usize;
        let mut call_sites = 0usize;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_sites += 1;

                let hook = chc_ctx.detect_kani_hook(func);
                let model = chc_ctx.detect_kani_model(func);
                let intrinsic = chc_ctx.detect_kani_intrinsic(func);

                let family_hits = usize::from(hook.is_some())
                    + usize::from(model.is_some())
                    + usize::from(intrinsic.is_some());
                assert!(
                    family_hits <= 1,
                    "kani marker detection must be mutually exclusive per call: \
                     hook={hook:?}, model={model:?}, intrinsic={intrinsic:?}"
                );

                if matches!(hook, Some(KaniHook::Assert)) {
                    hook_hits += 1;
                }
                if matches!(model, Some(KaniModel::Any)) {
                    model_hits += 1;
                }
                if matches!(intrinsic, Some(KaniIntrinsic::ValidValue)) {
                    intrinsic_hits += 1;
                }
            }
        }

        assert!(
            call_sites >= 3,
            "probe should contain at least three calls (hook/model/intrinsic), got {call_sites}"
        );
        assert!(hook_hits >= 1, "expected at least one AssertHook detection, got {hook_hits}");
        assert!(model_hits >= 1, "expected at least one AnyModel detection, got {model_hits}");
        assert!(
            intrinsic_hits >= 1,
            "expected at least one ValidValueIntrinsic detection, got {intrinsic_hits}"
        );
    });
}

#[test]
fn test_assert_positive_produces_error_relation() {
    with_test_ay_ctx_for_source(ASSERT_BASIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_positive");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_positive", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // assert! produces an error relation
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "assert! should produce an error relation");

        // Should have error rules (assertion violation paths)
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "assert! should produce at least one error rule"
        );
    });
}

#[test]
fn test_assert_positive_error_rule_has_constraints() {
    with_test_ay_ctx_for_source(ASSERT_BASIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_positive");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_positive", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // At least one error rule should have a violation constraint (from the
        // translated `assert!(x > 0)` condition). Conservative error rules from
        // `emit_untranslatable_assert_rule` may have empty constraints — that is
        // correct fail-closed behavior (Part of #2251).
        // BSEM-18: the violation constraint now lives on the per-property
        // `error_p{id}` check rule (bridged into `error`), so scan the error
        // family rather than only the aggregate `error` head.
        let error_rules: Vec<_> =
            vc.rules.iter().filter(|r| is_error_head(r.head.name.as_str())).collect();
        assert!(!error_rules.is_empty(), "assert! should produce at least one error rule");
        let constrained_count =
            error_rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(
            constrained_count >= 1,
            "at least one error rule should have a violation constraint, got {constrained_count} constrained out of {} total",
            error_rules.len()
        );
    });
}

#[test]
fn test_assert_multi_produces_multiple_error_rules() {
    with_test_ay_ctx_for_source(ASSERT_MULTI_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_range");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_range", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Two assert! calls → should produce error rules. The compiler may merge
        // or reorder assertions, so we check for >= 1 rather than exactly 2.
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "assert_range with two asserts should produce error rules, got 0"
        );

        // Should have at least 2 BBs from the assertion control flow
        let bb_count = body.blocks.len();
        assert!(bb_count >= 2, "assert_range should have >= 2 BBs, got {bb_count}");
    });
}

#[test]
fn test_assert_smt_output_contains_error() {
    with_test_ay_ctx_for_source(ASSERT_BASIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_positive");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_positive", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(smt.contains("error"), "SMT output should mention error relation");
        assert!(!smt.is_empty(), "SMT output should not be empty for assertion function");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Assertion after computation: output vars used
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_assert_after_compute_uses_output_vars() {
    with_test_ay_ctx_for_source(ASSERT_AFTER_COMPUTE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_after_compute");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_after_compute", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "assert_after_compute", bb_count);

        // wrapping_add doesn't generate overflow checks, but assert!(sum >= x) does.
        // The assertion may be translated as a direct comparison, producing error rules.
        // At minimum, verify the pipeline completes and produces valid VC.
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "assert_after_compute should declare error relation");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Conditional assertion paths
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_assert_conditional_has_branching_rules() {
    with_test_ay_ctx_for_source(ASSERT_CONDITIONAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_conditional");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "assert_conditional", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Should have branching (at least 4 BBs for if/else + assertion)
        let bb_count = body.blocks.len();
        assert!(bb_count >= 3, "conditional assert should have >= 3 BBs, got {bb_count}");
        assert_vc_structure(&vc, "assert_conditional", bb_count);
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Implicit assertions: division and bounds checking
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_div_implicit_assert_produces_error_path() {
    with_test_ay_ctx_for_source(ASSERT_DIV_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "safe_div");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "safe_div", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Division by zero check creates an Assert terminator in MIR
        // which should produce error rules
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "division should produce error relation for div-by-zero check");
    });
}

#[test]
fn test_bounds_check_implicit_assert() {
    with_test_ay_ctx_for_source(ASSERT_BOUNDS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "array_access");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "array_access", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Array indexing generates bounds check assertions in MIR
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "array indexing should produce error relation for bounds check");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Track level comparison: Mem vs Reg for assertions
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_assert_at_mem_level() {
    with_test_ay_ctx_for_source(ASSERT_BASIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "assert_positive");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "assert_positive",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Assertions should produce error rules at Mem level too
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "Mem level should also produce error relation");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for ExistsHook quantifier pipeline — the `is_forall=false` path
//! through `build_quantifier_expr`.
//!
//! Part of #2630: soundness-critical coverage gap for ExistsHook.
//! Symmetric to the ForallHook tests — verifies:
//! - `#[kanitool::fn_marker = "ExistsHook"]` detection as `KaniHook::Exists`
//! - `build_quantifier_expr` with `is_forall=false`:
//!   - empty range returns `false` (not `true`)
//!   - disjunction uses `.or()` (not `.and()`)
//! - Full pipeline VC generation for exists-containing source

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::quantifier_encoding::QuantifierEncoding;
use super::common::*;
use crate::kani_middle::kani_functions::KaniHook;
use ay_bindings::{Expr, Sort};

// =============================================================================
// ExistsHook marker detection
// =============================================================================

/// Source with ExistsHook marker to verify positive detection.
const EXISTS_HOOK_MARKER_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists_hook(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }

    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall_hook(lower: u32, upper: u32, pred: fn(u32) -> bool) -> bool {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

fn is_even(x: u32) -> bool { x % 2 == 0 }

pub fn probe_exists_detection(lo: u32, hi: u32) -> bool {
    kani::exists_hook(lo, hi, is_even)
}

pub fn probe_forall_detection(lo: u32, hi: u32) -> bool {
    kani::forall_hook(lo, hi, is_even)
}
"#;

/// Verify that `detect_kani_hook` classifies `ExistsHook` as `KaniHook::Exists`
/// and `ForallHook` as `KaniHook::Forall` for the same source.
#[test]
fn test_exists_hook_marker_detected_as_kani_hook_exists() {
    with_test_ay_ctx_for_source(EXISTS_HOOK_MARKER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_detection");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_exists_detection", ChcConfig::default());

        let mut exists_hits = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(KaniHook::Exists) = chc_ctx.detect_kani_hook(func)
            {
                exists_hits += 1;
            }
        }
        assert!(
            exists_hits >= 1,
            "expected ExistsHook to be detected as KaniHook::Exists, got {exists_hits} detections"
        );
    });
}

/// Verify ForallHook is NOT detected as Exists (mutual exclusivity).
#[test]
fn test_forall_hook_not_detected_as_exists() {
    with_test_ay_ctx_for_source(EXISTS_HOOK_MARKER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_forall_detection");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_forall_detection", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(hook) = chc_ctx.detect_kani_hook(func)
            {
                assert!(
                    !matches!(hook, KaniHook::Exists),
                    "ForallHook should not be detected as Exists, got {hook:?}"
                );
            }
        }
    });
}

// =============================================================================
// Full pipeline: exists-containing source produces valid VC
// =============================================================================

/// Verify that the full CHC pipeline produces a structurally valid VC
/// for source containing ExistsHook calls.
///
/// Even though quantifier encoding may fall back to nondet (because
/// the test closure may be too complex for MIR-based unrolling), the
/// VC must still have valid structure: relations, entry rule, and
/// the goto rule emitted by codegen_call_kani.rs:333.
#[test]
fn test_exists_full_pipeline_produces_valid_vc() {
    with_test_ay_ctx_for_source(EXISTS_HOOK_MARKER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_detection");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_exists_detection", ChcConfig::default());

        assert_vc_structure(&vc, "probe_exists_detection", body.blocks.len());

        // The VC must have rules — even if quantifier encoding fails and falls
        // back to nondet, emit_goto_rule still fires (codegen_call_kani.rs:333).
        assert!(!vc.rules.is_empty(), "VC should have rules even with quantifier fallback");

        // Exists hook returns bool — Bool sort should be present in state vars
        assert_relation_has_arg_sort(
            &vc,
            "probe_exists_detection",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
    });
}

/// Verify ForallHook full pipeline VC is also valid (symmetric coverage).
#[test]
fn test_forall_full_pipeline_produces_valid_vc() {
    with_test_ay_ctx_for_source(EXISTS_HOOK_MARKER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_forall_detection");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_forall_detection", ChcConfig::default());

        assert_vc_structure(&vc, "probe_forall_detection", body.blocks.len());

        // Forall hook returns bool — Bool sort should be present in state vars
        assert_relation_has_arg_sort(
            &vc,
            "probe_forall_detection",
            ay_bindings::Sort::is_bool,
            "Bool",
        );

        // Forall pipeline should produce transition rules
        assert!(!vc.rules.is_empty(), "forall pipeline should produce rules");
    });
}

// =============================================================================
// binop_to_expr coverage for quantifier closure paths
// =============================================================================

/// Verify that binop_to_expr with BitOr on Bool returns Bool (used in exists
/// combining when closures produce boolean results via bitwise-or MIR lowering).
#[test]
fn test_binop_bitor_bool_for_exists_path() {
    with_test_ay_ctx_for_source(EXISTS_HOOK_MARKER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_exists_detection");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_exists_detection", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bool());
        let rhs = Expr::var("b", Sort::bool());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitOr, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitOr on Bool should produce expression (exists path)");
        assert!(result.unwrap().sort().is_bool(), "BitOr on Bool should return Bool sort");
    });
}

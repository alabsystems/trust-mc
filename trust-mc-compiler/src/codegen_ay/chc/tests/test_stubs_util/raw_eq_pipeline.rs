// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! raw_eq pipeline test — mir_to_chc exercises all BBs (#2113).
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// raw_eq pipeline test — mir_to_chc exercises all BBs (#2113)
// =============================================================================

/// Test that raw_eq on [u8; 4] arrays produces a constrained result
/// through the full mir_to_chc pipeline. This validates that the CHC
/// codegen processes ALL basic blocks, including those after intrinsic
/// calls like copy_nonoverlapping.
#[test]
fn test_raw_eq_pipeline_all_bbs_processed() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq_pipeline(a: &[u8; 4], b: &[u8; 4]) -> bool {
            unsafe { core::intrinsics::raw_eq(a, b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_pipeline");
        let body = instance.body().expect("function body");

        // Verify the raw_eq call is detected
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_eq_pipeline", ChcConfig::default());
        let mut has_raw_eq = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_raw_eq_call(func)
            {
                has_raw_eq = true;
            }
        }
        assert!(has_raw_eq, "probe should contain a raw_eq call");

        // Run full pipeline: all BBs should be declared and have rules
        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_pipeline", ChcConfig::default());

        // Every BB should have a declared relation
        let bb_count = body.blocks.len();
        let relation_count = vc.relations.len();
        // Relations = N block relations + 1 error relation
        assert!(
            relation_count >= bb_count,
            "VC should declare at least {} relations (one per BB), got {}",
            bb_count,
            relation_count
        );

        // Rules should connect blocks: at least N-1 transition rules
        // plus the entry rule for bb0
        let rule_count = vc.rules.len();
        assert!(
            rule_count >= bb_count,
            "VC should have at least {} rules (entry + transitions), got {}",
            bb_count,
            rule_count
        );
    });
}

/// Test that copy_nonoverlapping + array equality through mir_to_chc
/// produces VCs with all BBs covered. This matches the harness pattern
/// from copy_dynamic_count.rs::copy_with_zero_count (#2113).
#[test]
fn test_copy_then_raw_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::ptr;

        pub fn probe_copy_then_eq() -> bool {
            let src: [u8; 4] = [1, 2, 3, 4];
            let mut dst: [u8; 4] = [0; 4];
            unsafe {
                ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 0);
            }
            dst == [0, 0, 0, 0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_then_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_then_eq", ChcConfig::default());

        let bb_count = body.blocks.len();
        let relation_count = vc.relations.len();
        let rule_count = vc.rules.len();

        // All BBs should be declared as relations
        assert!(
            relation_count >= bb_count,
            "VC should declare relations for all {} BBs, got {}",
            bb_count,
            relation_count
        );

        // All blocks should have transition rules
        assert!(
            rule_count >= bb_count,
            "VC should generate rules for all {} BBs, got {}",
            bb_count,
            rule_count
        );
    });
}

// PrimitiveClone detection tests for Copy types (u32, bool) were deleted in #2459.
// Reason: Clone::clone on Copy types is always lowered to a bitwise copy assignment
// in MIR, never a Call terminator. These tests were always vacuously passing.
// PrimitiveClone detection for non-Copy types is covered by test_call_primitive_clone.rs.

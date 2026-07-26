// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::decl::codegen_decl_panic_filter::{
    compute_locals_in_normal_blocks, compute_locals_in_relevant_blocks,
    compute_return_reachable_blocks, compute_semantically_relevant_blocks,
};

// declare_block_relations tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify that declare_block_relations creates one relation per basic block.
#[test]
fn test_declare_block_relations_count_matches_blocks() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let block_count = body.blocks.len();
        assert!(block_count > 0, "simple_fn should have at least one basic block");
        assert_eq!(
            chc_ctx.block_relations.len(),
            block_count,
            "should have one relation per basic block"
        );
    });
}

/// Verify that branching functions have more blocks and corresponding relations.
#[test]
fn test_declare_block_relations_branching() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "branching_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "branching_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let block_count = body.blocks.len();
        assert!(
            block_count >= 3,
            "branching_fn should have at least 3 basic blocks (if/else), got {block_count}"
        );
        assert_eq!(chc_ctx.block_relations.len(), block_count);

        // Verify relation names contain the function name
        for rel_name in chc_ctx.block_relations.values() {
            assert!(
                rel_name.contains("branching_fn"),
                "relation name should contain fn name, got: {rel_name}"
            );
        }
    });
}

/// Verify that loop functions have the expected block structure.
#[test]
fn test_declare_block_relations_loop() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "loop_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "loop_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let block_count = body.blocks.len();
        assert!(
            block_count >= 3,
            "loop_fn should have at least 3 basic blocks (entry, loop body, exit), got {block_count}"
        );
        assert_eq!(chc_ctx.block_relations.len(), block_count);
    });
}

#[test]
fn test_semantically_relevant_blocks_keep_cleanup_chain() {
    with_test_ay_ctx_for_source(CLEANUP_ONLY_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cleanup_only_local");
        let body = instance.body().expect("body");

        let return_reachable = compute_return_reachable_blocks(&body);
        let relevant_blocks = compute_semantically_relevant_blocks(&body);

        let (call_bb, cleanup_bb) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, bb)| match &bb.terminator.kind {
                rustc_public::mir::TerminatorKind::Call {
                    target: None,
                    unwind: rustc_public::mir::UnwindAction::Cleanup(cleanup_bb),
                    ..
                } => Some((bb_idx, *cleanup_bb)),
                _ => None,
            })
            .expect("probe_cleanup_only_local should contain a diverging call with cleanup");

        assert!(
            !return_reachable[cleanup_bb],
            "cleanup bb{cleanup_bb} should not be return-reachable in this fixture"
        );
        assert!(
            relevant_blocks[call_bb],
            "diverging call bb{call_bb} should remain semantically relevant"
        );
        assert!(
            relevant_blocks[cleanup_bb],
            "cleanup bb{cleanup_bb} should remain semantically relevant"
        );
    });
}

#[test]
fn test_relevant_locals_include_cleanup_only_local() {
    with_test_ay_ctx_for_source(CLEANUP_ONLY_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cleanup_only_local");
        let body = instance.body().expect("body");

        let return_reachable = compute_return_reachable_blocks(&body);
        let normal_locals = compute_locals_in_normal_blocks(&body, &return_reachable);
        let relevant_locals = compute_locals_in_relevant_blocks(&body);

        let marker_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(idx, decl)| {
                format!("{:?}", decl.ty).contains("CleanupMarker").then_some(idx)
            })
            .expect("fixture should contain a CleanupMarker local");

        assert!(
            !normal_locals.contains(&marker_local),
            "cleanup-only local _{marker_local} should be absent from return-only liveness"
        );
        assert!(
            relevant_locals.contains(&marker_local),
            "cleanup-only local _{marker_local} should be retained by cleanup-aware liveness"
        );
    });
}

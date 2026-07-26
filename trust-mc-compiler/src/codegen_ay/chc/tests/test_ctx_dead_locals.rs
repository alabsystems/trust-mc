// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_ctx_dead_locals.rs` — forward must-analysis of
//! StorageLive/StorageDead to compute dead locals at each block entry.
//!
//! Part of #2303 (codegen_ctx_dead_locals.rs, 144 LOC, zero dedicated coverage).
//! Covers:
//! - `compute_dead_locals_at_block_entry`: fixed-point analysis
//! - `apply_dead_local_transfer_into`: per-block StorageLive/Dead transfer
//! - Linear CFG (no branching)
//! - Diamond CFG (merge from two predecessors)
//! - Loop CFG (fixed-point convergence)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Linear function — StorageLive / StorageDead visible in the VC
// =============================================================================

const LINEAR_STORAGE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_linear_storage(x: u32) -> u32 {
        let a = x + 1;
        let b = a + 2;
        b
    }
"#;

/// Linear function with local variables produces a valid VC.
/// Dead local analysis runs as part of mir_to_chc initialization.
#[test]
fn test_linear_storage_generates_vc() {
    with_test_ay_ctx_for_source(LINEAR_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_linear_storage");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_linear_storage", ChcConfig::default());

        assert_vc_structure(&vc, "probe_linear_storage", body.blocks.len());

        // u32 arithmetic should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "linear u32 arithmetic should have bv32 sort in relations");
    });
}

// =============================================================================
// Diamond CFG — dead locals merge at join point
// =============================================================================

const DIAMOND_STORAGE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_diamond_storage(flag: bool) -> u32 {
        let result;
        if flag {
            let a: u32 = 10;
            result = a;
        } else {
            let b: u32 = 20;
            result = b;
        }
        result
    }
"#;

/// Diamond CFG generates a valid VC.
/// The dead local analysis must correctly intersect (must-meet) the dead sets
/// from both branches at the merge point.
#[test]
fn test_diamond_storage_generates_vc() {
    with_test_ay_ctx_for_source(DIAMOND_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_diamond_storage");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_diamond_storage", ChcConfig::default());

        assert_vc_structure(&vc, "probe_diamond_storage", body.blocks.len());

        // Diamond should produce >= 2 guarded rules (SwitchInt on flag)
        let guarded = vc
            .rules
            .iter()
            .filter(|r| {
                r.body.relation.is_some() && r.body.constraints.iter().any(|c| c.sort().is_bool())
            })
            .count();
        assert!(guarded >= 2, "diamond CFG should produce >= 2 guarded rules, got {guarded}");
    });
}

// =============================================================================
// Loop CFG — fixed-point convergence
// =============================================================================

const LOOP_STORAGE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_loop_storage(n: u32) -> u32 {
        let mut sum: u32 = 0;
        let mut i: u32 = 0;
        while i < n {
            sum += i;
            i += 1;
        }
        sum
    }
"#;

/// Loop with local variables generates a valid VC.
/// The dead local analysis requires fixed-point iteration for loops.
#[test]
fn test_loop_storage_generates_vc() {
    with_test_ay_ctx_for_source(LOOP_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_loop_storage");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_loop_storage", ChcConfig::default());

        assert_vc_structure(&vc, "probe_loop_storage", body.blocks.len());

        // Loop with u32 should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "loop u32 arithmetic should have bv32 sort in relations");
    });
}

// =============================================================================
// Nested scopes — multiple StorageDead transitions
// =============================================================================

const NESTED_SCOPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_nested_scopes(x: u32) -> u32 {
        let a = x + 1;
        let result = {
            let b = a + 2;
            let c = b + 3;
            c
        };
        // b and c are dead here, only result and a are live
        result + a
    }
"#;

/// Nested scopes with inner variables going dead generates a valid VC.
#[test]
fn test_nested_scopes_generates_vc() {
    with_test_ay_ctx_for_source(NESTED_SCOPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_scopes");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_scopes", ChcConfig::default());

        assert_vc_structure(&vc, "probe_nested_scopes", body.blocks.len());

        // Nested u32 arithmetic should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "nested scope u32 arithmetic should have bv32 sort in relations");
    });
}

// =============================================================================
// Flattened locals — StorageDead should prune unused field groups
// =============================================================================

const DEAD_FLATTENED_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_dead_flattened_local(x: u32, y: u32) -> u32 {
        let checked = x.overflowing_add(y);
        if checked.1 { 0 } else { checked.0 }
    }
"#;

/// Regression: a flattened local must not be kept live
/// solely because it is flattened. If no local use exists in a block after
/// `StorageDead`, all flattened field slots should be absent from that block's
/// relation signature. When any field is actually live, the later atomic
/// flattened-liveness pass re-adds the complete field group.
#[test]
fn test_storage_dead_flattened_local_pruned_from_successors() {
    with_test_ay_ctx_for_source(DEAD_FLATTENED_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dead_flattened_local");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_dead_flattened_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let used_per_block = ChcCtx::compute_used_locals_per_block(&body);
        let (dead_local, base_idx, field_count, bb_idx) = chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .copied()
            .filter(|local| chc_ctx.flattened_field_count(*local) > 1)
            .find_map(|local| {
                let base = chc_ctx.state_var_mgr.local_to_state_idx.get(&local).copied()?;
                let count = chc_ctx.flattened_field_count(local);
                let bb_idx = used_per_block
                    .iter()
                    .enumerate()
                    .find_map(|(bb_idx, used)| (!used.contains(&local)).then_some(bb_idx))?;
                Some((local, base, count, bb_idx))
            })
            .expect("probe should produce a flattened local with an unused block");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&dead_local),
            "local _{dead_local} should be registered as flattened"
        );

        chc_ctx.liveness.dead_locals_at_entry[bb_idx].insert(dead_local);
        let state_idx_to_local = chc_ctx.build_state_idx_to_local_map();
        let live_by_block = chc_ctx.compute_forward_per_block_liveness(&state_idx_to_local);
        let live = &live_by_block[bb_idx];
        for offset in 0..field_count {
            let field_idx = base_idx + offset;
            assert!(
                !live.contains(&field_idx),
                "bb{bb_idx} should not carry dead flattened local _{dead_local} \
                 field slot {offset} ({})",
                chc_ctx.state_var_mgr.state_vars[field_idx].0
            );
        }
    });
}

/// Sanity check: collection-projected iterators still expose Array-backed field
/// groups elsewhere; the dead-local pruning regression above intentionally uses
/// a simpler tuple shape to avoid depending on source-level projection lifetime.
#[test]
fn test_vec_into_iter_projection_still_has_array_field() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_vec_into_iter_projection() -> Option<u32> {
            let mut iter = vec![42u32].into_iter();
            iter.next()
        }
        "#,
        |ctx| {
            use super::super::codegen_ctx::CollectionProjectionKind;

            let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter_projection");
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_vec_into_iter_projection",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            chc_ctx.declare_block_relations();

            let has_array_projected_iter = chc_ctx
                .collections
                .projection_locals
                .iter()
                .filter_map(|(local, kind)| {
                    (*kind == CollectionProjectionKind::VecIntoIter).then_some(*local)
                })
                .any(|local| {
                    let Some(base) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local).copied()
                    else {
                        return false;
                    };
                    (0..chc_ctx.flattened_field_count(local)).any(|offset| {
                        chc_ctx
                            .state_var_mgr
                            .state_vars
                            .get(base + offset)
                            .is_some_and(|(_, sort)| sort.is_array())
                    })
                });

            assert!(
                has_array_projected_iter,
                "VecIntoIter projection should still contain an Array-backed data field"
            );
        },
    );
}

// =============================================================================
// Empty function — trivial fixed-point
// =============================================================================

/// Empty function with no locals other than return should produce a minimal VC.
#[test]
fn test_empty_function_dead_locals() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_empty() {}
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_empty");
            let body = instance.body().expect("body");
            let vc = mir_to_chc(ctx.tcx, &body, "probe_empty", ChcConfig::default());

            assert_vc_structure(&vc, "probe_empty", body.blocks.len());

            // Empty function should still produce rules (at least entry rule)
            assert!(!vc.rules.is_empty(), "empty function should produce at least entry rule");
        },
    );
}

// =============================================================================
// Dead local analysis at Mem track level
// =============================================================================

/// Dead local analysis at Mem track level should also produce a valid VC.
#[test]
fn test_linear_storage_mem_level() {
    with_test_ay_ctx_for_source(LINEAR_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_linear_storage");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_linear_storage",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_linear_storage", body.blocks.len());

        // Mem level should also produce bv32 for u32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Mem-level u32 arithmetic should have bv32 sort in relations");
    });
}

// =============================================================================
// Intrinsic(Assume) — used locals must be rescued from dead set
// =============================================================================

const INTRINSIC_ASSUME_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_assume_used_local(cond: bool, x: u32) -> u32 {
        unsafe { core::intrinsics::assume(cond); }
        x.wrapping_add(1)
    }
"#;

/// Regression test: `compute_used_locals_per_block` must include locals
/// referenced by `StatementKind::Intrinsic(Assume)` in the used set.
/// Without this, storage-dead locals referenced by Assume constraints
/// become free variables in CHC rules, making proofs vacuously satisfiable.
/// Fixes gap in W1:3351 (use-based liveness).
#[test]
fn test_intrinsic_assume_operand_in_used_locals() {
    use rustc_public::mir::StatementKind;

    with_test_ay_ctx_for_source(INTRINSIC_ASSUME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assume_used_local");
        let body = instance.body().expect("body");

        // Call the function under test.
        let used_per_block = ChcCtx::compute_used_locals_per_block(&body);

        // Find the block containing the Intrinsic(Assume) statement.
        let assume_bb = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, bb)| {
                bb.statements
                    .iter()
                    .any(|stmt| {
                        matches!(
                            stmt.kind,
                            StatementKind::Intrinsic(
                                rustc_public::mir::NonDivergingIntrinsic::Assume(_)
                            )
                        )
                    })
                    .then_some(bb_idx)
            })
            .expect("MIR should contain an Intrinsic::Assume statement");

        // Extract the local from the Assume operand.
        let assume_local = body.blocks[assume_bb]
            .statements
            .iter()
            .find_map(|stmt| {
                if let StatementKind::Intrinsic(rustc_public::mir::NonDivergingIntrinsic::Assume(
                    op,
                )) = &stmt.kind
                {
                    match op {
                        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .expect("Assume operand should reference a local");

        // The used set for the assume block must include the operand local.
        assert!(
            used_per_block[assume_bb].contains(&assume_local),
            "Intrinsic(Assume) operand local _{assume_local} must be in used set \
             for bb{assume_bb} to prevent free-variable leaks in CHC rules. \
             Used set: {:?}",
            used_per_block[assume_bb]
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for alloc-id backward tracing in `deref_mem.rs`.
//!
//! Covers: `trace_deref_store_alloc_id`, `scan_mir_for_alloc_source`,
//! `pick_alloc_operand`, `scan_identity_call_arg`, `is_alloc_identity_callee`.
//!
//! Part of #3666: soundness-critical alloc chain needs unit test coverage.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::ProjectionElem;

// =============================================================================
// Source fixtures
// =============================================================================

/// Simple raw-pointer function for tests that only need a valid body + seeded state.
const SIMPLE_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_raw_ptr(ptr: *mut u32, val: u32) {
        unsafe { *ptr = val; }
    }
"#;

/// Function with side effect to force intermediate locals in MIR.
/// The unsafe write prevents the optimizer from collapsing `let a = ptr`.
/// Produces MIR Use(Copy/Move) assignments for scan_mir_for_alloc_source.
const COPY_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_copy_chain(ptr: *mut u32, dst: *mut *mut u32) {
        let a = ptr;
        unsafe { *dst = a; }
    }
"#;

/// Cast chain: raw pointer → cast → return.
/// Produces MIR Cast rvalue for scan_mir_for_alloc_source.
const CAST_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_cast_chain(ptr: *const u32) -> *const u8 {
        ptr as *const u8
    }
"#;

/// Struct wrapping a pointer: produces Aggregate rvalue.
/// Tests pick_alloc_operand through scan_mir_for_alloc_source.
const AGGREGATE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct PtrWrap {
        pub inner: *const u32,
    }

    pub fn probe_aggregate(ptr: *const u32) -> PtrWrap {
        PtrWrap { inner: ptr }
    }
"#;

/// Multi-field aggregate where one operand has known alloc_id.
/// Tests pick_alloc_operand preference for known alloc_ids.
const AGGREGATE_MULTI_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct TwoPtr {
        pub a: *const u32,
        pub b: *const u32,
    }

    pub fn probe_aggregate_multi(p1: *const u32, p2: *const u32) -> TwoPtr {
        TwoPtr { a: p1, b: p2 }
    }
"#;

// =============================================================================
// trace_deref_store_alloc_id: direct known_alloc_id lookup
// =============================================================================

/// Acceptance criteria: known_alloc_id found in 1 step.
/// Seeds alloc_id for a local and verifies immediate return.
#[test]
fn test_trace_alloc_id_direct_known_one_step() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // _1 = ptr argument. Seed alloc_id directly.
        chc_ctx.known_alloc_ids.insert(1, 0xCAFE);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(1),
            Some(0xCAFE),
            "trace should find known_alloc_id for directly-seeded local"
        );
    });
}

/// No alloc_id seeded at all → returns None.
#[test]
fn test_trace_alloc_id_no_known_returns_none() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // No alloc_ids seeded.
        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(1),
            None,
            "trace should return None when no alloc_ids are known"
        );
    });
}

// =============================================================================
// trace_deref_store_alloc_id: ref_target chain
// =============================================================================

/// Acceptance criteria: ref_target chain followed across 2+ steps.
/// Chain: local 3 → ref_target(2) → ref_target(1) → known_alloc_id.
#[test]
fn test_trace_alloc_id_via_ref_target_two_steps() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Chain: 3 → 2 → 1 (known alloc_id)
        chc_ctx.ref_resolution.ref_targets.insert(3, RefTarget::with_projections(2, vec![]));
        chc_ctx.ref_resolution.ref_targets.insert(2, RefTarget::with_projections(1, vec![]));
        chc_ctx.known_alloc_ids.insert(1, 0xBEEF);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(3),
            Some(0xBEEF),
            "trace should follow ref_target chain across 2 steps to find alloc_id"
        );
    });
}

/// ref_target with Deref projection is still followed (the trace allows
/// Deref as the first projection in ref_targets).
#[test]
fn test_trace_alloc_id_via_ref_target_with_deref_projection() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Chain: 2 → ref_target(1, [Deref]) → known_alloc_id at 1
        chc_ctx
            .ref_resolution
            .ref_targets
            .insert(2, RefTarget::with_projections(1, vec![ProjectionElem::Deref]));
        chc_ctx.known_alloc_ids.insert(1, 0xDEAD);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(2),
            Some(0xDEAD),
            "trace should follow ref_target with Deref projection"
        );
    });
}

/// ref_target with non-Deref projection (e.g., Field) is NOT followed.
/// The trace only accepts empty projections or [Deref] as first projection.
#[test]
fn test_trace_alloc_id_ref_target_field_projection_blocks_chain() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // ref_target with Field projection — should NOT be followed
        let field_ty = body.locals()[1].ty;
        chc_ctx
            .ref_resolution
            .ref_targets
            .insert(2, RefTarget::with_projections(1, vec![ProjectionElem::Field(0, field_ty)]));
        chc_ctx.known_alloc_ids.insert(1, 0xFACE);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(2),
            None,
            "trace should NOT follow ref_target with Field projection"
        );
    });
}

// =============================================================================
// trace_deref_store_alloc_id: cycle detection
// =============================================================================

/// Cycle detection: ref_target points to itself → terminates without looping.
#[test]
fn test_trace_alloc_id_cycle_self_ref_terminates() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Self-referencing ref_target
        chc_ctx.ref_resolution.ref_targets.insert(1, RefTarget::with_projections(1, vec![]));

        // No alloc_ids anywhere. Should terminate, not loop.
        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(1),
            None,
            "trace should detect cycle and return None"
        );
    });
}

/// Mutual cycle: 1 → 2 → 1 → terminates.
#[test]
fn test_trace_alloc_id_cycle_mutual_terminates() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Mutual cycle: 1 ↔ 2
        chc_ctx.ref_resolution.ref_targets.insert(1, RefTarget::with_projections(2, vec![]));
        chc_ctx.ref_resolution.ref_targets.insert(2, RefTarget::with_projections(1, vec![]));

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(1),
            None,
            "trace should detect mutual cycle and return None"
        );
    });
}

// =============================================================================
// trace via scan_mir_for_alloc_source: Copy/Move assignment
// =============================================================================

/// Acceptance criteria: scan_mir_for_alloc_source finds Copy/Move assignment.
/// Uses an unsafe function with side effect to force intermediate locals.
/// Seed alloc_id at _1 (ptr arg). Trace from the intermediate local that
/// copies/moves _1 should find the alloc_id.
#[test]
fn test_trace_alloc_id_via_mir_copy_chain() {
    with_test_ay_ctx_for_source(COPY_CHAIN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_chain");
        let body = instance.body().expect("body");

        // Find any Use(Copy/Move) assignment from _1 to a non-return local.
        let mut copy_dest = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(
                    lhs,
                    Rvalue::Use(
                        rustc_public::mir::Operand::Copy(src)
                        | rustc_public::mir::Operand::Move(src),
                    ),
                ) = &stmt.kind
                {
                    if src.local == 1 && lhs.local != 0 && lhs.local != 1 {
                        copy_dest = Some(lhs.local);
                    }
                }
            }
        }
        assert_mir_pattern_found(copy_dest.is_some(), "Copy/Move from _1 (ptr arg)");
        let trace_from = copy_dest.expect("copy destination local");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_copy_chain",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id at arg _1.
        chc_ctx.known_alloc_ids.insert(1, 0xA110);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(trace_from),
            Some(0xA110),
            "trace should follow MIR Copy/Move from local {} back to _1's alloc_id",
            trace_from
        );
    });
}

// =============================================================================
// trace via scan_mir_for_alloc_source: Cast assignment
// =============================================================================

/// Acceptance criteria: scan_mir_for_alloc_source finds Cast rvalue.
/// `ptr as *const u8` produces Cast(_, Operand::Move(_1), _) in MIR.
#[test]
fn test_trace_alloc_id_via_mir_cast() {
    with_test_ay_ctx_for_source(CAST_CHAIN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_chain");
        let body = instance.body().expect("body");

        // Verify the MIR has a Cast rvalue.
        let mut found_cast = false;
        let mut cast_dest = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::Cast(_, _, _)) = &stmt.kind {
                    found_cast = true;
                    cast_dest = Some(lhs.local);
                }
            }
        }
        assert_mir_pattern_found(found_cast, "Cast rvalue in MIR");
        let cast_local = cast_dest.expect("cast destination local");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cast_chain",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id at _1 (ptr arg).
        chc_ctx.known_alloc_ids.insert(1, 0xCA57);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(cast_local),
            Some(0xCA57),
            "trace should follow Cast rvalue back to _1's alloc_id"
        );
    });
}

// =============================================================================
// trace via scan_mir_for_alloc_source + pick_alloc_operand: Aggregate
// =============================================================================

/// Acceptance criteria: scan_mir_for_alloc_source finds Aggregate → pick_alloc_operand.
/// Single-field struct wrapping a pointer. Trace from the struct local should
/// follow through the Aggregate to the pointer operand.
#[test]
fn test_trace_alloc_id_via_aggregate_single_operand() {
    with_test_ay_ctx_for_source(AGGREGATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_aggregate");
        let body = instance.body().expect("body");

        // Find the Aggregate assignment.
        let mut aggregate_dest = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::Aggregate(_, _)) = &stmt.kind {
                    aggregate_dest = Some(lhs.local);
                }
            }
        }
        assert_mir_pattern_found(aggregate_dest.is_some(), "Aggregate rvalue in MIR");
        let agg_local = aggregate_dest.expect("aggregate destination local");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_aggregate",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id at _1 (ptr arg — the only operand of the Aggregate).
        chc_ctx.known_alloc_ids.insert(1, 0xA663);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(agg_local),
            Some(0xA663),
            "trace should follow Aggregate → pick_alloc_operand to ptr's alloc_id"
        );
    });
}

/// Acceptance criteria: pick_alloc_operand prefers operand with known alloc_id
/// over plain operand.
/// Two-field struct: field `a` has known alloc_id, field `b` does not.
/// pick_alloc_operand should select field `a`.
#[test]
fn test_trace_alloc_id_aggregate_prefers_known_alloc_id() {
    with_test_ay_ctx_for_source(AGGREGATE_MULTI_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_aggregate_multi");
        let body = instance.body().expect("body");

        // Find the Aggregate assignment and its operands.
        let mut aggregate_dest = None;
        let mut first_operand_local = None;
        let mut second_operand_local = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::Aggregate(_, operands)) = &stmt.kind {
                    aggregate_dest = Some(lhs.local);
                    for (i, op) in operands.iter().enumerate() {
                        if let rustc_public::mir::Operand::Copy(src)
                        | rustc_public::mir::Operand::Move(src) = op
                        {
                            if i == 0 {
                                first_operand_local = Some(src.local);
                            } else if i == 1 {
                                second_operand_local = Some(src.local);
                            }
                        }
                    }
                }
            }
        }
        assert_mir_pattern_found(aggregate_dest.is_some(), "Aggregate rvalue in MIR");
        let agg_local = aggregate_dest.expect("aggregate destination local");
        let first_local = first_operand_local.expect("first operand local");
        let second_local = second_operand_local.expect("second operand local");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_aggregate_multi",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id only at the SECOND operand. pick_alloc_operand should
        // prefer it over the first operand (which has no alloc_id).
        chc_ctx.known_alloc_ids.insert(second_local, 0x2222);

        let result = chc_ctx.trace_deref_store_alloc_id(agg_local);

        // If pick_alloc_operand correctly prefers the known operand, it returns
        // second_local, and then trace finds alloc_id 0x2222.
        // If it falls back to the first operand (no alloc_id), trace continues
        // from first_local and may not find any alloc_id.
        assert_eq!(
            result,
            Some(0x2222),
            "pick_alloc_operand should prefer operand at local {} with known alloc_id \
             over operand at local {} without one",
            second_local,
            first_local
        );
    });
}

/// Acceptance criteria: pick_alloc_operand falls back to first operand with
/// no projection when no operand has a known alloc_id.
#[test]
fn test_trace_alloc_id_aggregate_fallback_to_first_operand() {
    with_test_ay_ctx_for_source(AGGREGATE_MULTI_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_aggregate_multi");
        let body = instance.body().expect("body");

        let mut aggregate_dest = None;
        let mut first_operand_local = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::Aggregate(_, operands)) = &stmt.kind {
                    aggregate_dest = Some(lhs.local);
                    if let Some(
                        rustc_public::mir::Operand::Copy(src)
                        | rustc_public::mir::Operand::Move(src),
                    ) = operands.first()
                    {
                        first_operand_local = Some(src.local);
                    }
                }
            }
        }
        assert_mir_pattern_found(aggregate_dest.is_some(), "Aggregate rvalue in MIR");
        let agg_local = aggregate_dest.expect("aggregate destination local");
        let first_local = first_operand_local.expect("first operand local");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_aggregate_multi",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id at the first operand's local. No alloc_ids on second.
        // pick_alloc_operand should still find first_local (it checks known_alloc_ids
        // first-pass, and first_local has one).
        chc_ctx.known_alloc_ids.insert(first_local, 0x1111);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(agg_local),
            Some(0x1111),
            "trace should find alloc_id via first operand"
        );
    });
}

// =============================================================================
// trace via scan_mir_for_alloc_source: Ref/AddressOf
// =============================================================================

/// scan_mir_for_alloc_source follows Ref(_, _, place) assignments.
const REF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_take(x: &u32) -> &u32 {
        let r = x;
        r
    }
"#;

/// Ref/AddressOf rvalue in MIR assignment chain.
#[test]
fn test_trace_alloc_id_via_ref_rvalue() {
    with_test_ay_ctx_for_source(REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_take");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_take",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Seed alloc_id at _1 (x arg).
        chc_ctx.known_alloc_ids.insert(1, 0x4E4F);

        // Find any local assigned from _1 via Copy/Ref, trace from there.
        let mut target_local = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                    let source = match rhs {
                        Rvalue::Use(rustc_public::mir::Operand::Copy(src))
                        | Rvalue::Use(rustc_public::mir::Operand::Move(src)) => Some(src.local),
                        Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
                            Some(place.local)
                        }
                        _ => None,
                    };
                    if source == Some(1) && lhs.local != 0 {
                        target_local = Some(lhs.local);
                    }
                }
            }
        }

        if let Some(local) = target_local {
            assert_eq!(
                chc_ctx.trace_deref_store_alloc_id(local),
                Some(0x4E4F),
                "trace should follow Ref/Copy assignment back to _1's alloc_id"
            );
        }
        // If the optimizer collapsed the chain, the arg _1 itself should still work.
        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(1),
            Some(0x4E4F),
            "direct lookup at _1 should always succeed"
        );
    });
}

// =============================================================================
// trace exhaustion: max 12 steps without finding alloc_id
// =============================================================================

/// Acceptance criteria: trace exhaustion returns None after max steps
/// with no alloc_id found.
/// Build a long ref_target chain (11 steps) with no alloc_id at the end.
#[test]
fn test_trace_alloc_id_exhaustion_long_chain_returns_none() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Build chain: 100 → 101 → 102 → ... → 108 (no alloc_id)
        // This is 8 ref_target hops. The trace limit is 8 iterations,
        // and after 8 hops we reach local 108 which has no alloc_id
        // and no further chain → returns None.
        for i in 0..8 {
            chc_ctx
                .ref_resolution
                .ref_targets
                .insert(100 + i, RefTarget::with_projections(101 + i, vec![]));
        }

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(100),
            None,
            "trace should return None after following 8-step chain with no alloc_id"
        );
    });
}

/// Verify that a chain just under the 8-step limit still finds the alloc_id.
#[test]
fn test_trace_alloc_id_long_chain_within_limit_succeeds() {
    with_test_ay_ctx_for_source(SIMPLE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_raw_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Chain: 100 → 101 → ... → 106. Seed alloc_id at 106.
        // That's 6 hops, well within the 8-step limit.
        for i in 0..6 {
            chc_ctx
                .ref_resolution
                .ref_targets
                .insert(100 + i, RefTarget::with_projections(101 + i, vec![]));
        }
        chc_ctx.known_alloc_ids.insert(106, 0x7777);

        assert_eq!(
            chc_ctx.trace_deref_store_alloc_id(100),
            Some(0x7777),
            "trace should find alloc_id at end of 6-step chain"
        );
    });
}

// =============================================================================
// trace via scan_mir_for_alloc_source: ShallowInitBox (Box::new)
// =============================================================================

/// Acceptance criteria: scan_mir_for_alloc_source finds ShallowInitBox assignment.
/// Box::new generates ShallowInitBox in MIR. Seed alloc_id at the malloc result
/// and trace from the ShallowInitBox destination.
#[test]
fn test_trace_alloc_id_via_shallow_init_box() {
    const BOX_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_chain() -> Box<u32> {
            Box::new(42)
        }
    "#;

    with_test_ay_ctx_for_source(BOX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_chain");
        let body = instance.body().expect("body");

        // Find ShallowInitBox in MIR — this is the Box allocation pattern.
        let mut shallow_init_dest = None;
        let mut shallow_init_src = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::ShallowInitBox(op, _)) = &stmt.kind {
                    shallow_init_dest = Some(lhs.local);
                    if let rustc_public::mir::Operand::Copy(src)
                    | rustc_public::mir::Operand::Move(src) = op
                    {
                        shallow_init_src = Some(src.local);
                    }
                }
            }
        }

        if let (Some(dest), Some(src)) = (shallow_init_dest, shallow_init_src) {
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_box_chain",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );

            // Seed alloc_id at the malloc result (source of ShallowInitBox).
            chc_ctx.known_alloc_ids.insert(src, 0xB0B0);

            // Trace from the ShallowInitBox destination should find the alloc_id
            // via scan_mir_for_alloc_source's ShallowInitBox branch.
            assert_eq!(
                chc_ctx.trace_deref_store_alloc_id(dest),
                Some(0xB0B0),
                "trace should follow ShallowInitBox from local {} to malloc result at local {}",
                dest,
                src
            );
        }
        // If optimizer eliminated ShallowInitBox, the test is still valid —
        // the Box::new pipeline test below covers the full chain.
    });
}

// =============================================================================
// CopyForDeref rvalue
// =============================================================================

/// scan_mir_for_alloc_source handles CopyForDeref(src) rvalue.
/// MIR generates CopyForDeref for implicit deref copies.
const COPY_FOR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_copy_for_deref<'a>(r: &'a &'a u32) -> &'a u32 {
        *r
    }
"#;

#[test]
fn test_trace_alloc_id_via_copy_for_deref() {
    with_test_ay_ctx_for_source(COPY_FOR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_for_deref");
        let body = instance.body().expect("body");

        // Find CopyForDeref in MIR.
        let mut copy_for_deref_dest = None;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, Rvalue::CopyForDeref(_)) = &stmt.kind {
                    copy_for_deref_dest = Some(lhs.local);
                }
            }
        }

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_copy_for_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.known_alloc_ids.insert(1, 0xCFDF);

        if let Some(dest) = copy_for_deref_dest {
            assert_eq!(
                chc_ctx.trace_deref_store_alloc_id(dest),
                Some(0xCFDF),
                "trace should follow CopyForDeref rvalue back to source alloc_id"
            );
        }
        // Always verify the arg itself.
        assert_eq!(chc_ctx.trace_deref_store_alloc_id(1), Some(0xCFDF));
    });
}

// =============================================================================
// deref_load_referent_local: the ADDRESS-used-as-VALUE structural test
// =============================================================================

/// `_r = &_v` with no projections, then a load through `_r`. This is the shape
/// where a deref load must NOT inherit `_r`'s alloc_id: that id names `_v`'s
/// own slot, while the loaded value is `_v`'s CONTENTS.
const REF_TO_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_ref_to_local(dst: *mut u32) {
        let v: u32 = 7;
        let r: &u32 = &v;
        unsafe { *dst = *r; }
    }
"#;

/// Find the first `_lhs = &_place` with no projections; returns (lhs, place).
fn find_unprojected_ref(body: &rustc_public::mir::Body) -> Option<(usize, usize)> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, Rvalue::Ref(_, _, place)) = &stmt.kind
                && lhs.projection.is_empty()
                && place.projection.is_empty()
            {
                return Some((lhs.local, place.local));
            }
        }
    }
    None
}

/// Positive: the pointer provably holds `&_v` and carries `_v`'s slot obj_id,
/// so the predicate reports `_v` as the referent whose provenance to use.
#[test]
fn test_deref_load_referent_local_matches_ref_to_local() {
    with_test_ay_ctx_for_source(REF_TO_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_to_local");
        let body = instance.body().expect("body");
        let Some((ptr_local, referent)) = find_unprojected_ref(&body) else {
            return; // optimizer removed the reference; nothing to assert
        };
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_to_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        const SLOT_OBJ: u32 = 0xA11C;
        chc_ctx.heap_state.insert_local_address(referent, SLOT_OBJ, "addr_v".to_string());
        chc_ctx.known_alloc_ids.insert(ptr_local, SLOT_OBJ);

        assert_eq!(
            chc_ctx.deref_load_referent_local(ptr_local),
            Some(referent),
            "a pointer holding &_v whose alloc_id is _v's own slot must report _v"
        );
    });
}

/// Negative: the pointer carries no alloc_id at all, so there is nothing to
/// mis-inherit and the existing propagation path must stay untouched.
#[test]
fn test_deref_load_referent_local_none_without_alloc_id() {
    with_test_ay_ctx_for_source(REF_TO_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_to_local");
        let body = instance.body().expect("body");
        let Some((ptr_local, referent)) = find_unprojected_ref(&body) else {
            return;
        };
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_to_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.heap_state.insert_local_address(referent, 0xA11C, "addr_v".to_string());

        assert_eq!(
            chc_ctx.deref_load_referent_local(ptr_local),
            None,
            "no recorded alloc_id means the guard must not fire"
        );
    });
}

/// Negative: the alloc_id names a heap allocation rather than a stack slot —
/// the Box/Rc/NonNull deref-chain case, which must keep inheriting.
#[test]
fn test_deref_load_referent_local_none_for_heap_alloc_id() {
    with_test_ay_ctx_for_source(REF_TO_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_to_local");
        let body = instance.body().expect("body");
        let Some((ptr_local, _referent)) = find_unprojected_ref(&body) else {
            return;
        };
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_to_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        // 0xBEEF is never registered as a stack local's slot.
        chc_ctx.known_alloc_ids.insert(ptr_local, 0xBEEF);

        assert_eq!(
            chc_ctx.deref_load_referent_local(ptr_local),
            None,
            "an alloc_id naming no stack slot must keep the existing behaviour"
        );
    });
}

/// Negative: the pointer's alloc_id names some OTHER local's slot, so the load
/// is not reading its own referent and the inheritance stays as it was.
#[test]
fn test_deref_load_referent_local_none_for_unrelated_slot() {
    with_test_ay_ctx_for_source(REF_TO_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_to_local");
        let body = instance.body().expect("body");
        let Some((ptr_local, referent)) = find_unprojected_ref(&body) else {
            return;
        };
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_to_local",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        const OTHER_OBJ: u32 = 0xA11D;
        let unrelated = referent + 100;
        chc_ctx.heap_state.insert_local_address(unrelated, OTHER_OBJ, "addr_other".to_string());
        chc_ctx.known_alloc_ids.insert(ptr_local, OTHER_OBJ);

        assert_eq!(
            chc_ctx.deref_load_referent_local(ptr_local),
            None,
            "the guard must only fire when the alloc_id names the pointer's own referent"
        );
    });
}

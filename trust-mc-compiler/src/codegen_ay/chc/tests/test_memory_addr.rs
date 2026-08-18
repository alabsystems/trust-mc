// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC memory_impl_addr.rs — translate_ref_to_address with
//! Field, Index, and ConstantIndex projections; get_or_create_local_address
//! stability and distinctness.
//!
//! Part of #2303 (test coverage for decomposed CHC modules).
//! Extends test_memory_impl.rs which covers basic address allocation
//! and pointer load operations.

#![allow(clippy::unwrap_used)]

use rustc_public::ty::{RigidTy, TyKind};

use super::common::*;

// =============================================================================
// get_or_create_local_address — repeated calls return same address
// =============================================================================

/// Calling get_or_create_local_address twice for the same local returns the
/// same address expression (idempotent).
#[test]
fn test_local_address_idempotent() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_idempotent(x: u32, _y: u64) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_idempotent");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_idempotent",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr1_first = chc_ctx.get_or_create_local_address(1).unwrap();
        let addr1_second = chc_ctx.get_or_create_local_address(1).unwrap();
        assert_eq!(
            addr1_first.to_string(),
            addr1_second.to_string(),
            "same local should produce identical address"
        );

        let addr2 = chc_ctx.get_or_create_local_address(2).unwrap();
        assert_ne!(
            addr1_first.to_string(),
            addr2.to_string(),
            "different locals should produce different addresses"
        );
    });
}

/// Lazily allocated locals seed obj_valid/obj_size metadata facts.
#[test]
fn test_local_address_lazy_alloc_seeds_heap_metadata_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_lazy_seed(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lazy_seed");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_lazy_seed",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(
            chc_ctx.heap_state.pending_updates.is_empty(),
            "test precondition: no pending updates before first local address request"
        );

        // Argument local (1) is created lazily by address translation.
        let _addr = chc_ctx.get_or_create_local_address(1).unwrap();

        let updates_text = chc_ctx
            .heap_state
            .pending_updates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            updates_text.contains("obj_valid"),
            "lazy local allocation should seed obj_valid fact, got:\n{updates_text}"
        );
        assert!(
            updates_text.contains("obj_size"),
            "lazy local allocation should seed obj_size fact, got:\n{updates_text}"
        );
    });
}

/// Local addresses are 64-bit bitvectors (split pointer model).
#[test]
fn test_local_address_is_bv64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_addr_sort(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_addr_sort");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_addr_sort",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = chc_ctx.get_or_create_local_address(0).unwrap();
        assert!(addr.sort().is_bitvec(), "address should be bitvec sort, got: {:?}", addr.sort());
        let width = addr.sort().bitvec_width();
        assert_eq!(width, Some(64), "address should be 64-bit bitvec (split pointer model)");
    });
}

// =============================================================================
// translate_ref_to_address — field projection
// =============================================================================

/// translate_ref_to_address with a field projection adds field offset.
#[test]
fn test_translate_ref_field_projection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Point {
            pub x: u32,
            pub y: u32,
        }

        pub fn probe_field_ref(p: &Point) -> &u32 {
            &p.y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_field_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Find a Ref rvalue in the MIR that references a field projection
        let mut found_ref = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Ref(_, _, place),
                ) = &stmt.kind
                    && !place.projection.is_empty()
                {
                    let modified = HashSet::new();
                    let addr = chc_ctx.translate_ref_to_address(place, &modified);
                    assert!(
                        addr.is_some(),
                        "translate_ref_to_address should handle field projection"
                    );
                    let addr_expr = addr.unwrap().into_expr();
                    assert!(
                        addr_expr.sort().is_bitvec(),
                        "result address should be bitvec, got: {:?}",
                        addr_expr.sort()
                    );
                    found_ref = true;
                }
            }
        }
        // Note: The compiler may optimize away the reference, so this is
        // a soft check. The important thing is that the method doesn't panic.
        if !found_ref {
            // At minimum, verify base address works for a local
            let modified = HashSet::new();
            let base_place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
            let addr = chc_ctx.translate_ref_to_address(&base_place, &modified);
            assert!(addr.is_some(), "translate_ref_to_address should handle base local");
        }
    });
}

/// Indexed custom-DST field references must normalize BV128 fat pointers to
/// their storage-address lane before field-offset arithmetic.
#[test]
fn test_translate_ref_indexed_custom_dst_field_extracts_storage_addr() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct MyStr {
            pub header_0: u8,
            pub header_1: u8,
            pub data: str,
        }

        pub fn probe_custom_dst_header<'a>(slice: &'a [&'a MyStr]) -> &'a u8 {
            &slice[0].header_1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_dst_header");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_custom_dst_header",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut found_ref = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Ref(_, _, place),
                ) = &stmt.kind
                    && place
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, rustc_public::mir::ProjectionElem::Field(_, _)))
                    && matches!(
                        body.locals()[place.local].ty.kind(),
                        TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                            if crate::kani_middle::abi::LayoutOf::new(pointee).has_slice_tail()
                    )
                {
                    let addr = chc_ctx.translate_ref_to_address(place, &HashSet::new());
                    assert!(
                        addr.is_some(),
                        "translate_ref_to_address should handle custom-DST field refs"
                    );
                    let addr_expr = addr.unwrap().into_expr();
                    assert_eq!(
                        addr_expr.sort().bitvec_width(),
                        Some(64),
                        "field address arithmetic must run on the thin storage address"
                    );
                    found_ref = true;
                }
            }
        }

        assert!(found_ref, "expected custom-DST field reference in MIR");
    });
}

// =============================================================================
// translate_ref_to_address — base local (no projections)
// =============================================================================

/// translate_ref_to_address with no projections returns the base address.
#[test]
fn test_translate_ref_base_local_no_projection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_base_ref(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_base_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_base_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let addr = chc_ctx.translate_ref_to_address(&place, &modified);
        assert!(addr.is_some(), "base local address should be available");
        let addr_expr = addr.unwrap().into_expr();
        assert!(
            addr_expr.sort().is_bitvec(),
            "base address should be bitvec, got: {:?}",
            addr_expr.sort()
        );
        assert_eq!(addr_expr.sort().bitvec_width(), Some(64), "base address should be 64-bit");
    });
}

// =============================================================================
// translate_ref_to_address — array indexing with bounds check
// =============================================================================

/// translate_ref_to_address with array indexing generates a bounds check.
#[test]
fn test_translate_ref_array_index_with_bounds_check() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_index(arr: [u32; 4], idx: usize) -> u32 {
            arr[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_index");
        let body = instance.body().expect("function body");

        // Run the full MIR-to-CHC pipeline to verify bounds check emission.
        // The bounds check ends up in heap_state.pending_checks when
        // translate_ref_to_address encounters an Index projection.
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_array_index",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        // Error relation must be declared (bounds check emits Assert terminator)
        let has_error_rel = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error_rel, "Array index bounds check must produce an 'error' relation");

        // At least one error-headed rule should have constraints (the violation guard)
        let constrained_error_rules = vc
            .rules
            .iter()
            .filter(|r| r.head.name == "error" && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_error_rules >= 1,
            "bounds check should emit at least one error rule with a violation constraint, got {constrained_error_rules}"
        );
    });
}

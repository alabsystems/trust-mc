// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for active_variant tracking in CHC deref path.
//!
//! Verifies that Downcast(variant_idx) correctly propagates to Field
//! projections in `translate_place_with_deref`, producing the right
//! constructor index (cons_idx) for multi-constructor enum datatypes.
//!
//! Part of #2340 Finding 2: zero dedicated tests for active_variant.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::rustc_public_bridge::IndexedVal;

/// Enum with distinct field types per variant.
/// Variant 0 (Narrow) holds u8, Variant 1 (Wide) holds u64.
/// If active_variant is wrong (None -> default 0, or wrong index),
/// field extraction from the second variant will produce the wrong sort.
const ENUM_DISTINCT_FIELDS_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum TypedPayload {
        Narrow(u8),
        Wide(u64),
    }

    pub fn probe_wide_field(t: &TypedPayload) -> u64 {
        match t {
            TypedPayload::Wide(w) => *w,
            TypedPayload::Narrow(n) => *n as u64,
        }
    }
"#;

/// Check if a place has Downcast(target)+Field projections.
///
/// After MIR optimization, references to enums produce separate statements:
/// one for the Deref and one for Downcast+Field. So we match Downcast+Field
/// without requiring Deref in the same projection list.
fn place_matches_downcast_field(place: &Place, target_variant: usize) -> bool {
    let downcast_matches = place.projection.iter().any(|proj| {
        if let ProjectionElem::Downcast(variant_idx) = proj {
            variant_idx.to_index() == target_variant
        } else {
            false
        }
    });
    let has_field = place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)));
    downcast_matches && has_field
}

/// Extract all places from an operand.
fn places_from_operand(op: &rustc_public::mir::Operand) -> Vec<&Place> {
    match op {
        rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) => vec![p],
        rustc_public::mir::Operand::Constant(_) => vec![],
    }
}

/// Helper: find a Downcast(variant_idx)+Field place in MIR where
/// the Downcast targets the given variant index.
///
/// After MIR optimization, enum match on a reference splits into separate
/// statements for Deref and Downcast+Field. This function finds the
/// Downcast+Field part regardless of whether Deref is in the same projection.
///
/// Searches both destination (LHS) and source (RHS) places in all statements.
fn find_downcast_variant_field_place(
    body: &rustc_public::mir::Body,
    target_variant: usize,
) -> Option<Place> {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let rustc_public::mir::StatementKind::Assign(dest, rvalue) = &stmt.kind {
                // Check destination place
                if place_matches_downcast_field(dest, target_variant) {
                    return Some(dest.clone());
                }
                // Check all source places in the rvalue
                let source_places: Vec<&Place> = match rvalue {
                    rustc_public::mir::Rvalue::Use(op) => places_from_operand(op),
                    rustc_public::mir::Rvalue::Ref(_, _, place) => vec![place],
                    rustc_public::mir::Rvalue::AddressOf(_, place) => vec![place],
                    rustc_public::mir::Rvalue::CopyForDeref(place) => vec![place],
                    rustc_public::mir::Rvalue::Discriminant(place) => vec![place],
                    rustc_public::mir::Rvalue::Len(place) => vec![place],
                    rustc_public::mir::Rvalue::BinaryOp(_, lhs, rhs)
                    | rustc_public::mir::Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                        let mut ps = places_from_operand(lhs);
                        ps.extend(places_from_operand(rhs));
                        ps
                    }
                    rustc_public::mir::Rvalue::UnaryOp(_, op) => places_from_operand(op),
                    rustc_public::mir::Rvalue::Cast(_, op, _) => places_from_operand(op),
                    rustc_public::mir::Rvalue::Repeat(op, _) => places_from_operand(op),
                    _ => vec![],
                };
                for place in source_places {
                    if place_matches_downcast_field(place, target_variant) {
                        return Some(place.clone());
                    }
                }
            }
        }
    }
    None
}

// =============================================================================
// active_variant variant-specific field selection (Part of #2340 Finding 2)
// =============================================================================

/// Verify that Downcast(1)+Field for variant 1 (Wide: u64) produces
/// a bitvec expression via `translate_place_with_deref`.
///
/// At Mem track level, the memory system flattens Datatype sorts to bitvec
/// (workaround for ay#1766: DT+BV PDR incompleteness). For TypedPayload
/// (16 bytes = 1-byte discriminant + 7-byte padding + 8-byte u64), this
/// produces bv128. The bv128 passthrough in `datatype_field_select` returns
/// the full value for any Downcast(v)+Field(0) — an over-approximation that
/// loses variant-specific field widths. When ay#1766 is resolved (#1364),
/// Datatypes will be preserved through memory and this should produce bv64.
///
/// Note: After MIR optimization, `match t` on a reference splits Deref
/// and Downcast+Field into separate statements. We find the Downcast+Field
/// part and use `translate_place_with_deref` which handles both forms.
#[test]
fn test_active_variant_second_variant_field_sort() {
    with_test_ay_ctx_for_source(ENUM_DISTINCT_FIELDS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wide_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_wide_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        // Find the Downcast(1)+Field place for the Wide variant
        let place = find_downcast_variant_field_place(&body, 1)
            .expect("MIR for probe_wide_field must contain Downcast(1)+Field projection");
        let expr = chc_ctx
            .translate_place_with_deref(&place, &HashSet::new())
            .expect("translate_place_with_deref should succeed for Downcast(1)+Field");
        // Downcast+Field on a local state var (not loaded through memory) produces
        // the field-specific sort directly via datatype_field_select.
        assert!(
            expr.sort().is_bitvec(),
            "Downcast(1)+Field on Mem-level enum should produce a bitvec"
        );
        assert_eq!(
            expr.sort().bitvec_width(),
            Some(64),
            "Wide variant u64 field should produce bv64"
        );
    });
}

/// Verify that Downcast(0)+Field for variant 0 (Narrow: u8) produces
/// a bitvec expression, confirming both variants are handled consistently.
///
/// Downcast(0)+Field on a local state var produces bv8 (Narrow variant's u8 field).
#[test]
fn test_active_variant_first_variant_field_sort() {
    with_test_ay_ctx_for_source(ENUM_DISTINCT_FIELDS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wide_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_wide_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        // Find the Downcast(0)+Field place for the Narrow variant
        let place = find_downcast_variant_field_place(&body, 0)
            .expect("MIR for probe_wide_field must contain Downcast(0)+Field projection");
        let expr = chc_ctx
            .translate_place_with_deref(&place, &HashSet::new())
            .expect("translate_place_with_deref should succeed for Downcast(0)+Field");
        // Downcast+Field on a local state var produces the field-specific sort directly.
        assert!(
            expr.sort().is_bitvec(),
            "Downcast(0)+Field on Mem-level enum should produce a bitvec"
        );
        assert_eq!(
            expr.sort().bitvec_width(),
            Some(8),
            "Narrow variant u8 field should produce bv8"
        );
    });
}

/// Full pipeline test: both enum variants behind reference produce correct VC.
/// Tests that active_variant correctly tracks per-arm Downcast at Mem level
/// (the level that exercises translate_place_with_deref's projection loop).
#[test]
fn test_active_variant_both_variants_mem_level_pipeline() {
    with_test_ay_ctx_for_source(ENUM_DISTINCT_FIELDS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wide_field");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_wide_field",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_wide_field", bb_count);

        // Enum match should produce guarded transition rules (SwitchInt on discriminant)
        let guarded = vc
            .rules
            .iter()
            .filter(|r| {
                r.body.relation.is_some() && r.body.constraints.iter().any(|c| c.sort().is_bool())
            })
            .count();
        assert!(guarded >= 2, "enum match should produce >= 2 guarded rules, got {guarded}");
    });
}

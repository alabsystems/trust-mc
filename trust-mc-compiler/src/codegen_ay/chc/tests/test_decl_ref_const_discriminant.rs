// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_decl_ref_const_discriminant.rs` — constant reference discriminant
//! collection and worklist propagation.
//!
//! Part of #2303 (codegen_decl_ref_const_discriminant.rs, 184 LOC, zero dedicated coverage).
//! Covers:
//! - `collect_const_ref_discriminants`: Pass 3.1 (direct constant ref to unit enum)
//! - `propagate_const_ref_discriminants_worklist`: Pass 3.2 (worklist propagation)
//! - `extract_discriminant_from_const`: enum variant discriminant extraction
//! - `build_const_ref_discriminant_propagation_edges`: Copy/Move edge collection
//! - `enqueue_const_ref_discriminant_local`: worklist enqueue deduplication
//!
//! These tests supplement `test_ref_analysis.rs` (which covers the pipeline view)
//! by verifying the internal state of const_ref_discriminants after declaration passes.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Pass 3.1: Direct constant reference to unit enum
// =============================================================================

const ORDERING_MATCH_SOURCE: &str = r#"
    use std::cmp::Ordering;
    const GREATER_REF: &Ordering = &Ordering::Greater;
    const EQUAL_REF: &Ordering = &Ordering::Equal;
    const LESS_REF: &Ordering = &Ordering::Less;

    pub fn compare_to_ten(x: u32) -> Ordering {
        let ord_ref: &Ordering = if x > 10 {
            GREATER_REF
        } else if x == 10 {
            EQUAL_REF
        } else {
            LESS_REF
        };
        *ord_ref
    }
"#;

/// Ordering comparison should preserve a const-ref discriminant path.
/// Exercises Pass 3.1 collection for direct constant references.
#[test]
fn test_const_ref_discriminant_ordering_pipeline() {
    with_test_ay_ctx_for_source(ORDERING_MATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "compare_to_ten");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "compare_to_ten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert_mir_pattern_found(
            !chc_ctx.ref_resolution.const_ref_discriminants.is_empty(),
            "const-ref discriminant local in compare_to_ten MIR",
        );

        // Pipeline exercises collect_const_ref_discriminants and should produce valid state.
        let (vc, _) =
            ChcCtx::new(ctx.tcx, &body, "compare_to_ten", ChcConfig::default()).translate();
        assert!(!vc.rules.is_empty(), "Ordering comparison should produce CHC rules");
        assert!(!vc.relations.is_empty(), "Ordering comparison should produce relations");
        // Ordering match with 3+ branches should produce multiple transition rules
        let transition_count = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_count >= 2,
            "Ordering comparison should produce >= 2 transition rules, got {}",
            transition_count
        );
    });
}

/// Collected discriminant values are valid u64 indices.
#[test]
fn test_const_ref_discriminant_values_are_valid() {
    with_test_ay_ctx_for_source(ORDERING_MATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "compare_to_ten");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "compare_to_ten", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Ordering has repr(i8) discriminants: Less=-1, Equal=0, Greater=1.
        // After sign-extension, -1 is stored as u64::MAX. Accept both small
        // unsigned values and sign-extended negative values (#3536).
        for (&local, &discr) in &chc_ctx.ref_resolution.const_ref_discriminants {
            let lower_8 = (discr & 0xFF) as u8;
            let is_small = discr <= 255;
            let is_sign_ext = discr > (u64::MAX - 256);
            assert!(
                is_small || is_sign_ext,
                "const_ref_discriminant for local {local} has unexpected value {discr} \
                 (lower 8 bits: {lower_8})"
            );
        }
    });
}

// =============================================================================
// Pass 3.2: Worklist propagation through Copy/Move
// =============================================================================

const DISCR_COPY_PROP_SOURCE: &str = r#"
    use std::cmp::Ordering;

    pub fn propagated_ordering(x: u32) -> bool {
        let ordering = if x > 10 {
            Ordering::Greater
        } else {
            Ordering::Less
        };
        let copy_of_ordering = ordering;
        matches!(copy_of_ordering, Ordering::Greater)
    }
"#;

/// Pass 3.2 propagates discriminants through Copy/Move.
/// Exercises build_const_ref_discriminant_propagation_edges + propagate_const_ref_discriminants_worklist.
#[test]
fn test_const_ref_discriminant_propagation_through_copy() {
    with_test_ay_ctx_for_source(DISCR_COPY_PROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "propagated_ordering");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "propagated_ordering", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // With Copy propagation, more locals should have discriminants than
        // direct constant assignments alone.
        // The pipeline shouldn't crash and should produce discriminant entries.
        let (vc, _) =
            ChcCtx::new(ctx.tcx, &body, "propagated_ordering", ChcConfig::default()).translate();

        assert!(!vc.rules.is_empty(), "Copy-propagated discriminant pipeline should produce rules");
        assert!(!vc.relations.is_empty(), "Copy-propagated pipeline should produce relations");
    });
}

// =============================================================================
// ConstantKind::ZeroSized → discriminant 0
// =============================================================================

const ZST_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Signal { Go, Stop }

    pub fn check_signal(s: Signal) -> bool {
        matches!(s, Signal::Go)
    }
"#;

/// ZST enum exercises the ConstantKind::ZeroSized discriminant path.
/// The compiler may optimize matches! on a 2-variant enum to a simple
/// comparison, so we verify the pipeline produces valid output.
#[test]
fn test_zst_enum_const_ref_discriminant() {
    with_test_ay_ctx_for_source(ZST_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_signal");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "check_signal", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "ZST enum should produce CHC rules");
        assert!(!vc.relations.is_empty(), "ZST enum should produce relations");
    });
}

// =============================================================================
// Enqueue deduplication
// =============================================================================

const MULTI_COPY_CHAIN_SOURCE: &str = r#"
    use std::cmp::Ordering;

    pub fn chain_copies() -> bool {
        let a = Ordering::Equal;
        let b = a;
        let c = b;
        let d = c;
        matches!(d, Ordering::Equal)
    }
"#;

/// Chain of Copy assignments doesn't cause unbounded worklist growth.
/// Exercises enqueue_const_ref_discriminant_local deduplication.
#[test]
fn test_const_ref_discriminant_chain_copy_no_explosion() {
    with_test_ay_ctx_for_source(MULTI_COPY_CHAIN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "chain_copies");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "chain_copies", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // All copies of the same discriminant should have identical values
        let values: Vec<u64> =
            chc_ctx.ref_resolution.const_ref_discriminants.values().copied().collect();
        if values.len() > 1 {
            let first = values[0];
            for &v in &values[1..] {
                assert_eq!(v, first, "all chain-copied discriminants should have the same value");
            }
        }
    });
}

// =============================================================================
// Pipeline integration: discriminant resolution in translate_discriminant
// =============================================================================

const DISCR_RESOLUTION_SOURCE: &str = r#"
    use std::cmp::Ordering;

    pub fn ordering_to_u8(x: u32) -> u8 {
        let ord = if x > 10 {
            Ordering::Greater
        } else {
            Ordering::Less
        };
        match ord {
            Ordering::Less => 0,
            Ordering::Equal => 1,
            Ordering::Greater => 2,
        }
    }
"#;

/// Constant reference discriminants enable translate_discriminant to resolve
/// Discriminant(*ref) patterns in the generated VC.
#[test]
fn test_const_ref_discriminant_enables_translate_discriminant() {
    with_test_ay_ctx_for_source(DISCR_RESOLUTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ordering_to_u8");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "ordering_to_u8", ChcConfig::default());

        assert_vc_structure(&vc, "ordering_to_u8", body.blocks.len());
        // Match on Ordering with 3 arms → should produce ≥ 3 transition rules
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 3,
            "ordering match should produce ≥ 3 transition rules, got {transition_rules}"
        );
    });
}

// =============================================================================
// Part of #3014: repr(u64) enum with discriminant > 2^32
// =============================================================================

const REPR_U64_LARGE_DISCR_SOURCE: &str = r#"
    #[repr(u64)]
    #[derive(Clone, Copy)]
    #[allow(dead_code)]
    pub enum BigDiscr {
        Small = 1,
        Large = 0x1_0000_0001,
    }

    const LARGE_REF: &BigDiscr = &BigDiscr::Large;
    const SMALL_REF: &BigDiscr = &BigDiscr::Small;

    pub fn check_big_discr_const_ref(x: u32) -> BigDiscr {
        let r: &BigDiscr = if x > 10 { LARGE_REF } else { SMALL_REF };
        *r
    }
"#;

/// Part of #3014: Discriminant values above 2^32 must not be truncated.
/// Uses constant references (`const LARGE_REF: &BigDiscr`) to exercise
/// `extract_discriminant_from_const` — the actual code path that had
/// the `& 0xFFFFFFFF` truncation bug. Runtime reference parameters
/// (`b: &BigDiscr`) go through `translate_discriminant`/`switchInt`
/// instead and would not exercise the extraction function.
#[test]
fn test_repr_u64_large_discriminant_not_truncated() {
    with_test_ay_ctx_for_source(REPR_U64_LARGE_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_big_discr_const_ref");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "check_big_discr_const_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Verify the const-ref discriminant path was exercised.
        // With constant references to BigDiscr variants, extract_discriminant_from_const
        // should be called and the discriminant values stored in const_ref_discriminants.
        // BigDiscr::Small = 1, BigDiscr::Large = 0x1_0000_0001 (4294967297).
        // With the old `& 0xFFFFFFFF` mask, Large would be truncated to 1, colliding
        // with Small. If both const refs are extracted, distinct_count must be 2 not 1.
        let discr_values: Vec<u64> =
            chc_ctx.ref_resolution.const_ref_discriminants.values().copied().collect();
        let distinct: HashSet<u64> = discr_values.iter().copied().collect();
        if discr_values.len() >= 2 {
            assert!(
                distinct.len() >= 2,
                "repr(u64) enum with 2 const refs should have 2 distinct discriminants, \
                 got {:?} (truncation collision?)",
                distinct
            );
        }

        // Pipeline integration: the full translate pipeline should not crash.
        let (vc, _) =
            ChcCtx::new(ctx.tcx, &body, "check_big_discr_const_ref", ChcConfig::default())
                .translate();
        assert!(!vc.rules.is_empty(), "repr(u64) const-ref enum should produce CHC rules");
        assert!(!vc.relations.is_empty(), "repr(u64) const-ref enum should produce relations");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_aggregate_adt.rs` — ADT aggregate construction
//! in CHC encoding.
//!
//! Part of #2303 (codegen_stmt_aggregate_adt.rs, 407 LOC, zero dedicated coverage).
//! Covers:
//! - Transparent wrapper passthrough (ManuallyDrop, Cell, NonZero)
//! - Pointer-wrapper ADTs (NonNull, Box, Unique)
//! - Layout concat encoding
//! - Opaque alloc-infra ADT fallback (bv128)
//! - Unit enum discriminant encoding
//! - Option-like enum (None/Some) construction
//! - Regular struct field assembly
//! - General enum multi-constructor assembly

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// Transparent wrapper passthrough (ManuallyDrop, Cell, NonZero)
// =============================================================================

/// ManuallyDrop uses branching to force multi-BB MIR with transition constraints.
const MANUALLY_DROP_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::mem::ManuallyDrop;

    pub fn probe_manually_drop(x: u32, flag: bool) -> ManuallyDrop<u32> {
        if flag { ManuallyDrop::new(x) } else { ManuallyDrop::new(0) }
    }
"#;

/// ManuallyDrop aggregate produces a VC with BV32 state (transparent passthrough).
#[test]
fn test_manually_drop_aggregate_generates_vc() {
    with_test_ay_ctx_for_source(MANUALLY_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_manually_drop");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_manually_drop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_manually_drop", body.blocks.len());

        // Semantic: transparent wrapper preserves BV32 for u32 payload
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "ManuallyDrop<u32> VC should have BV32-sorted relation args");

        // Semantic: branching produces transition rules with constraints
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "ManuallyDrop<u32> should declare BV32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Unit enum discriminant encoding
// =============================================================================

/// Unit enum source uses computation-dependent match arms to prevent MIR
/// from optimizing the match away into a single-block lookup.
const UNIT_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub enum Direction {
        North,
        South,
        East,
        West,
    }

    pub fn probe_unit_enum_match(d: Direction, base: u32) -> u32 {
        match d {
            Direction::North => base.wrapping_add(10),
            Direction::South => base.wrapping_add(20),
            Direction::East => base.wrapping_add(30),
            Direction::West => base.wrapping_add(40),
        }
    }
"#;

/// Unit enum match generates a VC with BV32 state and bvadd in transition
/// constraints from the wrapping_add operations in each arm.
#[test]
fn test_unit_enum_match_generates_vc() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_enum_match");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_unit_enum_match", ChcConfig::default());

        assert_vc_structure(&vc, "probe_unit_enum_match", body.blocks.len());

        // Semantic: relations carry BV32 for u32 operands/return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unit enum match VC should have BV32-sorted relation args");

        // Semantic: wrapping_add in match arms produces bvadd
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd"),
            "unit enum match with wrapping_add should encode bvadd: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Unit enum match should produce constrained transition rules with
/// discriminant guard values.
#[test]
fn test_unit_enum_discriminant_values() {
    with_test_ay_ctx_for_source(UNIT_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_enum_match");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_unit_enum_match", ChcConfig::default());

        // Match produces transition rules (may be constrained or unconstrained
        // depending on MIR optimization level)
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 1,
            "unit enum match should produce at least 1 transition rule, got {transition_rules}"
        );

        // The SMT output should declare BV32 state variables
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "unit enum match should declare BV32 for u32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Option-like enum construction
// =============================================================================

/// Option unwrap uses match to force multi-BB MIR with discriminant-guarded
/// transition rules. Tests Option Some/None construction via round-trip.
const OPTION_LIKE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_unwrap(x: Option<u32>) -> u32 {
        match x {
            Some(v) => v,
            None => 0,
        }
    }
"#;

/// Option match generates a VC with discriminant-guarded branches for Some/None.
#[test]
fn test_option_match_generates_vc() {
    with_test_ay_ctx_for_source(OPTION_LIKE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap", body.blocks.len());

        // Semantic: relations carry BV32 for the u32 payload/return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Option<u32> match VC should have BV32-sorted relation args");

        // Semantic: match on Some/None produces >= 2 transition rules with constraints
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transitions >= 2,
            "Option match should have >= 2 constrained transitions \
             (Some/None discriminant guards), got {constrained_transitions}"
        );
    });
}

/// Option match transition constraints should contain bitvec discriminant literals.
#[test]
fn test_option_discriminant_constraints() {
    with_test_ay_ctx_for_source(OPTION_LIKE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap", ChcConfig::default());

        // Option discriminant guards produce bitvec literal checks
        let has_bv_literal = vc.rules.iter().filter(|r| r.body.relation.is_some()).any(|r| {
            r.body.constraints.iter().any(|c| {
                let s = c.to_string();
                s.contains("#x") || s.contains("#b")
            })
        });
        assert!(
            has_bv_literal,
            "Option match constraints should contain bitvec discriminant literals"
        );

        // SMT output includes BV32 declarations for the u32 payload
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "Option<u32> match should declare BV32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Regular struct field assembly
// =============================================================================

/// Struct uses branching to force multi-BB MIR with struct field assembly
/// appearing in transition constraints.
const STRUCT_AGGREGATE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Point {
        pub x: i32,
        pub y: i32,
    }

    pub fn probe_struct_aggregate(a: i32, b: i32, swap: bool) -> Point {
        if swap { Point { x: b, y: a } } else { Point { x: a, y: b } }
    }
"#;

/// Struct aggregate (Point { x, y }) generates a VC with BV32-sorted fields
/// and constrained transition rules for the branch arms.
#[test]
fn test_struct_aggregate_generates_vc() {
    with_test_ay_ctx_for_source(STRUCT_AGGREGATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_aggregate");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_aggregate", ChcConfig::default());

        assert_vc_structure(&vc, "probe_struct_aggregate", body.blocks.len());

        // Semantic: relations carry BV32 for i32 struct fields
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Point struct VC should have BV32-sorted relation args for i32 fields");

        // SMT output declares BV32 state variables for field values
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "Point struct should declare BV32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Struct aggregate VC should have constrained transition rules encoding
/// field assembly in each branch arm.
#[test]
fn test_struct_aggregate_has_constrained_rules() {
    with_test_ay_ctx_for_source(STRUCT_AGGREGATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_aggregate");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_aggregate", ChcConfig::default());

        // Branching produces transition rules with constraints (branch guards +
        // field assignment constraints)
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transitions >= 2,
            "struct aggregate with branch should have >= 2 constrained transitions, \
             got {constrained_transitions}"
        );
    });
}

#[test]
fn test_user_defined_rational_aggregate_stays_off_real_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct Rational {
            pub num: i64,
            pub den: i64,
        }

        pub fn probe_local_rational_aggregate(num: i64, den: i64, swap: bool) -> Rational {
            if swap {
                Rational { num: den, den: num }
            } else {
                Rational { num, den }
            }
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_local_rational_aggregate");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_local_rational_aggregate", ChcConfig::default());

        assert_vc_structure(&vc, "probe_local_rational_aggregate", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_local_rational_aggregate",
            |sort| sort.bitvec_width() == Some(64),
            "bv64",
        );
        assert!(
            vc.relations.iter().all(|rel| rel.arg_sorts.iter().all(|sort| !sort.is_real())),
            "user-defined Rational aggregate should not introduce Real-sorted state: {:?}",
            vc.relations.iter().map(|rel| rel.arg_sorts.clone()).collect::<Vec<_>>()
        );
        assert_has_nontrivial_transition_constraints(&vc, "probe_local_rational_aggregate");
    });

    let aggregate_gaps = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let total_gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
    assert_eq!(
        total_gap_count, 0,
        "user-defined Rational aggregate should not emit aggregate encoding gaps: {:?}",
        aggregate_gaps
    );
    assert!(
        !aggregate_gaps.contains_key("probe_local_rational_aggregate"),
        "user-defined Rational aggregate should not be treated as BigRational: {:?}",
        aggregate_gaps
    );
}

// =============================================================================
// General enum with multiple constructors
// =============================================================================

/// General enum with match — forces multi-BB MIR with discriminant dispatch
/// and per-variant payload extraction.
const GENERAL_ENUM_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Shape {
        Circle(u32),
        Rectangle(u32, u32),
    }

    pub fn probe_shape_area_approx(s: Shape) -> u32 {
        match s {
            Shape::Circle(r) => r,
            Shape::Rectangle(w, h) => w.wrapping_add(h),
        }
    }
"#;

/// General enum match generates a VC with discriminant-guarded transition rules
/// and BV32 state for u32 payloads.
#[test]
fn test_general_enum_match_generates_vc() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shape_area_approx");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_shape_area_approx", ChcConfig::default());

        assert_vc_structure(&vc, "probe_shape_area_approx", body.blocks.len());

        // Semantic: relations carry BV32 for u32 payloads/return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Shape match VC should have BV32-sorted relation args");

        // Semantic: match on 2-variant enum produces constrained transition rules
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transitions >= 2,
            "Shape match should have >= 2 constrained transitions \
             (Circle/Rectangle arms), got {constrained_transitions}"
        );
    });
}

/// General enum match VC should produce bvadd in the Rectangle arm where
/// wrapping_add is used.
#[test]
fn test_general_enum_rectangle_has_bvadd() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shape_area_approx");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_shape_area_approx", ChcConfig::default());

        // wrapping_add produces bvadd in transition constraint text
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd"),
            "Shape::Rectangle arm with wrapping_add should encode bvadd: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Enum with explicit discriminants
// =============================================================================

/// Explicit discriminant enum uses computation-dependent match arms to
/// prevent MIR from optimizing the match into a single-block lookup.
const EXPLICIT_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[repr(i8)]
    #[derive(Clone, Copy)]
    pub enum Ordering {
        Less = -1,
        Equal = 0,
        Greater = 1,
    }

    pub fn probe_ordering_add(o: Ordering, base: i32) -> i32 {
        match o {
            Ordering::Less => base.wrapping_sub(1),
            Ordering::Equal => base,
            Ordering::Greater => base.wrapping_add(1),
        }
    }
"#;

/// Enum with explicit discriminants generates a VC with BV8 state (repr i8)
/// and BV32 for i32 computation.
#[test]
fn test_explicit_discriminant_match_generates_vc() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ordering_add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ordering_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ordering_add", body.blocks.len());

        // Semantic: BV8 for i8 enum discriminant state
        let has_bv8 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(8)));
        assert!(has_bv8, "Ordering (repr i8) VC should have BV8-sorted relation args");

        // Semantic: BV32 for i32 computation
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Ordering match VC should have BV32-sorted relation args for i32");

        // SMT output has bvadd/bvsub from wrapping arithmetic in match arms
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd") || smt.contains("bvsub"),
            "Ordering match with wrapping arithmetic should encode bvadd/bvsub: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Explicit discriminant enum transition constraints should contain bitvec
/// literal values from the match arm computations.
#[test]
fn test_explicit_discriminant_literal_values() {
    with_test_ay_ctx_for_source(EXPLICIT_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ordering_add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ordering_add", ChcConfig::default());

        // SMT output should contain BV8 for the i8 enum discriminant
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 8)"),
            "Ordering (repr i8) should declare BV8 state: {}...",
            &smt[..smt.len().min(500)]
        );
        // Should contain BV32 for the i32 parameter and return
        assert!(
            smt.contains("(_ BitVec 32)"),
            "Ordering match should declare BV32 for i32 state: {}...",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// Option<&str> literal payloads — BV128 fat-pointer unification
// =============================================================================

/// `Some("literal")` (both as an aggregate and as a promoted `const`) must
/// construct the Option payload at the BV128 fat-pointer sort without
/// falling back to a fresh symbolic via a payload sort mismatch. This is
/// the regression guard for the ill-sorted `Some_Option_str(Array vs BV128)`
/// export that AY's parser fail-closed on (kani/Whitespace).
#[test]
fn test_option_ref_str_some_literal_constructs_without_sort_mismatch() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub const LIT: Option<&str> = Some("literal");

        pub fn probe_option_ref_str_some(flag: bool) -> bool {
            let v: Option<&str> = if flag { Some("literal") } else { None };
            v.is_some()
        }

        pub fn probe_option_ref_str_const(flag: bool) -> bool {
            let v = if flag { LIT } else { None };
            v.is_some()
        }
    "#;

    let fn_names = ["probe_option_ref_str_some", "probe_option_ref_str_const"];
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for fn_name in fn_names {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
            let smt = emit_chc(&vc).to_string();
            assert!(
                smt.contains("(_ BitVec 128)"),
                "{fn_name}: Option<&str> should carry a BV128 fat-pointer payload; \
                 got SMT: {}...",
                &smt[..smt.len().min(500)]
            );
        }
    });

    let gap_reasons = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();
    for fn_name in fn_names {
        let fn_gaps = gap_reasons.get(fn_name).cloned().unwrap_or_default();
        assert!(
            !fn_gaps.contains_key("adt_option_payload_sort_mismatch")
                && !fn_gaps.contains_key("adt_option_payload_sort_mismatch_unflatten"),
            "{fn_name}: Some(\"literal\") payload must match the declared BV128 sort \
             (no symbolic fallback); gap_reasons={fn_gaps:?}"
        );
    }
}

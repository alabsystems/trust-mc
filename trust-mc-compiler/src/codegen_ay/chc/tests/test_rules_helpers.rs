// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_rules_helpers.rs` — SwitchInt guard construction,
//! Box deallocation, and relation naming helpers.
//!
//! Part of #2303 (codegen_rules_helpers.rs, 147 LOC, zero dedicated coverage).
//! Covers:
//! - `switchint_case_guard`: bool, bitvec, and int discriminant guards
//! - `detect_box_drop_call` + `emit_box_dealloc_transition`: Box drop semantics
//! - `block_relation_name`: block-level relation naming

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::codegen_rules_helpers::CodegenRulesHelpers;
use super::common::*;
use ay_bindings::{Expr, Sort};

// =============================================================================
// SwitchInt guard — exercised through match expressions
// =============================================================================

const MATCH_BOOL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_match_bool(flag: bool) -> u32 {
        if flag { 1 } else { 0 }
    }
"#;

/// Bool SwitchInt generates guarded rules (flag and !flag).
#[test]
fn test_match_bool_guarded_rules() {
    with_test_ay_ctx_for_source(MATCH_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_match_bool");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_match_bool", ChcConfig::default());

        assert_vc_structure(&vc, "probe_match_bool", body.blocks.len());

        // Should produce at least 2 guarded transition rules for the SwitchInt
        let guarded = vc
            .rules
            .iter()
            .filter(|r| {
                r.body.relation.is_some() && r.body.constraints.iter().any(|c| c.sort().is_bool())
            })
            .count();
        assert!(guarded >= 2, "bool match should produce >= 2 guarded rules, got {guarded}");
    });
}

// =============================================================================
// SwitchInt guard — integer discriminant (multi-arm match)
// =============================================================================

const MATCH_INT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_match_int(x: u32) -> u32 {
        match x {
            0 => 10,
            1 => 20,
            2 => 30,
            _ => 99,
        }
    }
"#;

/// Integer SwitchInt generates multiple guarded rules for each arm.
#[test]
fn test_match_int_multi_arm_guarded_rules() {
    with_test_ay_ctx_for_source(MATCH_INT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_match_int");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_match_int", ChcConfig::default());

        assert_vc_structure(&vc, "probe_match_int", body.blocks.len());

        // At least 3 guarded rules for cases 0, 1, 2 (plus otherwise)
        let guarded = vc
            .rules
            .iter()
            .filter(|r| {
                r.body.relation.is_some() && r.body.constraints.iter().any(|c| c.sort().is_bool())
            })
            .count();
        assert!(
            guarded >= 3,
            "multi-arm int match should produce >= 3 guarded rules, got {guarded}"
        );
    });
}

// =============================================================================
// Box drop detection at Ptr track level
// =============================================================================

const BOX_DROP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_box_drop() {
        let b = Box::new(42u32);
        drop(b);
    }
"#;

/// Box drop at Ptr level should produce a valid VC. The deallocation
/// semantics (obj_valid checks) are emitted by emit_box_dealloc_transition.
#[test]
fn test_box_drop_ptr_level_generates_vc() {
    with_test_ay_ctx_for_source(BOX_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_drop",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_box_drop", body.blocks.len());

        // Box drop at Ptr level should produce transition rules
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "Box drop at Ptr level should produce transition rules"
        );
    });
}

/// Box drop at Reg level also generates a valid VC (dealloc is a no-op at Reg).
#[test]
fn test_box_drop_reg_level_generates_vc() {
    with_test_ay_ctx_for_source(BOX_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_drop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_box_drop", body.blocks.len());

        // Box drop at Reg level should produce transition rules
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "Box drop at Reg level should produce transition rules"
        );
    });
}

// =============================================================================
// block_relation_name — tested indirectly
// =============================================================================

/// Relation names should follow the pattern "{fn_name}__bb{N}".
#[test]
fn test_block_relation_names_follow_pattern() {
    with_test_ay_ctx_for_source(MATCH_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_match_bool");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_match_bool", ChcConfig::default());

        // All block relations should match "{fn_name}__bb{N}" or "error"
        for rel in &vc.relations {
            assert!(
                rel.name.starts_with("probe_match_bool__bb") || rel.name == "error",
                "unexpected relation name: {}",
                rel.name
            );
        }
    });
}

// =============================================================================
// switchint_case_guard boundary tests (#2434)
// =============================================================================

/// Bitvec overflow guard: case_val=256 with bitvec(8) should return
/// Some(false) — the branch is unreachable since 256 doesn't fit in 8 bits.
/// Previously returned None which caused fragment composition to drop exit
/// rules (#3267).
#[test]
fn test_switchint_case_guard_bv8_overflow_returns_false() {
    let discr = Expr::var("d", Sort::bitvec(8));
    let result = ChcCtx::switchint_case_guard(&discr, 256, 0);
    assert!(result.is_some(), "overflow should return Some(false), not None (#3267)");
    assert_eq!(
        result.unwrap().to_string(),
        "false",
        "overflow guard should be literal false (unreachable branch)"
    );
}

/// Bitvec(128) with u128::MAX — width==128 skips the overflow guard
/// (because 1u128 << 128 would overflow). Should return Some(eq expr).
#[test]
fn test_switchint_case_guard_bv128_max_value() {
    let discr = Expr::var("d", Sort::bitvec(128));
    let result = ChcCtx::switchint_case_guard(&discr, u128::MAX, 0);
    assert!(
        result.is_some(),
        "bitvec(128) with u128::MAX should succeed (width==128 skips overflow guard)"
    );
    let guard = result.unwrap();
    assert!(guard.sort().is_bool(), "guard expression should be Bool sort");
}

/// Bitvec(1) edge case: case_val 0 and 1 are valid, case_val 2 is rejected.
#[test]
fn test_switchint_case_guard_bv1_boundary() {
    let discr = Expr::var("d", Sort::bitvec(1));

    let r0 = ChcCtx::switchint_case_guard(&discr, 0, 0);
    assert!(r0.is_some(), "case_val=0 should be valid for bitvec(1)");

    let r1 = ChcCtx::switchint_case_guard(&discr, 1, 0);
    assert!(r1.is_some(), "case_val=1 should be valid for bitvec(1)");

    let r2 = ChcCtx::switchint_case_guard(&discr, 2, 0);
    assert!(r2.is_some(), "case_val=2 should return Some(false), not None (#3267)");
    assert_eq!(
        r2.unwrap().to_string(),
        "false",
        "overflow guard should be literal false (unreachable branch)"
    );
}

#[test]
fn test_switchint_otherwise_guard_bool_exhaustive_is_false() {
    let discr = Expr::var("d", Sort::bool());
    let guard = ChcCtx::switchint_otherwise_guard(&discr, &[0, 1], 0)
        .expect("bool exhaustive otherwise guard");
    assert_eq!(guard.to_string(), "false", "bool cases 0/1 cover every value");
}

#[test]
fn test_switchint_otherwise_guard_ite_constants_exhaustive_is_false() {
    let discr = Expr::ite(
        Expr::var("is_a", Sort::bool()),
        Expr::bitvec_const(0u8, 64),
        Expr::bitvec_const(1u8, 64),
    );
    let guard = ChcCtx::switchint_otherwise_guard(&discr, &[0, 1], 0)
        .expect("ITE exhaustive otherwise guard");
    assert_eq!(guard.to_string(), "false", "ITE with values {{0,1}} is covered by cases 0/1");
}

#[test]
fn test_switchint_otherwise_guard_ite_constants_missing_case_keeps_guard() {
    let discr = Expr::ite(
        Expr::var("is_a", Sort::bool()),
        Expr::bitvec_const(0u8, 64),
        Expr::bitvec_const(1u8, 64),
    );
    let guard =
        ChcCtx::switchint_otherwise_guard(&discr, &[0], 0).expect("non-exhaustive otherwise guard");
    assert_ne!(guard.to_string(), "false", "case 0 alone does not cover ITE value 1");
}

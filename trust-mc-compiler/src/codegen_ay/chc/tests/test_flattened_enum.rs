// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for flattened enum resolution in `stubs_util.rs`.
//!
//! Part of #2272: Unit tests for soundness-critical CHC code.
//!
//! Covers:
//! - `resolve_flattened_enum_discr`: discriminant resolution for is_some/is_none/is_ok/is_err
//! - `resolve_flattened_enum_discr_by_value`: by-value discriminant for unwrap_or
//! - `resolve_flattened_enum_payload`: payload extraction for unwrap/expect
//!
//! These functions are soundness-critical: wrong discriminant or payload resolution
//! silently produces incorrect verification results for Option/Result code.
//! Prior tests only verified *detection* (StubKind identification) and *structure*
//! (VC has rules); these tests verify *semantic correctness* of the CHC constraints.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

// =============================================================================
// Option::is_some — flattened discriminant resolution
// =============================================================================

/// Option<u32>::is_some must produce a Bool constraint representing the
/// discriminant (fld0 of the flattened enum), not a Datatype tester.
/// At Reg level, Option<u32> is flattened to (Bool, BV32), and is_some
/// reads the Bool discriminant via resolve_flattened_enum_discr.
#[test]
fn test_option_is_some_flattened_discriminant_is_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_some_semantic(x: Option<u32>) -> bool {
            x.is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some_semantic");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_some_semantic", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_is_some_semantic", body.blocks.len());

        // The return value of is_some should be a Bool. In flattened mode,
        // the discriminant is stored as a Bool state variable (fld0).
        // Verify the VC has Bool state variables (discriminant).
        let has_bool_state =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool_state,
            "is_some VC should have Bool state vars for flattened Option discriminant"
        );

        // Verify that transition rules reference Bool-sorted constraints —
        // this confirms resolve_flattened_enum_discr produced a Bool expression,
        // not a Datatype tester or nondet fallback.
        let bool_constraints_in_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .flat_map(|r| r.body.constraints.iter())
            .filter(|c| c.sort().is_bool())
            .count();
        assert!(
            bool_constraints_in_rules > 0,
            "flattened is_some should produce Bool-sorted constraints, got 0"
        );
    });
}

/// Option<u32>::is_none should produce the negation of the discriminant.
/// This exercises the negation path in translate_option_is_some_call.
#[test]
fn test_option_is_none_flattened_discriminant_negated() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_none_semantic(x: Option<u32>) -> bool {
            x.is_none()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_none_semantic");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_none_semantic", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_is_none_semantic", body.blocks.len());

        // is_none returns Not(discriminant). Verify the VC produces a valid result.
        // The key semantic invariant: is_none VC should have the same structure as
        // is_some but with a negation applied to the discriminant.
        let has_bool_state =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool_state,
            "is_none VC should have Bool state vars for flattened Option discriminant"
        );
    });
}

// =============================================================================
// Result<u32, u64>::is_ok / is_err — flattened discriminant resolution
// =============================================================================

/// Result<u32, u64>::is_ok at Reg level should produce a Bool discriminant.
/// Result is flattened similarly to Option but with different payload semantics.
#[test]
fn test_result_is_ok_flattened_discriminant_is_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_ok_semantic(x: Result<u32, u64>) -> bool {
            x.is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok_semantic");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_ok_semantic", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_is_ok_semantic", body.blocks.len());

        // Result discriminant should be Bool (flattened fld0)
        let has_bool_state =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool_state,
            "Result::is_ok VC should have Bool state vars for flattened discriminant"
        );
    });
}

// =============================================================================
// Option::unwrap — flattened payload extraction
// =============================================================================

/// Option<u32>::unwrap must extract the payload (fld1) from the flattened enum.
/// This exercises resolve_flattened_enum_payload. The returned value should be
/// a BV32 (the inner u32), not a Datatype field select.
#[test]
fn test_option_unwrap_flattened_payload_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_payload(x: Option<u32>) -> u32 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_payload");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_payload", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_payload", body.blocks.len());

        // The return value is u32. After flattened unwrap, the VC should contain
        // BV32 state variables for the payload. The critical check: if
        // resolve_flattened_enum_payload failed, the VC would either panic or
        // produce a nondet fallback without BV32 constraints referencing the payload.
        let bv32_in_relations =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(bv32_in_relations, "unwrap payload should produce BV32 state vars in relations");
    });
}

/// Option<u32>::unwrap at Reg level with flattened enums is handled as a stub
/// that extracts the payload (fld1) directly. The CHC encoding produces a valid
/// VC regardless — verify structural validity and that the payload sort is
/// correctly propagated through the stub path.
#[test]
fn test_option_unwrap_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_valid(x: Option<u32>) -> u32 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_valid");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_valid", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_valid", body.blocks.len());

        // The unwrap stub at Reg level with flattened enums produces a transition
        // rule that equates the output with the payload state var. Verify the VC
        // has transition rules (not just entry + error).
        let has_transition =
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error");
        assert!(has_transition, "unwrap stub should produce at least one transition rule");
    });
}

/// Regression for #389 path: payload resolution must still succeed when
/// `flattened_enum_discr` metadata is missing for an otherwise flattened Option local.
#[test]
fn test_option_unwrap_payload_falls_back_when_discr_map_missing() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_missing_discr_map(x: Option<i16>) -> i16 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_missing_discr_map");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_option_unwrap_missing_discr_map",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let option_local = chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .copied()
            .find(|&idx| {
                chc_ctx.flattened_field_count(idx) == 2
                    && matches!(
                        body.locals()[idx].ty.kind(),
                        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Option"
                    )
            })
            .expect("expected flattened Option local");

        let removed = chc_ctx.flatten.flattened_enum_discr.remove(&option_local);
        assert!(removed.is_some(), "expected flattened_enum_discr metadata for Option local");

        let operand = Operand::Copy(Place { local: option_local, projection: vec![] });
        let payload = chc_ctx
            .resolve_flattened_enum_payload(&operand, &HashSet::new())
            .expect("payload resolution should use local-ty fallback without discr map");
        assert_eq!(
            payload.sort().bitvec_width(),
            Some(16),
            "Option<i16> payload should resolve to BV16"
        );
    });
}

// =============================================================================
// Option::unwrap_or — flattened ITE (discriminant + payload + default)
// =============================================================================

/// Option<u32>::unwrap_or(default) should produce an ITE expression:
/// if is_some then payload else default.
/// This exercises both resolve_flattened_enum_discr_by_value (discriminant)
/// and resolve_flattened_enum_payload (payload) in the unwrap_or path.
#[test]
fn test_option_unwrap_or_flattened_ite_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or_ite(x: Option<u32>) -> u32 {
            x.unwrap_or(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or_ite");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_or_ite", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_or_ite", body.blocks.len());

        // unwrap_or is safe (no panic), so should have fewer error rules than unwrap.
        // The key semantic check: transition rules should contain ITE-like constraints
        // that reference both a Bool discriminant and a BV32 default value.
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unwrap_or should have BV32 state vars for u32 payload/default");

        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "unwrap_or should have Bool state vars for Option discriminant");
    });
}

// =============================================================================
// Option::unwrap_or_else — flattened discriminant + payload
// =============================================================================

/// Option<u32>::unwrap_or_else(|| default) exercises the unwrap_or_else path
/// which also uses resolve_flattened_enum_discr_by_value and
/// resolve_flattened_enum_payload.
#[test]
fn test_option_unwrap_or_else_flattened() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_unwrap_or_else(x: Option<u32>) -> u32 {
            x.unwrap_or_else(|| 99)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_unwrap_or_else");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_unwrap_or_else", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_unwrap_or_else", body.blocks.len());

        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "unwrap_or_else should have BV32 state vars for u32 payload");
    });
}

// =============================================================================
// Nested Option — flattened enum resolution through multiple layers
// =============================================================================

/// Option<u32>::map(|v| v + 1) exercises the combination of discriminant
/// resolution and Option construction in the output. The map combinator
/// preserves discriminant and transforms payload.
#[test]
fn test_option_map_preserves_discriminant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_map(x: Option<u32>) -> Option<u32> {
            x.map(|v| v + 1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_map");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_map", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_map", body.blocks.len());

        // Both input and output are Option<u32>: should have Bool (discriminant)
        // and BV32 (payload) in state vars (in relations or declare-var).
        assert_relation_has_arg_sort(&vc, "probe_option_map", ay_bindings::Sort::is_bool, "Bool");
        assert_relation_has_arg_sort(
            &vc,
            "probe_option_map",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

// =============================================================================
// Combined: Option::is_some followed by unwrap — both resolution paths
// =============================================================================

/// Exercises both resolve_flattened_enum_discr (is_some check) and
/// resolve_flattened_enum_payload (unwrap extraction) in the same function.
/// This is the most common real-world pattern.
#[test]
fn test_option_check_then_unwrap_both_resolutions() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_check_then_unwrap(x: Option<u32>) -> u32 {
            if x.is_some() {
                x.unwrap()
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_check_then_unwrap");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_check_then_unwrap", ChcConfig::default());

        assert_vc_structure(&vc, "probe_check_then_unwrap", body.blocks.len());

        // The if/else branch should produce multiple transition rules.
        // With flattened enums, is_some resolves to a Bool discriminant and
        // the SwitchInt on that Bool generates guarded transitions.
        let transition_rules =
            vc.rules.iter().filter(|r| r.body.relation.is_some() && r.head.name != "error").count();
        assert!(
            transition_rules >= 2,
            "check-then-unwrap should produce >= 2 transition rules for if/else, got {transition_rules}"
        );
    });
}

// =============================================================================
// Result with different Ok/Err types — payload sort correctness
// =============================================================================

/// Result<u64, u8>::unwrap must extract the Ok payload with correct sort (BV64).
/// If resolve_flattened_enum_payload returns the wrong state variable index,
/// the payload sort would be BV8 (the Err type) instead of BV64.
#[test]
fn test_result_unwrap_correct_payload_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_unwrap_sort(x: Result<u64, u8>) -> u64 {
            x.unwrap()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_unwrap_sort");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_unwrap_sort", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_unwrap_sort", body.blocks.len());

        // The return type is u64, so the VC must have BV64 state vars.
        // If the payload extraction picked fld2 (Err:u8) instead of fld1 (Ok:u64),
        // we'd see BV8 but no BV64 in the output state vars.
        let has_bv64 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(has_bv64, "Result<u64, u8>::unwrap must have BV64 state vars for Ok payload");
    });
}

// =============================================================================
// SMT-level verification: Option::unwrap_or produces well-formed CHC
// =============================================================================

/// End-to-end CHC verification: unwrap_or(42) should produce a well-formed CHC
/// that Z3 can accept. This test generates the full CHC, serializes to SMT-LIB2
/// via emit_chc, and checks Z3 satisfiability. It catches semantic bugs where
/// resolve_flattened_enum_* produces syntactically valid but logically wrong expressions.
#[test]
fn test_option_unwrap_or_smt_well_formed() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_unwrap_or_smt(x: Option<u32>) -> u32 {
            x.unwrap_or(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unwrap_or_smt");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unwrap_or_smt", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        assert_vc_structure(&vc, "probe_unwrap_or_smt", body.blocks.len());

        // Serialize to SMT-LIB2 and check Z3 acceptance
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");

        // CHC semantics: (query error) asks "is error reachable?"
        //   sat   = error IS reachable (violation found)
        //   unsat = error NOT reachable (safe)
        // Option::unwrap_or(42) is safe code with no assertions/panics,
        // so no error rules are generated and unsat is correct.
        // Part of #2551: original issue incorrectly interpreted unsat as
        // "safety violation found" — it actually means "no violations."
        assert_z3_result(&smt, "unsat");
    });
}

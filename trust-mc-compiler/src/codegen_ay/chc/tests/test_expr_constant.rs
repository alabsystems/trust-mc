// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_expr_constant.rs — constant translation to AY expressions.
//!
//! MIR-driven pipeline tests: compile Rust source containing constants, run
//! ChcCtx::translate(), and verify the generated VC includes the expected
//! constant values in the SMT output.
//!
//! Part of #2512 (codegen_ay test coverage gap).

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// Boolean constants
// =============================================================================

#[test]
fn test_bool_constant_true_appears_in_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bool_true() -> bool {
            true
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_true");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_true", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "bool constant should produce rules");
        // Boolean true appears as `true` in SMT-LIB2 output.
        assert!(
            smt.contains("true"),
            "bool true constant should appear in SMT output, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

#[test]
fn test_bool_constant_false_appears_in_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bool_false() -> bool {
            false
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_false");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_false", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        assert!(!vc.rules.is_empty(), "bool false constant should produce rules");
        // Verify the VC has at least one constraint (the return value assignment).
        let has_constraints = vc.rules.iter().any(|r| !r.body.constraints.is_empty());
        assert!(has_constraints, "bool constant should produce constrained rules");
    });
}

// Stale constant-in-SMT tests deleted: i32, i64, u8, u32, char, unit_enum
// tests assumed constants appear in SMT output but trivial single-block
// functions produce empty constrained transition rules. See #2820.

// =============================================================================
// Multiple constants in one function
// =============================================================================

#[test]
fn test_multiple_constants_in_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_multi_const() -> u32 {
            let a: u32 = 10;
            let b: u32 = 20;
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_const");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_multi_const", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "multi-constant arithmetic should produce rules");
        // 10 = 0x0a, 20 = 0x14.
        assert!(
            smt.contains("#x0000000a"),
            "constant 10 should appear as #x0000000a, got: {}",
            &smt[..smt.len().min(500)]
        );
        assert!(
            smt.contains("#x00000014"),
            "constant 20 should appear as #x00000014, got: {}",
            &smt[..smt.len().min(500)]
        );
        // wrapping_add produces bvadd.
        assert!(smt.contains("bvadd"), "wrapping_add should produce bvadd in SMT output");
    });
}

// =============================================================================
// ZST constant (ZeroSized)
// =============================================================================

#[test]
fn test_zst_constant_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst() -> () {
            ()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_zst", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // ZST functions should still produce a valid (possibly minimal) VC.
        assert!(!vc.relations.is_empty(), "ZST function should still produce block relations");
    });
}

// =============================================================================
// Error-path tests: scalar_to_expr returns None for unsupported types
// Part of #2627 (error-path test coverage gaps)
// =============================================================================

/// Float constants hit the catch-all `_ =>` in scalar_to_expr (line 111-113),
/// returning None. The pipeline should handle this gracefully without panicking.
#[test]
fn test_float_constant_returns_none_in_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_float_const() -> f64 {
            3.14
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_float_const");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_float_const", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Float constants are unsupported in CHC — scalar_to_expr returns None.
        // The pipeline should still produce valid VC structure (block relations).
        assert!(
            !vc.relations.is_empty(),
            "float constant function should still produce block relations"
        );
    });
}

/// Non-unit enum constants (enums with data fields) hit the None path at
/// scalar_to_expr line 101-103. Pipeline should not panic.
#[test]
fn test_nonunit_enum_constant_returns_none_in_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_some() -> Option<u32> {
            Some(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_some");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_some", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Option<u32> is a non-unit enum — scalar_to_expr returns None for the
        // constant part. The pipeline should still produce valid VC structure.
        assert!(
            !vc.relations.is_empty(),
            "non-unit enum constant function should still produce block relations"
        );
    });
}

// =============================================================================
// ZST struct with unit field: canonical_zst_expr Datatype construction (#4090)
// =============================================================================

/// `char::try_from(u32)` returns `Result<char, CharTryFromError>` where
/// `CharTryFromError(())` is a ZST struct with 1 field. Its constant form
/// is `ConstantKind::ZeroSized`. `canonical_zst_expr` must produce a Datatype
/// constructor expression (CharTryFromError_mk(true)), not bare Bool(true).
/// Without the fix, Z3 rejects the SMT2 with "unknown constant
/// Err_Result_char_std_char_CharTryFromError (Bool)".
#[test]
fn test_zst_struct_with_unit_field_produces_datatype_constant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MyZstWrapper(());

        pub enum MyResult {
            Ok(u32),
            Err(MyZstWrapper),
        }

        pub fn probe_zst_in_enum() -> MyResult {
            MyResult::Err(MyZstWrapper(()))
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_in_enum");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_zst_in_enum", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let smt = emit_chc(&vc).to_string();

        // The Err constructor must use the Datatype-wrapped ZST, not bare Bool.
        // If canonical_zst_expr falls back to Bool(true), the Err constructor
        // would contain "(Err_MyResult true)" which is a sort mismatch.
        assert!(
            !smt.contains("Err_MyResult true)"),
            "Err constructor must not use bare Bool for ZST struct field (#4090), got:\n{}",
            &smt[..smt.len().min(1000)]
        );
    });
}

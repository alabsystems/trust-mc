// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

//! MIR-driven tests for CHC codegen_expr_signedness.rs.
//!
//! Tests cover:
//! - operand_signedness: signed/unsigned/bool/pointer operand detection
//! - is_signed_integer_op: binary operand signedness agreement
//! - operand_signedness_for_cast: cast-specific pointer treatment
//! - is_pointer_wrapper_adt: Box/Unique/NonNull detection
//!
//! Part of #2016: test coverage for codegen_ay/chc/codegen_expr_signedness.rs (259 lines, 0 tests).

use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::common::*;
use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use crate::codegen_ay::shared::{
    SignednessFallbackKind, signedness_fallback, signedness_fallback_for_arithmetic,
    signedness_fallback_for_binop, signedness_fallback_for_cast_or_coerce,
};

// ═══════════════════════════════════════════════════════════════════════
// Probe source with diverse types for signedness testing
// ═══════════════════════════════════════════════════════════════════════

const SIGNEDNESS_PROBE_SOURCE: &str = r#"
pub fn probe_signed(x: i32, y: i64) -> i32 {
    x + (y as i32)
}

pub fn probe_unsigned(a: u32, b: u64) -> u32 {
    a + (b as u32)
}

pub fn probe_bool_type(flag: bool) -> bool {
    !flag
}

pub fn probe_mixed_sign(s: i32, u: u32) -> i32 {
    s + (u as i32)
}

pub fn probe_ptr_deref(p: &i32) -> i32 {
    *p
}

pub fn probe_raw_ptr(p: *const u32) -> u32 {
    unsafe { *p }
}

pub fn probe_char_type(c: char) -> u32 {
    c as u32
}

pub fn probe_u8_ops(a: u8, b: u8) -> u8 {
    a + b
}

pub fn probe_i16_ops(a: i16, b: i16) -> i16 {
    a + b
}

pub fn probe_usize_ops(a: usize, b: usize) -> usize {
    a + b
}

pub fn probe_isize_ops(a: isize, b: isize) -> isize {
    a + b
}

pub struct GenericNewtype<T>(T);

pub fn probe_generic_newtype_i32(x: GenericNewtype<i32>) -> i32 {
    x.0
}

pub fn probe_generic_newtype_u32(x: GenericNewtype<u32>) -> u32 {
    x.0
}
"#;

/// Build an Operand::Copy for a local by index.
fn copy_local(idx: usize) -> Operand {
    Operand::Copy(Place { local: idx, projection: vec![] })
}

// ═══════════════════════════════════════════════════════════════════════
// operand_signedness tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_operand_signedness_i32_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed", ChcConfig::default());

        // arg 0 (local 1) is i32 → signed
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(true),
            "i32 operand should be signed"
        );
    });
}

#[test]
fn test_operand_signedness_i64_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed", ChcConfig::default());

        // arg 1 (local 2) is i64 → signed
        let operand = copy_local(2);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(true),
            "i64 operand should be signed"
        );
    });
}

#[test]
fn test_operand_signedness_u32_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsigned", ChcConfig::default());

        // arg 0 (local 1) is u32 → unsigned
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(false),
            "u32 operand should be unsigned"
        );
    });
}

#[test]
fn test_operand_signedness_u64_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsigned", ChcConfig::default());

        // arg 1 (local 2) is u64 → unsigned
        let operand = copy_local(2);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(false),
            "u64 operand should be unsigned"
        );
    });
}

#[test]
fn test_operand_signedness_bool_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_type");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_type", ChcConfig::default());

        // arg 0 (local 1) is bool → unsigned
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(false),
            "bool operand should be unsigned"
        );
    });
}

#[test]
fn test_operand_signedness_char_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_char_type");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_char_type", ChcConfig::default());

        // arg 0 (local 1) is char → unsigned
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(false),
            "char operand should be unsigned"
        );
    });
}

#[test]
fn test_operand_signedness_ref_i32_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_deref", ChcConfig::default());

        // arg 0 (local 1) is &i32 → ty_signedness recurses through Ref → signed
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(true),
            "&i32 should recurse to signed"
        );
    });
}

#[test]
fn test_operand_signedness_raw_ptr_u32_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_ptr", ChcConfig::default());

        // arg 0 (local 1) is *const u32 → ty_signedness recurses through RawPtr → unsigned
        let operand = copy_local(1);
        assert_eq!(
            chc_ctx.operand_signedness(&operand),
            Some(false),
            "*const u32 should recurse to unsigned"
        );
    });
}

// ─── Small integer widths ────────────────────────────────────────────

#[test]
fn test_operand_signedness_u8_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u8_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_u8_ops", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(false));
        assert_eq!(chc_ctx.operand_signedness(&copy_local(2)), Some(false));
    });
}

#[test]
fn test_operand_signedness_i16_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_i16_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_i16_ops", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(true));
        assert_eq!(chc_ctx.operand_signedness(&copy_local(2)), Some(true));
    });
}

#[test]
fn test_operand_signedness_usize_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_usize_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_usize_ops", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(false));
    });
}

#[test]
fn test_operand_signedness_isize_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_isize_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_isize_ops", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(true));
    });
}

#[test]
fn test_operand_signedness_generic_newtype_i32_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_generic_newtype_i32");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_generic_newtype_i32", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(true));
    });
}

#[test]
fn test_operand_signedness_generic_newtype_u32_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_generic_newtype_u32");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_generic_newtype_u32", ChcConfig::default());

        assert_eq!(chc_ctx.operand_signedness(&copy_local(1)), Some(false));
    });
}

// ═══════════════════════════════════════════════════════════════════════
// is_signed_integer_op tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_is_signed_integer_op_both_signed_agree() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed", ChcConfig::default());

        // Both i32 and i64 are signed → agree → Some(true)
        let lhs = copy_local(1); // i32
        let rhs = copy_local(2); // i64
        assert_eq!(
            chc_ctx.is_signed_integer_op(&lhs, &rhs),
            Some(true),
            "two signed operands should agree as signed"
        );
    });
}

#[test]
fn test_is_signed_integer_op_both_unsigned_agree() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsigned", ChcConfig::default());

        // Both u32 and u64 are unsigned → agree → Some(false)
        let lhs = copy_local(1); // u32
        let rhs = copy_local(2); // u64
        assert_eq!(
            chc_ctx.is_signed_integer_op(&lhs, &rhs),
            Some(false),
            "two unsigned operands should agree as unsigned"
        );
    });
}

#[test]
fn test_is_signed_integer_op_mixed_returns_none() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mixed_sign");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_mixed_sign", ChcConfig::default());

        // i32 (signed) and u32 (unsigned) → disagree → None
        let lhs = copy_local(1); // i32
        let rhs = copy_local(2); // u32
        assert_eq!(
            chc_ctx.is_signed_integer_op(&lhs, &rhs),
            None,
            "mixed signed/unsigned should return None"
        );
    });
}

/// Regression test: mixed-signedness `is_signed_integer_op` returns None,
/// which causes callers (e.g. codegen_stmt_flatten checked_binop) to use
/// `signedness_fallback` → true (signed). This is the conservative choice:
/// unsigned default would silently invert comparison results for negative values.
///
/// This test documents that the fallback chain is:
///   is_signed_integer_op(i32, u32) → None → signedness_fallback → true (signed)
#[test]
fn test_is_signed_integer_op_mixed_fallback_is_signed() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mixed_sign");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_mixed_sign", ChcConfig::default());

        let lhs = copy_local(1); // i32
        let rhs = copy_local(2); // u32

        // is_signed_integer_op returns None for mixed signedness
        let result = chc_ctx.is_signed_integer_op(&lhs, &rhs);
        assert_eq!(result, None, "mixed signed/unsigned should return None");

        // The caller uses: .unwrap_or_else(|| signedness_fallback("checked_binop"))
        // signedness_fallback always returns true (signed) — verify this chain.
        let effective = result.unwrap_or_else(|| signedness_fallback("mixed_fallback_test"));
        assert!(effective, "mixed-signedness fallback must resolve to signed (true) for soundness");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// operand_signedness_for_cast tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_cast_signedness_ref_i32_is_unsigned() {
    // For cast purposes, &i32 should be unsigned (pointer addresses are unsigned)
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_deref");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_deref", ChcConfig::default());

        let operand = copy_local(1); // &i32
        assert_eq!(
            chc_ctx.operand_signedness_for_cast(&operand),
            Some(false),
            "&i32 should be unsigned for cast (pointer address)"
        );
    });
}

#[test]
fn test_cast_signedness_raw_ptr_u32_is_unsigned() {
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_ptr", ChcConfig::default());

        let operand = copy_local(1); // *const u32
        assert_eq!(
            chc_ctx.operand_signedness_for_cast(&operand),
            Some(false),
            "*const u32 should be unsigned for cast"
        );
    });
}

#[test]
fn test_cast_signedness_i32_still_signed() {
    // Non-pointer signed types remain signed even in cast context
    with_test_ay_ctx_for_source(SIGNEDNESS_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed", ChcConfig::default());

        let operand = copy_local(1); // i32
        assert_eq!(
            chc_ctx.operand_signedness_for_cast(&operand),
            Some(true),
            "i32 should be signed even in cast context"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// is_pointer_wrapper_adt tests (pure function, no MIR needed)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_is_pointer_wrapper_box() {
    assert!(is_pointer_wrapper_adt("alloc::boxed::Box"));
    assert!(is_pointer_wrapper_adt("Box"));
}

#[test]
fn test_is_pointer_wrapper_unique() {
    assert!(is_pointer_wrapper_adt("core::ptr::Unique"));
    assert!(is_pointer_wrapper_adt("Unique"));
}

#[test]
fn test_is_pointer_wrapper_nonnull() {
    assert!(is_pointer_wrapper_adt("core::ptr::NonNull"));
    assert!(is_pointer_wrapper_adt("NonNull"));
}

#[test]
fn test_is_not_pointer_wrapper_vec() {
    assert!(!is_pointer_wrapper_adt("alloc::vec::Vec"));
    assert!(!is_pointer_wrapper_adt("Vec"));
}

#[test]
fn test_is_not_pointer_wrapper_string() {
    assert!(!is_pointer_wrapper_adt("alloc::string::String"));
    assert!(!is_pointer_wrapper_adt("String"));
}

#[test]
fn test_is_not_pointer_wrapper_option() {
    assert!(!is_pointer_wrapper_adt("core::option::Option"));
}

#[test]
fn test_signedness_fallback_returns_signed() {
    // No Mutex needed — only checks return value, not global counter state.
    let result = signedness_fallback("test_context");
    assert!(
        result,
        "signedness_fallback must return true (signed) — unsigned default is unsound for negatives"
    );
}

// test_signedness_fallback_increments_counter removed (Part of #2906).
// Return-value behavior covered by test_signedness_fallback_returns_signed.
// Counter side effect is an implementation detail tested through translate_with_diagnostics.

#[test]
fn test_arg_signedness_or_fallback_ignores_oob_local_without_panic() {
    let bogus = Operand::Copy(Place { local: 40, projection: vec![] });
    let locals: Vec<rustc_public::mir::LocalDecl> = Vec::new();

    let signed = arg_signedness_or_fallback(
        &bogus,
        &locals,
        "oob_signedness_test",
        SignednessFallbackKind::Comparison,
    );

    // Return value proves fallback was used (conservative signed default).
    assert!(signed, "oob local must use conservative signed fallback instead of panicking");
}

#[test]
fn test_signedness_fallback_divrem_defaults_unsigned() {
    let signed = signedness_fallback_for_binop(rustc_public::mir::BinOp::Div, "div_fallback_test");
    assert!(
        !signed,
        "Div/Rem fallback should default unsigned to avoid signed reinterpretation of unsigned values"
    );
}

#[test]
fn test_signedness_fallback_cast_coerce_defaults_unsigned() {
    let signed = signedness_fallback_for_cast_or_coerce("cast_fallback_test");
    assert!(!signed, "cast/coerce fallback should default unsigned (zero-extend)");
}

#[test]
fn test_signedness_fallback_arithmetic_defaults_signed() {
    let signed = signedness_fallback_for_arithmetic("arith_fallback_test");
    assert!(signed, "arithmetic fallback currently defaults signed");
}

/// Verify that `Rem` routes to DivRem (unsigned) like `Div`.
#[test]
fn test_signedness_fallback_binop_rem_defaults_unsigned() {
    let signed = signedness_fallback_for_binop(rustc_public::mir::BinOp::Rem, "rem_fallback_test");
    assert!(!signed, "Rem fallback should default unsigned (same arm as Div)");
}

/// Verify that comparison BinOps route to Comparison kind (signed).
#[test]
fn test_signedness_fallback_binop_comparison_ops_default_signed() {
    use rustc_public::mir::BinOp;
    for (op, name) in [
        (BinOp::Lt, "Lt"),
        (BinOp::Le, "Le"),
        (BinOp::Ge, "Ge"),
        (BinOp::Gt, "Gt"),
        (BinOp::Cmp, "Cmp"),
    ] {
        let signed = signedness_fallback_for_binop(op, &format!("{name}_fallback_test"));
        assert!(
            signed,
            "BinOp::{name} fallback should default signed for correct negative comparisons"
        );
    }
}

/// Verify that arithmetic BinOps route to Arithmetic kind (signed).
#[test]
fn test_signedness_fallback_binop_arithmetic_ops_default_signed() {
    use rustc_public::mir::BinOp;
    for (op, name) in [
        (BinOp::Add, "Add"),
        (BinOp::Sub, "Sub"),
        (BinOp::Mul, "Mul"),
        (BinOp::Shl, "Shl"),
        (BinOp::Offset, "Offset"),
    ] {
        let signed = signedness_fallback_for_binop(op, &format!("{name}_fallback_test"));
        assert!(signed, "BinOp::{name} fallback should default signed (Arithmetic kind)");
    }
}

/// Verify that Eq/Ne BinOps route to Equality kind (sign-agnostic, default unsigned).
/// SMT-LIB `=` is sort-polymorphic and produces identical results regardless of
/// signedness on same-width bitvectors. Part of #3446.
#[test]
fn test_signedness_fallback_binop_equality_ops_sign_agnostic() {
    use rustc_public::mir::BinOp;
    for (op, name) in [(BinOp::Eq, "Eq"), (BinOp::Ne, "Ne")] {
        let signed = signedness_fallback_for_binop(op, &format!("{name}_fallback_test"));
        assert!(
            !signed,
            "BinOp::{name} fallback should default unsigned (Equality kind, sign-agnostic)"
        );
    }
}

/// Verify that Eq/Ne do NOT increment the global signedness_fallback counter.
/// Part of #3446: equality is sign-agnostic, should not cause PROOF demotion.
#[test]
fn test_signedness_fallback_equality_ops_no_counter_increment() {
    use rustc_public::mir::BinOp;

    let before = crate::codegen_ay::shared::get_signedness_fallback_count();

    signedness_fallback_for_binop(BinOp::Eq, "counter_test_eq");
    signedness_fallback_for_binop(BinOp::Ne, "counter_test_ne");

    let after = crate::codegen_ay::shared::get_signedness_fallback_count();

    assert_eq!(
        before, after,
        "Eq/Ne ops must NOT increment the signedness fallback counter (before={before}, after={after})"
    );
}

/// Verify that bitwise BinOps route to Bitwise kind (sign-agnostic, default unsigned).
/// bvand/bvor/bvxor produce identical results regardless of signedness — the choice
/// is arbitrary and does NOT increment the signedness_fallback counter (Part of #3355).
#[test]
fn test_signedness_fallback_binop_bitwise_ops_sign_agnostic() {
    use rustc_public::mir::BinOp;
    for (op, name) in
        [(BinOp::BitAnd, "BitAnd"), (BinOp::BitOr, "BitOr"), (BinOp::BitXor, "BitXor")]
    {
        let signed = signedness_fallback_for_binop(op, &format!("{name}_fallback_test"));
        assert!(
            !signed,
            "BinOp::{name} fallback should default unsigned (Bitwise kind, sign-agnostic)"
        );
    }
}

/// Verify that bitwise ops do NOT increment the global signedness_fallback counter.
/// This is the key property: sign-agnostic operations should not cause PROOF demotion
/// even when type signedness is unknown (Part of #3355).
#[test]
fn test_signedness_fallback_bitwise_ops_no_counter_increment() {
    use rustc_public::mir::BinOp;

    let before = crate::codegen_ay::shared::get_signedness_fallback_count();

    // Call bitwise fallbacks — these should NOT increment the counter.
    signedness_fallback_for_binop(BinOp::BitAnd, "counter_test_and");
    signedness_fallback_for_binop(BinOp::BitOr, "counter_test_or");
    signedness_fallback_for_binop(BinOp::BitXor, "counter_test_xor");

    let after = crate::codegen_ay::shared::get_signedness_fallback_count();

    assert_eq!(
        before, after,
        "Bitwise ops must NOT increment the signedness fallback counter (before={before}, after={after})"
    );
}

/// Verify unchecked arithmetic variants also route to signed fallback.
#[test]
fn test_signedness_fallback_binop_unchecked_variants_default_signed() {
    use rustc_public::mir::BinOp;
    for (op, name) in [
        (BinOp::AddUnchecked, "AddUnchecked"),
        (BinOp::SubUnchecked, "SubUnchecked"),
        (BinOp::MulUnchecked, "MulUnchecked"),
        (BinOp::ShlUnchecked, "ShlUnchecked"),
    ] {
        let signed = signedness_fallback_for_binop(op, &format!("{name}_fallback_test"));
        assert!(signed, "BinOp::{name} fallback should default signed (Arithmetic kind)");
    }
}

/// Shr/ShrUnchecked must default unsigned (Shift kind) — bvashr sign-extends the
/// high bit which produces wrong bit patterns for unsigned operands. Unlike Add/Sub/Mul
/// where signedness only affects overflow, shift right produces different values.
/// Part of #2845.
#[test]
fn test_signedness_fallback_binop_shr_defaults_unsigned() {
    use rustc_public::mir::BinOp;
    let signed = signedness_fallback_for_binop(BinOp::Shr, "shr_fallback_test");
    assert!(
        !signed,
        "BinOp::Shr fallback must default unsigned (logical shift) — \
         bvashr sign-extends, producing wrong bit patterns for unsigned operands"
    );
}

#[test]
fn test_signedness_fallback_binop_shr_unchecked_defaults_unsigned() {
    use rustc_public::mir::BinOp;
    let signed = signedness_fallback_for_binop(BinOp::ShrUnchecked, "shr_unchecked_fallback_test");
    assert!(
        !signed,
        "BinOp::ShrUnchecked fallback must default unsigned (logical shift) — \
         same reasoning as Shr"
    );
}

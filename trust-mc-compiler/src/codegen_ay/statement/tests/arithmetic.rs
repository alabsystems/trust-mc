// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Arithmetic helper and intrinsic pattern tests.
//
// Extracted from regression.rs per #1734.
//
// 25 trivial ay_bindings-only tests deleted per #2312 / #2391.
// These tests only constructed Expr/Sort types and asserted ay library
// properties without calling any production function from arithmetic.rs
// or arithmetic_checks.rs. Deleted categories:
// - overflow_check expression patterns (6 tests)
// - div-by-zero expression patterns (2 tests)
// - shift distance expression patterns (1 test)
// - offset overflow expression patterns (5 tests)
// - atomic operation expression patterns (8 tests)
// - wrapping/checked/saturating/overflowing expression patterns (10 tests)
// - negation overflow expression pattern (1 test)
//
// Remaining 3 tests call StatementCodegen production functions.

use super::*;

fn expr_contains(expr: &Expr, pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    if pred(expr.value()) {
        return true;
    }
    match expr.value() {
        ExprValue::Not(inner) => expr_contains(inner, pred),
        ExprValue::Eq(lhs, rhs)
        | ExprValue::BvAdd(lhs, rhs)
        | ExprValue::BvSub(lhs, rhs)
        | ExprValue::BvMul(lhs, rhs)
        | ExprValue::BvAddNoOverflowSigned(lhs, rhs)
        | ExprValue::BvAddNoOverflowUnsigned(lhs, rhs)
        | ExprValue::BvSubNoOverflowSigned(lhs, rhs)
        | ExprValue::BvSubNoUnderflowUnsigned(lhs, rhs)
        | ExprValue::BvMulNoOverflowSigned(lhs, rhs)
        | ExprValue::BvMulNoOverflowUnsigned(lhs, rhs) => {
            expr_contains(lhs, pred) || expr_contains(rhs, pred)
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            expr_contains(cond, pred)
                || expr_contains(then_expr, pred)
                || expr_contains(else_expr, pred)
        }
        ExprValue::BvSignExtend { expr: inner, .. }
        | ExprValue::BvZeroExtend { expr: inner, .. } => expr_contains(inner, pred),
        _ => false,
    }
}

const WRAPPING_ARITH_SOURCE: &str = r#"
pub fn wrapping_add_probe(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn wrapping_sub_probe(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

pub fn wrapping_mul_probe(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}
"#;

const SIGNED_ARITH_SOURCE: &str = r#"
pub fn signed_checked_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}
"#;

const UNSIGNED_ARITH_SOURCE: &str = r#"
pub fn unsigned_checked_add(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}
"#;

const ARITH_SIGNEDNESS_FALLBACK_SOURCE: &str = r#"
pub fn mixed_signedness_probe(lhs: i8, rhs: u8) -> i8 {
    lhs.wrapping_add(rhs as i8)
}
"#;

// -----------------------------------------------------------------------------
// Tests calling StatementCodegen production functions
// -----------------------------------------------------------------------------

/// Test that width coercion works correctly before overflow check.
/// arithmetic.rs:544-546: coerce_to_match_widths_typed before comparison.
#[test]
fn test_overflow_check_width_coercion() {
    // Different widths: 8-bit and 32-bit operands
    let lhs = Expr::bitvec_const(100u64, 8);
    let rhs = Expr::bitvec_const(50u64, 32);

    // The overflow_check function coerces to match widths first
    let (lhs_coerced, rhs_coerced) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);

    // Both should now be 32-bit (wider operand's width)
    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(32));

    // Now overflow check can be performed on same-width operands
    let no_overflow = lhs_coerced.bvadd_no_overflow_signed(rhs_coerced);
    assert!(no_overflow.sort().is_bool());
}

/// Test shift distance check coerces narrow distance to compare_width.
/// arithmetic.rs:418-425: distance < value_width (valid), NOT valid is violation.
/// The production pattern widens the distance bitvec to compare_width before comparison.
#[test]
fn test_shift_distance_coercion_widens_narrow_distance() {
    // u64 value shifted by u8 distance — distance must be widened to 64-bit
    let value_width = 64u32;
    let distance_width = 8u32;

    let distance = Expr::var("distance", Sort::bitvec(distance_width));
    let compare_width = std::cmp::max(value_width, distance_width); // 64

    // coerce_to_width_typed must widen 8-bit distance to 64-bit
    let distance_coerced = StatementCodegen::coerce_to_width_typed(distance, compare_width, false);
    assert_eq!(
        distance_coerced.sort().bitvec_width(),
        Some(64),
        "8-bit distance must be zero-extended to 64-bit compare_width"
    );

    let width_const = Expr::bitvec_const(value_width as u128, compare_width);
    let valid_distance = distance_coerced.bvult(width_const);
    assert!(valid_distance.sort().is_bool());
}

/// Regression guard: coerce_to_match_widths_typed with Int/BitVec mixed
/// operands converts both to Int sort, which causes bitvec_width() to return
/// None. This proves the precondition for the soundness fix in overflow_check
/// (arithmetic_checks.rs): after coercion, signed Div/Rem INT_MIN check
/// reaches the non-bitvec path where bitvec_width() returns None.
///
/// The fix (Part of #2608) replaced the silent `?` propagation with an explicit
/// `let Some(width) = ... else { warn!(...); return None; }` — making the gap
/// observable via tracing rather than silently unsound.
///
/// Part of #2527 (.expect() elimination campaign soundness audit).
#[test]
fn test_coerce_int_bitvec_mixed_drops_bitvec_width() {
    // Simulate: BigInt-produced Int sort operand + concrete bitvec operand
    let int_lhs = Expr::var("bigint_val", Sort::int());
    let bv_rhs = Expr::bitvec_const(0xFFFFFFFFu64, 32); // -1 in signed i32

    let (coerced_lhs, coerced_rhs) =
        StatementCodegen::coerce_to_match_widths_typed(int_lhs, bv_rhs, true);

    // After coercion: both are Int sort (bv_rhs converted via bv2int)
    assert!(coerced_lhs.sort().is_int(), "Int operand should remain Int after coercion");
    assert!(
        coerced_rhs.sort().is_int(),
        "BitVec operand should be promoted to Int after mixed coercion"
    );

    // bitvec_width() returns None on Int sort — this is the input that triggers
    // the warn! path in overflow_check (fixed by #2608: `let Some(width) = ...
    // else { warn!(...); return None; }` instead of silent `?` propagation).
    assert_eq!(
        coerced_lhs.sort().bitvec_width(),
        None,
        "Int sort has no bitvec_width — overflow_check emits warn! and returns None"
    );
}

/// Test coerce_to_width_typed: signed extension and narrowing (truncation).
/// Exercises the 3 paths in coerce_bitvec_width: identity, extend, extract.
#[test]
fn test_coerce_to_width_typed_signed_extend_and_narrow() {
    // Signed extension: 16-bit → 32-bit
    let narrow = Expr::var("signed_dist", Sort::bitvec(16));
    let widened = StatementCodegen::coerce_to_width_typed(narrow, 32, true);
    assert_eq!(
        widened.sort().bitvec_width(),
        Some(32),
        "16-bit signed value must be sign-extended to 32-bit"
    );

    // Narrowing (truncation): 32-bit → 16-bit
    let wide = Expr::var("wide_dist", Sort::bitvec(32));
    let narrowed = StatementCodegen::coerce_to_width_typed(wide, 16, false);
    assert_eq!(
        narrowed.sort().bitvec_width(),
        Some(16),
        "32-bit value must be extracted/truncated to 16-bit"
    );
}

#[test]
fn test_codegen_unchecked_arith_none_signedness_uses_signed_overflow_guard() {
    with_test_ay_ctx_for_source(ARITH_SIGNEDNESS_FALLBACK_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_signedness_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            None,
            "i8 + u8 must force signedness_fallback"
        );

        let dest = local_place(0);
        let result = codegen.codegen_unchecked_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(7),
            BinOp::Add,
        );
        assert_eq!(result, Some(7));

        let last_violation = codegen.ctx.bmc_vc.violations.last().expect("overflow violation");
        assert!(
            matches!(
                last_violation.condition.value(),
                ExprValue::Not(inner) if matches!(inner.value(), ExprValue::BvAddNoOverflowSigned(..))
            ),
            "fallback should emit signed add overflow guard, got {:?}",
            last_violation.condition.value()
        );
    });
}

#[test]
fn test_codegen_checked_arith_none_signedness_uses_signed_overflow_guard() {
    with_test_ay_ctx_for_source(ARITH_SIGNEDNESS_FALLBACK_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_signedness_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            None,
            "i8 + u8 must force signedness_fallback"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_checked_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(8),
            BinOp::Add,
        );
        assert_eq!(result, Some(8));

        let dest_base = codegen.ssa_base_name(&dest);
        let discrim_base = crate::codegen_ay::names::discrim_name(&dest_base);
        let discrim_expr =
            codegen.current_env.get(discrim_base.as_str()).expect("discriminant in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, discrim_expr).expect("discriminant SSA assignment should exist");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowSigned(..))),
            "checked_arith None-signedness path must use signed add overflow predicate, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowUnsigned(..))),
            "checked_arith None-signedness path must not use unsigned add overflow predicate, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_saturating_arith_none_signedness_uses_signed_overflow_guard() {
    with_test_ay_ctx_for_source(ARITH_SIGNEDNESS_FALLBACK_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_signedness_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            None,
            "i8 + u8 must force signedness_fallback"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_saturating_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(9),
            BinOp::Add,
        );
        assert_eq!(result, Some(9));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen.current_env.get(dest_base.as_str()).expect("destination in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, dest_expr).expect("destination SSA assignment should exist");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowSigned(..))),
            "saturating_arith None-signedness path must use signed add overflow predicate, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowUnsigned(..))),
            "saturating_arith None-signedness path must not use unsigned add overflow predicate, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_overflowing_arith_none_signedness_uses_signed_overflow_guard() {
    with_test_ay_ctx_for_source(ARITH_SIGNEDNESS_FALLBACK_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_signedness_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            None,
            "i8 + u8 must force signedness_fallback"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_overflowing_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(10),
            BinOp::Add,
        );
        assert_eq!(result, Some(10));

        let dest_base = codegen.ssa_base_name(&dest);
        let overflow_base = crate::codegen_ay::names::payload_name(&dest_base);
        let overflow_expr =
            codegen.current_env.get(overflow_base.as_str()).expect("overflow flag in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs = extract_ssa_rhs(added, overflow_expr)
            .expect("overflow flag SSA assignment should exist");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowSigned(..))),
            "overflowing_arith None-signedness path must use signed add overflow predicate, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowUnsigned(..))),
            "overflowing_arith None-signedness path must not use unsigned add overflow predicate, got {:?}",
            rhs.value()
        );
    });
}

// -----------------------------------------------------------------------------
// codegen_wrapping_arith — wrapping arithmetic (Add/Sub/Mul)
// Acceptance criteria: #2411 arithmetic.rs coverage
// -----------------------------------------------------------------------------

#[test]
fn test_codegen_wrapping_arith_add_produces_bvadd() {
    with_test_ay_ctx_for_source(WRAPPING_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "wrapping_add_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_wrapping_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(5),
            BinOp::Add,
        );
        assert_eq!(result, Some(5), "wrapping_arith should return target block");

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen.current_env.get(dest_base.as_str()).expect("destination in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, dest_expr).expect("destination SSA assignment should exist");

        assert!(
            matches!(rhs.value(), ExprValue::BvAdd(..)),
            "wrapping add should produce BvAdd, got {:?}",
            rhs.value()
        );
        // Wrapping should NOT emit overflow violations
        assert!(
            codegen.ctx.bmc_vc.violations.is_empty(),
            "wrapping arithmetic must not emit overflow violations"
        );
    });
}

#[test]
fn test_codegen_wrapping_arith_sub_produces_bvsub() {
    with_test_ay_ctx_for_source(WRAPPING_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "wrapping_sub_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_wrapping_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(6),
            BinOp::Sub,
        );
        assert_eq!(result, Some(6));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen.current_env.get(dest_base.as_str()).expect("destination in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, dest_expr).expect("destination SSA assignment should exist");

        assert!(
            matches!(rhs.value(), ExprValue::BvSub(..)),
            "wrapping sub should produce BvSub, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_wrapping_arith_mul_produces_bvmul() {
    with_test_ay_ctx_for_source(WRAPPING_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "wrapping_mul_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_wrapping_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(7),
            BinOp::Mul,
        );
        assert_eq!(result, Some(7));

        let dest_base = codegen.ssa_base_name(&dest);
        let dest_expr = codegen.current_env.get(dest_base.as_str()).expect("destination in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, dest_expr).expect("destination SSA assignment should exist");

        assert!(
            matches!(rhs.value(), ExprValue::BvMul(..)),
            "wrapping mul should produce BvMul, got {:?}",
            rhs.value()
        );
    });
}

// -----------------------------------------------------------------------------
// Explicit signed/unsigned arithmetic paths
// Acceptance criteria: #2411 arithmetic.rs coverage
// -----------------------------------------------------------------------------

#[test]
fn test_codegen_checked_arith_signed_uses_signed_overflow() {
    with_test_ay_ctx_for_source(SIGNED_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "signed_checked_add");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            Some(true),
            "i32 + i32 must resolve as signed"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_checked_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(11),
            BinOp::Add,
        );
        assert_eq!(result, Some(11));

        let dest_base = codegen.ssa_base_name(&dest);
        let discrim_base = crate::codegen_ay::names::discrim_name(&dest_base);
        let discrim_expr =
            codegen.current_env.get(discrim_base.as_str()).expect("discriminant in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, discrim_expr).expect("discriminant SSA assignment should exist");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowSigned(..))),
            "signed checked_arith must use signed overflow predicate, got {:?}",
            rhs.value()
        );
    });
}

#[test]
fn test_codegen_checked_arith_unsigned_uses_unsigned_overflow() {
    with_test_ay_ctx_for_source(UNSIGNED_ARITH_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unsigned_checked_add");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.is_signed_integer_op(&local_operand(1), &local_operand(2)),
            Some(false),
            "u32 + u32 must resolve as unsigned"
        );

        let dest = local_place(0);
        let before = codegen.ctx.program.commands().len();
        let result = codegen.codegen_checked_arith(
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(12),
            BinOp::Add,
        );
        assert_eq!(result, Some(12));

        let dest_base = codegen.ssa_base_name(&dest);
        let discrim_base = crate::codegen_ay::names::discrim_name(&dest_base);
        let discrim_expr =
            codegen.current_env.get(discrim_base.as_str()).expect("discriminant in env");
        let added = &codegen.ctx.program.commands()[before..];
        let rhs =
            extract_ssa_rhs(added, discrim_expr).expect("discriminant SSA assignment should exist");

        assert!(
            expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowUnsigned(..))),
            "unsigned checked_arith must use unsigned overflow predicate, got {:?}",
            rhs.value()
        );
        assert!(
            !expr_contains(&rhs, &|v| matches!(v, ExprValue::BvAddNoOverflowSigned(..))),
            "unsigned checked_arith must NOT use signed overflow predicate, got {:?}",
            rhs.value()
        );
    });
}

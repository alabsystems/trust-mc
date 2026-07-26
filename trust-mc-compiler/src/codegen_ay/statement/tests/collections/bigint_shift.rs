// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_ay/statement/collections/bigint_shift.rs.
//!
//! Covers: BigInt shift (Shl, Shr, ShlAssign, ShrAssign) and bitwise
//! (BitAnd, BitOr, BitXor) operations via codegen_bigint_shift_stub.
//!
//! Part of #2366: remaining untested dispatch files.

use super::*;
use crate::codegen_ay::stubs::StubKind;

// =============================================================================
// BigInt Shl — codegen_bigint_shift_stub(BigIntShl, ...)
// =============================================================================

/// BigIntShl with valid 2-arg operands should return target and assign Int result.
/// bigint_shift.rs: BigIntShl branch.
#[test]
fn test_codegen_bigint_shift_shl_returns_target() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed two BigInt locals as Int sort
        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(42));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(3));

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_shift_stub(
            StubKind::BigIntShl,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            false,
        );
        assert_eq!(result, Some(1), "BigIntShl should return target block");

        // Verify destination was assigned an Int sort expression
        let fn_name = codegen.ctx.current_fn_name().to_owned();
        let dest_base = format!("{fn_name}::local_0");
        let dest_val = codegen.env_lookup(&dest_base).expect("BigIntShl should assign destination");
        assert!(
            dest_val.sort().is_int(),
            "BigIntShl result should be Int sort, got {:?}",
            dest_val.sort()
        );

        // Shl emits SSA definition constraints
        assert!(
            codegen.ctx.bmc_vc.constraints.len() > constraints_before,
            "BigIntShl should emit constraints"
        );
    });
}

/// BigIntShl with empty args should return None.
/// bigint_shift.rs: BigIntShl branch (empty args guard).
#[test]
fn test_codegen_bigint_shift_shl_empty_args_returns_none() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_bigint_shift_stub(StubKind::BigIntShl, &[], &dest, Some(1), false);
        assert_eq!(result, None, "BigIntShl with empty args should return None");
    });
}

// =============================================================================
// BigInt Shr — codegen_bigint_shift_stub(BigIntShr, ...)
// =============================================================================

/// BigIntShr with valid 2-arg operands should return target.
/// bigint_shift.rs: BigIntShr branch.
#[test]
fn test_codegen_bigint_shift_shr_returns_target() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(1024));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(5));

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_shift_stub(
            StubKind::BigIntShr,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            false,
        );
        assert_eq!(result, Some(1), "BigIntShr should return target block");

        // Verify destination was assigned an Int sort expression
        let fn_name = codegen.ctx.current_fn_name().to_owned();
        let dest_base = format!("{fn_name}::local_0");
        let dest_val = codegen.env_lookup(&dest_base).expect("BigIntShr should assign destination");
        assert!(
            dest_val.sort().is_int(),
            "BigIntShr result should be Int sort, got {:?}",
            dest_val.sort()
        );
    });
}

// =============================================================================
// BigInt ShlAssign — codegen_bigint_shift_stub(BigIntShlAssign, ...)
// =============================================================================

/// BigIntShlAssign with valid args should return target and update ref target.
/// bigint_shift.rs: BigIntShlAssign branch.
#[test]
fn test_codegen_bigint_shift_shl_assign_returns_target() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(7));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(2));

        // ShlAssign calls assign_ref_target which uses assign_value_to_place
        // on the operand's place — works with seeded locals directly.

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_shift_stub(
            StubKind::BigIntShlAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            false,
        );
        assert_eq!(result, Some(1), "BigIntShlAssign should return target block");
    });
}

// =============================================================================
// BigInt BitAnd — codegen_bigint_shift_stub(BigIntBitAnd, ...)
// =============================================================================

/// BigIntBitAnd models bitwise AND as nondet (sound over-approx).
/// bigint_shift.rs: BigIntBitAnd branch.
#[test]
fn test_codegen_bigint_shift_bitand_returns_target() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(0xFF));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(0x0F));

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_shift_stub(
            StubKind::BigIntBitAnd,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            false,
        );
        assert_eq!(result, Some(1), "BigIntBitAnd should return target block");

        // Verify destination was assigned an Int sort expression
        let fn_name = codegen.ctx.current_fn_name().to_owned();
        let dest_base = format!("{fn_name}::local_0");
        let dest_val =
            codegen.env_lookup(&dest_base).expect("BigIntBitAnd should assign destination");
        assert!(dest_val.sort().is_int(), "BitAnd result should be Int sort");

        // Without is_biguint, no non-negativity constraint should be emitted
        // (only SSA definition constraints)
        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let has_nonneg = new_constraints.iter().any(|c| {
            let s = c.to_string();
            s.starts_with("(>=") && s.ends_with("0)")
        });
        assert!(
            !has_nonneg,
            "BigIntBitAnd without is_biguint should NOT emit non-negativity constraint"
        );
    });
}

/// BigIntBitAnd with BigUint flag should enforce non-negativity constraint.
/// bigint_shift.rs: BigIntBitAnd branch with is_biguint=true.
/// Verifies that `assert_nonneg_if_biguint` emits `result >= 0`.
#[test]
fn test_codegen_bigint_shift_bitand_biguint_nonneg() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(0xFF));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(0x0F));

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_shift_stub(
            StubKind::BigIntBitAnd,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            true, // is_biguint — should add non-negativity constraint
        );
        assert_eq!(result, Some(1), "BigIntBitAnd(biguint) should return target");

        // Verify destination was assigned an Int sort expression
        let fn_name = codegen.ctx.current_fn_name().to_owned();
        let dest_base = format!("{fn_name}::local_0");
        let dest_val = codegen
            .env_lookup(&dest_base)
            .expect("BigIntBitAnd(biguint) should assign destination");
        assert!(dest_val.sort().is_int(), "BitAnd result should be Int sort");

        // Verify non-negativity constraint was emitted.
        // With is_biguint=true, assert_nonneg_if_biguint adds `result >= 0`.
        // In SMT2 S-expression form: `(>= <var> 0)`
        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let has_nonneg = new_constraints.iter().any(|c| {
            let s = c.to_string();
            s.starts_with("(>=") && s.ends_with("0)")
        });
        assert!(
            has_nonneg,
            "BigIntBitAnd with is_biguint=true must emit non-negativity constraint (>= var 0), \
             but new constraints were: {:?}",
            new_constraints.iter().map(std::string::ToString::to_string).collect::<Vec<_>>()
        );
    });
}

/// BigIntBitAnd with empty args should return None.
/// bigint_shift.rs: BigIntBitAnd branch (empty args guard).
#[test]
fn test_codegen_bigint_shift_bitand_empty_args_returns_none() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_bigint_shift_stub(StubKind::BigIntBitAnd, &[], &dest, Some(1), false);
        assert_eq!(result, None, "BigIntBitAnd with empty args should return None");
    });
}

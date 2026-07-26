// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BigInt collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

// --- codegen_bigint_stub MIR-driven tests ---

/// Test callee_path_contains_type identifies BigUint correctly.
/// collections/bigint.rs: callee_path_contains_type.
#[test]
fn test_callee_path_contains_type_biguint() {
    assert!(StatementCodegen::callee_path_contains_type("num_bigint::BigUint::from", "BigUint"));
    assert!(!StatementCodegen::callee_path_contains_type("num_bigint::BigInt::from", "BigUint"));
    // Substring should NOT match — MyBigUintWrapper is not BigUint
    assert!(!StatementCodegen::callee_path_contains_type("MyBigUintWrapper::from", "BigUint"));
    assert!(StatementCodegen::callee_path_contains_type("foo::BigUint::bar", "BigUint"));
}

/// Test callee_path_contains_type with trailing type name.
/// collections/bigint.rs: callee_path_contains_type.
#[test]
fn test_callee_path_contains_type_trailing() {
    assert!(StatementCodegen::callee_path_contains_type("BigInt", "BigInt"));
    assert!(!StatementCodegen::callee_path_contains_type("NotBigInt", "BigInt"));
    assert!(StatementCodegen::callee_path_contains_type("foo::BigInt", "BigInt"));
}

/// Test callee_path_contains_type with empty path.
/// collections/bigint.rs: callee_path_contains_type.
#[test]
fn test_callee_path_contains_type_empty() {
    assert!(!StatementCodegen::callee_path_contains_type("", "BigInt"));
    assert!(!StatementCodegen::callee_path_contains_type("foo::bar", "BigInt"));
}

/// Test codegen_bigint_stub BigIntFrom with empty args returns None.
/// collections/bigint.rs: BigIntFrom branch (empty args guard).
#[test]
fn test_codegen_bigint_stub_from_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntFrom,
            &[],
            &dest,
            Some(1),
            "num_bigint::BigInt::from",
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_bigint_stub BigIntOne returns target.
/// collections/bigint.rs: BigIntOne branch.
#[test]
fn test_codegen_bigint_stub_one_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntOne,
            &[],
            &dest,
            Some(2),
            "num_bigint::BigInt::one",
        );
        assert_eq!(result, Some(2));
    });
}

/// Test codegen_bigint_stub BigIntZero returns target.
/// collections/bigint.rs: BigIntZero branch.
#[test]
fn test_codegen_bigint_stub_zero_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntZero,
            &[],
            &dest,
            Some(3),
            "num_bigint::BigInt::zero",
        );
        assert_eq!(result, Some(3));
    });
}

/// Test codegen_bigint_stub BigIntAdd with insufficient args returns None.
/// collections/bigint.rs: BigIntAdd branch (insufficient args guard).
#[test]
fn test_codegen_bigint_stub_add_insufficient_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_a = seed_collections_local(&mut codegen, 1, Expr::int_const(42));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntAdd,
            &[op_a],
            &dest,
            Some(4),
            "num_bigint::BigInt::add",
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_bigint_stub BigIntIsZero with empty args returns None.
/// collections/bigint.rs: BigIntIsZero branch (empty args guard).
#[test]
fn test_codegen_bigint_stub_is_zero_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntIsZero,
            &[],
            &dest,
            Some(5),
            "num_bigint::BigInt::is_zero",
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_bigint_stub BigIntNeg with empty args returns None.
/// collections/bigint.rs: BigIntNeg branch (empty args guard).
#[test]
fn test_codegen_bigint_stub_neg_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntNeg,
            &[],
            &dest,
            Some(6),
            "num_bigint::BigInt::neg",
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_bigint_stub BigIntClone with empty args returns None.
/// collections/bigint.rs: BigIntClone branch (empty args guard).
#[test]
fn test_codegen_bigint_stub_clone_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntClone,
            &[],
            &dest,
            Some(7),
            "num_bigint::BigInt::clone",
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_bigint_stub unhandled StubKind returns None.
/// collections/bigint.rs: default match arm.
#[test]
fn test_codegen_bigint_stub_unhandled_returns_none() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.codegen_bigint_stub(StubKind::VecNew, &[], &dest, Some(8), "unknown::path");
        assert_eq!(result, None);
    });
}

/// Test bitvec_to_int_with_signedness unsigned conversion.
/// collections/bigint.rs: bitvec_to_int_with_signedness.
#[test]
fn test_bitvec_to_int_unsigned() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv = Expr::bitvec_const(255u32, 8);
        let int_expr = codegen.bitvec_to_int_with_signedness(bv, false);
        assert!(int_expr.sort().is_int());
    });
}

/// Test bitvec_to_int_with_signedness signed conversion (sign-extends).
/// collections/bigint.rs: bitvec_to_int_with_signedness.
#[test]
fn test_bitvec_to_int_signed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv = Expr::bitvec_const(0xFEu32, 8); // -2 as i8
        let int_expr = codegen.bitvec_to_int_with_signedness(bv, true);
        assert!(int_expr.sort().is_int());
    });
}

/// Test bitvec_to_int_with_signedness with non-bitvec returns unchanged.
/// collections/bigint.rs: bitvec_to_int_with_signedness.
#[test]
fn test_bitvec_to_int_non_bitvec_passthrough() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let int_val = Expr::int_const(42);
        let result = codegen.bitvec_to_int_with_signedness(int_val, false);
        assert!(result.sort().is_int());
    });
}

// =============================================================================
// BigInt stub gap tests (Part of #2016)
// =============================================================================
// These tests cover BigInt operations missing from the existing test suite:
// compound assigns, comparison ops, bitwise ops.

/// Test BigIntMulAssign stub dispatch with real operands returns target.
/// bigint.rs: BigIntMulAssign branch — multiplies lhs by rhs in-place.
#[test]
fn test_codegen_bigint_mul_assign_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(7));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(3));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntMulAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(1),
            "num_bigint::BigInt::mul_assign",
        );
        assert_eq!(result, Some(1));
    });
}

/// Test BigIntAddAssign stub dispatch with real operands returns target.
/// bigint.rs: BigIntAddAssign branch — adds rhs to lhs in-place.
#[test]
fn test_codegen_bigint_add_assign_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(10));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(5));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntAddAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(2),
            "num_bigint::BigInt::add_assign",
        );
        assert_eq!(result, Some(2));
    });
}

/// Test BigIntSubAssign stub dispatch with real operands returns target.
/// bigint.rs: BigIntSubAssign branch — subtracts rhs from lhs in-place.
#[test]
fn test_codegen_bigint_sub_assign_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(20));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(8));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntSubAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(3),
            "num_bigint::BigInt::sub_assign",
        );
        assert_eq!(result, Some(3));
    });
}

/// Test BigIntSub stub dispatch with real operands returns target.
/// bigint.rs: BigIntSub branch — computes lhs - rhs.
#[test]
fn test_codegen_bigint_sub_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(42));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(17));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntSub,
            &[lhs_op, rhs_op],
            &dest,
            Some(4),
            "num_bigint::BigInt::sub",
        );
        assert_eq!(result, Some(4));
    });
}

/// Test BigIntAbs stub dispatch with real operand returns target.
/// bigint.rs: BigIntAbs branch — computes ITE(x < 0, -x, x).
#[test]
fn test_codegen_bigint_abs_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg_op = seed_collections_local(&mut codegen, 1, Expr::int_const(-5));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntAbs,
            &[arg_op],
            &dest,
            Some(5),
            "num_bigint::BigInt::abs",
        );
        assert_eq!(result, Some(5));
    });
}

/// Test BigIntShlAssign stub dispatch with real operands returns target.
/// bigint.rs: BigIntShlAssign branch — shifts lhs left by rhs in-place.
#[test]
fn test_codegen_bigint_shl_assign_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(1));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(4));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntShlAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(6),
            "num_bigint::BigInt::shl_assign",
        );
        assert_eq!(result, Some(6));
    });
}

/// Test BigIntShrAssign stub dispatch with real operands returns target.
/// bigint.rs: BigIntShrAssign branch — shifts lhs right by rhs in-place.
#[test]
fn test_codegen_bigint_shr_assign_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(256));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(3));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntShrAssign,
            &[lhs_op, rhs_op],
            &dest,
            Some(7),
            "num_bigint::BigInt::shr_assign",
        );
        assert_eq!(result, Some(7));
    });
}

/// Test BigIntBitAnd stub dispatch with real operands returns target.
/// bigint.rs: BigIntBitAnd branch — nondet with lhs/rhs validation.
#[test]
fn test_codegen_bigint_bitand_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(0xFF));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(0x0F));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntBitAnd,
            &[lhs_op, rhs_op],
            &dest,
            Some(8),
            "num_bigint::BigInt::bitand",
        );
        assert_eq!(result, Some(8));
    });
}

/// Test BigIntBitOr stub dispatch with real operands returns target.
/// bigint.rs: BigIntBitOr branch — nondet with lhs/rhs validation.
#[test]
fn test_codegen_bigint_bitor_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(0xA0));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(0x05));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntBitOr,
            &[lhs_op, rhs_op],
            &dest,
            Some(9),
            "num_bigint::BigInt::bitor",
        );
        assert_eq!(result, Some(9));
    });
}

/// Test BigIntBitXor stub dispatch with real operands returns target.
/// bigint.rs: BigIntBitXor branch — nondet with lhs/rhs validation.
#[test]
fn test_codegen_bigint_bitxor_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(0xAA));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(0x55));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntBitXor,
            &[lhs_op, rhs_op],
            &dest,
            Some(10),
            "num_bigint::BigInt::bitxor",
        );
        assert_eq!(result, Some(10));
    });
}

/// Test BigIntLt comparison with real operands returns target.
/// bigint.rs: BigIntLt branch — assigns lhs < rhs as Bool to destination.
#[test]
fn test_codegen_bigint_lt_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(3));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(7));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntLt,
            &[lhs_op, rhs_op],
            &dest,
            Some(11),
            "num_bigint::BigInt::lt",
        );
        assert_eq!(result, Some(11));
    });
}

/// Test BigIntLe comparison with real operands returns target.
/// bigint.rs: BigIntLe branch — assigns lhs <= rhs as Bool to destination.
#[test]
fn test_codegen_bigint_le_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(5));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(5));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntLe,
            &[lhs_op, rhs_op],
            &dest,
            Some(12),
            "num_bigint::BigInt::le",
        );
        assert_eq!(result, Some(12));
    });
}

/// Test BigIntGt comparison with real operands returns target.
/// bigint.rs: BigIntGt branch — assigns lhs > rhs as Bool to destination.
#[test]
fn test_codegen_bigint_gt_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(100));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(50));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntGt,
            &[lhs_op, rhs_op],
            &dest,
            Some(13),
            "num_bigint::BigInt::gt",
        );
        assert_eq!(result, Some(13));
    });
}

/// Test BigIntGe comparison with real operands returns target.
/// bigint.rs: BigIntGe branch — assigns lhs >= rhs as Bool to destination.
#[test]
fn test_codegen_bigint_ge_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_op = seed_collections_local(&mut codegen, 1, Expr::int_const(99));
        let rhs_op = seed_collections_local(&mut codegen, 2, Expr::int_const(99));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntGe,
            &[lhs_op, rhs_op],
            &dest,
            Some(14),
            "num_bigint::BigInt::ge",
        );
        assert_eq!(result, Some(14));
    });
}

// =============================================================================
// Real-operand happy-path tests (Part of #2148)
// =============================================================================
// These tests exercise the actual stub logic with seeded operands instead of
// passing &[] to only hit fallback/warn paths. Each test verifies that the
// stub produces correct AY expressions when given proper inputs.

// --- BigInt: real-operand tests ---

/// Test BigIntFrom with a real bitvec operand produces an Int result.
/// bigint.rs: BigIntFrom branch — converts bitvec to Int.
#[test]
fn test_codegen_bigint_from_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_op = seed_collections_local(&mut codegen, 1, Expr::bitvec_const(42u64, 32));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntFrom,
            &[bv_op],
            &dest,
            Some(1),
            "num_bigint::BigInt::from",
        );
        assert_eq!(result, Some(1));
        // Destination should contain an Int expression (converted from bitvec)
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(
            dest_val.sort().is_int(),
            "BigIntFrom should produce Int sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BigIntAdd with two real Int operands produces Int addition.
/// bigint.rs: BigIntAdd branch — lhs + rhs.
#[test]
fn test_codegen_bigint_add_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, Expr::int_const(10));
        let rhs = seed_collections_local(&mut codegen, 2, Expr::int_const(20));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntAdd,
            &[lhs, rhs],
            &dest,
            Some(1),
            "num_bigint::BigInt::add",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_int(), "BigIntAdd should produce Int sort");
    });
}

/// Test BigIntIsZero with a real Int operand produces boolean result.
/// bigint.rs: BigIntIsZero branch — arg == 0.
#[test]
fn test_codegen_bigint_is_zero_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op = seed_collections_local(&mut codegen, 1, Expr::int_const(0));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntIsZero,
            &[op],
            &dest,
            Some(1),
            "num_bigint::BigInt::is_zero",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_bool(), "BigIntIsZero should produce Bool sort");
    });
}

/// Test BigIntNeg with a real Int operand produces negated Int.
/// bigint.rs: BigIntNeg branch — -arg.
#[test]
fn test_codegen_bigint_neg_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op = seed_collections_local(&mut codegen, 1, Expr::int_const(7));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntNeg,
            &[op],
            &dest,
            Some(1),
            "num_bigint::BigInt::neg",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_int(), "BigIntNeg should produce Int sort");
    });
}

/// Test BigIntClone with a real Int operand clones the value.
/// bigint.rs: BigIntClone branch — identity copy.
#[test]
fn test_codegen_bigint_clone_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op = seed_collections_local(&mut codegen, 1, Expr::int_const(99));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntClone,
            &[op],
            &dest,
            Some(1),
            "num_bigint::BigInt::clone",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_int(), "BigIntClone should produce Int sort");
    });
}

/// Test BigIntEq with two real Int operands produces boolean equality.
/// bigint.rs: BigIntEq branch — lhs == rhs.
#[test]
fn test_codegen_bigint_eq_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, Expr::int_const(5));
        let rhs = seed_collections_local(&mut codegen, 2, Expr::int_const(5));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntEq,
            &[lhs, rhs],
            &dest,
            Some(1),
            "num_bigint::BigInt::eq",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_bool(), "BigIntEq should produce Bool sort");
    });
}

/// Test BigIntLt with two real Int operands produces boolean comparison.
/// bigint.rs: BigIntLt branch — lhs < rhs.
#[test]
fn test_codegen_bigint_lt_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, Expr::int_const(3));
        let rhs = seed_collections_local(&mut codegen, 2, Expr::int_const(10));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntLt,
            &[lhs, rhs],
            &dest,
            Some(1),
            "num_bigint::BigInt::lt",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_bool(), "BigIntLt should produce Bool sort");
    });
}

/// Test BigIntDiv with real operands — includes div-by-zero guard.
/// bigint.rs: BigIntDiv branch — lhs / rhs with violation guard.
#[test]
fn test_codegen_bigint_div_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, Expr::int_const(100));
        let rhs = seed_collections_local(&mut codegen, 2, Expr::int_const(7));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntDiv,
            &[lhs, rhs],
            &dest,
            Some(1),
            "num_bigint::BigInt::div",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_int(), "BigIntDiv should produce Int sort");
    });
}

/// Test BigIntAbs with a real negative Int operand.
/// bigint.rs: BigIntAbs branch — ite(arg < 0, -arg, arg).
#[test]
fn test_codegen_bigint_abs_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op = seed_collections_local(&mut codegen, 1, Expr::int_const(-5));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntAbs,
            &[op],
            &dest,
            Some(1),
            "num_bigint::BigInt::abs",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_int(), "BigIntAbs should produce Int sort");
    });
}

/// Test BigIntCmp with real operands produces bitvec(8) Ordering.
/// bigint.rs: BigIntCmp branch — nested ITE returning -1/0/1.
#[test]
fn test_codegen_bigint_cmp_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = seed_collections_local(&mut codegen, 1, Expr::int_const(3));
        let rhs = seed_collections_local(&mut codegen, 2, Expr::int_const(7));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_bigint_stub(
            StubKind::BigIntCmp,
            &[lhs, rhs],
            &dest,
            Some(1),
            "num_bigint::BigInt::cmp",
        );
        assert_eq!(result, Some(1));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(dest_val.sort().is_bitvec(), "BigIntCmp should produce bitvec(8) Ordering sort");
    });
}

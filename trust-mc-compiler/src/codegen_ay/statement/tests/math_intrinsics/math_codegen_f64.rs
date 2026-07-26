// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven f64 math intrinsic codegen tests.
//!
//! These tests use with_test_ay_ctx_for_source to create a real StatementCodegen,
//! seed the SSA environment with f64 constants, and call the math intrinsic
//! codegen methods directly.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test codegen_math_intrinsic_f64 with symbolic input.
/// Verifies: assigns bv64 destination and emits constraints.
#[test]
fn test_codegen_math_f64_symbolic_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Symbolic f64 — cannot constant-fold, so codegen produces a havoc assignment
        let op_x = seed_math_local(&mut codegen, 1, Expr::var("sym_f64", Sort::bitvec(64)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("sqrtf64", &[op_x], &dest, Some(3));
        assert_eq!(result, Some(3));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("symbolic sqrtf64 should assign destination (havoc)");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64), "sqrtf64 destination should be bv64");
    });
}

/// Test codegen_math_intrinsic_f64 with constant input.
/// Verifies: sqrt(9.0) folds to 3.0 (IEEE 754 bit pattern).
#[test]
fn test_codegen_math_f64_const_fold_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Constant f64: 9.0 — sqrt should fold to 3.0
        let nine_bits = 9.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(nine_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("sqrtf64", &[op_x], &dest, Some(4));
        assert_eq!(result, Some(4));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(3.0f64.to_bits() as u128),
                    "sqrtf64(9.0) should fold to 3.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst, got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with ceil intrinsic (symbolic).
/// Verifies: assigns bv64 destination for symbolic ceilf64 (havoc path).
#[test]
fn test_codegen_math_f64_ceil_symbolic() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_math_local(&mut codegen, 1, Expr::var("sym_f64", Sort::bitvec(64)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("ceilf64", &[op_x], &dest, Some(9));
        assert_eq!(result, Some(9));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("symbolic ceilf64 should assign destination (havoc)");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64), "ceilf64 destination should be bv64");
    });
}

/// Test codegen_math_intrinsic_f64 const-folds cosf64 correctly.
/// Exercises a different try_fold_math_f64 dispatch arm than sqrtf64.
#[test]
fn test_codegen_math_f64_cos_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // cos(0.0) = 1.0 — exact const-fold
        let zero_bits = 0.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(zero_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("cosf64", &[op_x], &dest, Some(15));
        assert_eq!(result, Some(15));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(1.0f64.to_bits() as u128),
                    "cosf64(0.0) should fold to 1.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for cos(0.0), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with powf64 binary fold arm.
/// Verifies: pow(2.0, 10.0) = 1024.0
#[test]
fn test_codegen_math_f64_powf_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let two_bits = 2.0f64.to_bits() as u128;
        let ten_bits = 10.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(two_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(ten_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("powf64", &[op_x, op_y], &dest, Some(20));
        assert_eq!(result, Some(20));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(1024.0f64.to_bits() as u128),
                    "powf64(2.0, 10.0) should fold to 1024.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for pow(2,10), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with minnumf64 binary fold arm.
/// Verifies: min(1.25, 2.75) = 1.25
#[test]
fn test_codegen_math_f64_minnum_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 1.25f64.to_bits() as u128;
        let rhs_bits = 2.75f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f64("minnumf64", &[op_x, op_y], &dest, Some(21));
        assert_eq!(result, Some(21));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(1.25f64.to_bits() as u128),
                    "minnumf64(1.25, 2.75) should fold to 1.25"
                );
            }
            other => panic!("expected folded f64 BitVecConst for min(1.25, 2.75), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with fmaf64 ternary fold arm.
/// Verifies: fma(2.0, 3.0, 4.0) = 10.0
#[test]
fn test_codegen_math_f64_fma_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_ternary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x =
            seed_math_local(&mut codegen, 1, Expr::bitvec_const(2.0f64.to_bits() as u128, 64));
        let op_y =
            seed_math_local(&mut codegen, 2, Expr::bitvec_const(3.0f64.to_bits() as u128, 64));
        let op_z =
            seed_math_local(&mut codegen, 3, Expr::bitvec_const(4.0f64.to_bits() as u128, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f64("fmaf64", &[op_x, op_y, op_z], &dest, Some(22));
        assert_eq!(result, Some(22));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(10.0f64.to_bits() as u128),
                    "fmaf64(2.0, 3.0, 4.0) should fold to 10.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for fma(2,3,4), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with copysignf64 binary fold arm.
/// Exercises: try_fold_math_f64 → copysignf64 → val0.copysign(val1)
/// Verifies: copysign(-5.0, 1.0) = 5.0
#[test]
fn test_codegen_math_f64_copysign_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // copysign(-5.0, 1.0) = 5.0
        let lhs_bits = (-5.0f64).to_bits() as u128;
        let rhs_bits = 1.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f64("copysignf64", &[op_x, op_y], &dest, Some(25));
        assert_eq!(result, Some(25));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(5.0f64.to_bits() as u128),
                    "copysignf64(-5.0, 1.0) should fold to 5.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for copysign, got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with maxnumf64 binary fold arm.
/// Exercises: try_fold_math_f64 → maxnumf64 → val0.max(val1)
/// Verifies: max(1.0, 2.0) = 2.0
#[test]
fn test_codegen_math_f64_maxnum_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // max(1.0, 2.0) = 2.0
        let lhs_bits = 1.0f64.to_bits() as u128;
        let rhs_bits = 2.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f64("maxnumf64", &[op_x, op_y], &dest, Some(26));
        assert_eq!(result, Some(26));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(2.0f64.to_bits() as u128),
                    "maxnumf64(1.0, 2.0) should fold to 2.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for max(1,2), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f64 with powif64 (integer exponent) binary fold arm.
/// Verifies: constant folds 2.0f64.powi(3) = 8.0f64, assigns BitVecConst result.
#[test]
fn test_codegen_math_f64_powif_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // powi(2.0, 3) = 8.0
        let base_bits = 2.0f64.to_bits() as u128;
        let exponent_bits = 3u128; // i32 exponent encoded as 32-bit bitvec
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(base_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(exponent_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f64("powif64", &[op_x, op_y], &dest, Some(27));
        assert_eq!(result, Some(27));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("powif64 should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64), "powif64 destination should be bv64");
        // powif64(2.0, 3) = 8.0 → should fold to BitVecConst with 8.0f64 bit pattern
        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64, "powif64 result should be 64-bit");
                assert_eq!(
                    *value,
                    BigInt::from(8.0f64.to_bits() as u128),
                    "powif64(2.0, 3) should fold to 8.0"
                );
            }
            other => panic!("expected folded f64 BitVecConst for powi(2,3), got {other:?}"),
        }
    });
}

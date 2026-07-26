// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven f32 math intrinsic codegen tests.
//!
//! These tests use with_test_ay_ctx_for_source to create a real StatementCodegen,
//! seed the SSA environment with f32 constants, and call the math intrinsic
//! codegen methods directly.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test codegen_math_intrinsic_f32 with symbolic input (non-foldable).
/// Verifies: returns target, assigns destination with correct bv32 sort,
/// and emits at least one constraint (the havoc assignment).
#[test]
fn test_codegen_math_f32_symbolic_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Symbolic f32 — cannot constant-fold, so codegen produces a havoc assignment
        let op_x = seed_math_local(&mut codegen, 1, Expr::var("sym_f32", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("sqrtf32", &[op_x], &dest, Some(1));
        assert_eq!(result, Some(1));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("symbolic sqrtf32 should assign destination (havoc)");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "sqrtf32 destination should be bv32");
    });
}

/// Test codegen_math_intrinsic_f32 with constant input produces folded result.
/// Verifies: sqrt(4.0) folds to 2.0 (IEEE 754 bit pattern).
#[test]
fn test_codegen_math_f32_const_fold_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Constant f32: 4.0 — sqrt should fold to 2.0
        let four_bits = 4.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(four_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("sqrtf32", &[op_x], &dest, Some(2));
        assert_eq!(result, Some(2));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(2.0f32.to_bits() as u128),
                    "sqrtf32(4.0) should fold to 2.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst, got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with various intrinsic names (symbolic paths).
/// Verifies: assigns bv32 destination for symbolic floorf32 (havoc path).
#[test]
fn test_codegen_math_f32_floor_symbolic() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_math_local(&mut codegen, 1, Expr::var("sym_f32", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("floorf32", &[op_x], &dest, Some(8));
        assert_eq!(result, Some(8));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("symbolic floorf32 should assign destination (havoc)");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "floorf32 destination should be bv32"
        );
    });
}

/// Test codegen_math_intrinsic_f32 const-folds sinf32 correctly.
/// Exercises a different try_fold_math_f32 dispatch arm than sqrtf32.
#[test]
fn test_codegen_math_f32_sin_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // sin(0.0) = 0.0 — exact const-fold
        let zero_bits = 0.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(zero_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("sinf32", &[op_x], &dest, Some(14));
        assert_eq!(result, Some(14));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(0.0f32.sin().to_bits() as u128),
                    "sinf32(0.0) should fold to 0.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for sin(0.0), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with binary intrinsic powf32 (2 operands).
#[test]
fn test_codegen_math_f32_powf_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // powf(2.0, 3.0) = 8.0
        let two_bits = 2.0f32.to_bits() as u128;
        let three_bits = 3.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(two_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(three_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("powf32", &[op_x, op_y], &dest, Some(16));
        assert_eq!(result, Some(16));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(8.0f32.to_bits() as u128),
                    "powf32(2.0, 3.0) should fold to 8.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for pow(2,3), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with powif32 alias (integer exponent path).
/// Verifies: constant folds 2.0f32.powi(3) = 8.0f32, assigns BitVecConst result.
#[test]
fn test_codegen_math_f32_powif_alias_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let two_bits = 2.0f32.to_bits() as u128;
        let exponent_bits = 3u128; // i32 exponent encoded as 32-bit bitvec.
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(two_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(exponent_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_math_intrinsic_f32("powif32", &[op_x, op_y], &dest, Some(17));
        assert_eq!(result, Some(17));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("powif32 should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32), "powif32 destination should be bv32");
        // powif32(2.0, 3) = 8.0 → should fold to BitVecConst with 8.0f32 bit pattern
        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32, "powif32 result should be 32-bit");
                assert_eq!(
                    *value,
                    BigInt::from(8.0f32.to_bits() as u128),
                    "powif32(2.0, 3) should fold to 8.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for powi(2,3), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with copysignf32 binary fold arm.
#[test]
fn test_codegen_math_f32_copysign_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = (-5.0f32).to_bits() as u128;
        let rhs_bits = 1.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f32("copysignf32", &[op_x, op_y], &dest, Some(18));
        assert_eq!(result, Some(18));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                // copysign(-5.0, 1.0) = 5.0 (takes magnitude of first, sign of second)
                assert_eq!(
                    *value,
                    BigInt::from(5.0f32.to_bits() as u128),
                    "copysignf32(-5.0, 1.0) should fold to 5.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for copysign, got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with fmaf32 ternary fold arm.
/// Verifies: fma(2.0, 3.0, 4.0) = 2*3+4 = 10.0
#[test]
fn test_codegen_math_f32_fma_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_ternary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x =
            seed_math_local(&mut codegen, 1, Expr::bitvec_const(2.0f32.to_bits() as u128, 32));
        let op_y =
            seed_math_local(&mut codegen, 2, Expr::bitvec_const(3.0f32.to_bits() as u128, 32));
        let op_z =
            seed_math_local(&mut codegen, 3, Expr::bitvec_const(4.0f32.to_bits() as u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f32("fmaf32", &[op_x, op_y, op_z], &dest, Some(19));
        assert_eq!(result, Some(19));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(10.0f32.to_bits() as u128),
                    "fmaf32(2.0, 3.0, 4.0) should fold to 10.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for fma, got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with minnumf32 binary fold arm.
/// Exercises: try_fold_math_f32 → minnumf32 → val0.min(val1)
#[test]
fn test_codegen_math_f32_minnum_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // min(3.0, 5.0) = 3.0
        let lhs_bits = 3.0f32.to_bits() as u128;
        let rhs_bits = 5.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f32("minnumf32", &[op_x, op_y], &dest, Some(23));
        assert_eq!(result, Some(23));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(3.0f32.to_bits() as u128),
                    "minnumf32(3.0, 5.0) should fold to 3.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for min(3,5), got {other:?}"),
        }
    });
}

/// Test codegen_math_intrinsic_f32 with maxnumf32 binary fold arm.
/// Exercises: try_fold_math_f32 → maxnumf32 → val0.max(val1)
/// Verifies: max(3.0, 5.0) = 5.0
#[test]
fn test_codegen_math_f32_maxnum_const_fold() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // max(3.0, 5.0) = 5.0
        let lhs_bits = 3.0f32.to_bits() as u128;
        let rhs_bits = 5.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_math_intrinsic_f32("maxnumf32", &[op_x, op_y], &dest, Some(24));
        assert_eq!(result, Some(24));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(5.0f32.to_bits() as u128),
                    "maxnumf32(3.0, 5.0) should fold to 5.0"
                );
            }
            other => panic!("expected folded f32 BitVecConst for max(3,5), got {other:?}"),
        }
    });
}

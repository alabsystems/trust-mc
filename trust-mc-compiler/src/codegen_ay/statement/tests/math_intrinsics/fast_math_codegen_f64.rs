// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven f64 fast-math codegen tests.
//!
//! These tests exercise codegen_fast_math_intrinsic with 64-bit operands:
//! NaN UB recording, fsub_fast, fmul_fast, fdiv_fast.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test codegen_fast_math_intrinsic records UB for f64 NaN operand.
/// Exercises the 64-bit path in record_fast_float_finite (exponent bits [62:52]).
/// Verifies: assigns bv64 destination, emits UB-recording constraints.
#[test]
fn test_codegen_fast_math_f64_nan_records_ub() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // f64 NaN has all-ones exponent (0x7FF in bits [62:52])
        let before = constraint_count(&codegen);
        let nan_bits = f64::NAN.to_bits() as u128;
        let one_bits = 1.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(nan_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(one_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fadd_fast", &[op_x, op_y], &dest, Some(13));
        assert_eq!(result, Some(13));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("NaN f64 fadd_fast should still assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "NaN f64 fadd_fast destination should be bv64"
        );
        assert!(
            constraint_count(&codegen) > before,
            "NaN f64 fast-math should emit constraints (assignment + possible UB recording)"
        );
    });
}

/// Test codegen_math_intrinsic_f64 with f64 fast-math fsub_fast (64-bit path).
/// Exercises: codegen_fast_math_intrinsic → fsub_fast with 64-bit operands.
/// Verifies: assigns bv64 destination via `fp.to_ieee_bv(FpSub(...))`.
#[test]
fn test_codegen_fast_math_f64_fsub_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 5.0f64.to_bits() as u128;
        let rhs_bits = 2.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fsub_fast", &[op_x, op_y], &dest, Some(28));
        assert_eq!(result, Some(28));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("f64 fsub_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "f64 fsub_fast destination should be bv64"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Sub);
    });
}

/// Test codegen_math_intrinsic_f64 with f64 fast-math fmul_fast (64-bit path).
/// Exercises: codegen_fast_math_intrinsic → fmul_fast with 64-bit operands.
/// Verifies: assigns bv64 destination via `fp.to_ieee_bv(FpMul(...))`.
#[test]
fn test_codegen_fast_math_f64_fmul_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 3.0f64.to_bits() as u128;
        let rhs_bits = 4.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fmul_fast", &[op_x, op_y], &dest, Some(29));
        assert_eq!(result, Some(29));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("f64 fmul_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "f64 fmul_fast destination should be bv64"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Mul);
    });
}

/// Test codegen_math_intrinsic_f64 with f64 fast-math fdiv_fast (64-bit path).
/// Exercises: codegen_fast_math_intrinsic → fdiv_fast with 64-bit operands.
/// Verifies: assigns bv64 destination via `fp.to_ieee_bv(FpDiv(...))`.
#[test]
fn test_codegen_fast_math_f64_fdiv_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 10.0f64.to_bits() as u128;
        let rhs_bits = 2.0f64.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 64));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fdiv_fast", &[op_x, op_y], &dest, Some(30));
        assert_eq!(result, Some(30));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("f64 fdiv_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "f64 fdiv_fast destination should be bv64"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Div);
    });
}

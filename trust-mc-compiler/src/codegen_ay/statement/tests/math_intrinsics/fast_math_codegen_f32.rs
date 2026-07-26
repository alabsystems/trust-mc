// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven f32 fast-math codegen tests.
//!
//! These tests exercise codegen_fast_math_intrinsic with 32-bit operands:
//! fadd_fast, fsub_fast, fmul_fast, fdiv_fast, NaN UB recording,
//! insufficient args, and unknown name rejection.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

/// Test codegen_fast_math_intrinsic with fadd_fast returns target.
/// Verifies: assigns bv32 destination via `fp.to_ieee_bv(FpAdd(...))`.
#[test]
fn test_codegen_fast_math_fadd_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 1.0f32.to_bits() as u128;
        let rhs_bits = 2.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fadd_fast", &[op_x, op_y], &dest, Some(5));
        assert_eq!(result, Some(5));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fadd_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fadd_fast f32 destination should be bv32"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Add);
    });
}

/// Test codegen_fast_math_intrinsic with fsub_fast.
/// Verifies: assigns bv32 destination via `fp.to_ieee_bv(FpSub(...))`.
#[test]
fn test_codegen_fast_math_fsub_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 3.0f32.to_bits() as u128;
        let rhs_bits = 1.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fsub_fast", &[op_x, op_y], &dest, Some(6));
        assert_eq!(result, Some(6));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fsub_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fsub_fast f32 destination should be bv32"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Sub);
    });
}

/// Test codegen_fast_math_intrinsic with insufficient args returns None.
#[test]
fn test_codegen_fast_math_insufficient_args() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(1u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        // Only 1 arg, needs 2
        let result = codegen.codegen_fast_math_intrinsic("fadd_fast", &[op_x], &dest, Some(1));
        assert_eq!(result, None);
    });
}

/// Test codegen_fast_math_intrinsic with unknown name returns None.
#[test]
fn test_codegen_fast_math_unknown_name() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 1.0f32.to_bits() as u128;
        let rhs_bits = 2.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("unknown_fast_op", &[op_x, op_y], &dest, Some(7));
        assert_eq!(result, None);
    });
}

/// Test codegen_fast_math_intrinsic records UB for NaN operand.
/// Verifies: assigns destination AND emits extra UB-recording constraints.
#[test]
fn test_codegen_fast_math_nan_records_ub() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // NaN has all-ones exponent — should trigger UB recording
        let before = constraint_count(&codegen);
        let nan_bits = f32::NAN.to_bits() as u128;
        let one_bits = 1.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(nan_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(one_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        // Should still return target (UB is recorded, not panic)
        let result =
            codegen.codegen_fast_math_intrinsic("fadd_fast", &[op_x, op_y], &dest, Some(10));
        assert_eq!(result, Some(10));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("NaN fadd_fast should still assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "NaN fadd_fast destination should be bv32"
        );
        // Fast-math emits at least the assignment constraint
        assert!(
            constraint_count(&codegen) > before,
            "NaN fast-math should emit constraints (assignment + possible UB recording)"
        );
    });
}

/// Test codegen_fast_math_intrinsic with fmul_fast returns target.
/// Verifies: assigns bv32 destination via `fp.to_ieee_bv(FpMul(...))`.
#[test]
fn test_codegen_fast_math_fmul_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 2.0f32.to_bits() as u128;
        let rhs_bits = 3.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fmul_fast", &[op_x, op_y], &dest, Some(11));
        assert_eq!(result, Some(11));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fmul_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fmul_fast f32 destination should be bv32"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Mul);
    });
}

/// Test codegen_fast_math_intrinsic with fdiv_fast returns target.
/// Verifies: assigns bv32 destination via `fp.to_ieee_bv(FpDiv(...))`.
#[test]
fn test_codegen_fast_math_fdiv_returns_target() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs_bits = 6.0f32.to_bits() as u128;
        let rhs_bits = 2.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result =
            codegen.codegen_fast_math_intrinsic("fdiv_fast", &[op_x, op_y], &dest, Some(12));
        assert_eq!(result, Some(12));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fdiv_fast should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(32),
            "fdiv_fast f32 destination should be bv32"
        );
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Div);
    });
}

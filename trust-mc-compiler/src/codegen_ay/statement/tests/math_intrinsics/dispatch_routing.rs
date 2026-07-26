// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Intrinsic dispatch routing tests.
//!
//! These tests validate dispatch_math() routing, not just the individual codegen
//! handlers. They verify that the top-level dispatcher correctly routes to
//! fast-math, f32, and f64 codegen paths.
//!
//! Part of #3730: extracted from the math_intrinsics monolith.

use super::*;

#[test]
fn test_dispatch_math_routes_fast_math_intrinsics() {
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
            codegen.dispatch_math("core::intrinsics::fadd_fast", &[op_x, op_y], &dest, Some(31));
        assert_eq!(result, Some(31));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("fast-math dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let rhs = latest_assignment_rhs(&codegen);
        assert_fp_to_ieee_bv_assignment(&rhs, rustc_public::mir::BinOp::Add);
    });
}

#[test]
fn test_dispatch_math_routes_f32_intrinsics() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x =
            seed_math_local(&mut codegen, 1, Expr::bitvec_const(2.5f32.to_bits() as u128, 32));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_math(
            "core::intrinsics::round_ties_even_f32",
            &[op_x],
            &dest,
            Some(32),
        );
        assert_eq!(result, Some(32));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("f32 math dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 32);
                assert_eq!(
                    *value,
                    BigInt::from(2.0f32.to_bits() as u128),
                    "round_ties_even_f32 should fold 2.5 -> 2.0"
                );
            }
            other => panic!("expected folded f32 bitvector constant, got {other:?}"),
        }
    });
}

#[test]
fn test_dispatch_math_routes_f64_intrinsics() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f64_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let op_x =
            seed_math_local(&mut codegen, 1, Expr::bitvec_const(9.0f64.to_bits() as u128, 64));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_math("core::intrinsics::sqrtf64", &[op_x], &dest, Some(33));
        assert_eq!(result, Some(33));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("f64 math dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64));

        let rhs = latest_assignment_rhs(&codegen);
        match rhs.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, 64);
                assert_eq!(
                    *value,
                    BigInt::from(3.0f64.to_bits() as u128),
                    "sqrtf64 should fold 9 -> 3"
                );
            }
            other => panic!("expected folded f64 bitvector constant, got {other:?}"),
        }
    });
}

#[test]
fn test_dispatch_math_unknown_intrinsic_returns_none() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let before = constraint_count(&codegen);

        let op_x = seed_math_local(&mut codegen, 1, Expr::var("sym_f32_unknown", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_math(
            "core::intrinsics::definitely_not_math",
            &[op_x],
            &dest,
            Some(34),
        );
        assert_eq!(result, None);
        assert_eq!(
            constraint_count(&codegen),
            before,
            "unknown math intrinsic should not emit constraints"
        );
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "unknown math intrinsic should not assign destination"
        );
    });
}

#[test]
fn test_dispatch_math_fast_math_name_mismatch_returns_none() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_binary_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let before = constraint_count(&codegen);

        let lhs_bits = 1.0f32.to_bits() as u128;
        let rhs_bits = 2.0f32.to_bits() as u128;
        let op_x = seed_math_local(&mut codegen, 1, Expr::bitvec_const(lhs_bits, 32));
        let op_y = seed_math_local(&mut codegen, 2, Expr::bitvec_const(rhs_bits, 32));
        let dest = Place { local: 0, projection: vec![] };

        // dispatch_math() uses contains("fadd_fast"), entering codegen_fast_math_intrinsic.
        // The suffix mismatch ("fadd_fast_extra" doesn't end with "fadd_fast") causes
        // None return. Finite checks go to property_violations (via record_violation_guarded),
        // not bmc_vc.constraints, so constraint_count is unchanged.
        let result = codegen.dispatch_math(
            "core::intrinsics::fadd_fast_extra",
            &[op_x, op_y],
            &dest,
            Some(35),
        );
        assert_eq!(result, None);
        assert_eq!(
            constraint_count(&codegen),
            before,
            "finite checks use property_violations, not bmc_vc.constraints"
        );
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "fast-math suffix mismatch should not assign destination"
        );
    });
}

#[test]
fn test_dispatch_math_fast_math_requires_two_args() {
    with_test_ay_ctx_for_source(MATH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "math_f32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let before = constraint_count(&codegen);

        let op_x =
            seed_math_local(&mut codegen, 1, Expr::var("sym_f32_fast_math", Sort::bitvec(32)));
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_math("core::intrinsics::fmul_fast", &[op_x], &dest, Some(36));
        assert_eq!(result, None);
        assert_eq!(
            constraint_count(&codegen),
            before,
            "fast-math with insufficient args should exit before emitting constraints"
        );
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "fast-math with insufficient args should not assign destination"
        );
    });
}

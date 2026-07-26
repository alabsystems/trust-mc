// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD arithmetic handler tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_codegen_simd_rem_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_rem(&[local_operand(1), local_operand(2)], &dest, Some(3));
        assert_eq!(result, Some(3));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_rem should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvurem"), "unsigned simd_rem should emit bvurem, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_add_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_add(&[local_operand(1), local_operand(2)], &dest, Some(16));
        assert_eq!(result, Some(16));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_add should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvadd"), "simd_add should emit bvadd, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_sub_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_sub(&[local_operand(1), local_operand(2)], &dest, Some(17));
        assert_eq!(result, Some(17));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_sub should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvsub"), "simd_sub should emit bvsub, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_mul_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_mul(&[local_operand(1), local_operand(2)], &dest, Some(18));
        assert_eq!(result, Some(18));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_mul should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvmul"), "simd_mul should emit bvmul, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_div_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_div(&[local_operand(1), local_operand(2)], &dest, Some(19));
        assert_eq!(result, Some(19));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_div should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvudiv"), "unsigned simd_div should emit bvudiv, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_add_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_add(&[local_operand(1)], &return_dest_place(), Some(33));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_div_signed_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "signed_arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_div(&[local_operand(1), local_operand(2)], &dest, Some(41));
        assert_eq!(result, Some(41));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed simd_div should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvsdiv"), "signed simd_div should emit bvsdiv, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_rem_signed_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "signed_arith_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_rem(&[local_operand(1), local_operand(2)], &dest, Some(42));
        assert_eq!(result, Some(42));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed simd_rem should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvsrem"), "signed simd_rem should emit bvsrem, got {emitted}");
    });
}

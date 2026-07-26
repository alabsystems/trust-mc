// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD bitwise and shift handler tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_codegen_simd_and_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_and(&[local_operand(1), local_operand(2)], &dest, Some(1));
        assert_eq!(result, Some(1));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_and should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvand"), "simd_and should emit bvand, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_shr_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_shr(&[local_operand(1), local_operand(2)], &dest, Some(2));
        assert_eq!(result, Some(2));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_shr should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvashr"), "signed simd_shr should emit bvashr, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_and_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_and(&[local_operand(1)], &return_dest_place(), Some(11));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_or_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_or(&[local_operand(1), local_operand(2)], &dest, Some(13));
        assert_eq!(result, Some(13));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_or should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvor"), "simd_or should emit bvor, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_xor_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_xor(&[local_operand(1), local_operand(2)], &dest, Some(14));
        assert_eq!(result, Some(14));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_xor should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvxor"), "simd_xor should emit bvxor, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_shl_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_shl(&[local_operand(1), local_operand(2)], &dest, Some(15));
        assert_eq!(result, Some(15));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_shl should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvshl"), "simd_shl should emit bvshl, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_or_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_or(&[local_operand(1)], &return_dest_place(), Some(32));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_shr_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_shr(&[local_operand(1)], &return_dest_place(), Some(40));
        assert_eq!(result, None);
    });
}

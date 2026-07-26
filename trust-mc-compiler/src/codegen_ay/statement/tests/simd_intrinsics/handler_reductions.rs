// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD reduction handler tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_codegen_simd_reduce_add_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_add(&[local_operand(1)], &dest, Some(5));
        assert_eq!(result, Some(5));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_add should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvadd"), "simd_reduce_add should emit bvadd fold, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_reduce_any_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_any(&[local_operand(1)], &dest, Some(6));
        assert_eq!(result, Some(6));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_any should assign destination");
        assert!(dest_expr.sort().is_bool(), "simd_reduce_any should produce Bool sort");
    });
}

#[test]
fn test_codegen_simd_reduce_mul_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_mul(&[local_operand(1)], &dest, Some(25));
        assert_eq!(result, Some(25));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_mul should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvmul"), "simd_reduce_mul should emit bvmul fold, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_reduce_and_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_and(&[local_operand(1)], &dest, Some(26));
        assert_eq!(result, Some(26));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_and should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvand"), "simd_reduce_and should emit bvand fold, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_reduce_or_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_or(&[local_operand(1)], &dest, Some(27));
        assert_eq!(result, Some(27));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_or should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvor"), "simd_reduce_or should emit bvor fold, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_reduce_xor_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_xor(&[local_operand(1)], &dest, Some(28));
        assert_eq!(result, Some(28));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_xor should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvxor"), "simd_reduce_xor should emit bvxor fold, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_reduce_min_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_min(&[local_operand(1)], &dest, Some(29));
        assert_eq!(result, Some(29));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_min should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_reduce_min should emit ite comparison fold, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_reduce_max_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_max(&[local_operand(1)], &dest, Some(30));
        assert_eq!(result, Some(30));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_max should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_reduce_max should emit ite comparison fold, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_reduce_all_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_all(&[local_operand(1)], &dest, Some(31));
        assert_eq!(result, Some(31));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_all should assign destination");
        assert!(dest_expr.sort().is_bool(), "simd_reduce_all should produce Bool sort");
    });
}

#[test]
fn test_codegen_simd_reduce_add_empty_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_simd_reduce_add(&[], &return_dest_place(), Some(35));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_reduce_any_empty_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_simd_reduce_any(&[], &return_dest_place(), Some(36));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_reduce_min_signed_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "signed_reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_min(&[local_operand(1)], &dest, Some(47));
        assert_eq!(result, Some(47));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed simd_reduce_min should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "signed simd_reduce_min should emit ite fold, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_reduce_max_signed_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "signed_reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_reduce_max(&[local_operand(1)], &dest, Some(48));
        assert_eq!(result, Some(48));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("signed simd_reduce_max should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "signed simd_reduce_max should emit ite fold, got {emitted}"
        );
    });
}

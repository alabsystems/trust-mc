// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD comparison handler tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_codegen_simd_lt_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_lt(&[local_operand(1), local_operand(2)], &dest, Some(4));
        assert_eq!(result, Some(4));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_lt should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_lt should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_eq_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_eq(&[local_operand(1), local_operand(2)], &dest, Some(20));
        assert_eq!(result, Some(20));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_eq should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_eq should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_ne_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_ne(&[local_operand(1), local_operand(2)], &dest, Some(21));
        assert_eq!(result, Some(21));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_ne should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_ne should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_le_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_le(&[local_operand(1), local_operand(2)], &dest, Some(22));
        assert_eq!(result, Some(22));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_le should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_le should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_gt_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_gt(&[local_operand(1), local_operand(2)], &dest, Some(23));
        assert_eq!(result, Some(23));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_gt should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_gt should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_ge_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_ge(&[local_operand(1), local_operand(2)], &dest, Some(24));
        assert_eq!(result, Some(24));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_ge should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_ge should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_lt_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_lt(&[local_operand(1)], &return_dest_place(), Some(34));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_lt_unsigned_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unsigned_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_lt(&[local_operand(1), local_operand(2)], &dest, Some(43));
        assert_eq!(result, Some(43));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned simd_lt should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "unsigned simd_lt should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_le_unsigned_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unsigned_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_le(&[local_operand(1), local_operand(2)], &dest, Some(44));
        assert_eq!(result, Some(44));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned simd_le should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "unsigned simd_le should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_gt_unsigned_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unsigned_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_gt(&[local_operand(1), local_operand(2)], &dest, Some(45));
        assert_eq!(result, Some(45));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned simd_gt should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "unsigned simd_gt should emit ite mask, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_ge_unsigned_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unsigned_cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_ge(&[local_operand(1), local_operand(2)], &dest, Some(46));
        assert_eq!(result, Some(46));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("unsigned simd_ge should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "unsigned simd_ge should emit ite mask, got {emitted}");
    });
}

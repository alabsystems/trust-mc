// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD lane-operation handler tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_codegen_simd_shuffle_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shuffle_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_shuffle(
            &[local_operand(1), local_operand(2), local_operand(3)],
            &dest,
            Some(7),
        );
        assert_eq!(result, Some(7));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_shuffle should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_shuffle should emit ITE lane selection, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_cast_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_cast(&[local_operand(1)], &dest, Some(8));
        assert_eq!(result, Some(8));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_cast should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U16x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("zero_extend"),
            "unsigned simd_cast widen should emit zero_extend, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_extract_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "extract_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result =
            codegen.codegen_simd_extract(&[local_operand(1), local_operand(2)], &dest, Some(9));
        assert_eq!(result, Some(9));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_extract should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_extract should emit ITE lane selection, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_insert_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "insert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_insert(
            &[local_operand(1), local_operand(2), local_operand(3)],
            &dest,
            Some(10),
        );
        assert_eq!(result, Some(10));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_insert should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("ite"), "simd_insert should emit ITE per-lane, got {emitted}");
    });
}

#[test]
fn test_codegen_simd_shuffle_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shuffle_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_shuffle(
            &[local_operand(1), local_operand(2)],
            &return_dest_place(),
            Some(12),
        );
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_extract_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "extract_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result =
            codegen.codegen_simd_extract(&[local_operand(1)], &return_dest_place(), Some(37));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_insert_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "insert_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let result = codegen.codegen_simd_insert(
            &[local_operand(1), local_operand(2)],
            &return_dest_place(),
            Some(38),
        );
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_cast_empty_args_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_simd_cast(&[], &return_dest_place(), Some(39));
        assert_eq!(result, None);
    });
}

#[test]
fn test_codegen_simd_cast_narrow_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_narrow_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_cast(&[local_operand(1)], &dest, Some(49));
        assert_eq!(result, Some(49));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_cast narrow should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U8x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("extract"),
            "simd_cast narrowing should emit extract, got {emitted}"
        );
    });
}

#[test]
fn test_codegen_simd_cast_signed_widen_returns_target() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_signed_widen_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.codegen_simd_cast(&[local_operand(1)], &dest, Some(50));
        assert_eq!(result, Some(50));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_cast signed widen should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("I16x4"));
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("sign_extend"),
            "simd_cast signed widening should emit sign_extend, got {emitted}"
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD dispatch routing tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

#[test]
fn test_dispatch_simd_routes_bitwise_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_and",
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(51),
        );
        assert_eq!(result, Some(51));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_and dispatch should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));

        let emitted = latest_constraint_text(&codegen);
        assert!(emitted.contains("bvand"), "simd_and dispatch should emit bvand, got {emitted}");
    });
}

#[test]
fn test_dispatch_simd_routes_reduce_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_reduce_add",
            &[local_operand(1)],
            &dest,
            Some(52),
        );
        assert_eq!(result, Some(52));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_add dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("bvadd"),
            "simd_reduce_add dispatch should emit bvadd reduction, got {emitted}"
        );
    });
}

#[test]
fn test_dispatch_simd_non_simd_name_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let before = constraint_count(&codegen);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::rotate_left",
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(53),
        );
        assert_eq!(result, None);
        assert_eq!(
            constraint_count(&codegen),
            before,
            "non-SIMD names should not emit constraints"
        );
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "non-SIMD dispatch should not assign destination"
        );
    });
}

#[test]
fn test_dispatch_simd_unknown_simd_name_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let before = constraint_count(&codegen);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_add_reduce",
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(54),
        );
        assert_eq!(result, None);
        assert_eq!(
            constraint_count(&codegen),
            before,
            "unknown SIMD names should not emit constraints"
        );
        assert!(
            assigned_expr_for_place(&mut codegen, &dest).is_none(),
            "unknown SIMD names should not assign destination"
        );
    });
}

#[test]
fn test_dispatch_simd_routes_shuffle_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shuffle_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_shuffle8",
            &[local_operand(1), local_operand(2), local_operand(3)],
            &dest,
            Some(55),
        );
        assert_eq!(result, Some(55));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_shuffle dispatch should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U32x4"));

        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_shuffle dispatch should emit indexed ITE selection, got {emitted}"
        );
    });
}

#[test]
fn test_dispatch_simd_routes_extract_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "extract_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_extract",
            &[local_operand(1), local_operand(2)],
            &dest,
            Some(56),
        );
        assert_eq!(result, Some(56));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_extract dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(32));

        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("ite"),
            "simd_extract dispatch should emit ITE lane selection, got {emitted}"
        );
    });
}

#[test]
fn test_dispatch_simd_routes_cast_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_cast",
            &[local_operand(1)],
            &dest,
            Some(57),
        );
        assert_eq!(result, Some(57));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_cast dispatch should assign destination");
        assert_eq!(dest_expr.sort().datatype_name(), Some("U16x4"));

        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("zero_extend"),
            "simd_cast widen should emit zero_extend operations, got {emitted}"
        );
    });
}

#[test]
fn test_dispatch_simd_routes_reduce_any_intrinsic() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);
        let dest = return_dest_place();

        let result = codegen.dispatch_simd(
            "core::intrinsics::simd_reduce_any",
            &[local_operand(1)],
            &dest,
            Some(58),
        );
        assert_eq!(result, Some(58));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("simd_reduce_any dispatch should assign destination");
        assert!(dest_expr.sort().is_bool(), "simd_reduce_any destination should be bool");

        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("or"),
            "simd_reduce_any should emit OR aggregation, got {emitted}"
        );
    });
}

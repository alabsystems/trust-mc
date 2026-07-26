// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for place_post_deref.rs — projection handling after deref resolution.
//!
//! Covers:
//! - `apply_post_deref_projections` with Field/ConstantIndex projections (direct)
//! - Downcast + Field via MIR-driven codegen (enum match patterns)
//! - Transparent wrapper bv64 passthrough (NonNull/Unique)
//! - Strict vs lenient mode for multi-constructor enums
//! - Fallthrough vs Unsupported on failure paths
//! - ConstantIndex array select
//!
//! Note: VariantIdx is opaque from rustc_public and cannot be directly constructed.
//! Downcast projection paths are tested via MIR-driven codegen on real enum sources.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::statement::place_post_deref::DerefProjectionResult;

// ─── MIR probe sources ───────────────────────────────────────────────────

/// Enum with variants (multi-constructor) — exercises Downcast + Field
const ENUM_DEREF_PROBE: &str = r#"
pub enum Shape {
    Circle(u32),
    Rect(u32, u32),
}
pub fn match_shape(s: &Shape) -> u32 {
    match s {
        Shape::Circle(r) => *r,
        Shape::Rect(w, _h) => *w,
    }
}
pub fn simple_struct_field(p: &(u32, u32)) -> u32 {
    p.0
}
pub fn array_index(arr: &[u32; 4]) -> u32 {
    arr[0]
}
pub fn enum_field_extract(s: Shape) -> u32 {
    match s {
        Shape::Circle(r) => r,
        Shape::Rect(w, h) => w + h,
    }
}
"#;

fn seed_arg_locals(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("postderef_arg_{local_idx}"), sort));
        }
    }
}

// ─── MIR-driven: enum match exercises Downcast + Field ────────────────

/// Match on a multi-variant enum exercises Downcast projection followed by
/// Field extraction — the core path through apply_post_deref_projections.
#[test]
fn test_enum_match_exercises_downcast_field_mir() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "match_shape");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        // Process all statements — exercises apply_post_deref_projections
        // through Downcast + Field on the multi-variant Shape enum
        let mut stmt_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
                stmt_count += 1;
            }
        }

        // Enum match should have MIR statements (Downcast + Field projections)
        assert!(stmt_count > 0, "match_shape should have MIR statements");
        // Seeded arg should still be in env after codegen
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let arg_base = format!("{fn_name}::local_1");
        assert!(codegen.env_lookup(&arg_base).is_some(), "seeded arg should persist in env");
    });
}

/// Enum field extraction by value (owned) also exercises Downcast + Field
/// through apply_post_deref_projections.
#[test]
fn test_enum_field_extract_owned_mir() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "enum_field_extract");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let mut stmt_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
                stmt_count += 1;
            }
        }

        // Owned enum field extraction should have MIR statements
        assert!(stmt_count > 0, "enum_field_extract should have MIR statements");
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let arg_base = format!("{fn_name}::local_1");
        assert!(codegen.env_lookup(&arg_base).is_some(), "seeded arg should persist in env");
    });
}

// ─── MIR-driven: struct field exercises Field on single-constructor ────

/// Tuple struct field access exercises Field projection on a single-constructor
/// datatype — the lenient path where active_variant defaults to 0.
#[test]
fn test_struct_field_single_constructor_mir() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let mut stmt_count = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
                stmt_count += 1;
            }
        }

        // Struct field access should have MIR statements
        assert!(stmt_count > 0, "simple_struct_field should have MIR statements");
        let fn_name =
            codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
        let arg_base = format!("{fn_name}::local_1");
        assert!(codegen.env_lookup(&arg_base).is_some(), "seeded arg should persist in env");
    });
}

// ─── Expression-level: apply_post_deref_projections directly ──────────

/// Empty projection list returns Success(expr) unchanged.
#[test]
fn test_empty_projections_returns_success() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let expr = Expr::bitvec_const(42u128, 32);
        let result = codegen.apply_post_deref_projections(expr.clone(), &[], false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(e.sort(), expr.sort(), "empty projections should return expr unchanged");
            }
            _ => panic!("empty projections should return Success"),
        }
    });
}

/// Field(0) on bv64 is transparent wrapper passthrough (NonNull/Unique pattern).
#[test]
fn test_transparent_wrapper_bv64_field0_passthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv64_expr = Expr::var("ptr_val", Sort::bitvec(POINTER_WIDTH));
        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result =
            codegen.apply_post_deref_projections(bv64_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                // bv64 Field(0) is transparent — expr unchanged
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(POINTER_WIDTH),
                    "transparent wrapper should preserve bv64 sort"
                );
            }
            _ => panic!("bv64 Field(0) should succeed as transparent wrapper"),
        }
    });
}

/// ConstantIndex on array sort produces array select expression.
#[test]
fn test_constant_index_on_array_selects() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("test_array", arr_sort);
        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 2, min_length: 4, from_end: false }];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert!(e.sort().is_bitvec(), "array select should produce element sort (bv32)");
                assert_eq!(e.sort().bitvec_width(), Some(32));
            }
            _ => panic!("ConstantIndex on array should succeed"),
        }
    });
}

/// ConstantIndex from_end returns Unsupported (not implemented).
#[test]
fn test_constant_index_from_end_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("test_array", arr_sort);
        // Part of #3186: from_end is now supported — actual_offset = min_length - offset = 4 - 1 = 3
        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 1, min_length: 4, from_end: true }];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(expr) => {
                assert!(expr.sort().is_bitvec(), "from_end select should produce bitvec element");
            }
            DerefProjectionResult::Fallthrough => {
                panic!("ConstantIndex from_end should succeed, got Fallthrough")
            }
            DerefProjectionResult::Unsupported => {
                panic!("ConstantIndex from_end should succeed, got Unsupported")
            }
        }
    });
}

/// ConstantIndex on non-array with fallthrough returns Fallthrough.
#[test]
fn test_constant_index_non_array_fallthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv32_expr = Expr::var("not_an_array", Sort::bitvec(32));
        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 0, min_length: 1, from_end: false }];
        let result =
            codegen.apply_post_deref_projections(bv32_expr, &projections, false, true, "test");

        match result {
            DerefProjectionResult::Fallthrough => {}
            _ => panic!("ConstantIndex on non-array with fallthrough should return Fallthrough"),
        }
    });
}

/// Field on datatype with single constructor succeeds without prior Downcast.
#[test]
fn test_field_on_single_constructor_datatype_no_downcast() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create a single-constructor datatype (struct-like)
        let dt_sort =
            struct_sort("Point", [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
        let dt_expr = Expr::var("point_val", dt_sort);

        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result =
            codegen.apply_post_deref_projections(dt_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "field select on Point should yield bv32"
                );
            }
            _ => panic!("Field on single-constructor datatype should succeed"),
        }
    });
}

/// Strict mode: Field on multi-constructor without prior Downcast returns Unsupported.
#[test]
fn test_strict_mode_field_multi_constructor_no_downcast() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Multi-constructor datatype (enum-like)
        let dt_sort = enum_sort(
            "MyEnum",
            [
                ("Variant0", vec![("fld_a", Sort::bitvec(32))]),
                ("Variant1", vec![("fld_b", Sort::bitvec(64))]),
            ],
        );
        let dt_expr = Expr::var("enum_val", dt_sort);

        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result = codegen.apply_post_deref_projections(
            dt_expr,
            &projections,
            true, // strict
            false,
            "test",
        );

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!("strict mode + multi-constructor + no Downcast should be Unsupported"),
        }
    });
}

/// Lenient mode: Field on multi-constructor without prior Downcast defaults to variant 0.
#[test]
fn test_lenient_mode_field_multi_constructor_defaults_variant0() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Multi-constructor datatype (enum-like)
        let dt_sort = enum_sort(
            "MyEnum",
            [
                ("Variant0", vec![("fld_a", Sort::bitvec(32))]),
                ("Variant1", vec![("fld_b", Sort::bitvec(64))]),
            ],
        );
        let dt_expr = Expr::var("enum_val", dt_sort);

        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result = codegen.apply_post_deref_projections(
            dt_expr,
            &projections,
            false, // lenient
            false,
            "test",
        );

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "lenient mode should default to variant 0 field (bv32)"
                );
            }
            _ => panic!("lenient mode + multi-constructor should succeed with variant 0"),
        }
    });
}

/// Field on non-datatype non-bv64 sort returns Unsupported.
#[test]
fn test_field_on_non_datatype_non_bv64_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let int_expr = Expr::var("int_val", Sort::int());
        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result =
            codegen.apply_post_deref_projections(int_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!("Field on non-datatype non-bv64 should return Unsupported"),
        }
    });
}

/// Field on non-datatype with fallthrough returns Fallthrough.
#[test]
fn test_field_on_non_datatype_fallthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let int_expr = Expr::var("int_val", Sort::int());
        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result = codegen.apply_post_deref_projections(
            int_expr,
            &projections,
            false,
            true, // fallthrough
            "test",
        );

        match result {
            DerefProjectionResult::Fallthrough => {}
            _ => panic!("Field on non-datatype with fallthrough should return Fallthrough"),
        }
    });
}

// ─── Gap coverage: paths not tested above ──────────────────────────────
// Part of #2848: cover the 12+ code paths with documented unsound fallback.

/// Downcast on non-datatype, non-bv64 sort returns Unsupported (strict path).
#[test]
fn test_downcast_on_non_datatype_non_bv64_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // bv32 is not bv64 (POINTER_WIDTH), so Downcast fails
        let bv32_expr = Expr::var("small_val", Sort::bitvec(32));
        let projections = vec![ProjectionElem::Downcast(rustc_public::ty::VariantIdx::to_val(0))];
        let result =
            codegen.apply_post_deref_projections(bv32_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!("Downcast on bv32 (non-datatype, non-bv64) should return Unsupported"),
        }
    });
}

/// Downcast on non-datatype, non-bv64 with fallthrough returns Fallthrough.
#[test]
fn test_downcast_on_non_datatype_non_bv64_fallthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv32_expr = Expr::var("small_val", Sort::bitvec(32));
        let projections = vec![ProjectionElem::Downcast(rustc_public::ty::VariantIdx::to_val(0))];
        let result =
            codegen.apply_post_deref_projections(bv32_expr, &projections, false, true, "test");

        match result {
            DerefProjectionResult::Fallthrough => {}
            _ => panic!("Downcast on bv32 with fallthrough should return Fallthrough"),
        }
    });
}

/// Downcast on bv64 (POINTER_WIDTH) variant 0 is transparent passthrough,
/// allowing a subsequent Field(0) to succeed on the same bv64 expr.
#[test]
fn test_downcast_bv64_variant0_transparent_then_field() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // bv64 + Downcast(0) should be transparent, then Field(0) is the wrapper passthrough
        let bv64_expr = Expr::var("ptr_like", Sort::bitvec(POINTER_WIDTH));
        let projections = vec![
            ProjectionElem::Downcast(rustc_public::ty::VariantIdx::to_val(0)),
            ProjectionElem::Field(0, body.arg_locals()[0].ty),
        ];
        let result =
            codegen.apply_post_deref_projections(bv64_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(POINTER_WIDTH),
                    "Downcast(0) + Field(0) on bv64 should preserve pointer width"
                );
            }
            _ => panic!("Downcast(0) + Field(0) on bv64 should succeed as transparent wrapper"),
        }
    });
}

/// Downcast on bv64 with non-zero variant returns Unsupported (only variant 0 is transparent).
#[test]
fn test_downcast_bv64_nonzero_variant_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv64_expr = Expr::var("ptr_like", Sort::bitvec(POINTER_WIDTH));
        let projections = vec![ProjectionElem::Downcast(rustc_public::ty::VariantIdx::to_val(1))];
        let result =
            codegen.apply_post_deref_projections(bv64_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!(
                "Downcast(1) on bv64 should return Unsupported (only variant 0 is transparent)"
            ),
        }
    });
}

/// Strict mode + fallthrough: Field on multi-constructor without Downcast returns Fallthrough
/// (not Unsupported), because fallthrough_on_failure is true.
#[test]
fn test_strict_fallthrough_multi_constructor_no_downcast() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dt_sort = enum_sort(
            "TwoVariant",
            [("A", vec![("fld_x", Sort::bitvec(32))]), ("B", vec![("fld_y", Sort::bitvec(64))])],
        );
        let dt_expr = Expr::var("two_variant", dt_sort);

        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result = codegen.apply_post_deref_projections(
            dt_expr,
            &projections,
            true, // strict
            true, // fallthrough
            "test",
        );

        match result {
            DerefProjectionResult::Fallthrough => {}
            _ => panic!(
                "strict + fallthrough + multi-constructor + no Downcast should return Fallthrough"
            ),
        }
    });
}

/// Field on ZST/marker bv32 sort is a passthrough — expr is returned unchanged.
#[test]
fn test_field_on_zst_marker_bv32_passthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // bv32 is treated as ZST/marker type — Field projection is a no-op
        let bv32_expr = Expr::var("zst_marker", Sort::bitvec(32));
        let projections = vec![ProjectionElem::Field(0, body.arg_locals()[0].ty)];
        let result =
            codegen.apply_post_deref_projections(bv32_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "ZST/marker bv32 Field should return unchanged expr"
                );
                assert_eq!(e.to_string(), "zst_marker", "expr should be unchanged");
            }
            _ => panic!("Field on ZST/marker bv32 should succeed (passthrough)"),
        }
    });
}

/// ConstantIndex on non-array datatype with fld_data extracts backing array, then selects.
#[test]
fn test_constant_index_on_datatype_with_fld_data() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Build a datatype that has fld_data (like Vec or Slice)
        let elem_sort = Sort::bitvec(32);
        let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
        let dt_sort = struct_sort(
            "SliceLike",
            [
                ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
                ("fld_data", data_sort),
            ],
        );
        let dt_name = dt_sort.datatype_name().unwrap().to_string();
        let ctor_name = dt_sort.datatype_default_constructor().unwrap().to_string();
        let data_array =
            Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u128, 32))
                .store(Expr::bitvec_const(0u128, POINTER_WIDTH), Expr::bitvec_const(99u128, 32));
        let dt_expr = Expr::datatype_constructor(
            dt_name,
            ctor_name,
            vec![
                Expr::bitvec_const(0x1000u128, POINTER_WIDTH),
                Expr::bitvec_const(3u128, POINTER_WIDTH),
                data_array,
            ],
            dt_sort,
        );

        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 0, min_length: 1, from_end: false }];
        let result =
            codegen.apply_post_deref_projections(dt_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                // Should have extracted fld_data and selected element at offset 0
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "ConstantIndex on datatype with fld_data should produce element sort"
                );
                let rendered = e.to_string();
                assert!(
                    rendered.contains("select") && rendered.contains("fld_data"),
                    "should select from fld_data: {rendered}"
                );
            }
            _ => panic!("ConstantIndex on datatype with fld_data should succeed"),
        }
    });
}

/// ConstantIndex on non-array sort without fld_data and without fallthrough returns Unsupported.
#[test]
fn test_constant_index_non_array_no_fld_data_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Datatype without fld_data
        let dt_sort =
            struct_sort("NoData", [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
        let dt_expr = Expr::var("no_data_val", dt_sort);
        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 0, min_length: 1, from_end: false }];
        let result =
            codegen.apply_post_deref_projections(dt_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!(
                "ConstantIndex on non-array datatype without fld_data should return Unsupported"
            ),
        }
    });
}

/// Part of #3186: ConstantIndex from_end is now supported — succeeds even with fallthrough enabled.
#[test]
fn test_constant_index_from_end_fallthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_struct_field");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("test_array", arr_sort);
        // from_end: actual_offset = min_length - offset = 4 - 1 = 3
        let projections =
            vec![ProjectionElem::ConstantIndex { offset: 1, min_length: 4, from_end: true }];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, true, "test");

        match result {
            DerefProjectionResult::Success(expr) => {
                assert!(expr.sort().is_bitvec(), "from_end select should produce bitvec element");
            }
            DerefProjectionResult::Fallthrough => {
                panic!("ConstantIndex from_end should succeed, got Fallthrough")
            }
            DerefProjectionResult::Unsupported => {
                panic!("ConstantIndex from_end should succeed, got Unsupported")
            }
        }
    });
}

/// Index projection with env-seeded index local succeeds with array select.
#[test]
fn test_index_projection_with_env_lookup() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed index local (local 2) into env with the name the codegen will look up
        let fn_name = codegen.ctx.current_fn_name().to_string();
        let idx_name = crate::codegen_ay::names::local_name(&fn_name, 2);
        let idx_val = Expr::bitvec_const(1u128, POINTER_WIDTH);
        codegen.env_update(idx_name, idx_val);

        // Build array expression
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("backing_arr", arr_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "Index on array should produce element sort"
                );
                let rendered = e.to_string();
                assert!(rendered.contains("select"), "should contain array select: {rendered}");
            }
            _ => panic!("Index with env-seeded local should succeed"),
        }
    });
}

/// Index projection with narrow BV index (bv16) is zero-extended to POINTER_WIDTH.
#[test]
fn test_index_projection_narrow_bv_zero_extends() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed index local with narrow bv16
        let fn_name = codegen.ctx.current_fn_name().to_string();
        let idx_name = crate::codegen_ay::names::local_name(&fn_name, 2);
        let narrow_idx = Expr::bitvec_const(3u128, 16);
        codegen.env_update(idx_name, narrow_idx);

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("backing_arr", arr_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "narrow-index select should produce element sort"
                );
                let rendered = e.to_string();
                assert!(
                    rendered.contains("zero_extend") || rendered.contains("select"),
                    "narrow index should be zero-extended for array select: {rendered}"
                );
            }
            _ => panic!("Index with narrow bv16 local should succeed via zero-extension"),
        }
    });
}

/// Index projection with non-BV index sort (e.g., Int) returns Unsupported.
#[test]
fn test_index_projection_non_bv_sort_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed index local with non-BV sort (Int)
        let fn_name = codegen.ctx.current_fn_name().to_string();
        let idx_name = crate::codegen_ay::names::local_name(&fn_name, 2);
        codegen.env_update(idx_name, Expr::var("int_idx", Sort::int()));

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("backing_arr", arr_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!("Index with non-BV sort should return Unsupported"),
        }
    });
}

/// Index projection where local is not in env returns Unsupported (or Fallthrough).
#[test]
fn test_index_projection_missing_local_unsupported() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Do NOT seed index local — it won't be found in env or SSA
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("backing_arr", arr_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Unsupported => {}
            _ => panic!("Index with missing local should return Unsupported"),
        }
    });
}

/// Index projection where local is missing with fallthrough returns Fallthrough.
#[test]
fn test_index_projection_missing_local_fallthrough() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
        let arr_expr = Expr::var("backing_arr", arr_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(arr_expr, &projections, false, true, "test");

        match result {
            DerefProjectionResult::Fallthrough => {}
            _ => panic!("Index with missing local + fallthrough should return Fallthrough"),
        }
    });
}

/// Index on non-array datatype with fld_data extracts backing array, then selects.
#[test]
fn test_index_on_datatype_with_fld_data() {
    with_test_ay_ctx_for_source(ENUM_DEREF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed index local
        let fn_name = codegen.ctx.current_fn_name().to_string();
        let idx_name = crate::codegen_ay::names::local_name(&fn_name, 2);
        codegen.env_update(idx_name, Expr::bitvec_const(0u128, POINTER_WIDTH));

        // Build datatype with fld_data (Slice-like)
        let elem_sort = Sort::bitvec(32);
        let data_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
        let dt_sort = struct_sort(
            "SliceForIndex",
            [
                ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
                ("fld_data", data_sort),
            ],
        );
        let dt_expr = Expr::var("slice_val", dt_sort);

        let projections = vec![ProjectionElem::Index(Local::from(2usize))];
        let result =
            codegen.apply_post_deref_projections(dt_expr, &projections, false, false, "test");

        match result {
            DerefProjectionResult::Success(e) => {
                assert_eq!(
                    e.sort().bitvec_width(),
                    Some(32),
                    "Index on datatype with fld_data should produce element sort"
                );
                let rendered = e.to_string();
                assert!(
                    rendered.contains("fld_data"),
                    "should reference fld_data in select: {rendered}"
                );
            }
            _ => panic!("Index on datatype with fld_data should succeed"),
        }
    });
}

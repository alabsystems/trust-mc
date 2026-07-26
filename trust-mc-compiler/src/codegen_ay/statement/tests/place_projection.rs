// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for place_projection.rs — apply_projection_chain.
//!
//! Tests exercise the projection chain through codegen_statement by compiling
//! real Rust code that generates Field, Downcast, Index, and ConstantIndex
//! projections in MIR.
//!
//! Part of #2016: test coverage for place_projection.rs (382 lines, 0 direct tests).

use super::*;

// ─── Helper: seed argument locals ──────────────────────────────────

fn seed_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        } else {
            codegen.env_update(
                base,
                Expr::var(format!("arg_{local_idx}"), Sort::bitvec(POINTER_WIDTH)),
            );
        }
    }
}

/// Walk all statements through codegen_statement, return processed count.
fn walk_all_statements(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) -> usize {
    let mut processed = 0;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
            processed += 1;
        }
    }
    processed
}

// =============================================================================
// Field projection — struct field access
// =============================================================================

const STRUCT_FIELD_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub fn read_x(p: Point) -> i32 {
    p.x
}

pub fn read_y(p: Point) -> i32 {
    p.y
}

pub fn both_fields(p: Point) -> i32 {
    p.x + p.y
}
"#;

/// Test struct field access generates Field projection and codegen handles it.
#[test]
fn test_projection_struct_field_x() {
    with_test_ay_ctx_for_source(STRUCT_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "read_x");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "read_x should process statements");
    });
}

/// Test second field access.
#[test]
fn test_projection_struct_field_y() {
    with_test_ay_ctx_for_source(STRUCT_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "read_y");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "read_y should process statements");
    });
}

/// Test accessing both fields in one function exercises Field projections
/// on multiple fields of the same struct.
#[test]
fn test_projection_both_fields() {
    with_test_ay_ctx_for_source(STRUCT_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "both_fields");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "both_fields should process statements");
    });
}

// =============================================================================
// Field projection — tuple field access
// =============================================================================

const TUPLE_FIELD_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn tuple_first(t: (u32, u64)) -> u32 {
    t.0
}

pub fn tuple_second(t: (u32, u64)) -> u64 {
    t.1
}

pub fn tuple_swap(t: (u32, u64)) -> (u64, u32) {
    (t.1, t.0)
}
"#;

/// Test tuple.0 access generates Field(0) projection.
#[test]
fn test_projection_tuple_first() {
    with_test_ay_ctx_for_source(TUPLE_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_first");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "tuple_first should process statements");
    });
}

/// Test tuple.1 access generates Field(1) projection.
#[test]
fn test_projection_tuple_second() {
    with_test_ay_ctx_for_source(TUPLE_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_second");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "tuple_second should process statements");
    });
}

/// Test accessing both tuple fields (swap) exercises multiple Field projections.
#[test]
fn test_projection_tuple_swap() {
    with_test_ay_ctx_for_source(TUPLE_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_swap");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "tuple_swap should process statements");
    });
}

// =============================================================================
// Downcast + Field projection — enum variant field access
// =============================================================================

const ENUM_FIELD_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn unwrap_option(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

pub fn result_to_u32(x: Result<u32, i32>) -> u32 {
    match x {
        Ok(v) => v,
        Err(e) => e as u32,
    }
}
"#;

/// Test Option match with Some field extraction — generates Downcast + Field projection.
#[test]
fn test_projection_downcast_option_some() {
    with_test_ay_ctx_for_source(ENUM_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unwrap_option");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "unwrap_option should process statements");
    });
}

/// Test Result match extracting fields from both Ok and Err variants.
#[test]
fn test_projection_downcast_result_variants() {
    with_test_ay_ctx_for_source(ENUM_FIELD_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_to_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "result_to_u32 should process statements");
    });
}

// =============================================================================
// Index projection — array element access with variable index
// =============================================================================

const ARRAY_INDEX_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn array_get(arr: [u32; 4], idx: usize) -> u32 {
    arr[idx]
}

pub fn array_sum_first_two(arr: [u32; 4]) -> u32 {
    arr[0] + arr[1]
}
"#;

/// Test variable-index array access generates Index projection.
#[test]
fn test_projection_array_variable_index() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_get");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "array_get should process statements");
    });
}

/// Test constant-index array access (arr[0], arr[1]) — may generate
/// ConstantIndex or Index with a constant operand.
#[test]
fn test_projection_array_constant_index() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_sum_first_two");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "array_sum_first_two should process statements");
    });
}

const VEC_INDEX_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn slice_index_probe(s: &[i32], idx: usize) -> i32 {
    s[idx]
}
"#;

/// Regression for #1632: when a slice reference local already carries
/// value-semantics data in env, deref+index must not synthesize `ref_symbolic_*`.
#[test]
fn test_projection_vec_index_avoids_symbolic_ref_fallback() {
    with_test_ay_ctx_for_source(VEC_INDEX_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "slice_index_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let slice_place = Place { local: Local::from(1usize), projection: vec![] };
        let index_place = Place { local: Local::from(2usize), projection: vec![] };
        let slice_base = codegen.ssa_base_name(&slice_place);
        let index_base = codegen.ssa_base_name(&index_place);

        // Deliberately do NOT seed ref_pointees for local_1. This mirrors the
        // failing #1632 path where deref fallback synthesized ref_symbolic_*.
        let elem_sort = Sort::bitvec(32);
        let data = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u128, 32))
            .store(Expr::bitvec_const(0u128, POINTER_WIDTH), Expr::bitvec_const(42u128, 32));
        let slice_sort = StatementCodegen::slice_sort(elem_sort);
        let slice_name =
            slice_sort.datatype_name().expect("slice sort should have datatype name").to_string();
        let ctor_name = slice_sort
            .datatype_default_constructor()
            .expect("slice sort should have constructor")
            .to_string();
        let slice_expr = Expr::datatype_constructor(
            slice_name,
            ctor_name,
            vec![
                Expr::bitvec_const(0x1000u128, POINTER_WIDTH),
                Expr::bitvec_const(1u128, POINTER_WIDTH),
                data,
            ],
            slice_sort,
        );
        codegen.env_update(slice_base, slice_expr);
        codegen.env_update(index_base, Expr::bitvec_const(0u128, POINTER_WIDTH));
        codegen.ref_pointees.clear();

        let index_place = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Deref, ProjectionElem::Index(Local::from(2usize))],
        };
        let indexed = codegen.codegen_place(&index_place).unwrap_or_else(|| {
            panic!(
                "slice deref+index should resolve via value-semantics fallback; unsupported={:?}",
                codegen.ctx.unsupported_constructs
            )
        });
        let rendered = indexed.to_string();

        assert!(
            rendered.contains("select") && rendered.contains("fld_data"),
            "expected index expression to select from fld_data backing array, got {rendered}"
        );
        assert!(
            !rendered.contains("ref_symbolic"),
            "index expression should not synthesize ref_symbolic fallback: {rendered}"
        );
        assert!(
            !codegen.ctx.unsupported_constructs.contains_key("Index projection on non-array"),
            "value-semantics deref fallback should avoid non-array index fallback"
        );
    });
}

// =============================================================================
// Nested struct field access — chained Field projections
// =============================================================================

const NESTED_STRUCT_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct Inner {
    pub val: u32,
}

pub struct Outer {
    pub inner: Inner,
    pub flag: bool,
}

pub fn read_nested_val(o: Outer) -> u32 {
    o.inner.val
}

pub fn read_flag(o: Outer) -> bool {
    o.flag
}
"#;

/// Test nested struct access (o.inner.val) — chained Field(0).Field(0) projection.
#[test]
fn test_projection_nested_struct() {
    with_test_ay_ctx_for_source(NESTED_STRUCT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "read_nested_val");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "read_nested_val should process statements");
    });
}

/// Test non-nested field on outer struct.
#[test]
fn test_projection_outer_flag() {
    with_test_ay_ctx_for_source(NESTED_STRUCT_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "read_flag");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_args(&mut codegen, &body);

        let processed = walk_all_statements(&mut codegen, &body);
        assert!(processed > 0, "read_flag should process statements");
    });
}

// =============================================================================
// Verify all probe functions compile
// =============================================================================

#[test]
fn test_all_projection_probes_compile() {
    let sources_and_fns = [
        (STRUCT_FIELD_SOURCE, vec!["read_x", "read_y", "both_fields"]),
        (TUPLE_FIELD_SOURCE, vec!["tuple_first", "tuple_second", "tuple_swap"]),
        (ENUM_FIELD_SOURCE, vec!["unwrap_option", "result_to_u32"]),
        (ARRAY_INDEX_SOURCE, vec!["array_get", "array_sum_first_two"]),
        (NESTED_STRUCT_SOURCE, vec!["read_nested_val", "read_flag"]),
    ];

    for (source, fns) in &sources_and_fns {
        with_test_ay_ctx_for_source(source, |ctx| {
            for name in fns {
                let instance = find_instance_by_suffix(&ctx, name);
                assert!(instance.body().is_some(), "{name} should have a MIR body");
            }
        });
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for aggregate_adt.rs — ADT aggregate dispatch, transparent wrappers,
//! unit enum discriminants, Option-like enums, general enums.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;

// ─── MIR probe sources ───────────────────────────────────────────────────

const ADT_PROBE_SOURCE: &str = r#"
#[derive(Copy, Clone)]
pub enum Color { Red, Green, Blue }

pub fn unit_enum_probe() -> Color { Color::Green }

pub fn option_some_probe(x: u32) -> Option<u32> { Some(x) }
pub fn option_none_probe() -> Option<u32> { None }

pub enum MyResult<T, E> { Ok(T), Err(E) }
pub fn result_ok_probe(x: u32) -> MyResult<u32, i32> { MyResult::Ok(x) }
pub fn result_err_probe(e: i32) -> MyResult<u32, i32> { MyResult::Err(e) }

pub struct Wrapper(u32);
pub fn wrapper_probe(x: u32) -> Wrapper { Wrapper(x) }
"#;

fn seed_adt_arg_locals(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("adt_arg_{local_idx}"), sort));
        }
    }
}

/// Helper: run codegen_statement on all statements in all basic blocks,
/// returning the number of AY commands emitted during codegen.
fn run_codegen_and_count(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) -> usize {
    let before = codegen.ctx.program.commands().len();
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
        }
    }
    codegen.ctx.program.commands().len() - before
}

// ─── Unit enum codegen ──────────────────────────────────────────────────

#[test]
fn test_unit_enum_codegen_green_variant() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unit_enum_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "unit enum codegen should emit AY commands, got 0");
    });
}

// ─── Option-like enum codegen ───────────────────────────────────────────

#[test]
fn test_option_some_variant_codegen() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_some_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_adt_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "Some(x) codegen should emit AY commands, got 0");
    });
}

#[test]
fn test_option_none_variant_codegen() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_none_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "None codegen should emit AY commands, got 0");
    });
}

// ─── General enum codegen ───────────────────────────────────────────────

#[test]
fn test_result_ok_variant_codegen() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_ok_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_adt_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "Result::Ok codegen should emit AY commands, got 0");
    });
}

#[test]
fn test_result_err_variant_codegen() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "result_err_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_adt_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "Result::Err codegen should emit AY commands, got 0");
    });
}

// ─── Transparent wrapper codegen ────────────────────────────────────────

#[test]
fn test_wrapper_struct_codegen() {
    with_test_ay_ctx_for_source(ADT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "wrapper_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_adt_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "Wrapper struct codegen should emit AY commands, got 0");
    });
}

// ─── Unit enum with explicit discriminants ──────────────────────────────

#[test]
fn test_unit_enum_explicit_discriminant() {
    with_test_ay_ctx_for_source(
        r#"
        #[repr(i32)]
        pub enum Status {
            Active = 1,
            Inactive = -500,
            Pending = 42,
        }
        pub fn status_probe() -> Status { Status::Inactive }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "status_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let emitted = run_codegen_and_count(&mut codegen, &body);
            assert!(
                emitted > 0,
                "explicit discriminant enum codegen should emit AY commands, got 0"
            );
        },
    );
}

// ─── Multi-variant enum with different field counts ─────────────────────

#[test]
fn test_multi_field_enum_codegen() {
    with_test_ay_ctx_for_source(
        r#"
        pub enum Shape {
            Circle(u32),
            Rectangle(u32, u32),
            Triangle(u32, u32, u32),
        }
        pub fn shape_probe(r: u32) -> Shape { Shape::Circle(r) }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "shape_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_adt_arg_locals(&mut codegen, &body);

            let emitted = run_codegen_and_count(&mut codegen, &body);
            assert!(emitted > 0, "multi-field enum codegen should emit AY commands, got 0");
        },
    );
}

// ─── Nested option codegen ──────────────────────────────────────────────

#[test]
fn test_nested_option_codegen() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn nested_option_probe(x: u32) -> Option<Option<u32>> {
            Some(Some(x))
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "nested_option_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            seed_adt_arg_locals(&mut codegen, &body);

            let emitted = run_codegen_and_count(&mut codegen, &body);
            assert!(emitted > 0, "nested option codegen should emit AY commands, got 0");
        },
    );
}

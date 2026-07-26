// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_assign_ptr.rs — raw pointer deref, Box unwrap,
//! and array index assignment handlers.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;

// ─── MIR probe sources ───────────────────────────────────────────────────

/// Source for raw pointer deref assignment MIR probes.
const PTR_ASSIGN_PROBE: &str = r#"
pub fn raw_ptr_deref_probe(ptr: *mut u32, val: u32) {
    unsafe { *ptr = val; }
}

pub fn raw_ptr_field_probe(ptr: *mut (u32, u32), val: u32) {
    unsafe { (*ptr).0 = val; }
}

pub fn box_deref_assign_probe(mut b: Box<u32>, val: u32) {
    *b = val;
}

pub fn array_index_assign_probe(arr: &mut [u32; 4], idx: usize, val: u32) {
    arr[idx] = val;
}
"#;

fn seed_assign_arg_locals(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("assign_arg_{local_idx}"), sort));
        }
    }
}

/// Helper: run codegen_statement on all statements, return count of AY commands emitted.
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

// ─── Raw pointer deref assignment ───────────────────────────────────────

#[test]
fn test_raw_ptr_deref_assign_mir() {
    with_test_ay_ctx_for_source(PTR_ASSIGN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "raw ptr deref assign codegen should emit AY commands, got 0");
    });
}

// ─── Raw pointer field store ────────────────────────────────────────────

#[test]
fn test_raw_ptr_field_store_mir() {
    with_test_ay_ctx_for_source(PTR_ASSIGN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_field_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "raw ptr field store codegen should emit AY commands, got 0");
    });
}

// ─── Box unwrap assignment ──────────────────────────────────────────────

#[test]
fn test_box_deref_assign_mir() {
    with_test_ay_ctx_for_source(PTR_ASSIGN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "box_deref_assign_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "box deref assign codegen should emit AY commands, got 0");
    });
}

// ─── Array index assignment ─────────────────────────────────────────────

#[test]
fn test_array_index_assign_mir() {
    with_test_ay_ctx_for_source(PTR_ASSIGN_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_index_assign_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_assign_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "array index assign codegen should emit AY commands, got 0");
    });
}

// ─── Box field mutation ─────────────────────────────────────────────────

#[test]
fn test_box_struct_field_mutation_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub struct Pair { pub x: u32, pub y: u32 }
        pub fn box_field_mutation_probe(mut b: Box<Pair>, val: u32) {
            b.x = val;
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "box_field_mutation_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for (idx, local_decl) in body.arg_locals().iter().enumerate() {
                let local_idx = idx + 1;
                let place = local_place(local_idx);
                let base = codegen.ssa_base_name(&place);
                if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
                    codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
                }
            }

            let emitted = run_codegen_and_count(&mut codegen, &body);
            assert!(emitted > 0, "box field mutation codegen should emit AY commands, got 0");
        },
    );
}

// ─── Multiple pointer writes in sequence ────────────────────────────────

#[test]
fn test_multi_ptr_write_sequence_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn multi_write_probe(ptr: *mut u32) {
            unsafe {
                *ptr = 10;
                *ptr = 20;
            }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "multi_write_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for (idx, local_decl) in body.arg_locals().iter().enumerate() {
                let local_idx = idx + 1;
                let place = local_place(local_idx);
                let base = codegen.ssa_base_name(&place);
                if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
                    codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
                }
            }

            let emitted = run_codegen_and_count(&mut codegen, &body);
            assert!(emitted > 0, "multi ptr write codegen should emit AY commands, got 0");
        },
    );
}

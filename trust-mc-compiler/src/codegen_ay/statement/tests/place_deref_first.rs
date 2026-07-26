// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for place_deref_first.rs — leading-deref resolution for place translation.
//!
//! Covers:
//! - `codegen_place_deref_first` entry point
//! - ref_pointees resolution path (direct, derived, synthesized)
//! - heap_pointees resolution path (direct key, ptr_source_map)
//! - Raw pointer memory load (byte-offset field projections)
//! - DerefFirstResult enum variants (NotDeref, Resolved, Unresolved, Unsupported)
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;

// ─── MIR probe sources ───────────────────────────────────────────────────

const DEREF_FIRST_PROBE: &str = r#"
pub fn ref_deref_probe(r: &u32) -> u32 { *r }

pub fn ref_field_deref_probe(r: &(u32, u32)) -> u32 { r.0 }

pub fn raw_ptr_deref_probe(ptr: *const u32) -> u32 { unsafe { *ptr } }

pub fn raw_ptr_field_deref_probe(ptr: *const (u32, u32)) -> u32 { unsafe { (*ptr).0 } }

pub fn box_deref_probe(b: Box<u32>) -> u32 { *b }

pub fn no_deref_probe(x: u32) -> u32 { x }

#[derive(Copy, Clone)]
pub struct CopyPair { pub x: u32, pub y: u32 }

pub fn raw_ptr_non_bitvec_copy_probe(pair: CopyPair) -> CopyPair {
    let ptr: *const CopyPair = &pair as *const CopyPair;
    unsafe { *ptr }
}

pub fn raw_ptr_non_bitvec_missing_store_probe(ptr: *const CopyPair) -> CopyPair {
    unsafe { *ptr }
}
"#;

fn seed_deref_arg_locals(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("deref_arg_{local_idx}"), sort));
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

// ─── Reference deref (ref_pointees path) ────────────────────────────────

#[test]
fn test_ref_deref_basic_mir() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "ref deref codegen should emit AY commands, got 0");
    });
}

#[test]
fn test_ref_field_deref_mir() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_field_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "ref field deref codegen should emit AY commands, got 0");
    });
}

// ─── Raw pointer deref (memory load path) ───────────────────────────────

#[test]
fn test_raw_ptr_deref_mir() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "raw ptr deref codegen should emit AY commands, got 0");
    });
}

#[test]
fn test_raw_ptr_field_deref_mir() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_field_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "raw ptr field deref codegen should emit AY commands, got 0");
    });
}

#[test]
fn test_raw_ptr_non_bitvec_deref_recovers_symbolic_value() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_non_bitvec_copy_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        // Regression for #2599: `&pair as *const _` stores a non-bitvec value
        // symbolically in memory; deref should recover that symbolic value instead
        // of calling load_memory_bytes and panicking fail-closed.
        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "raw ptr non-bitvec deref should emit AY commands, got 0");
    });
}

#[test]
fn test_raw_ptr_non_bitvec_deref_missing_store_uses_fallback() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "raw_ptr_non_bitvec_missing_store_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);
        crate::codegen_ay::take_unsupported_construct_fallback_count();

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(
            emitted > 0,
            "raw ptr non-bitvec deref without tracked store should still emit AY commands"
        );
        assert!(
            crate::codegen_ay::take_unsupported_construct_fallback_count() > 0,
            "missing symbolic store should record a fallback instead of panicking"
        );
    });
}

// ─── Box deref (heap_pointees path) ─────────────────────────────────────

#[test]
fn test_box_deref_mir() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "box_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        let emitted = run_codegen_and_count(&mut codegen, &body);
        assert!(emitted > 0, "box deref codegen should emit AY commands, got 0");
    });
}

// ─── No-deref path (DerefFirstResult::NotDeref) ─────────────────────────

#[test]
fn test_no_deref_place_not_deref_result() {
    with_test_ay_ctx_for_source(DEREF_FIRST_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "no_deref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_deref_arg_locals(&mut codegen, &body);

        // A simple local place has no Deref projection —
        // codegen_place should resolve it via env lookup, not deref path.
        let place = local_place(1);
        let result = codegen.codegen_place(&place);
        assert!(result.is_some(), "non-deref place should resolve via env lookup");
    });
}

// ─── Nested reference deref ─────────────────────────────────────────────

#[test]
fn test_double_ref_deref_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn double_ref_probe(r: &&u32) -> u32 { **r }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "double_ref_probe");
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
            assert!(emitted > 0, "double ref deref codegen should emit AY commands, got 0");
        },
    );
}

// ─── Struct field through reference ─────────────────────────────────────

#[test]
fn test_ref_struct_field_deref_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub struct Point { pub x: u32, pub y: u32 }
        pub fn ref_struct_field_probe(p: &Point) -> u32 { p.x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ref_struct_field_probe");
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
            assert!(emitted > 0, "ref struct field deref codegen should emit AY commands, got 0");
        },
    );
}

// ─── Mutable reference deref ────────────────────────────────────────────

#[test]
fn test_mut_ref_deref_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn mut_ref_probe(r: &mut u32) -> u32 { *r }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "mut_ref_probe");
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
            assert!(emitted > 0, "mut ref deref codegen should emit AY commands, got 0");
        },
    );
}

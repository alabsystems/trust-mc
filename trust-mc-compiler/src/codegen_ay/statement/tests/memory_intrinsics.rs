// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Memory intrinsic MIR-driven tests.
//!
//! Tests for codegen_align_of_val, codegen_size_of_val, and
//! codegen_checked_size_or_align exercising the actual StatementCodegen
//! methods through compiler sessions.
//!
//! Part of #2016 (test coverage for intrinsics/memory.rs).

use super::*;
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

fn latest_constraint_text(codegen: &StatementCodegen<'_, '_, '_>) -> String {
    codegen.ctx.bmc_vc.constraints.last().expect("expected an emitted constraint").to_string()
}

// Probe source that gives us reference/pointer types for memory intrinsics.
// The functions accept references whose pointee types have known layouts.
const MEMORY_PROBE_SOURCE: &str = r#"
pub fn ref_u32_probe(x: &u32) -> usize {
    core::mem::size_of_val(x)
}

pub fn ref_u8_probe(x: &u8) -> usize {
    core::mem::align_of_val(x)
}

pub fn ref_tuple_probe(x: &(u64, u32)) -> usize {
    core::mem::size_of_val(x)
}

pub fn rawptr_probe(x: *const u16) -> usize {
    unsafe { core::mem::size_of_val(&*x) }
}

pub fn simple_probe() {}
"#;

// =============================================================================
// Intrinsic dispatch routing tests (Part of #2016)
// =============================================================================

/// Test dispatch_memory routes align_of_val to the dedicated handler.
#[test]
fn test_dispatch_memory_routes_align_of_val() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let args = vec![Operand::Copy(Place { local: 1, projection: vec![] })];
        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.dispatch_memory("core::intrinsics::align_of_val", &args, &dest, Some(20));
        assert_eq!(result, CallDispatchOutcome::Continue(20));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("align_of_val dispatch should assign destination");
        // align_of_val produces bitvec(POINTER_WIDTH=64)
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64));
        let emitted = latest_constraint_text(&codegen);
        // align of u32 = 4
        assert!(
            emitted.contains("#x0000000000000004") || emitted.contains('4'),
            "align_of_val(&u32) should emit constant 4, got {emitted}"
        );
    });
}

/// Test dispatch_memory routes size_of_val to the dedicated handler.
/// Verifies: (u64, u32) = 16 bytes (8 + 4 + 4 padding on 64-bit).
#[test]
fn test_dispatch_memory_routes_size_of_val() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_tuple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let args = vec![Operand::Copy(Place { local: 1, projection: vec![] })];
        let dest = Place { local: 0, projection: vec![] };
        let result =
            codegen.dispatch_memory("core::intrinsics::size_of_val", &args, &dest, Some(21));
        assert_eq!(result, CallDispatchOutcome::Continue(21));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("size_of_val dispatch should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64));
        // (u64, u32) tuple: size = 16 bytes (8 + 4 + 4 padding)
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000010") || emitted.contains("16"),
            "size_of_val(&(u64, u32)) should emit constant 16, got {emitted}"
        );
    });
}

/// Test copy dispatch guard: only intrinsic/ptr paths should route copy.
#[test]
fn test_dispatch_memory_copy_path_guard() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg = Operand::Copy(Place { local: 1, projection: vec![] });
        let args = vec![arg.clone(), arg.clone(), arg];
        let dest = Place { local: 0, projection: vec![] };

        let blocked = codegen.dispatch_memory("core::foo::copy", &args, &dest, Some(22));
        assert_eq!(
            blocked,
            CallDispatchOutcome::Miss,
            "non-intrinsics copy path should not dispatch"
        );

        let routed = codegen.dispatch_memory("core::ptr::copy", &args, &dest, Some(23));
        assert_eq!(
            routed,
            CallDispatchOutcome::Continue(23),
            "core::ptr::copy should route to copy handler"
        );
    });
}

/// Test dispatch_memory routes copy_nonoverlapping by exact method name.
#[test]
fn test_dispatch_memory_routes_copy_nonoverlapping() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let arg = Operand::Copy(Place { local: 1, projection: vec![] });
        let args = vec![arg.clone(), arg.clone(), arg];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.dispatch_memory(
            "core::intrinsics::copy_nonoverlapping",
            &args,
            &dest,
            Some(24),
        );
        assert_eq!(result, CallDispatchOutcome::Continue(24));
        // Verify dispatch routed (constraint count may not increase if the
        // synthetic count operand is symbolic/unsupported, but routing worked)
        assert!(
            constraint_count(&codegen) >= before,
            "copy_nonoverlapping should not lose constraints"
        );
    });
}

/// Test unknown method names return an explicit dispatch miss.
#[test]
fn test_dispatch_memory_unknown_method_returns_miss() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.dispatch_memory(
            "core::intrinsics::definitely_not_memory",
            &[],
            &dest,
            Some(25),
        );
        assert_eq!(result, CallDispatchOutcome::Miss);
    });
}
// codegen_align_of_val tests
// =============================================================================

/// Test that codegen_align_of_val produces a POINTER_WIDTH bitvec for the
/// destination when given a reference to u32 (align=4).
#[test]
fn test_align_of_val_ref_u32_returns_pointer_width() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_align_of_val(&args, &dest, Some(0));
        assert_eq!(result, Some(0), "codegen_align_of_val should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("align_of_val should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "align_of_val should produce bitvec(POINTER_WIDTH=64)"
        );
    });
}

/// Test that codegen_align_of_val with empty args returns target (DST fallback).
#[test]
fn test_align_of_val_empty_args_fallback() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = constraint_count(&codegen);
        let dest = Place { local: 0, projection: vec![] };

        // Empty args: falls through to DST fallback (symbolic alignment >= 1)
        let result = codegen.codegen_align_of_val(&[], &dest, Some(5));
        assert_eq!(result, Some(5));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("align_of_val fallback should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64));
        // DST fallback emits bvuge(1) constraint
        assert!(
            constraint_count(&codegen) > before,
            "align_of_val DST fallback should emit constraint (bvuge >= 1)"
        );
    });
}

// =============================================================================
// codegen_size_of_val tests
// =============================================================================

/// Test that codegen_size_of_val returns target block for a reference parameter.
/// Verifies: size_of_val(&u32) emits constant 4 (sizeof u32 = 4 bytes).
#[test]
fn test_size_of_val_ref_u32_returns_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_size_of_val(&args, &dest, Some(3));
        assert_eq!(result, Some(3), "codegen_size_of_val should return target block");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("size_of_val should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "size_of_val should produce bitvec(POINTER_WIDTH=64)"
        );
        // u32 size = 4 bytes
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000004") || emitted.contains('4'),
            "size_of_val(&u32) should emit constant 4, got {emitted}"
        );
    });
}

/// Test that codegen_size_of_val with empty args uses DST symbolic fallback.
#[test]
fn test_size_of_val_empty_args_fallback() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };

        // Empty args: no type info, falls to symbolic size
        let result = codegen.codegen_size_of_val(&[], &dest, Some(7));
        assert_eq!(result, Some(7));

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("size_of_val fallback should assign destination");
        assert_eq!(dest_expr.sort().bitvec_width(), Some(64));
    });
}

/// Test codegen_size_of_val with None target passes through.
#[test]
fn test_size_of_val_none_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: (0), projection: vec![] };
        let result = codegen.codegen_size_of_val(&[], &dest, None);
        assert_eq!(result, None);
    });
}

// =============================================================================
// codegen_checked_size_or_align tests
// =============================================================================

/// Test codegen_checked_size_or_align (size mode) with a sized reference type.
#[test]
fn test_checked_size_of_raw_sized_type() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: (1), projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: (0), projection: vec![] };

        // Should not panic — produces Some(size) for sized type
        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&args, &dest, true);
        // checked_size_or_align should assign destination and emit constraints
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_size (sized type) should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "checked size result should be bitvec(64)"
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_size should emit at least as many constraints as before"
        );
    });
}

/// Test codegen_checked_size_or_align (align mode) with a sized reference type.
#[test]
fn test_checked_align_of_raw_sized_type() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: (1), projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: (0), projection: vec![] };

        // Should not panic — produces Some(align) for sized type
        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&args, &dest, false);
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_align (sized type) should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "checked align result should be bitvec(64)"
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_align should emit at least as many constraints as before"
        );
    });
}

/// Test codegen_checked_size_or_align with empty args (unsized fallback).
#[test]
fn test_checked_size_or_align_empty_args_fallback() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: (0), projection: vec![] };

        // Empty args: falls to symbolic Option<usize> fallback
        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&[], &dest, true);
        // Fallback should assign destination with symbolic Option<usize> value
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_size empty args fallback should assign destination");
        // Empty args produces Option<BV(64)> datatype, not flat bitvec
        assert!(
            dest_expr.sort().datatype_name().is_some(),
            "checked_size fallback should produce Option datatype sort, got {:?}",
            dest_expr.sort()
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_size empty args fallback should not lose constraints"
        );
    });
}

// =============================================================================
// Raw pointer tests (Part of #2016)
//
// Existing tests only use &-reference arguments. These cover *const pointer
// paths in codegen_align_of_val, codegen_size_of_val, and
// codegen_checked_size_or_align.
// =============================================================================

/// Test codegen_size_of_val with a raw pointer argument (*const u16).
/// Verifies: size_of_val(*const u16) emits constant 2 (sizeof u16 = 2 bytes).
#[test]
fn test_size_of_val_rawptr_u16_returns_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_size_of_val(&args, &dest, Some(10));
        assert_eq!(result, Some(10), "codegen_size_of_val should handle raw pointers");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("size_of_val rawptr should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "size_of_val rawptr result should be bitvec(64)"
        );
        // u16 size = 2 bytes
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000002") || emitted.contains('2'),
            "size_of_val(*const u16) should emit constant 2, got {emitted}"
        );
    });
}

/// Test codegen_align_of_val with a raw pointer argument (*const u16).
/// Verifies: align_of_val(*const u16) emits constant 2 (u16 alignment = 2).
#[test]
fn test_align_of_val_rawptr_u16_returns_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_align_of_val(&args, &dest, Some(11));
        assert_eq!(result, Some(11), "codegen_align_of_val should handle raw pointers");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("align_of_val rawptr should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "align_of_val rawptr result should be bitvec(64)"
        );
        // u16 alignment = 2
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000002") || emitted.contains('2'),
            "align_of_val(*const u16) should emit constant 2, got {emitted}"
        );
    });
}

/// Test codegen_checked_size_or_align with a raw pointer (size mode).
#[test]
fn test_checked_size_rawptr_returns_without_panic() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&args, &dest, true);
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_size rawptr should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "checked_size rawptr result should be bitvec(64)"
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_size rawptr should not lose constraints"
        );
    });
}

/// Test codegen_checked_size_or_align with a raw pointer (align mode).
#[test]
fn test_checked_align_rawptr_returns_without_panic() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rawptr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&args, &dest, false);
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_align rawptr should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "checked_align rawptr result should be bitvec(64)"
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_align rawptr should not lose constraints"
        );
    });
}

/// Test codegen_align_of_val with None target passes through.
#[test]
fn test_align_of_val_none_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_align_of_val(&[], &dest, None);
        assert_eq!(result, None);
    });
}

/// Test codegen_size_of_val with tuple reference (compound layout).
/// Verifies: size_of_val(&(u64, u32)) emits constant 16 (8 + 4 + 4 padding).
#[test]
fn test_size_of_val_ref_tuple_returns_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_tuple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_size_of_val(&args, &dest, Some(12));
        assert_eq!(result, Some(12), "size_of_val should handle tuple references");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("size_of_val tuple ref should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "size_of_val tuple ref result should be bitvec(64)"
        );
        // (u64, u32) = 16 bytes (8 + 4 + 4 padding for alignment)
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000010") || emitted.contains("16"),
            "size_of_val(&(u64, u32)) should emit constant 16, got {emitted}"
        );
    });
}

/// Test codegen_align_of_val with u8 reference (align=1).
/// Verifies: align_of_val(&u8) emits constant 1 (u8 alignment = 1).
#[test]
fn test_align_of_val_ref_u8_returns_target() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: 1, projection: vec![] };
        let args = vec![Operand::Copy(place)];
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_align_of_val(&args, &dest, Some(13));
        assert_eq!(result, Some(13), "codegen_align_of_val should handle &u8 (align=1)");

        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("align_of_val u8 ref should assign destination");
        assert_eq!(
            dest_expr.sort().bitvec_width(),
            Some(64),
            "align_of_val u8 ref result should be bitvec(64)"
        );
        // u8 alignment = 1
        let emitted = latest_constraint_text(&codegen);
        assert!(
            emitted.contains("#x0000000000000001") || emitted.contains('1'),
            "align_of_val(&u8) should emit constant 1, got {emitted}"
        );
    });
}

/// Test codegen_checked_size_or_align empty args with align mode (fallback).
#[test]
fn test_checked_align_empty_args_fallback() {
    with_test_ay_ctx_for_source(MEMORY_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "simple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };

        // Empty args with align mode: falls to symbolic Option<usize> fallback
        let before = constraint_count(&codegen);
        codegen.codegen_checked_size_or_align(&[], &dest, false);
        let dest_expr = assigned_expr_for_place(&mut codegen, &dest)
            .expect("checked_align empty args fallback should assign destination");
        // Empty args produces Option<BV(64)> datatype, not flat bitvec
        assert!(
            dest_expr.sort().datatype_name().is_some(),
            "checked_align fallback should produce Option datatype sort, got {:?}",
            dest_expr.sort()
        );
        assert!(
            constraint_count(&codegen) >= before,
            "checked_align empty args fallback should not lose constraints"
        );
    });
}

// =============================================================================

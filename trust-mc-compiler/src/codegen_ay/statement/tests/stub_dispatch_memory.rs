// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for `dispatch/stub_dispatch_memory.rs` — pointer/memory
//! stub dispatch functions.
//!
//! Tests exercise the production functions through the full codegen pipeline:
//! `codegen_terminator_with_successors` → `codegen_stubbed_call` →
//! `try_codegen_pointer_memory_stub` → individual stub handlers.
//!
//! Coverage targets:
//! - `try_codegen_pointer_memory_stub` dispatch routing
//! - `codegen_nonnull_dangling_stub` — NonNull::dangling alignment
//! - `codegen_rawvec_new_in_stub` — RawVec construction with ptr > 0 constraint
//! - `codegen_rawvec_drop_stub` — no-op deallocation
//! - `codegen_checked_add_unsigned_stub` — wide-arithmetic Option result
//! - `codegen_rawvec_capacity_stub` — capacity field extraction
//! - `codegen_rawvec_ptr_stub` — pointer field extraction
//!
//! Part of #2615.

use super::*;
use crate::codegen_ay::stubs::StubKind;

// =============================================================================
// Shared source probes
// =============================================================================

/// Source that creates a Vec (triggers RawVec stubs during MIR codegen).
const VEC_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn vec_new_probe() -> Vec<u32> {
    Vec::new()
}

pub fn vec_push_probe() -> Vec<u32> {
    let mut v = Vec::new();
    v.push(42);
    v
}

pub fn vec_len_probe(v: &Vec<u32>) -> usize {
    v.len()
}

pub fn vec_capacity_probe(v: &Vec<u32>) -> usize {
    v.capacity()
}
"#;

/// Source that uses checked arithmetic.
const CHECKED_ARITH_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn checked_add_probe(x: i32, y: u32) -> Option<i32> {
    x.checked_add_unsigned(y)
}
"#;

/// Simple source for direct stub dispatch testing.
const SIMPLE_PROBE_SOURCE: &str = r#"
pub fn probe(x: u32) -> u32 { x }
"#;

// =============================================================================
// Helper: exercise full codegen pipeline for a function
// =============================================================================

/// Run the full statement + terminator codegen pipeline on a function,
/// counting Call terminators encountered.
fn exercise_pipeline(
    ctx: &mut crate::codegen_ay::context::AYCtx<'_, '_>,
    fn_suffix: &str,
) -> usize {
    let instance = find_instance_by_suffix(ctx, fn_suffix);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    let mut call_count = 0;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
        }
        if matches!(bb.terminator.kind, rustc_public::mir::TerminatorKind::Call { .. }) {
            call_count += 1;
        }
        let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
    }
    call_count
}

// =============================================================================
// try_codegen_pointer_memory_stub — dispatch routing
// =============================================================================

/// try_codegen_pointer_memory_stub returns None for unrecognized StubKind.
#[test]
fn test_dispatch_returns_none_for_unrecognized_stub() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        // StubKind::MemSizeOf is NOT handled by try_codegen_pointer_memory_stub
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::MemSizeOf, &[], &dest, Some(1));
        assert!(
            result.is_none(),
            "try_codegen_pointer_memory_stub should return None for non-memory stubs"
        );
    });
}

/// try_codegen_pointer_memory_stub returns Some for RawVecDrop.
#[test]
fn test_dispatch_rawvec_drop_returns_some() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecDrop, &[], &dest, Some(3));
        assert!(result.is_some(), "try_codegen_pointer_memory_stub should handle RawVecDrop");
        // RawVecDrop is a no-op — returns the target unchanged
        assert_eq!(
            result.unwrap(),
            Some(3),
            "RawVecDrop should pass through the target block index"
        );
    });
}

/// try_codegen_pointer_memory_stub returns Some for NonNullDangling.
#[test]
fn test_dispatch_nonnull_dangling_returns_some() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::NonNullDangling, &[], &dest, Some(2));
        assert!(result.is_some(), "try_codegen_pointer_memory_stub should handle NonNullDangling");
    });
}

#[test]
fn test_nonnull_dangling_extra_checks_invalidates_provenance() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::NonNullDangling, &[], &dest, Some(2));
        assert!(result.is_some(), "NonNullDangling should still return the target");

        let rendered_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("false"),
            "extra-pointer-checks NonNull::dangling should store false into obj_valid: {rendered_constraints}"
        );
    });
}

/// try_codegen_pointer_memory_stub returns Some for RawVecNewIn.
#[test]
fn test_dispatch_rawvec_new_in_returns_some() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecNewIn, &[], &dest, Some(1));
        assert!(result.is_some(), "try_codegen_pointer_memory_stub should handle RawVecNewIn");
    });
}

/// try_codegen_pointer_memory_stub returns Some for CheckedAddUnsigned with args.
#[test]
fn test_dispatch_checked_add_unsigned_returns_some() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        // CheckedAddUnsigned with < 2 args falls back to symbolic result
        let result = codegen.try_codegen_pointer_memory_stub(
            StubKind::CheckedAddUnsigned,
            &[],
            &dest,
            Some(1),
        );
        assert!(
            result.is_some(),
            "try_codegen_pointer_memory_stub should handle CheckedAddUnsigned"
        );
    });
}

// =============================================================================
// codegen_rawvec_new_in_stub — RawVec construction with ptr > 0 constraint
// =============================================================================

/// RawVec::new_in adds a constraint that ptr > 0 (non-null pointer).
#[test]
fn test_rawvec_new_in_adds_nonnull_constraint() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = codegen.ctx.program.commands().len();
        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecNewIn, &[], &dest, Some(1));
        assert!(result.is_some());
        let constraints_after = codegen.ctx.program.commands().len();

        // RawVec::new_in declares a variable and asserts ptr > 0
        assert!(
            constraints_after > constraints_before,
            "RawVec::new_in should add constraints (ptr > 0 and SSA assignment)"
        );
    });
}

#[test]
fn test_rawvec_new_in_extra_checks_invalidates_provenance() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecNewIn, &[], &dest, Some(1));
        assert!(result.is_some(), "RawVec::new_in should still succeed");

        let rendered_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("false"),
            "extra-pointer-checks RawVec::new_in should store false into obj_valid: {rendered_constraints}"
        );
    });
}

// =============================================================================
// Full MIR pipeline — Vec operations trigger RawVec stubs
// =============================================================================

/// Vec::new() exercises the full pipeline including RawVec stubs without panic.
#[test]
fn test_mir_vec_new_pipeline_no_panic() {
    with_test_ay_ctx_for_source(VEC_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_pipeline(&mut ctx, "vec_new_probe");
        // Vec::new() desugars to RawVec construction in MIR
        assert!(calls >= 1, "Vec::new should have Call terminators, got {calls}");
    });
}

/// Vec::push exercises the full pipeline including RawVec grow stubs.
#[test]
fn test_mir_vec_push_pipeline_no_panic() {
    with_test_ay_ctx_for_source(VEC_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_pipeline(&mut ctx, "vec_push_probe");
        // Vec::push desugars to multiple calls (reserve, ptr::write, etc.)
        assert!(calls >= 1, "Vec::push should have Call terminators, got {calls}");
    });
}

// =============================================================================
// Full MIR pipeline — checked_add_unsigned
// =============================================================================

/// checked_add_unsigned exercises the CheckedAddUnsigned stub path.
#[test]
fn test_mir_checked_add_unsigned_pipeline_no_panic() {
    with_test_ay_ctx_for_source(CHECKED_ARITH_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_pipeline(&mut ctx, "checked_add_probe");
        assert!(calls >= 1, "checked_add_unsigned should have Call terminators, got {calls}");
    });
}

// =============================================================================
// RawVecCapacity and RawVecPtr stubs with empty args — fallback paths
// =============================================================================

/// RawVec::capacity with no args produces a symbolic capacity value.
#[test]
fn test_rawvec_capacity_empty_args_fallback() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecCapacity, &[], &dest, Some(1));
        assert!(result.is_some(), "RawVecCapacity should handle call even with empty args");
    });
}

// =============================================================================
// Fail-closed tests — NonNullAsMutPtr, BoxIntoRawWithAllocator, UniqueNewUnchecked
// Part of #2497: verify that operand translation failure returns None (fail-closed)
// =============================================================================

/// NonNull::as_mut_ptr with empty args must fail-closed (return Some(None)).
#[test]
fn test_nonnull_as_mut_ptr_empty_args_fail_closed() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::NonNullAsMutPtr, &[], &dest, Some(5));
        assert_eq!(result, Some(None), "NonNullAsMutPtr with no args must fail-closed (#2497)");
    });
}

/// Box::into_raw_with_allocator with empty args must fail-closed (return Some(None)).
#[test]
fn test_box_into_raw_with_allocator_empty_args_fail_closed() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.try_codegen_pointer_memory_stub(
            StubKind::BoxIntoRawWithAllocator,
            &[],
            &dest,
            Some(6),
        );
        assert_eq!(
            result,
            Some(None),
            "BoxIntoRawWithAllocator with no args must fail-closed (#2497)"
        );
    });
}

/// Unique::new_unchecked with empty args must fail-closed (return Some(None)).
#[test]
fn test_unique_new_unchecked_empty_args_fail_closed() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.try_codegen_pointer_memory_stub(
            StubKind::UniqueNewUnchecked,
            &[],
            &dest,
            Some(7),
        );
        assert_eq!(result, Some(None), "UniqueNewUnchecked with no args must fail-closed (#2497)");
    });
}

/// RawVec::ptr with no args produces a symbolic pointer value.
#[test]
fn test_rawvec_ptr_empty_args_fallback() {
    with_test_ay_ctx_for_source(SIMPLE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result =
            codegen.try_codegen_pointer_memory_stub(StubKind::RawVecPtr, &[], &dest, Some(1));
        assert!(result.is_some(), "RawVecPtr should handle call even with empty args");
    });
}

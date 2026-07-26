// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for dispatch module — helpers.rs and stub_dispatch.rs inline stubs.
//!
//! Split from a single 2846-line monolith per #3678.
//! Shared helper kernel lives here; family-specific tests in submodules.

use super::*;

mod mir_alloc_kani_mem;
mod mir_collection_dispatch;
mod mir_helpers;
mod mir_inline_dispatch;
mod mir_iter_dispatch;
mod mir_misc_intrinsics;
mod mir_numeric_intrinsics;
mod mir_option_result;
mod mir_string_slice_clone;
mod pointer_semantics;
mod precheck_patterns;
mod stub_shapes;

// =============================================================================
// MIR-driven tests: collection stubs through full dispatch pipeline
// Part of #2016: exercise try_dispatch_stub → codegen_*_stub paths.
// =============================================================================

/// Probe source that creates Vec and calls push/len — triggers VecNew, VecPush, VecLen stubs.
const VEC_DISPATCH_PROBE: &str = r#"
pub fn vec_push_len() -> usize {
    let mut v: Vec<i32> = Vec::new();
    v.push(42);
    v.len()
}

pub fn vec_with_capacity_and_pop() -> Option<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(16);
    v.push(1);
    v.pop()
}
"#;

/// Test Vec::new + push + len dispatches through the stub pipeline.
#[test]
fn test_mir_vec_push_len_dispatch() {
    with_test_ay_ctx_for_source(VEC_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_push_len");
        assert!(
            info.call_count >= 3,
            "expected at least 3 Call terminators, got {}",
            info.call_count
        );
        // Verify Vec-related callee paths were resolved
        let has_vec = info.call_paths.iter().any(|p| p.contains("Vec") || p.contains("vec"));
        assert!(has_vec, "should resolve Vec-related paths, got {:?}", info.call_paths);
        assert!(info.any_dest_assigned, "at least one call destination should be assigned");
    });
}

/// Critical semantic stub #1 (#2250): Vec::new + push + len must return 1.
#[test]
fn test_mir_vec_push_len_semantic_return_is_one() {
    with_test_ay_ctx_for_source(VEC_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_push_len");
        let ret_expr = info.ret_expr.expect("vec_push_len should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bitvec_const(1u64, POINTER_WIDTH),
            "vec_push_len_is_one",
        );
    });
}

/// Test Vec::with_capacity + push + pop dispatches through the stub pipeline.
#[test]
fn test_mir_vec_with_capacity_pop_dispatch() {
    with_test_ay_ctx_for_source(VEC_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_with_capacity_and_pop");
        assert!(
            info.call_count >= 3,
            "expected at least 3 Call terminators, got {}",
            info.call_count
        );
        let has_vec = info.call_paths.iter().any(|p| p.contains("Vec") || p.contains("vec"));
        assert!(has_vec, "should resolve Vec-related paths, got {:?}", info.call_paths);
        assert!(info.any_dest_assigned, "at least one call destination should be assigned");
    });
}

/// Probe source for String operations — triggers StringNew, StringPush, StringLen stubs.
const STRING_DISPATCH_PROBE: &str = r#"
pub fn string_push_len() -> usize {
    let mut s = String::new();
    s.push('a');
    s.len()
}
"#;

/// Test String::new + push + len dispatches through the stub pipeline.
#[test]
fn test_mir_string_push_len_dispatch() {
    with_test_ay_ctx_for_source(STRING_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_push_len");
        assert!(
            info.call_count >= 3,
            "expected at least 3 Call terminators, got {}",
            info.call_count
        );
        let has_string =
            info.call_paths.iter().any(|p| p.contains("String") || p.contains("string"));
        assert!(has_string, "should resolve String-related paths, got {:?}", info.call_paths);
        assert!(info.any_dest_assigned, "at least one call destination should be assigned");
    });
}

// =============================================================================
// Shared MIR dispatch helper kernel
// =============================================================================

/// Result of running full codegen on a function and collecting dispatch metadata.
pub(super) struct CodegenInfo {
    pub(super) call_count: usize,
    pub(super) block_count: usize,
    /// Resolved callee paths for all Call terminators (via resolve_callee_path).
    pub(super) call_paths: Vec<String>,
    /// Function argument locals after codegen, keyed by MIR local index.
    pub(super) local_exprs: std::collections::BTreeMap<usize, Expr>,
    /// Return local (local 0) expression after codegen, if assigned.
    pub(super) ret_expr: Option<Expr>,
    /// Bitvec width of the return local (local 0) after codegen, if assigned.
    pub(super) ret_bitvec_width: Option<u32>,
    /// Whether the return local sort is bool.
    pub(super) ret_is_bool: bool,
    /// Whether any Call destination was assigned in the SSA env.
    pub(super) any_dest_assigned: bool,
}

/// Helper: build a StatementCodegen for a function, processing all statements
/// and terminators. Returns rich CodegenInfo for semantic assertions.
pub(super) fn build_codegen_for_fn_info(
    ctx: &mut AYCtx<'_, 'static>,
    fn_suffix: &str,
) -> CodegenInfo {
    let instance = find_instance_by_suffix(ctx, fn_suffix);
    let body = instance.body().expect("body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    // Process all statements
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
        }
    }

    // Count Call terminators, resolve paths, process terminators, check destinations
    let mut call_count = 0;
    let block_count = body.blocks.len();
    let mut call_paths = Vec::new();
    let mut any_dest_assigned = false;
    for bb in &body.blocks {
        if let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
            &bb.terminator.kind
        {
            call_count += 1;
            if let Some(path) = codegen.resolve_callee_path(func) {
                call_paths.push(path);
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            let dest_base = codegen.ssa_base_name(destination);
            if codegen.env_lookup(&dest_base).is_some() {
                any_dest_assigned = true;
            }
        } else {
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
    }

    let local_exprs = body
        .arg_locals()
        .iter()
        .enumerate()
        .filter_map(|(idx, _)| {
            let local_idx = idx + 1;
            let base = codegen.ssa_base_name(&local_place(local_idx));
            codegen.env_lookup(&base).cloned().map(|expr| (local_idx, expr))
        })
        .collect();

    // Check return local (local 0)
    let ret_place = local_place(0);
    let ret_base = codegen.ssa_base_name(&ret_place);
    let ret_expr = codegen.env_lookup(&ret_base).cloned();
    let ret_bitvec_width = ret_expr.as_ref().and_then(|e| e.sort().bitvec_width());
    let ret_is_bool = ret_expr.as_ref().is_some_and(|e| e.sort().is_bool());

    CodegenInfo {
        call_count,
        block_count,
        call_paths,
        local_exprs,
        ret_expr,
        ret_bitvec_width,
        ret_is_bool,
        any_dest_assigned,
    }
}

/// Backwards-compatible wrapper returning just (call_count, block_count).
pub(super) fn build_codegen_for_fn(
    ctx: &mut AYCtx<'_, 'static>,
    fn_suffix: &str,
) -> (usize, usize) {
    let info = build_codegen_for_fn_info(ctx, fn_suffix);
    (info.call_count, info.block_count)
}

pub(super) fn assert_semantic_return_equals(
    ctx: &AYCtx<'_, 'static>,
    ret_expr: Expr,
    expected: Expr,
    proof_name: &str,
) {
    assert_semantic_return_equals_under_guard(
        ctx,
        Expr::bool_const(true),
        ret_expr,
        expected,
        proof_name,
    );
}

pub(super) fn assert_semantic_return_equals_under_guard(
    ctx: &AYCtx<'_, 'static>,
    guard: Expr,
    ret_expr: Expr,
    expected: Expr,
    proof_name: &str,
) {
    super::assert_unsat_for_violation(
        ctx,
        guard.and(ret_expr.eq(expected).not()),
        "ay_violation_dispatch_semantic",
        proof_name,
    );
}

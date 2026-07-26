// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven semantic tests for BMC inline dispatch: closure_call, fn_inline, fn_ptr.
//!
//! Part of #3377: BMC missing fn_inline and fn_ptr dispatch capabilities.
//! Covers D6 of designs/2026-03-13-issue-3377-bmc-mini-inline-fnptr-port.md.

use super::super::*;
use super::{
    assert_semantic_return_equals, assert_semantic_return_equals_under_guard,
    build_codegen_for_fn_info,
};

// =============================================================================
// D6.1: Closure call semantic pilot
// =============================================================================

/// Probe: closure that adds 1, called via FnOnce::call_once pattern.
const CLOSURE_ADD_ONE_PROBE: &str = r#"
pub fn closure_add_one(x: u32) -> u32 {
    let f = |a: u32| -> u32 { a + 1 };
    f(x)
}
"#;

/// Closure call dispatch produces a concrete inlined result.
/// This checks the actual call boundary: the closure result must equal `x + 1`,
/// not a fresh symbolic value or constant-folded literal. The guard excludes
/// the checked-add overflow path, which is tracked separately by #2440.
#[test]
fn test_mir_closure_inline_dispatch() {
    with_test_ay_ctx_for_source(CLOSURE_ADD_ONE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "closure_add_one");
        assert!(info.block_count >= 1, "should have at least 1 basic block");
        let ret = info.ret_expr.expect("closure_add_one should produce a return expression");
        let arg = info
            .local_exprs
            .get(&1)
            .cloned()
            .expect("closure_add_one should keep caller arg local_1");
        let no_overflow = arg.clone().eq(Expr::bitvec_const(u32::MAX as u64, 32)).not();
        assert_semantic_return_equals_under_guard(
            &ctx,
            no_overflow,
            ret,
            arg.bvadd(Expr::bitvec_const(1u64, 32)),
            "closure_add_one_semantic_return",
        );
    });
}

// =============================================================================
// D6.2: Direct function call inlining (fn_inline)
// =============================================================================

/// Probe: small helper function called from a wrapper.
/// `#[inline(never)]` hints to rustc not to inline, preserving the Call terminator.
const FN_INLINE_PROBE: &str = r#"
#[inline(never)]
fn add_one_helper(x: u32) -> u32 {
    x + 1
}

pub fn fn_inline_probe(x: u32) -> u32 {
    add_one_helper(x)
}
"#;

/// Direct FnDef call through fn_inline dispatch.
/// Verifies the call dispatch chain processes without panicking.
/// The Call terminator to `add_one_helper` exercises the fn_inline path:
/// if inlining succeeds the destination is concrete, otherwise the
/// symbolic fallback fires — both are safe. The semantic assertion guards off
/// checked-add overflow, which is not modeled as a precise return value.
#[test]
fn test_mir_fn_inline_direct_call() {
    with_test_ay_ctx_for_source(FN_INLINE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "fn_inline_probe");
        // The Call terminator to add_one_helper must exist (not optimized away).
        assert!(info.call_count >= 1, "fn_inline_probe should have at least 1 Call terminator");
        // Whether the call was inlined or fell through, the MIR processed cleanly.
        assert!(info.block_count >= 1, "should have at least 1 basic block");
        // Verify fn_inline callee was resolved in the call path list.
        let has_helper = info.call_paths.iter().any(|p| p.contains("add_one_helper"));
        assert!(has_helper, "should resolve add_one_helper path, got: {:?}", info.call_paths);
        let ret = info.ret_expr.expect("fn_inline_probe should assign return local");
        let arg = info
            .local_exprs
            .get(&1)
            .cloned()
            .expect("fn_inline_probe should keep caller arg local_1");
        let no_overflow = arg.clone().eq(Expr::bitvec_const(u32::MAX as u64, 32)).not();
        assert_semantic_return_equals_under_guard(
            &ctx,
            no_overflow,
            ret,
            arg.bvadd(Expr::bitvec_const(1u64, 32)),
            "fn_inline_probe_semantic_return",
        );
    });
}

/// Probe: identity function to test simple pass-through inlining.
const FN_INLINE_IDENTITY_PROBE: &str = r#"
#[inline(never)]
fn identity(x: u32) -> u32 { x }

pub fn identity_probe(x: u32) -> u32 {
    identity(x)
}
"#;

/// Identity function exercising fn_inline dispatch path.
#[test]
fn test_mir_fn_inline_identity() {
    with_test_ay_ctx_for_source(FN_INLINE_IDENTITY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "identity_probe");
        assert!(info.call_count >= 1, "identity_probe should have at least 1 Call terminator");
        let has_identity = info.call_paths.iter().any(|p| p.contains("identity"));
        assert!(has_identity, "should resolve identity path, got: {:?}", info.call_paths);
        let ret = info.ret_expr.expect("identity_probe should assign return local");
        let arg = info
            .local_exprs
            .get(&1)
            .cloned()
            .expect("identity_probe should keep caller arg local_1");
        assert_semantic_return_equals(&ctx, ret, arg, "identity_probe_semantic_return");
    });
}

/// Probe: by-value wrapper carrying a mutable reference through fn_inline.
/// This mirrors the `Pin<&mut T>` shape from #3807 at a smaller MIR surface:
/// the callee receives a composite value parameter, then dereferences its ref
/// field. Mini-inline must preserve nested ref metadata for the callee local.
const FN_INLINE_WRAPPER_REF_PROBE: &str = r#"
struct Wrapper<'a>(&'a mut u32);

#[inline(never)]
fn read_wrapper(w: Wrapper<'_>) -> u32 {
    *w.0
}

pub fn fn_inline_wrapper_ref_probe(x: &mut u32) -> u32 {
    read_wrapper(Wrapper(x))
}
"#;

/// Mini-inline must transplant nested `ref_pointees` from a composite value
/// parameter into the callee local so field-copy + deref reads stay precise.
#[test]
fn test_mir_fn_inline_wrapper_ref_preserves_nested_ref_metadata() {
    with_test_ay_ctx_for_source(FN_INLINE_WRAPPER_REF_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "fn_inline_wrapper_ref_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut call_paths = Vec::new();
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
                && let Some(path) = codegen.resolve_callee_path(func)
            {
                call_paths.push(path);
            }
            let _ = codegen.codegen_terminator_with_successors(&bb.terminator);
        }

        assert!(
            call_paths.iter().any(|path| path.contains("read_wrapper")),
            "expected fn_inline wrapper helper call path, got {:?}",
            call_paths
        );

        let arg_place = local_place(1);
        let arg_base = codegen.ssa_base_name(&arg_place);
        let arg_pointee_base = codegen
            .ref_pointees
            .get(arg_base.as_str())
            .cloned()
            .expect("&mut arg should keep a tracked pointee");
        let expected = codegen
            .env_lookup(&arg_pointee_base)
            .cloned()
            .expect("arg pointee should remain available in env");

        let ret_base = codegen.ssa_base_name(&local_place(0));
        let ret_expr = codegen
            .env_lookup(&ret_base)
            .cloned()
            .expect("fn_inline_wrapper_ref_probe should assign return local");

        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            expected,
            "fn_inline_wrapper_ref_probe_semantic_return",
        );
    });
}

/// Probe: a regular helper that accepts a closure argument but uses Rust ABI.
/// This must stay on the direct fn_inline path instead of being mistaken for a
/// closure RustCall shim.
const FN_INLINE_CLOSURE_ARG_PROBE: &str = r#"
#[inline(never)]
fn passthrough_closure_arg<F: Fn(u32) -> u32 + Copy>(_f: F, x: u32) -> u32 {
    x
}

pub fn fn_inline_closure_arg_probe(x: u32) -> u32 {
    let f = |a: u32| -> u32 { a + 2 };
    passthrough_closure_arg(f, x)
}
"#;

/// Direct fn_inline should preserve precision for helpers that merely accept a
/// closure argument. These are normal Rust ABI functions, not closure trait shims.
#[test]
fn test_mir_fn_inline_closure_arg_passthrough() {
    with_test_ay_ctx_for_source(FN_INLINE_CLOSURE_ARG_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "fn_inline_closure_arg_probe");
        assert!(
            info.call_count >= 1,
            "fn_inline_closure_arg_probe should have at least 1 Call terminator"
        );
        let has_passthrough = info.call_paths.iter().any(|p| p.contains("passthrough_closure_arg"));
        assert!(
            has_passthrough,
            "should resolve passthrough_closure_arg path, got: {:?}",
            info.call_paths
        );
        let ret = info.ret_expr.expect("fn_inline_closure_arg_probe should assign return local");
        let arg = info
            .local_exprs
            .get(&1)
            .cloned()
            .expect("fn_inline_closure_arg_probe should keep caller arg local_1");
        assert_semantic_return_equals(
            &ctx,
            ret,
            arg,
            "fn_inline_closure_arg_probe_semantic_return",
        );
    });
}

// =============================================================================
// D6.3: Function pointer resolution (fn_ptr via ReifyFnPointer)
// =============================================================================

/// Probe: function pointer coerced from a named function via ReifyFnPointer.
const FN_PTR_REIFY_PROBE: &str = r#"
fn add_two(x: u32) -> u32 {
    x + 2
}

pub fn fn_ptr_reify_probe(x: u32) -> u32 {
    let f: fn(u32) -> u32 = add_two;
    f(x)
}
"#;

/// Function pointer call resolved via ReifyFnPointer MIR cast.
/// The fn_ptr dispatcher should resolve the concrete callee and inline it.
/// Guard off the checked-add overflow cases (`x >= u32::MAX - 1`).
#[test]
fn test_mir_fn_ptr_reify_dispatch() {
    with_test_ay_ctx_for_source(FN_PTR_REIFY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "fn_ptr_reify_probe");
        assert!(info.block_count >= 1, "should have at least 1 basic block");
        let ret = info.ret_expr.expect("fn_ptr_reify_probe should assign return local");
        let arg = info
            .local_exprs
            .get(&1)
            .cloned()
            .expect("fn_ptr_reify_probe should keep caller arg local_1");
        let no_overflow = arg.clone().bvuge(Expr::bitvec_const((u32::MAX as u64) - 1, 32)).not();
        assert_semantic_return_equals_under_guard(
            &ctx,
            no_overflow,
            ret,
            arg.bvadd(Expr::bitvec_const(2u64, 32)),
            "fn_ptr_reify_probe_semantic_return",
        );
    });
}

// =============================================================================
// D6.5: Guard test — inline limit rejection
// =============================================================================

/// Probe: function with enough branching to exceed the inline limit.
/// The body has >16 effective blocks, so the mini-inliner should reject it.
const LARGE_BODY_PROBE: &str = r#"
#[inline(never)]
fn large_body(x: u32) -> u32 {
    let mut result = x;
    if result > 100 { result = result.wrapping_add(1); }
    if result > 200 { result = result.wrapping_add(2); }
    if result > 300 { result = result.wrapping_add(3); }
    if result > 400 { result = result.wrapping_add(4); }
    if result > 500 { result = result.wrapping_add(5); }
    if result > 600 { result = result.wrapping_add(6); }
    if result > 700 { result = result.wrapping_add(7); }
    if result > 800 { result = result.wrapping_add(8); }
    if result > 900 { result = result.wrapping_add(9); }
    result
}

pub fn large_body_probe(x: u32) -> u32 {
    large_body(x)
}
"#;

/// Large callee body exceeds the inline limit — the mini-inliner declines,
/// and the call falls through to the symbolic/unsupported fallback.
/// This test verifies the guard works: no crash, no infinite recursion.
#[test]
fn test_mir_inline_limit_guard() {
    with_test_ay_ctx_for_source(LARGE_BODY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "large_body_probe");
        // The function should still be processed without panicking.
        // Whether the return expression is concrete or symbolic depends on
        // whether rustc inlined large_body. Either outcome is acceptable —
        // the key property is no crash.
        assert!(info.block_count >= 1, "should have at least 1 basic block");
    });
}

/// Probe: the large_body function itself — verify its block count exceeds the limit.
#[test]
fn test_mir_large_body_exceeds_inline_limit() {
    use crate::codegen_ay::shared::{MAX_INLINE_EFFECTIVE_BLOCKS, count_effective_blocks};
    with_test_ay_ctx_for_source(LARGE_BODY_PROBE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "large_body");
        let body = instance.body().expect("body");
        let effective = count_effective_blocks(&body);
        // 9 if-else branches generate at least 18 effective blocks.
        // The mini-inliner limit is MAX_INLINE_EFFECTIVE_BLOCKS (16).
        assert!(
            effective > MAX_INLINE_EFFECTIVE_BLOCKS,
            "large_body should have >{MAX_INLINE_EFFECTIVE_BLOCKS} effective blocks, got {effective}"
        );
    });
}

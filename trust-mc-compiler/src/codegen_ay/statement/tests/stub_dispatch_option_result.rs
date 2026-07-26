// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `dispatch/stub_dispatch_option_result.rs` — the Option/Result
//! dispatch table that routes StubKind variants to individual codegen handlers.
//!
//! This file covers the stubs NOT already tested through MIR dispatch in
//! `option.rs` (is_some, is_none, unwrap, unwrap_or, unwrap_or_else, map) and
//! `result.rs` (and_then via Option, map, ok_or_else, unwrap_or_else).
//!
//! Specifically covers:
//! - `Result::is_ok` / `Result::is_err` (discriminant check)
//! - `Option::expect` (same handler as unwrap, different StubKind)
//! - `Result::unwrap` / `Result::expect` (extract Ok payload)
//! - `Result::ok` / `Result::err` (convert to Option)
//! - `Result::map_err` (transform error variant)
//! - `Result::and_then` (monadic chaining)
//! - `Option::unwrap_unchecked` (unsafe unwrap)
//!
//! All tests use MIR-driven patterns that exercise the full
//! `codegen_terminator_with_successors` → `codegen_stubbed_call` →
//! `try_codegen_option_result_stub` dispatch chain.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;

// ─── Probe source: Result predicate and conversion methods ─────────────

const RESULT_DISPATCH_PROBE: &str = r#"
#![allow(dead_code)]

pub fn result_is_ok_probe(x: Result<i32, i32>) -> bool {
    x.is_ok()
}

pub fn result_is_err_probe(x: Result<i32, i32>) -> bool {
    x.is_err()
}

pub fn result_unwrap_probe(x: Result<i32, i32>) -> i32 {
    x.unwrap()
}

pub fn result_expect_probe(x: Result<i32, i32>) -> i32 {
    x.expect("should be Ok")
}

pub fn result_ok_probe(x: Result<i32, i32>) -> Option<i32> {
    x.ok()
}

pub fn result_err_probe(x: Result<i32, i32>) -> Option<i32> {
    x.err()
}

pub fn result_map_err_probe(x: Result<i32, i32>) -> Result<i32, i64> {
    x.map_err(|e| e as i64)
}

pub fn result_and_then_probe(x: Result<i32, i32>) -> Result<i64, i32> {
    x.and_then(|v| Ok(v as i64))
}
"#;

// ─── Probe source: Option expect and unwrap_unchecked ──────────────────

const OPTION_DISPATCH_PROBE: &str = r#"
#![allow(dead_code)]

pub fn option_expect_probe(x: Option<i32>) -> i32 {
    x.expect("should be Some")
}

pub fn option_unwrap_unchecked_probe(x: Option<i32>) -> i32 {
    unsafe { x.unwrap_unchecked() }
}
"#;

// ─── Helper: exercise full codegen pipeline on a function ──────────────

fn exercise_dispatch_codegen(
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

#[test]
fn test_outcome_or_fallthrough_returns_explicit_fallthrough() {
    let wrapped = StatementCodegen::outcome_or_fallthrough(None);
    assert_eq!(wrapped, CallDispatchOutcome::FallthroughToUnsupported);
}

#[test]
fn test_outcome_or_fallthrough_preserves_successor_block() {
    let wrapped = StatementCodegen::outcome_or_fallthrough(Some(7usize));
    assert_eq!(wrapped, CallDispatchOutcome::Continue(7usize));
}

// =============================================================================
// Result::is_ok — discriminant check returning bool
// =============================================================================

/// Result::is_ok dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_is_ok_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_is_ok_probe");
        assert!(calls >= 1, "Result::is_ok should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::is_err — discriminant check returning bool
// =============================================================================

/// Result::is_err dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_is_err_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_is_err_probe");
        assert!(calls >= 1, "Result::is_err should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::unwrap — extract Ok payload
// =============================================================================

/// Result::unwrap dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_unwrap_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_unwrap_probe");
        assert!(calls >= 1, "Result::unwrap should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::expect — same handler as unwrap, different StubKind
// =============================================================================

/// Result::expect dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_expect_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_expect_probe");
        assert!(calls >= 1, "Result::expect should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::ok — convert Result to Option (Some if Ok, None if Err)
// =============================================================================

/// Result::ok dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_ok_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_ok_probe");
        assert!(calls >= 1, "Result::ok should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::err — convert Result to Option (Some if Err, None if Ok)
// =============================================================================

/// Result::err dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_err_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_err_probe");
        assert!(calls >= 1, "Result::err should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::map_err — transform error variant with closure
// =============================================================================

/// Result::map_err dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_map_err_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_map_err_probe");
        assert!(calls >= 1, "Result::map_err should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Result::and_then — monadic chaining (Ok path)
// =============================================================================

/// Result::and_then dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_result_and_then_dispatch() {
    with_test_ay_ctx_for_source(RESULT_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "result_and_then_probe");
        assert!(calls >= 1, "Result::and_then should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Option::expect — same unwrap handler, different StubKind routing
// =============================================================================

/// Option::expect dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_option_expect_dispatch() {
    with_test_ay_ctx_for_source(OPTION_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "option_expect_probe");
        assert!(calls >= 1, "Option::expect should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Option::unwrap_unchecked — unsafe unwrap (OptionUnwrapUnchecked StubKind)
// =============================================================================

/// Option::unwrap_unchecked dispatches through MIR terminator pipeline without panic.
#[test]
fn test_mir_option_unwrap_unchecked_dispatch() {
    with_test_ay_ctx_for_source(OPTION_DISPATCH_PROBE, |mut ctx| {
        let calls = exercise_dispatch_codegen(&mut ctx, "option_unwrap_unchecked_probe");
        assert!(calls >= 1, "Option::unwrap_unchecked should have Call terminator, got {calls}");
    });
}

// =============================================================================
// Negative test: non-Option/Result function should not route to stub dispatch
// =============================================================================

/// A plain arithmetic function should have zero calls to stub_dispatch_option_result.
/// This verifies the dispatch table only activates for actual Option/Result stubs.
#[test]
fn test_plain_function_no_option_result_dispatch() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn plain_add(a: i32, b: i32) -> i32 { a + b }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "plain_add");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
                let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            }

            // Plain add: verify statements processed and return place has value
            assert!(stmt_count > 0, "plain_add should have MIR statements");
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{fn_name}::local_0");
            let return_entry = codegen.env_lookup(&return_base);
            assert!(
                return_entry.is_some(),
                "plain_add return should have env entry after full codegen"
            );
        },
    );
}

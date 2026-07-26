// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for option.rs — Option<T> codegen dispatch.
//!
//! 25 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY datatype_constructor/is_constructor/field_select/ITE patterns,
//! not production codegen).
//! Remaining tests use with_test_ay_ctx_for_source to exercise Option method
//! dispatch through the real MIR pipeline.

use super::*;

// =============================================================================
// MIR-driven dispatch tests — exercises actual codegen methods through compiler
// =============================================================================

/// Probe source: exercises is_some, is_none, unwrap, unwrap_or.
const OPTION_CORE_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn is_some_probe(x: Option<i32>) -> bool {
    x.is_some()
}

pub fn is_none_probe(x: Option<i32>) -> bool {
    x.is_none()
}

pub fn unwrap_probe(x: Option<i32>) -> i32 {
    x.unwrap()
}

pub fn unwrap_or_probe(x: Option<i32>) -> i32 {
    x.unwrap_or(0)
}

pub fn unwrap_or_else_probe(x: Option<i32>) -> i32 {
    x.unwrap_or_else(|| -1)
}

pub fn map_probe(x: Option<i32>) -> Option<i64> {
    x.map(|v| v as i64)
}
"#;

/// Run full codegen for a probe function and count Call terminators.
fn exercise_option_codegen(ctx: &mut AYCtx<'_, 'static>, fn_name: &str) -> usize {
    let instance = find_instance_by_suffix(ctx, fn_name);
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

/// Option::is_some dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_is_some_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "is_some_probe");
        assert!(calls >= 1, "Option::is_some should have Call, got {calls}");
    });
}

/// Option::is_none dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_is_none_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "is_none_probe");
        assert!(calls >= 1, "Option::is_none should have Call, got {calls}");
    });
}

/// Option::unwrap dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_unwrap_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "unwrap_probe");
        assert!(calls >= 1, "Option::unwrap should have Call, got {calls}");
    });
}

/// Option::unwrap_or dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_unwrap_or_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "unwrap_or_probe");
        assert!(calls >= 1, "Option::unwrap_or should have Call, got {calls}");
    });
}

/// Option::unwrap_or_else dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_unwrap_or_else_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "unwrap_or_else_probe");
        assert!(calls >= 1, "Option::unwrap_or_else should have Call, got {calls}");
    });
}

/// Option::map dispatches through MIR and produces at least 1 Call.
#[test]
fn test_mir_option_map_dispatch() {
    with_test_ay_ctx_for_source(OPTION_CORE_PROBE_SOURCE, |mut ctx| {
        let calls = exercise_option_codegen(&mut ctx, "map_probe");
        assert!(calls >= 1, "Option::map should have Call, got {calls}");
    });
}

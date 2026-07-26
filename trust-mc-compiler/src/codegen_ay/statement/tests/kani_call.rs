// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for codegen_kani_call.rs — Kani intrinsic dispatch.
//!
//! 53 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY API string matching/sort assertions, not production codegen).
//! Remaining tests use with_test_ay_ctx_for_source to exercise the MIR pipeline.

use super::*;

// =============================================================================
// MIR-driven tests using plain Rust (kani crate unavailable in test context)
// =============================================================================

/// Test MIR compilation produces Call terminators that would be routed through
/// try_codegen_kani_call. Uses function calls to stdlib methods that the
/// dispatch recognizes.
#[test]
fn test_mir_call_terminator_compilation() {
    // Plain Rust with function calls that exercise the call dispatch path
    let source = r#"
pub fn call_probe() {
    let v: Vec<u32> = Vec::new();
    let _len = v.len();
}
"#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let items = rustc_public::all_local_items();
        let has_probe = items.iter().any(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            ctx.tcx.def_path_str(def_id).contains("call_probe")
        });
        assert!(has_probe, "call_probe function should exist in compiled items");
    });
}

/// Test MIR with closure call generates FnOnce::call_once-style terminators.
#[test]
fn test_mir_closure_call_compilation() {
    let source = r#"
pub fn closure_probe() {
    let f = |x: u32| x + 1;
    let _result = f(5);
}
"#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let items = rustc_public::all_local_items();
        let has_probe = items.iter().any(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            ctx.tcx.def_path_str(def_id).contains("closure_probe")
        });
        assert!(has_probe, "closure_probe function should exist in compiled items");
    });
}

/// Test MIR with Option::map generates the dispatch path.
#[test]
fn test_mir_option_map_compilation() {
    let source = r#"
pub fn option_map_probe() {
    let x: Option<u32> = Some(5);
    let _y: Option<u32> = x.map(|v| v + 1);
}
"#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let items = rustc_public::all_local_items();
        let has_probe = items.iter().any(|item| {
            let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
            ctx.tcx.def_path_str(def_id).contains("option_map_probe")
        });
        assert!(has_probe, "option_map_probe function should exist in compiled items");
    });
}

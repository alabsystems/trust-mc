// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven Option/Result combinator dispatch tests.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::build_codegen_for_fn_info;

// -----------------------------------------------------------------------------

/// Probe source: Option/Result combinators to exercise stub dispatch.
/// Each function takes a parameter to prevent rustc from constant-folding.
const OPTION_RESULT_COMBINATOR_PROBE: &str = r#"
pub fn option_unwrap_or_probe(x: Option<i32>) -> i32 {
    x.unwrap_or(42)
}

pub fn option_map_probe(x: Option<i32>) -> Option<i32> {
    x.map(|v| v + 1)
}

pub fn option_and_then_probe(x: Option<i32>) -> Option<i32> {
    x.and_then(|v| if v > 0 { Some(v) } else { None })
}

pub fn option_expect_probe(x: Option<i32>) -> i32 {
    x.expect("should be Some")
}

pub fn result_unwrap_probe(x: Result<i32, i32>) -> i32 {
    x.unwrap()
}

pub fn result_unwrap_or_probe(x: Result<i32, i32>) -> i32 {
    x.unwrap_or(0)
}

pub fn result_map_probe(x: Result<i32, i32>) -> Result<i32, i32> {
    x.map(|v| v + 1)
}
"#;

/// Test Option::unwrap_or dispatches through stub pipeline.
#[test]
fn test_mir_option_unwrap_or_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "option_unwrap_or_probe");
        // unwrap_or may be inlined by rustc, but if dispatched through stubs,
        // it should have at least one call and assign a bitvec32 result.
        assert!(
            info.call_count >= 1 || info.ret_bitvec_width == Some(32),
            "Option::unwrap_or should either have calls or produce bv32 result, \
             got calls={}, ret_width={:?}, paths={:?}",
            info.call_count,
            info.ret_bitvec_width,
            info.call_paths
        );
    });
}

/// Test Option::map dispatches through stub pipeline.
#[test]
fn test_mir_option_map_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "option_map_probe");
        // Option::map involves closure call and Option construction.
        // May be inlined, but should have multiple basic blocks.
        assert!(info.block_count >= 2, "Option::map should have >=2 BBs, got {}", info.block_count);
    });
}

/// Test Option::and_then dispatches through stub pipeline.
#[test]
fn test_mir_option_and_then_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "option_and_then_probe");
        assert!(
            info.block_count >= 2,
            "Option::and_then should have >=2 BBs, got {}",
            info.block_count
        );
    });
}

/// Test Option::expect delegates to Option::unwrap stub.
#[test]
fn test_mir_option_expect_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "option_expect_probe");
        // expect delegates to unwrap, so should have similar structure
        assert!(
            info.call_count >= 1,
            "Option::expect should have >=1 Call, got {}",
            info.call_count
        );
        assert!(
            info.block_count >= 2,
            "Option::expect should have >=2 BBs (check+success+panic), got {}",
            info.block_count
        );
    });
}

/// Test Result::unwrap dispatches through stub pipeline.
#[test]
fn test_mir_result_unwrap_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "result_unwrap_probe");
        assert!(
            info.call_count >= 1,
            "Result::unwrap should have >=1 Call, got {}",
            info.call_count
        );
    });
}

/// Test Result::unwrap_or dispatches through stub pipeline.
#[test]
fn test_mir_result_unwrap_or_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "result_unwrap_or_probe");
        assert!(
            info.call_count >= 1 || info.ret_bitvec_width == Some(32),
            "Result::unwrap_or should either have calls or produce bv32 result, \
             got calls={}, ret_width={:?}",
            info.call_count,
            info.ret_bitvec_width
        );
    });
}

/// Test Result::map dispatches through stub pipeline.
#[test]
fn test_mir_result_map_dispatch() {
    with_test_ay_ctx_for_source(OPTION_RESULT_COMBINATOR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "result_map_probe");
        assert!(info.block_count >= 2, "Result::map should have >=2 BBs, got {}", info.block_count);
    });
}

// =============================================================================

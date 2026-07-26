// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_dispatch_collections.rs` — numeric/collection call
//! dispatch orchestration.
//!
//! Part of #2303 (codegen_call_dispatch_collections.rs, 243 LOC, zero dedicated coverage).
//! The individual stub detection functions (detect_bigint_stub, detect_hashmap_stub,
//! detect_stub_matching(is_vec_core), etc.) are tested in their respective test files.
//! These tests verify the *dispatch orchestration* path:
//!   codegen_call_terminator → try_dispatch_call_numeric_collections → detect_* → codegen_call_*
//!
//! Each test compiles a Rust source that exercises a specific dispatch branch,
//! runs the full CHC pipeline, and checks the resulting VC structure.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_dispatch_collections::CallDispatchCollections;
use super::common::*;

// =============================================================================
// Vec — detect_stub_matching(is_vec_core) branch
// =============================================================================

const VEC_PUSH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_push() -> Vec<u32> {
        let mut v = Vec::new();
        v.push(42);
        v
    }
"#;

/// Vec::push should be dispatched through try_dispatch_call_numeric_collections
/// via detect_stub_matching(is_vec_core) → codegen_call_vec_core.
#[test]
fn test_dispatch_vec_push_vc() {
    with_test_ay_ctx_for_source(VEC_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_push", body.blocks.len());
    });
}

const VEC_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_len(v: &Vec<u32>) -> usize {
        v.len()
    }
"#;

/// Vec::len exercises the collection predicate stub branch.
#[test]
fn test_dispatch_vec_len_vc() {
    with_test_ay_ctx_for_source(VEC_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_len", body.blocks.len());
    });
}

// =============================================================================
// Vec::is_empty — detect_collection_predicate_stub branch
// =============================================================================

const VEC_IS_EMPTY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_is_empty(v: &Vec<u32>) -> bool {
        v.is_empty()
    }
"#;

/// Vec::is_empty exercises detect_collection_predicate_stub.
#[test]
fn test_dispatch_vec_is_empty_vc() {
    with_test_ay_ctx_for_source(VEC_IS_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_is_empty", body.blocks.len());
    });
}

/// Numeric/collection dispatch should not silently drop a recognized call when
/// `target=None`; it must increment the per-context `diverging_call_drop` metric (#2587).
#[test]
fn test_dispatch_collections_target_none_records_drop_count() {
    with_test_ay_ctx_for_source(VEC_IS_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && chc_ctx
                        .detect_stub_matching(func, StubKind::is_collection_predicate)
                        .is_some()
                {
                    Some((bb_idx, func, args, destination))
                } else {
                    None
                }
            })
            .expect("expected collection predicate call terminator");

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();

        let target_none = None;
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_none,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };
        let handled = chc_ctx.try_dispatch_call_numeric_collections(&dcx);

        assert!(handled, "collections dispatch should claim recognized Vec::is_empty call");
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "target=None collection dispatch should record one diverging drop"
        );
    });
}

// =============================================================================
// String — detect_string_core_stub branch
// =============================================================================

const STRING_NEW_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_string_new() -> String {
        String::new()
    }
"#;

/// String::new should be dispatched through detect_string_core_stub.
#[test]
fn test_dispatch_string_new_vc() {
    with_test_ay_ctx_for_source(STRING_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_new");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_new", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_new", body.blocks.len());
    });
}

// =============================================================================
// Stub detection — verify collect helpers for dispatch coverage
// =============================================================================

/// Vec::push detection should fire through the stub detectors used by the
/// dispatch function.
#[test]
fn test_dispatch_vec_push_detects_vec_core_stub() {
    with_test_ay_ctx_for_source(VEC_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        // At least one Vec stub should be detected
        use rustc_public::mir::TerminatorKind;
        let any_vec_stub = body.blocks.iter().any(|block| {
            matches!(&block.terminator.kind, TerminatorKind::Call { func, .. }
                if chc_ctx.detect_stub_matching(func, StubKind::is_vec_core).is_some())
        });
        assert!(any_vec_stub, "Vec::push should be detected by detect_stub_matching(is_vec_core)");
    });
}

/// Vec::is_empty should be detected by detect_collection_predicate_stub.
#[test]
fn test_dispatch_vec_is_empty_detects_predicate_stub() {
    with_test_ay_ctx_for_source(VEC_IS_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        let detected = collect_detected_collection_predicate_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "Vec::is_empty should be detected as collection predicate");
    });
}

/// String::new should be detected by detect_string_core_stub.
#[test]
fn test_dispatch_string_new_detects_string_core_stub() {
    with_test_ay_ctx_for_source(STRING_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_new", ChcConfig::default());

        let detected = collect_detected_string_core_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "String::new should be detected as string core stub");
    });
}

// =============================================================================
// Negative: unrecognized function should not match any numeric/collection stub
// =============================================================================

const NO_COLLECTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_no_collections(x: u32) -> u32 {
        x.wrapping_add(1)
    }
"#;

/// Plain arithmetic should not trigger any collection dispatch stubs.
#[test]
fn test_dispatch_no_false_positive_collections() {
    with_test_ay_ctx_for_source(NO_COLLECTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_collections");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_collections", ChcConfig::default());

        let bigint = collect_detected_bigint_stubs(&chc_ctx, &body);
        let hashmap = collect_detected_hashmap_stubs(&chc_ctx, &body);
        let vec_iter = collect_detected_vec_iter_stubs(&chc_ctx, &body);
        let predicates = collect_detected_collection_predicate_stubs(&chc_ctx, &body);
        let string = collect_detected_string_core_stubs(&chc_ctx, &body);

        assert!(
            bigint.is_empty()
                && hashmap.is_empty()
                && vec_iter.is_empty()
                && predicates.is_empty()
                && string.is_empty(),
            "plain arithmetic should not trigger any collection dispatch stubs"
        );
    });
}

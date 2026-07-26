// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection predicate and pointer utility detection tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// Collection predicate detection tests
// =============================================================================

#[test]
fn test_detect_vec_is_empty_predicate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_is_empty(v: &Vec<u32>) -> bool {
            v.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());

        let detected = collect_detected_collection_predicate_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::VecIsEmpty),
            "VecIsEmpty should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_string_is_empty_predicate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_is_empty(s: &String) -> bool {
            s.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_is_empty", ChcConfig::default());

        let detected = collect_detected_collection_predicate_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::StringIsEmpty),
            "StringIsEmpty should be detected; got: {:?}",
            detected
        );
    });
}

// =============================================================================
// Pointer utility detection tests
// =============================================================================

#[test]
fn test_detect_ptr_is_null_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_is_null(p: *const u32) -> bool {
            p.is_null()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_is_null");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_is_null", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
            {
                assert!(
                    stub == StubKind::PtrIsNull || stub == StubKind::PtrIsNullRuntime,
                    "expected PtrIsNull or PtrIsNullRuntime, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert!(found, "PtrIsNull/PtrIsNullRuntime stub should be detected");
    });
}

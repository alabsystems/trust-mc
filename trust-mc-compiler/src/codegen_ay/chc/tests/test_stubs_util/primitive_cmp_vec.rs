// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Primitive cmp/eq StubKind detection and Vec core operation detection tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// Primitive cmp/eq StubKind-based detection tests (Part of #2196)
// =============================================================================

#[test]
fn test_detect_primitive_cmp_stub_eq() {
    // PartialEq::eq is used by assert_eq! and == on primitives.
    // Rustc may optimize small comparisons, so we use explicit trait call.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_eq(a: &u32, b: &u32) -> bool {
            PartialEq::eq(a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_eq");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_eq", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_primitive_cmp)
            {
                assert_eq!(stub, StubKind::PrimitivePartialEqEq);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "PrimitivePartialEqEq call in MIR");
    });
}

#[test]
fn test_detect_primitive_cmp_stub_lt() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_lt(a: &i32, b: &i32) -> bool {
            PartialOrd::lt(a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lt");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_lt", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_primitive_cmp)
            {
                assert!(
                    stub == StubKind::PrimitivePartialOrdLt
                        || stub == StubKind::PrimitivePartialEqEq
                        || stub == StubKind::PrimitivePartialEqNe,
                    "Expected a comparison StubKind, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert_mir_pattern_found(found, "primitive cmp stub (lt) call in MIR");
    });
}

#[test]
fn test_detect_primitive_cmp_stub_ord_cmp() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cmp(a: &u32, b: &u32) -> core::cmp::Ordering {
            Ord::cmp(a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cmp");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cmp", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_primitive_cmp)
            {
                assert_eq!(stub, StubKind::OrdCmp);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "OrdCmp call in MIR");
    });
}

// =============================================================================
// Vec core operation detection tests (Part of #2196)
// =============================================================================

#[test]
fn test_detect_vec_core_stub_new() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_vec_new() -> Vec<u32> {
            Vec::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_new", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                assert_eq!(stub, StubKind::VecNew);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "Vec::new call in MIR");
    });
}

#[test]
fn test_detect_vec_core_stub_push() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_vec_push(v: &mut Vec<u32>) {
            v.push(42);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_push", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                assert_eq!(stub, StubKind::VecPush);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "VecPush call in MIR");
    });
}

#[test]
fn test_detect_vec_core_stub_len() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_vec_len(v: &Vec<u32>) -> usize {
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                assert_eq!(stub, StubKind::VecLen);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "VecLen call in MIR");
    });
}

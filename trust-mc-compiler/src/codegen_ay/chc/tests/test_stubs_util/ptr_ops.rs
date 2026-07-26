// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer memory operation detection tests (ptr.add / ptr.read / ptr.write).
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// Pointer memory operation detection tests (ptr.add / ptr.read / ptr.write)
// =============================================================================

#[test]
fn test_detect_ptr_add_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add(p: *const u32, n: usize) -> *const u32 {
            unsafe { p.add(n) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrAdd);
                found = true;
            }
        }
        assert!(found, "PtrAdd stub should be detected");
    });
}

#[test]
fn test_detect_ptr_read_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read(p: *const u32) -> u32 {
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_read", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrRead);
                found = true;
            }
        }
        assert!(found, "PtrRead stub should be detected");
    });
}

#[test]
fn test_detect_ptr_write_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write(p: *mut u32, val: u32) {
            unsafe { p.write(val) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_write", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrWrite);
                found = true;
            }
        }
        assert!(found, "PtrWrite stub should be detected");
    });
}

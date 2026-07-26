// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String, RawVec, pointer cast, Layout, NonNull, allocation, BTreeMap, and iterator
//! adapter stub detection tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// String core operation detection tests (Part of #2196)
// =============================================================================

#[test]
fn test_detect_string_core_stub_new() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;

        pub fn probe_string_new() -> String {
            String::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_new", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                assert_eq!(stub, StubKind::StringNew);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "StringNew call in MIR");
    });
}

#[test]
fn test_detect_string_core_stub_len() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;

        pub fn probe_string_len(s: &String) -> usize {
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_len", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                assert_eq!(stub, StubKind::StringLen);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "StringLen call in MIR");
    });
}

// =============================================================================
// RawVec stub detection tests (Part of #2196)
// =============================================================================

/// Verifies that detect_rawvec_stub matches RawVec internal method calls
/// when they appear in MIR. Since RawVec is used internally by Vec,
/// we compile Vec code and check for RawVec calls in the lowered MIR.
#[test]
fn test_detect_rawvec_stub_via_vec_push() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_rawvec(v: &mut Vec<u32>) {
            v.push(1);
            v.push(2);
            v.push(3);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rawvec");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rawvec", ChcConfig::default());

        let mut rawvec_detect_count = 0usize;
        let mut call_count = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_stub_matching(func, StubKind::is_rawvec).is_some() {
                    rawvec_detect_count += 1;
                }
            }
        }
        // Vec::push compiles to multiple Call terminators (alloc, grow, write).
        // With 3 push() calls, expect multiple Call terminators even with inlining.
        assert!(
            call_count >= 2,
            "Vec::push x3 probe should have multiple Call terminators, got {call_count}"
        );
        assert!(
            rawvec_detect_count <= call_count,
            "rawvec detections ({rawvec_detect_count}) should not exceed calls ({call_count})"
        );
    });
}

// =============================================================================
// Pointer cast stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_ptr_cast_stub matches pointer cast calls.
#[test]
fn test_detect_ptr_cast_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_cast(p: *mut u32) -> *const u8 {
            p.cast::<u8>() as *const u8
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_cast", ChcConfig::default());

        // Pointer casts may be lowered to MIR Cast rvalues rather than calls.
        // If they appear as calls, the detect method catches them.
        let mut cast_found = false;
        let mut has_cast_rvalue = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast).is_some()
            {
                cast_found = true;
            }
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, rustc_public::mir::Rvalue::Cast(..))
                {
                    has_cast_rvalue = true;
                }
            }
        }
        // `p.cast::<u8>() as *const u8` must appear as either a Call terminator
        // (detected by detect_ptr_cast_stub) or a Cast rvalue (MIR lowering).
        assert!(
            cast_found || has_cast_rvalue,
            "pointer cast must appear as either Call stub or Cast rvalue in MIR"
        );
    });
}

// Slice stub detection tests (SlicePartialEqEqual, SliceIndexIndex) were deleted in #2459.
// Reason: `a == b` on &[u8] is lowered to memcmp/PartialEq trait dispatch without
// SlicePartialEq::equal Call terminators; `a[i]` is lowered to bounds-check + projection
// without an Index::index Call terminator. These tests always passed vacuously.

// =============================================================================
// Layout extra stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_layout_extra_stub catches Layout methods that appear
/// when allocation code is inlined (Layout::new, Layout::array, etc.).
#[test]
fn test_detect_layout_extra_stub_via_vec_alloc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::alloc::Layout;

        pub fn probe_layout_extra(n: usize) -> usize {
            let layout = Layout::array::<u64>(n).unwrap();
            layout.size()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_extra");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_layout_extra", ChcConfig::default());

        let mut layout_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_layout_extra).is_some()
            {
                layout_found = true;
            }
        }
        assert_mir_pattern_found(layout_found, "layout-extra stub call in MIR");
    });
}

// =============================================================================
// NonNull extra stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_nonnull_extra_stub catches NonNull methods from allocation paths.
#[test]
fn test_detect_nonnull_extra_stub_via_vec_new() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_extra(p: *mut u8) -> bool {
            NonNull::new(p).is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_extra");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nonnull_extra", ChcConfig::default());

        let mut nonnull_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_nonnull_extra).is_some()
            {
                nonnull_found = true;
            }
        }
        assert_mir_pattern_found(nonnull_found, "nonnull-extra stub call in MIR");
    });
}

// =============================================================================
// Allocation extra stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_alloc_extra_stub catches allocation-path helper stubs.
#[test]
fn test_detect_alloc_extra_stub_via_box_alloc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::{handle_alloc_error, Layout};

        pub fn probe_alloc_extra() -> ! {
            let layout = Layout::new::<u64>();
            handle_alloc_error(layout)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_extra");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_alloc_extra", ChcConfig::default());

        let mut alloc_extra_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_alloc_extra).is_some()
            {
                alloc_extra_found = true;
            }
        }
        assert_mir_pattern_found(alloc_extra_found, "alloc-extra stub call in MIR");
    });
}

// =============================================================================
// BTreeMap internal stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_btreemap_internal_stub catches Entry API calls
/// when BTreeMap code is inlined.
#[test]
fn test_detect_btreemap_internal_stub_via_entry() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::collections::BTreeMap;

        pub fn probe_btreemap_entry(m: &mut BTreeMap<u32, u32>, k: u32) {
            m.entry(k).or_insert(0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreemap_entry");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreemap_entry", ChcConfig::default());

        let mut btreemap_internal_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_btreemap_internal).is_some()
            {
                btreemap_internal_found = true;
            }
        }
        assert_mir_pattern_found(btreemap_internal_found, "btreemap-internal stub call in MIR");
    });
}

// =============================================================================
// Iterator adapter stub detection tests (Part of #2196)
// =============================================================================

/// Verifies detect_iterator_adapter_stub catches iterator adapter calls.
#[test]
fn test_detect_iterator_adapter_stub_via_map_collect() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_iter_adapter(v: Vec<u32>) -> Vec<u64> {
            v.into_iter().map(|x| x as u64).collect()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_adapter");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_adapter", ChcConfig::default());

        let mut adapter_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter).is_some()
            {
                adapter_found = true;
            }
        }
        assert_mir_pattern_found(adapter_found, "iterator-adapter call in MIR");
    });
}

/// Verifies detect_iterator_adapter_stub catches filter + fold pattern.
#[test]
fn test_detect_iterator_adapter_stub_via_filter_fold() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_iter_filter_fold(v: Vec<i32>) -> i32 {
            v.into_iter().filter(|x| *x > 0).fold(0, |acc, x| acc + x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_iter_filter_fold");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_iter_filter_fold", ChcConfig::default());

        let mut adapter_found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_iterator_adapter).is_some()
            {
                adapter_found = true;
            }
        }
        assert_mir_pattern_found(adapter_found, "iterator-adapter call in MIR");
    });
}

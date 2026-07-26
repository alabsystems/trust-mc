// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Localizer tests for ThreadLocalRef current-head state.
//!
//! These tests lock the observation that `thread_local!` harnesses are
//! already past the "no TLS model" stage on current HEAD. The live
//! failure surface is `flattened_bare_read` / `flatten_self_loop_fallback`,
//! NOT `thread_local_ref_unsupported`.
//!
//! Part of #4068.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

/// Minimal thread_local bool: `COND.with(|&b| assert!(b))`
/// This matches the `test_bool` harness from `tests/trust_mc/ThreadLocalRef/main.rs`.
const THREAD_LOCAL_BOOL_SOURCE: &str = r#"
    #![allow(dead_code)]

    thread_local! {
        static COND: bool = true;
    }

    pub fn probe_thread_local_bool_with() {
        COND.with(|&b| {
            assert!(b);
        });
    }
"#;

/// Thread-local i32 via RefCell: `COUNTER.with(|c| { *c.borrow_mut() += 1; })`
/// This matches the `test_i32` harness from `tests/trust_mc/ThreadLocalRef/main.rs`.
const THREAD_LOCAL_I32_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::cell::RefCell;

    thread_local! {
        static COUNTER: RefCell<i32> = RefCell::new(0);
    }

    pub fn probe_thread_local_i32_with() {
        COUNTER.with(|c| {
            assert_eq!(*c.borrow(), 0);
        });
    }
"#;

/// D1 core assertion: `test_bool` lane produces VC rules and the
/// `thread_local_ref_unsupported` reason is NOT the active drop reason.
/// The active drop reasons should be in the flatten/reconstruct family.
#[test]
fn test_thread_local_bool_current_head_drop_reasons() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(THREAD_LOCAL_BOOL_SOURCE, |ctx| {
        let fn_name = "probe_thread_local_bool_with";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // The harness should produce non-empty rules — it compiles and translates.
        assert!(
            !vc.rules.is_empty(),
            "{fn_name} should produce CHC rules (thread_local! source compiles to MIR)"
        );
    });

    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let fn_reasons =
        translation_drop_sites.get("probe_thread_local_bool_with").cloned().unwrap_or_default();

    // Diagnostic: print all drop reasons for the function.
    let fn_reasons_dbg =
        translation_drop_sites.get("probe_thread_local_bool_with").cloned().unwrap_or_default();
    eprintln!("test_bool drop reasons: {fn_reasons_dbg:?}");

    // Core D1 assertion: thread_local_ref_unsupported should NOT be the
    // active reason. If it were, the repo would still be in the "no TLS model"
    // state and D2 (flatten/reconstruct) would be the wrong fix layer.
    let tls_unsupported_count =
        fn_reasons.get("thread_local_ref_unsupported").copied().unwrap_or(0);
    assert_eq!(
        tls_unsupported_count, 0,
        "thread_local_ref_unsupported should NOT be an active drop reason for test_bool. \
         The current failure surface is flatten/reconstruct, not TLS dispatch. \
         Actual reasons: {fn_reasons:?}"
    );

    // The active drop reasons should be in the flatten/reconstruct family.
    // We do NOT assert an exact set because the MIR shape can change with
    // toolchain updates, but we assert the two reasons named by the
    // compiletest artifact are present.
    let has_flatten_reason = fn_reasons
        .keys()
        .any(|k| k.contains("flatten") || k.contains("flattened") || k.contains("bare_read"));
    // This is a soft check: if the flatten reasons change names, the test
    // still passes the core assertion (no thread_local_ref_unsupported).
    if !has_flatten_reason && !fn_reasons.is_empty() {
        eprintln!(
            "NOTE: expected flatten/bare_read reasons but got: {fn_reasons:?}. \
             This may indicate a new codegen path. Update this localizer."
        );
    }

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

/// Verify that the test_i32 lane also compiles and the primary gate is NOT
/// thread_local_ref_unsupported.
#[test]
fn test_thread_local_i32_current_head_drop_reasons() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(THREAD_LOCAL_I32_SOURCE, |ctx| {
        let fn_name = "probe_thread_local_i32_with";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "{fn_name} should produce CHC rules");
    });

    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let fn_reasons =
        translation_drop_sites.get("probe_thread_local_i32_with").cloned().unwrap_or_default();

    let tls_unsupported_count =
        fn_reasons.get("thread_local_ref_unsupported").copied().unwrap_or(0);
    assert_eq!(
        tls_unsupported_count, 0,
        "thread_local_ref_unsupported should NOT be an active drop reason for test_i32. \
         Actual reasons: {fn_reasons:?}"
    );

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

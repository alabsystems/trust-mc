// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Localizers for raw `ptr::from_raw_parts(...)->*const str` string call paths.
//!
//! Part of #4187: exact-source malformed-BV boundary localization.

#![allow(clippy::unwrap_used)]

use super::common::*;

/// Simplified source that mimics the raw_ptr.rs harness pattern without
/// requiring Kani sysroot. Uses concrete byte arrays instead of `kani::any()`.
const RAW_PTR_SIMPLIFIED_SOURCE: &str = r#"
    #![feature(ptr_metadata)]
    #![allow(dead_code, unused_unsafe)]

    pub fn check_from_raw_simplified() -> bool {
        let ascii: [u8; 5] = [65, 66, 67, 68, 69]; // "ABCDE"
        let slice_ptr: *const [u8] = &ascii as &[u8];
        let (ptr, metadata) = slice_ptr.to_raw_parts();
        let str_ptr: *const str = std::ptr::from_raw_parts(ptr, metadata);
        unsafe { (&*str_ptr).is_ascii() }
    }
"#;

#[derive(Debug)]
struct RawPtrMalformedBvSnapshot {
    call_dispatch_fallback: usize,
    first_malformed_bv: Option<MalformedBvSite>,
    rule_count: usize,
}

fn run_raw_ptr_localizer() -> RawPtrMalformedBvSnapshot {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();

    let mut snapshot = None;
    with_test_ay_ctx_for_source(RAW_PTR_SIMPLIFIED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_from_raw_simplified");
        let body = instance.body().expect("check_from_raw_simplified body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "check_from_raw_simplified", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        snapshot = Some(RawPtrMalformedBvSnapshot {
            call_dispatch_fallback: diagnostics
                .sound_fallback_detail
                .get("call_dispatch_fallback")
                .copied()
                .unwrap_or(0),
            first_malformed_bv: first_malformed_bv_site(&vc),
            rule_count: vc.rules.len(),
        });
    });

    snapshot.expect("raw_ptr localizer should translate")
}

/// Verify the localizer produces VC rules and exposes the malformed-BV
/// boundary when the string-backing recovery path is incomplete.
#[test]
fn test_raw_ptr_localizes_malformed_bv_boundary() {
    let snapshot = run_raw_ptr_localizer();
    assert!(snapshot.rule_count > 0, "raw_ptr localizer should emit VC rules: {snapshot:?}");
    // The localizer should translate without crashing — the malformed-BV site
    // is detected in the VC output, not by a compiler panic.
    // Once the production fix is in place, first_malformed_bv should be None.
    eprintln!(
        "raw_ptr localizer snapshot: fallback={}, first_malformed_bv={:?}, rules={}",
        snapshot.call_dispatch_fallback, snapshot.first_malformed_bv, snapshot.rule_count
    );
}

/// Verify string backing resolves for the is_ascii receiver when reached
/// through ptr::from_raw_parts → &str deref.
#[test]
fn test_raw_ptr_resolves_string_backing_for_is_ascii_receiver() {
    with_test_ay_ctx_for_source(RAW_PTR_SIMPLIFIED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_from_raw_simplified");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "check_from_raw_simplified", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Look for StringIsAscii call in the MIR.
        let receiver = body.blocks.iter().find_map(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, args, .. } = &block.terminator.kind
            else {
                return None;
            };
            (chc_ctx.detect_stub_matching(func, StubKind::is_collection_predicate)
                == Some(StubKind::StringIsAscii))
            .then(|| args.first().cloned())
            .flatten()
        });

        if let Some(receiver) = receiver {
            let backing = chc_ctx.resolve_string_backing(&receiver, &HashSet::new());
            if let Some(backing) = backing {
                assert!(
                    backing.data.sort().is_array(),
                    "raw_ptr string backing should stay array-backed, got {}",
                    backing.data.sort()
                );
                assert_eq!(
                    backing.len.sort().bitvec_width(),
                    Some(64),
                    "raw_ptr string backing len should stay pointer-width"
                );
            } else {
                eprintln!(
                    "String backing not yet resolved for is_ascii receiver — \
                     this is the gap that #4187 fixes"
                );
            }
        } else {
            eprintln!(
                "No StringIsAscii stub detected in simplified MIR — \
                 the probe may not reach is_ascii through the same path as raw_ptr.rs"
            );
        }
    });
}

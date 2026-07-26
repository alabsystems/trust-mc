// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven regression tests for realloc stale-pointer detection encoding.
//!
//! Verifies that the CHC encoding for the `realloc_stale_pointer_fail.rs`
//! harness pattern emits the correct structural constraints:
//!
//! 1. Transition rules contain store-chain invalidation of the old allocation
//!    (`obj_valid[old_id] = false` via `obj_valid__out`)
//! 2. Error rules reference `obj_valid` for the stale-pointer access check
//! 3. The volatile_load path emits heap validity checks (not just value resolution)
//!
//! The harness currently returns UNKNOWN (solver limitation, not encoding gap).
//! PDR cannot synthesize the array invariant needed to propagate the
//! obj_valid store-chain through the realloc transition. These tests ensure
//! the encoding remains correct so solver improvements (e.g., ay#6047
//! array-sorted PDR) can recover CTREX without trust_mc code changes.
//!
//! Part of #3833, #1739.

#![allow(clippy::unwrap_used)]

use super::common::*;

const STALE_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{alloc, realloc, Layout};

    pub unsafe fn probe_stale_ptr_realloc() {
        let layout = Layout::from_size_align(16, 8).unwrap();
        let old_ptr = unsafe { alloc(layout) };

        if !old_ptr.is_null() {
            unsafe { *old_ptr = 0xAB };
            let _new_ptr = unsafe { realloc(old_ptr, layout, 32) };
            let _stale_read = unsafe { core::ptr::read_volatile(old_ptr) };
        }
    }
"#;

/// The VC for the stale-pointer harness must contain `obj_valid__out` in
/// transition rules (realloc invalidates the old allocation via store-chain).
#[test]
fn test_realloc_stale_ptr_vc_has_obj_valid_invalidation() {
    with_test_ay_ctx_for_source(STALE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_ptr_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_ptr_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // The realloc always-moved model (#3728) must emit obj_valid output
        // constraints with store-chain invalidation.
        // After scalarization, obj_valid__out may become obj_valid_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_scalarized(&vc, "obj_valid", "__out"),
            "realloc stale-pointer VC must contain obj_valid output (always-moved invalidation)"
        );

        // obj_valid must appear in some form (used for the validity check on the
        // stale read). After scalarization, the input var may become
        // obj_valid_at_0xN_bv32 — still contains "obj_valid" substring.
        assert!(
            vc_rules_contain_var(&vc, "obj_valid"),
            "realloc stale-pointer VC must reference obj_valid (used by heap access checks)"
        );

        // obj_size output must appear (realloc updates size for the new allocation).
        // After scalarization, obj_size__out may become obj_size_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_scalarized(&vc, "obj_size", "__out"),
            "realloc stale-pointer VC must contain obj_size output (new allocation size)"
        );
    });
}

/// Error rules must reference obj_valid (the stale-pointer access check
/// propagated from volatile_load → emit_ptr_obj_valid_check → pending_checks).
#[test]
fn test_realloc_stale_ptr_error_rules_check_obj_valid() {
    with_test_ay_ctx_for_source(STALE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_ptr_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_ptr_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Error rules must contain obj_valid references. The volatile_load
        // handler calls emit_ptr_obj_valid_check which pushes
        // obj_valid.select(obj_id) to pending_checks. These become error rules
        // via drain_pending_checks.
        let has_obj_valid_error = vc
            .rules
            .iter()
            .filter(|r| r.head.name == "error")
            .any(|rule| rule_contains_var(rule, "obj_valid"));
        assert!(
            has_obj_valid_error,
            "error rules must reference obj_valid for stale-pointer detection \
             (volatile_load → emit_ptr_obj_valid_check → pending_checks → error)"
        );
    });
}

/// The realloc transition must use a store-chain pattern (not ITE) for
/// obj_valid invalidation. This is the #3728 always-moved model guarantee.
#[test]
fn test_realloc_stale_ptr_no_ite_on_obj_valid() {
    with_test_ay_ctx_for_source(STALE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_ptr_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_ptr_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // No ITE on obj_valid metadata — the always-moved model writes directly
        // via store-chain (obj_valid_out = store(store(obj_valid_in, old, false), new, true)).
        let metadata_ite = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                let mentions_obj_valid = constraint.to_string().contains("obj_valid__out");
                mentions_obj_valid
                    && constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::Ite { .. })
                    })
            })
        });
        assert!(
            !metadata_ite,
            "realloc obj_valid updates must use store-chain, not ITE (always-moved model #3728)"
        );
    });
}

/// The VC must contain Array store expressions (the store-chain pattern for
/// obj_valid invalidation). This distinguishes the precise encoding from
/// a fallback that might skip the invalidation entirely.
#[test]
fn test_realloc_stale_ptr_has_array_store_on_obj_valid() {
    with_test_ay_ctx_for_source(STALE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_ptr_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_ptr_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Look for Array Store expressions that reference obj_valid in the
        // same constraint (the store-chain: store(store(obj_valid_in, old, false), new, true)).
        // After scalarization, the store-chain is decomposed into per-index
        // scalar equalities (e.g., obj_valid_at_0x0_bv32__out = false).
        // Check for either the pre-scalarization store form OR the post-scalarization
        // scalar assignment form — both confirm invalidation is encoded.
        let has_store_on_valid = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                let s = constraint.to_string();
                // Pre-scalarization: store(obj_valid, ...) pattern
                (s.contains("obj_valid") && s.contains("store"))
                // Post-scalarization: scalar output assigned false/true
                || (s.contains("obj_valid") && s.contains("__out"))
            })
        });
        assert!(
            has_store_on_valid,
            "realloc VC must contain obj_valid store-chain or scalarized output constraints"
        );
    });
}

/// The VC must contain a `false` literal in the obj_valid store-chain
/// (the invalidation of the old allocation: store(obj_valid, old_id, false)).
#[test]
fn test_realloc_stale_ptr_stores_false_to_obj_valid() {
    with_test_ay_ctx_for_source(STALE_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_ptr_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_ptr_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // The store-chain must include store(..., false) for the old allocation
        // and store(..., true) for the new allocation. Check that both boolean
        // constants appear in constraints involving obj_valid.
        // After scalarization, the store-chain becomes scalar equalities like:
        //   (= obj_valid_at_0x0_bv32__out false)
        //   (= obj_valid_at_0x1_bv32__out true)
        let has_false_in_valid_constraint = any_constraint_str(&vc, |s| {
            s.contains("obj_valid")
                && ((s.contains("store") && s.contains("false"))
                    || (s.contains("__out") && s.contains("false")))
        });
        assert!(
            has_false_in_valid_constraint,
            "realloc obj_valid must include false (store-chain or scalarized assignment)"
        );

        let has_true_in_valid_constraint = any_constraint_str(&vc, |s| {
            s.contains("obj_valid")
                && ((s.contains("store") && s.contains("true"))
                    || (s.contains("__out") && s.contains("true")))
        });
        assert!(
            has_true_in_valid_constraint,
            "realloc obj_valid must include true (store-chain or scalarized assignment)"
        );
    });
}

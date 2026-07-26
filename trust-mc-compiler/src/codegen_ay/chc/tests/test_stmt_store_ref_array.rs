// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_store_ref_array.rs` — array element store through
//! ref_target and arg-ref pointee paths.
//!
//! Part of #2921 (untested production file coverage).
//! Part of #2302 (cross-repo quality patterns).
//!
//! Covers:
//! - `handle_deref_store_array_via_ref_targets_impl`: arr[idx] = val via ref_targets (#1957)
//! - `handle_deref_store_array_arg_ref_impl`: (*arg_ref)[i] = val via arg pointee (#2750)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Array store through reference — exercises handle_deref_store_array_via_ref_targets_impl
// =============================================================================

const REF_ARRAY_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_array_store(arr: &mut [u32; 4], idx: usize, val: u32) {
        arr[idx] = val;
    }
"#;

/// Array element store through &mut reference produces a valid VC.
#[test]
fn test_ref_array_store_produces_vc() {
    with_test_ay_ctx_for_source(REF_ARRAY_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_array_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_array_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_array_store", body.blocks.len());
    });
}

/// Array store through reference should produce transition rules with constraints.
#[test]
fn test_ref_array_store_has_transitions() {
    with_test_ay_ctx_for_source(REF_ARRAY_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_array_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_array_store", ChcConfig::default());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "ref array store should produce transition rules"
        );
    });
}

// =============================================================================
// Constant-index array store through reference
// =============================================================================

const REF_ARRAY_CONST_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_array_const_store(arr: &mut [u32; 4]) {
        arr[0] = 100;
        arr[2] = 200;
    }
"#;

/// Constant-index array store through reference produces valid VC.
#[test]
fn test_ref_array_const_store_produces_vc() {
    with_test_ay_ctx_for_source(REF_ARRAY_CONST_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_array_const_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_array_const_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_array_const_store", body.blocks.len());
    });
}

// =============================================================================
// Arg-ref array store — exercises handle_deref_store_array_arg_ref_impl (#2750)
// =============================================================================

const ARG_REF_ARRAY_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_arg_ref_array_store(arr: &mut [u32], idx: usize, val: u32) {
        arr[idx] = val;
    }
"#;

/// Arg-ref array store (&mut [u32] slice arg) produces a valid VC.
#[test]
fn test_arg_ref_array_store_produces_vc() {
    with_test_ay_ctx_for_source(ARG_REF_ARRAY_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_ref_array_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_arg_ref_array_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_arg_ref_array_store", body.blocks.len());
    });
}

/// Arg-ref array store should produce non-trivial semantics.
#[test]
fn test_arg_ref_array_store_has_semantics() {
    with_test_ay_ctx_for_source(ARG_REF_ARRAY_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_ref_array_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_arg_ref_array_store", ChcConfig::default());

        assert_has_nontrivial_transition_constraints(&vc, "probe_arg_ref_array_store");
    });
}

// =============================================================================
// Struct field store through array reference
// =============================================================================

const REF_ARRAY_STRUCT_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub struct Pair { pub x: u32, pub y: u32 }

    pub fn probe_ref_array_struct_store(arr: &mut [Pair; 2], val: u32) {
        arr[0].x = val;
    }
"#;

/// Struct field store through array reference produces valid VC.
#[test]
fn test_ref_array_struct_field_store_produces_vc() {
    with_test_ay_ctx_for_source(REF_ARRAY_STRUCT_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_array_struct_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_array_struct_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_array_struct_store", body.blocks.len());
    });
}

// =============================================================================
// Array store at Mem level through reference
// =============================================================================

/// Ref array store at Mem track level should produce a valid VC.
#[test]
fn test_ref_array_store_mem_level() {
    with_test_ay_ctx_for_source(REF_ARRAY_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_array_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_ref_array_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_ref_array_store", body.blocks.len());
    });
}

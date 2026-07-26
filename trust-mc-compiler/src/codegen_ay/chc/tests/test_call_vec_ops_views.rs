// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_vec_ops_views.rs` — Vec view operation helpers
//! (capacity, as_slice).
//!
//! Part of #2921 (untested production file coverage).
//! Part of #2302 (cross-repo quality patterns).
//!
//! Covers:
//! - `vec_op_capacity`: capacity retrieval (sidecar → projected → Datatype)
//! - `vec_op_as_slice`: as_slice construction (Slice struct or backing data)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Vec::capacity() — exercises vec_op_capacity
// =============================================================================

const VEC_CAPACITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_capacity(v: Vec<u32>) -> usize {
        v.capacity()
    }
"#;

/// Vec::capacity() through CHC pipeline produces a valid VC.
#[test]
fn test_vec_capacity_produces_vc() {
    with_test_ay_ctx_for_source(VEC_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_capacity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_capacity", body.blocks.len());
    });
}

/// Vec::capacity() should produce transition rules.
#[test]
fn test_vec_capacity_has_transitions() {
    with_test_ay_ctx_for_source(VEC_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_capacity", ChcConfig::default());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "vec_capacity should produce transition rules"
        );
    });
}

// =============================================================================
// Vec::as_slice() — exercises vec_op_as_slice
// =============================================================================

const VEC_AS_SLICE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_as_slice(v: &Vec<u32>) -> &[u32] {
        v.as_slice()
    }
"#;

/// Vec::as_slice() through CHC pipeline produces a valid VC.
#[test]
fn test_vec_as_slice_produces_vc() {
    with_test_ay_ctx_for_source(VEC_AS_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_as_slice");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_as_slice", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_as_slice", body.blocks.len());
    });
}

// =============================================================================
// Vec capacity after push — sidecar cap variable path
// =============================================================================

const VEC_PUSH_CAPACITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_push_then_capacity(mut v: Vec<u32>, val: u32) -> usize {
        v.push(val);
        v.capacity()
    }
"#;

/// Vec capacity after push exercises the sidecar cap variable path.
#[test]
fn test_vec_push_then_capacity_produces_vc() {
    with_test_ay_ctx_for_source(VEC_PUSH_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_then_capacity");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_then_capacity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_then_capacity", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_push_then_capacity");
    });
}

// =============================================================================
// Vec as_slice at Mem level
// =============================================================================

/// Vec::as_slice at Mem track level should produce valid VC.
#[test]
fn test_vec_as_slice_mem_level() {
    with_test_ay_ctx_for_source(VEC_AS_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_as_slice");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_as_slice",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_vec_as_slice", body.blocks.len());
    });
}

// =============================================================================
// Vec::iter() — VecAsSlice → VecIter pipeline (#3012)
// =============================================================================

const VEC_ITER_PIPELINE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_iter_next(v: Vec<i32>) -> Option<i32> {
        let mut iter = v.iter();
        iter.next().copied()
    }
"#;

/// Vec::iter().next() through CHC pipeline produces a valid VC.
///
/// Part of #3012: exercises the const_ref_slice_views path where
/// VecAsSlice stores a Slice view and VecIter retrieves it.
#[test]
fn test_vec_iter_pipeline_produces_vc() {
    with_test_ay_ctx_for_source(VEC_ITER_PIPELINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_iter_next");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_iter_next", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_iter_next", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_iter_next");
    });
}

// =============================================================================
// VecAsSlice through struct field — BV64 memory load path (#3348)
// =============================================================================

const VEC_AS_SLICE_STRUCT_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Container {
        data: Vec<u32>,
    }

    impl Container {
        fn get_slice(&self) -> &[u32] {
            self.data.as_slice()
        }
    }

    pub fn probe_struct_vec_as_slice(c: &Container) -> &[u32] {
        c.get_slice()
    }
"#;

/// VecAsSlice through struct field exercises the BV64 memory load fallback.
///
/// When a Vec is accessed through `&self.field`, the collection local's state
/// var may be BV64 (pointer to Vec in memory). The memory load fallback in
/// `vec_op_as_slice` should resolve this to a Vec Datatype and extract fields.
///
/// Part of #3348: unblocks bv_concat_width_sum harness.
#[test]
fn test_vec_as_slice_struct_field_produces_vc() {
    with_test_ay_ctx_for_source(VEC_AS_SLICE_STRUCT_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_vec_as_slice");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_struct_vec_as_slice",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_struct_vec_as_slice", body.blocks.len());
    });
}

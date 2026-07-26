// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/stubs_collection_projection.rs — collection argument
//! resolution, datatype reconstruction from flattened fields, and
//! projected iterator decomposition.
//!
//! Verifies that:
//! - get_collection_arg resolves Vec arguments through ref_targets
//! - Vec::into_iter produces pipeline VCs with non-trivial transitions
//! - Vec iteration loop (for x in v) emits correct CHC encoding
//! - HashMap iteration pipeline produces valid VCs
//!
//! Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// get_collection_arg — Vec by mutable reference
// =============================================================================

/// get_collection_arg should resolve Vec<u32> passed by &mut ref through
/// the full MIR pipeline. The stub produces Store/Select on fld_data.
#[test]
fn test_get_collection_arg_vec_mut_ref() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_ref(v: &mut Vec<u32>) {
            v.push(42);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_ref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_ref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_ref", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_ref");
    });
}

// =============================================================================
// Vec into_iter pipeline — exercises reconstruct_projected_vec_into_iter_arg
// =============================================================================

/// Vec::into_iter produces a VecIntoIter that gets projected into flattened
/// slots. The pipeline should emit valid VCs with non-trivial semantics.
#[test]
fn test_vec_into_iter_pipeline_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_into_iter() -> u32 {
            let v = vec![1u32, 2, 3];
            let mut sum = 0u32;
            for x in v {
                sum = sum.wrapping_add(x);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_into_iter", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_into_iter", body.blocks.len());

        // The loop body should contain non-trivial transitions (BvAdd for sum).
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_into_iter");
    });
}

/// Vec iteration with early return exercises the projected collection
/// decomposition path at the iterator adapter call site.
#[test]
fn test_vec_into_iter_early_return() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_find_first(v: Vec<u32>, target: u32) -> Option<u32> {
            for x in v {
                if x == target {
                    return Some(x);
                }
            }
            None
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_find_first");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_find_first", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_find_first", body.blocks.len());
    });
}

// =============================================================================
// Vec by-value consumption
// =============================================================================

/// Consuming a Vec (move into function) should still produce valid VCs.
/// Tests the non-reference path of get_collection_arg.
#[test]
fn test_vec_consume_by_value() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_consume(v: Vec<u32>) -> usize {
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_consume");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_consume", ChcConfig::default());

        assert_vc_structure(&vc, "probe_consume", body.blocks.len());
    });
}

// =============================================================================
// decompose_projected_iterator_to_fields — Vec pipeline with index
// =============================================================================

/// Indexed iteration over Vec exercises decompose back to flattened fields.
#[test]
fn test_vec_indexed_iteration_decompose() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_indexed_iter() -> u32 {
            let v = vec![10u32, 20, 30];
            let mut result = 0u32;
            for (i, x) in v.into_iter().enumerate() {
                result = result.wrapping_add(x.wrapping_mul(i as u32));
            }
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_indexed_iter");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_indexed_iter", ChcConfig::default());

        assert_vc_structure(&vc, "probe_indexed_iter", body.blocks.len());
    });
}

// =============================================================================
// HashMap iteration — exercises HashMapIntoIter projection kind
// =============================================================================

/// HashMap iteration exercises the HashMapIntoIter collection projection kind
/// in reconstruct_projected_collection_arg.
#[test]
fn test_hashmap_iter_collection_projection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashmap_iter() -> u32 {
            let mut m = HashMap::new();
            m.insert(1u32, 100u32);
            let mut sum = 0u32;
            for (k, v) in m {
                sum = sum.wrapping_add(k.wrapping_add(v));
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_iter", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_iter", body.blocks.len());
    });
}

// =============================================================================
// Multiple collection operations in sequence
// =============================================================================

/// Multiple push + iteration exercises the reconstruct → decompose round-trip.
#[test]
fn test_vec_push_then_iterate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_push_iterate() -> u32 {
            let mut v = Vec::new();
            v.push(1u32);
            v.push(2);
            v.push(3);
            let mut sum = 0u32;
            for x in v {
                sum = sum.wrapping_add(x);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_push_iterate");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_push_iterate", ChcConfig::default());

        assert_vc_structure(&vc, "probe_push_iterate", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_push_iterate");
    });
}

// =============================================================================
// Vec::len via immutable reference — exercises non-projected fallback path
// =============================================================================

/// Vec::len through a shared reference tests the translate_operand_with_modified
/// fallback path in get_collection_arg when the target is not projected.
#[test]
fn test_vec_len_immutable_ref_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_len(v: &Vec<u32>) -> usize {
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_len", body.blocks.len());
    });
}

// =============================================================================
// Array IntoIter pipeline — exercises ArrayIntoIter projection reconstruction
// and decomposition through the full MIR pipeline
// =============================================================================

/// Iteration over a fixed array should use the ArrayIntoIter projection kind
/// without falling back to unhandled-call or known-stdlib-unconstrained paths.
#[test]
fn test_array_into_iter_pipeline_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_into_iter() -> u32 {
            let arr = [1u32, 2, 3];
            let mut sum = 0u32;
            for x in arr {
                sum = sum.wrapping_add(x);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_into_iter");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_into_iter", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, "probe_array_into_iter", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_array_into_iter");
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "array IntoIter pipeline should not leave calls unhandled"
        );
    });
}

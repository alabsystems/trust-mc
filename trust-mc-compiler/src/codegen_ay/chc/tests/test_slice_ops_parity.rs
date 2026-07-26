// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Parity tests for CHC slice operations.
//!
//! Verifies that CHC slice index and equality stubs produce constrained
//! transitions matching statement backend semantics, rather than the
//! prior unconstrained over-approximation.
//!
//! Part of #408: dispatch-layer slice parity.

#![allow(clippy::unwrap_used)]

use super::common::*;

fn has_constrained_transition(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().filter(|r| r.body.relation.is_some()).any(|r| !r.body.constraints.is_empty())
}

// =============================================================================
// SliceOp mapping tests
// =============================================================================

#[test]
fn test_slice_op_from_stub_maps_correctly() {
    use super::super::codegen_slice_op::SliceOp;
    use crate::codegen_ay::stubs::StubKind;

    assert_eq!(SliceOp::from_stub(StubKind::SlicePartialEqEqual), Some(SliceOp::Eq));
    assert_eq!(SliceOp::from_stub(StubKind::SliceIndexIndex), Some(SliceOp::Index));
    assert_eq!(SliceOp::from_stub(StubKind::IndexIndex), Some(SliceOp::Index));
    // Non-slice stubs should return None.
    assert_eq!(SliceOp::from_stub(StubKind::VecNew), None);
    assert_eq!(SliceOp::from_stub(StubKind::PrimitiveClone), None);
}

#[test]
fn test_slice_op_metadata() {
    use crate::codegen_ay::chc::codegen_slice_op::SliceOp;

    assert!(SliceOp::Eq.returns_bool());
    assert!(!SliceOp::Eq.returns_ref());
    assert!(!SliceOp::Eq.may_oob());

    assert!(!SliceOp::Index.returns_bool());
    assert!(SliceOp::Index.returns_ref());
    assert!(SliceOp::Index.may_oob());
}

// =============================================================================
// CHC slice index parity: constrained vs unconstrained
// =============================================================================

/// Slice indexing should now produce constrained transitions or error rules
/// (bounds check), not just unconstrained fallback.
#[test]
fn test_slice_index_produces_constrained_or_error_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_index_parity(s: &[u32], i: usize) -> u32 {
            s[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index_parity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_index_parity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_index_parity", body.blocks.len());

        // Count constrained transition rules (rules with non-empty constraints
        // that are not error rules).
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .filter(|r| r.head.name != "error")
            .filter(|r| !r.body.constraints.is_empty())
            .count();

        // Count error rules (bounds check or assertion violations).
        let error_rules = vc.rules.iter().filter(|r| r.head.name == "error").count();

        // At minimum, the new implementation should produce either constrained
        // transitions (from array select) or error rules (from bounds checks),
        // or both. The old implementation produced neither.
        assert!(
            constrained_transitions > 0 || error_rules > 0,
            "slice index should produce constrained transitions ({constrained_transitions}) \
             or error rules ({error_rules}); got neither"
        );
    });
}

/// Verify that the VC for slice indexing contains BV32 sorts for u32 elements.
#[test]
fn test_slice_index_has_element_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_index_sort(s: &[u32], i: usize) -> u32 {
            s[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index_sort");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_index_sort", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_index_sort", body.blocks.len());

        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "slice index VC should have BV32 for u32 return");
    });
}

// =============================================================================
// ZST slice index parity
// =============================================================================

/// ZST array index should produce a constrained transition (Unit constructor),
/// not just an unconstrained fallback.
#[test]
fn test_zst_array_index_produces_constrained_transition() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_index(arr: &[(); 10], i: usize) -> &() {
            &arr[i]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_index");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_zst_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_zst_index", body.blocks.len());

        assert!(
            has_constrained_transition(&vc),
            "ZST slice index should produce constrained rules"
        );
    });
}

/// Zero-length non-ZST arrays should preserve first() semantics (is_none=true).
#[test]
fn test_zero_len_non_zst_first_is_none_produces_constrained_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zero_len_non_zst_first_is_none(arr: &[u8; 0]) -> bool {
            arr.first().is_none()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zero_len_non_zst_first_is_none");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_zero_len_non_zst_first_is_none",
            ChcConfig::default(),
        );

        assert_vc_structure(&vc, "probe_zero_len_non_zst_first_is_none", body.blocks.len());
        assert!(
            has_constrained_transition(&vc),
            "zero-length first().is_none should be constrained"
        );
    });
}

/// Non-empty ZST arrays should preserve first() semantics (is_some=true).
#[test]
fn test_non_empty_zst_first_is_some_produces_constrained_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_non_empty_zst_first_is_some(arr: &[(); 10]) -> bool {
            arr.first().is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_empty_zst_first_is_some");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_non_empty_zst_first_is_some", ChcConfig::default());

        assert_vc_structure(&vc, "probe_non_empty_zst_first_is_some", body.blocks.len());
        assert!(
            has_constrained_transition(&vc),
            "non-empty ZST first().is_some should be constrained"
        );
    });
}

// =============================================================================
// Slice equality parity
// =============================================================================

/// Slice equality should produce constrained bool result.
#[test]
fn test_slice_eq_produces_constrained_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_eq_parity(a: &[u8], b: &[u8]) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_eq_parity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_eq_parity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_eq_parity", body.blocks.len());

        assert!(has_constrained_transition(&vc), "slice equality should produce constrained rules");
    });
}

/// Non-empty ZST array equality should stay constrained (no unconstrained fallback).
#[test]
fn test_zst_slice_eq_produces_constrained_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_slice_eq_parity(a: &[(); 10], b: &[(); 10]) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_slice_eq_parity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_zst_slice_eq_parity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_zst_slice_eq_parity", body.blocks.len());
        assert!(
            has_constrained_transition(&vc),
            "ZST slice equality should produce constrained rules"
        );
    });
}

/// ZST array equality lowered through `SlicePartialEq::equal` should prove
/// concrete equal-length arrays equal instead of leaving the bool symbolic.
#[test]
fn test_zst_array_clone_move_equality_proves() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_array_clone_move_equality() {
            let zst_array = [(); 10];
            let cloned = zst_array.clone();
            let moved = zst_array;
            assert_eq!(moved, cloned);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_array_clone_move_equality");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_zst_array_clone_move_equality", ChcConfig::default());
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

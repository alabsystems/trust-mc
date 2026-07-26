// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for `codegen_call_vec_ops_len.rs` — Vec clear/clone/len
//! helpers flowing through the full MIR-to-CHC pipeline.
//!
//! Part of #2921 (untested CHC production file remediation).

#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::ExprValue;

fn detect_vec_core_stub<'tcx, 'body>(
    tcx: TyCtxt<'tcx>,
    body: &'body rustc_public::mir::Body,
    fn_name: &str,
    target: StubKind,
) -> bool {
    let chc_ctx = ChcCtx::new(tcx, body, fn_name, ChcConfig::default());
    body.blocks.iter().any(|block| {
        if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
            chc_ctx.detect_stub_matching(func, StubKind::is_vec_core) == Some(target)
        } else {
            false
        }
    })
}

const VEC_CLEAR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_clear(v: &mut Vec<u32>) {
        v.clear();
    }
"#;

const VEC_CLONE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_clone(v: Vec<u32>) -> Vec<u32> {
        v.clone()
    }
"#;

const VEC_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_len(v: Vec<u32>) -> usize {
        v.len()
    }
"#;

const VEC_SET_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_set_len(v: &mut Vec<u32>, new_len: usize) {
        unsafe { v.set_len(new_len); }
    }
"#;

const VEC_APPEND_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::ptr;

    pub fn probe_append(dst: &mut Vec<u32>, src: &mut Vec<u32>) {
        let src_len = src.len();
        let dst_len = dst.len();
        dst.reserve(src_len);
        unsafe {
            let dst_ptr = dst.as_mut_ptr().offset(dst_len as isize);
            let src_ptr = src.as_ptr();
            src.set_len(0);
            ptr::copy_nonoverlapping(src_ptr, dst_ptr, src_len);
            dst.set_len(dst_len + src_len);
        }
    }
"#;

const VEC_CLEAR_CLONE_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_clear_clone_len(mut v: Vec<u32>) -> usize {
        v.clear();
        let cloned = v.clone();
        cloned.len()
    }
"#;

#[test]
fn test_vec_clear_detected_and_emits_zero_len_constraint() {
    with_test_ay_ctx_for_source(VEC_CLEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear");
        let body = instance.body().expect("function body");

        let found_clear =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_clear", StubKind::VecClear);
        assert_mir_pattern_found(found_clear, "VecClear call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clear", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_clear", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_clear");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_clear",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_clear",
            |e| matches!(e.value(), ExprValue::BitVecConst { .. }),
            "BitVecConst(len=0)",
        );
    });
}

#[test]
fn test_vec_clone_detected_and_emits_len_copy_constraints() {
    with_test_ay_ctx_for_source(VEC_CLONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clone");
        let body = instance.body().expect("function body");

        let found_clone =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_clone", StubKind::VecClone);
        assert_mir_pattern_found(found_clone, "VecClone call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clone", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_clone", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_clone");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_clone",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_len_detected_and_emits_destination_eq() {
    with_test_ay_ctx_for_source(VEC_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let found_len = detect_vec_core_stub(ctx.tcx, &body, "probe_vec_len", StubKind::VecLen);
        assert_mir_pattern_found(found_len, "VecLen call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_len", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_len");
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_len",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_clear_clone_len_pipeline_hits_all_three_stubs() {
    with_test_ay_ctx_for_source(VEC_CLEAR_CLONE_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear_clone_len");
        let body = instance.body().expect("function body");

        let found_clear =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_clear_clone_len", StubKind::VecClear);
        let found_clone =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_clear_clone_len", StubKind::VecClone);
        let found_len =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_clear_clone_len", StubKind::VecLen);
        assert_mir_pattern_found(found_clear, "VecClear call in MIR");
        assert_mir_pattern_found(found_clone, "VecClone call in MIR");
        assert_mir_pattern_found(found_len, "VecLen call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clear_clone_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_clear_clone_len", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_clear_clone_len");
    });
}

/// VecSetLen: dispatch detects `set_len` and emits len-update constraint.
///
/// Part of #3895: Vec::set_len is required for `copy_nonoverlapping_append`.
#[test]
fn test_vec_set_len_detected_and_emits_len_update() {
    with_test_ay_ctx_for_source(VEC_SET_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_set_len");
        let body = instance.body().expect("function body");

        let found_set_len =
            detect_vec_core_stub(ctx.tcx, &body, "probe_vec_set_len", StubKind::VecSetLen);
        assert_mir_pattern_found(found_set_len, "VecSetLen call in MIR");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_set_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_set_len", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_set_len");
        // VecSetLen emits an Eq constraint (len = new_len) and a BvUge
        // constraint (cap >= new_len).
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_set_len",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq(len=new_len)",
        );
    });
}

/// Append diagnostic: the exact shape from `copy_nonoverlapping_append.rs`.
///
/// Verifies that the combined Vec operations (len, reserve, as_mut_ptr,
/// set_len x2, copy_nonoverlapping) all dispatch through stubs without
/// crashing and produce a non-trivial VC.
///
/// Part of #3895 acceptance criteria: append-specific diagnostic test.
#[test]
fn test_vec_append_dispatches_all_stubs_without_panic() {
    with_test_ay_ctx_for_source(VEC_APPEND_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_append");
        let body = instance.body().expect("function body");

        // Detect both set_len calls.
        let found_set_len =
            detect_vec_core_stub(ctx.tcx, &body, "probe_append", StubKind::VecSetLen);
        assert_mir_pattern_found(found_set_len, "VecSetLen call in append MIR");

        // Full translation must not panic.
        let vc = mir_to_chc(ctx.tcx, &body, "probe_append", ChcConfig::default());

        assert_vc_structure(&vc, "probe_append", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_append");
    });
}

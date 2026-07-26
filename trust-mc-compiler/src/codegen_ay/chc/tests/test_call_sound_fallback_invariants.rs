// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sound-fallback correctness invariant tests (Part of #4158).
//!
//! These tests verify the critical soundness property: on a sound-fallback path,
//! destination locals become unconstrained output-state variables with NO equality
//! binding. This is the mechanism that ensures sound fallback only weakens
//! (over-approximates) the verification condition — never constrains it.
//!
//! The shared helper boundary (`emit_sound_fallback_goto` + `build_output_args`)
//! is the dominant correctness surface: 182+ call sites inherit these invariants.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::Sort;

use crate::codegen_ay::chc::codegen_call_coerce::{
    emit_sound_fallback_goto, emit_sound_fallback_goto_extra, try_emit_precise_call_result,
};

const PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn build_output_probe(x: u32, y: u32) -> u32 {
        let z = x + y;
        z
    }
"#;

/// Part of #4158: The sound-fallback rule body must NOT contain any equality
/// constraint referencing the destination local's output variable. The destination
/// is left genuinely unconstrained (fresh symbolic).
#[test]
fn test_sound_fallback_dest_is_unconstrained_in_rule_body() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let dest_local = 0usize;
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[dest_local],
            &[Expr::bool_const(true)],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(emitted.len(), 1, "should emit exactly one rule");

        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let (out_name, _) = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx];

        for constraint in emitted[0].body.constraints.iter() {
            let text = constraint.to_string();
            assert!(
                !text.contains(&**out_name),
                "sound-fallback rule body must NOT constrain destination output var '{}', \
                 but found it in constraint: {}",
                out_name,
                text
            );
        }
    });
}

/// Part of #4158: On a sound-fallback path, the rule head should use the
/// output-state variable for the destination local — not the input-state variable.
#[test]
fn test_sound_fallback_head_uses_output_var_for_dest() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let dest_local = 0usize;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let out_name_str = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.to_string();
        let in_name_str = chc_ctx.state_var_mgr.state_vars[dest_vec_idx].0.to_string();
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[dest_local],
            &[],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(emitted.len(), 1);

        let live = &chc_ctx.state_var_mgr.live_state_indices[target];
        if let Some(pos) = live.iter().position(|&idx| idx == dest_vec_idx) {
            let head_text = emitted[0].head.args[pos].to_string();
            assert!(
                head_text.contains(&out_name_str),
                "rule head should use output var '{}' for destination, got '{}'",
                out_name_str,
                head_text
            );
            assert!(
                !head_text.contains(&in_name_str) || out_name_str.contains(&in_name_str),
                "rule head should NOT use input var '{}' for destination",
                in_name_str,
            );
        }
    });
}

/// Part of #4158: Non-destination, non-modified locals should pass through
/// their input-state variables — not output-state variables.
#[test]
fn test_sound_fallback_non_dest_locals_use_input_vars() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let dest_local = 0usize;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[dest_local],
            &[],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(emitted.len(), 1);

        let output_args = chc_ctx.build_output_args(&HashSet::new(), &[dest_local]);
        for (idx, arg) in output_args.iter().enumerate() {
            if idx == dest_vec_idx || chc_ctx.encode.modified_state_indices.contains(&idx) {
                continue;
            }
            let (in_name, _) = &chc_ctx.state_var_mgr.state_vars[idx];
            let text = arg.to_string();
            assert!(
                text.contains(&**in_name),
                "non-destination local at vec_idx {} should use input var '{}', got '{}'",
                idx,
                in_name,
                text
            );
        }
    });
}

/// Part of #4158: `try_emit_precise_call_result` with `None` result must fall
/// through to the sound-fallback path, leaving the destination unconstrained.
#[test]
fn test_try_emit_precise_none_result_falls_through_to_unconstrained_fallback() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let dest_local = 0usize;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let out_name_str = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.to_string();
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_rules = chc_ctx.vc.rules.len();

        let success = try_emit_precise_call_result(
            &mut chc_ctx,
            None,
            dest_local,
            &from_app,
            target,
            &HashSet::new(),
            &[Expr::bool_const(true)],
            [],
            "test_none_fallback",
        );

        assert!(!success, "should return false on None result");
        assert_eq!(chc_ctx.sound_fallback_count(), before_fallback + 1);

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(emitted.len(), 1, "should emit exactly one fallback rule");

        for constraint in emitted[0].body.constraints.iter() {
            let text = constraint.to_string();
            assert!(
                !text.contains(&out_name_str),
                "try_emit_precise fallback must NOT constrain dest output var '{}', \
                 but found in constraint: {}",
                out_name_str,
                text
            );
        }
    });
}

/// Part of #4158: `emit_sound_fallback_goto_extra` with extra constraints must
/// NOT accidentally constrain the destination.
#[test]
fn test_sound_fallback_extra_constraints_dont_bind_dest() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let dest_local = 0usize;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let out_name_str = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.to_string();

        let extra_a = Expr::var("unrelated_range_lo", Sort::bitvec(32));
        let extra_b = Expr::var("unrelated_range_hi", Sort::bitvec(32));
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto_extra(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[dest_local],
            &[],
            [extra_a, extra_b],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(emitted.len(), 1);

        assert!(emitted[0].body.constraints.len() >= 2, "extra constraints should be appended");
        for constraint in emitted[0].body.constraints.iter() {
            let text = constraint.to_string();
            assert!(
                !text.contains(&out_name_str),
                "extra constraints must NOT reference dest output var '{}', found in: {}",
                out_name_str,
                text
            );
        }
    });
}

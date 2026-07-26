// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused CHC tests for `slice::is_empty`.
//!
//! Part of #3713: keep the bool-returning slice-length path isolated from the
//! broader slice stub suite.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// SliceIsEmpty — bool-returning slice length parity
// =============================================================================

#[test]
fn test_empty_array_is_empty_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_empty_array_is_empty() -> bool {
            let arr: [u32; 0] = [];
            arr.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_empty_array_is_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_empty_array_is_empty", ChcConfig::default());

        assert_vc_structure(&vc, "probe_empty_array_is_empty", body.blocks.len());

        let has_constrained_transition =
            vc.rules.iter().any(|r| r.body.relation.is_some() && !r.body.constraints.is_empty());
        assert!(
            has_constrained_transition,
            "probe_empty_array_is_empty should emit len == 0 constraints"
        );
    });
}

fn with_slice_is_empty_dispatch(source: &str, fn_name: &str, assertions: impl FnOnce(&str) + Send) {
    with_test_ay_ctx_for_source(source, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            {
                let Some(path) = chc_ctx.resolve_callee_path(func) else {
                    continue;
                };
                if !(path.ends_with("::is_empty")
                    && (path.contains("slice::") || path.contains("<[")))
                {
                    continue;
                }
                found = true;

                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let modified_locals = HashSet::new();
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };

                assert!(
                    chc_ctx.codegen_call_terminator(&dcx),
                    "slice::is_empty should be handled by call dispatch"
                );

                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "slice::is_empty should dispatch without recording a sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "slice::is_empty direct dispatch should emit exactly one rule"
                );

                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&smt);
                break;
            }
        }

        assert_mir_pattern_found(found, "slice::is_empty");
    });
}

#[test]
fn test_empty_array_is_empty_dispatches_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_empty_array_is_empty() -> bool {
            let arr: [u32; 0] = [];
            arr.is_empty()
        }
    "#;

    with_slice_is_empty_dispatch(SOURCE, "probe_empty_array_is_empty", |smt| {
        assert!(
            smt.contains("= #x0000000000000000") || smt.contains("(_ bv0 64)"),
            "array::is_empty should compare static length against zero, got: {smt}"
        );
    });
}

#[test]
fn test_slice_param_is_empty_dispatches_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_param_is_empty(slice: &[u32]) -> bool {
            slice.is_empty()
        }
    "#;

    with_slice_is_empty_dispatch(SOURCE, "probe_slice_param_is_empty", |_| {});
}

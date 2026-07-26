// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression test for the `VecIsEmpty` sound-fallback path in
//! `codegen_call_vec_core`.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_vec::CallVec;
use super::common::*;
use ay_bindings::Expr;
use trust_mc_core::chc::RelationApp;

/// Vec::is_empty without tracked length must use the vec_core sound fallback
/// instead of constraining the destination to a concrete `true`.
#[test]
fn test_vec_is_empty_untracked_via_vec_core_increments_sound_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_vec_is_empty_fallback(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_is_empty_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) = call_site.expect("expected call terminator in MIR");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: fallback counter at zero");

        let cx = ChcCallContext {
            stub: StubKind::VecIsEmpty,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_vec_core(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one transition rule from vec_core fallback"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "VecIsEmpty via vec_core without tracked length must increment sound fallback counter"
        );

        let fallback_rule = chc_ctx.vc.rules.last().expect("vec_core fallback rule");
        let constraint_texts: Vec<_> =
            fallback_rule.body.constraints.iter().map(ToString::to_string).collect();
        assert_eq!(
            constraint_texts,
            vec![Expr::bool_const(true).to_string()],
            "vec_core fallback must not add a concrete destination=true constraint"
        );
    });
}

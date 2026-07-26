// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared helpers for alloc-extra and layout-semantic call tests.
//!
//! Extracted from test_call_misc.rs (Part of #3746).

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;

/// Shared scaffold: compile a helper with a single `usize` argument, extract
/// the first call site, and provide call parameters to the test body.
pub(super) fn with_misc_usize_call_scaffold(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[inline(never)]
        fn helper(x: usize) -> usize { x.wrapping_add(1) }

        pub fn probe_misc_usize_call(x: usize) -> usize {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_misc_usize_call");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_misc_usize_call", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site =
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target));
                break;
            }
        }
        let (bb_idx, func, args, destination, target) =
            call_site.expect("expected call terminator in probe_misc_usize_call MIR");

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

        body_fn(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
        );
    });
}

pub(super) fn collect_layout_extra_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    body.blocks
        .iter()
        .filter_map(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                chc_ctx.detect_stub_matching(func, StubKind::is_layout_extra)
            } else {
                None
            }
        })
        .collect()
}

pub(super) fn transition_constraint_texts(vc: &trust_mc_core::chc::ChcVc) -> Vec<String> {
    vc.rules
        .iter()
        .filter(|rule| rule.body.relation.is_some())
        .flat_map(|rule| rule.body.constraints.iter())
        .map(ToString::to_string)
        .collect()
}

pub(super) fn has_constraint_with_fragments(constraints: &[String], fragments: &[&str]) -> bool {
    constraints.iter().any(|constraint| fragments.iter().all(|frag| constraint.contains(frag)))
}

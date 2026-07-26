// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_call_primitive_clone_impl — Clone::clone for Copy types.
//!
//! Extracted from test_call_misc.rs (Part of #3746).

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;

/// bool::clone() — ensures primitive clone works for non-integer types.
#[test]
fn test_primitive_clone_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_clone_bool(x: bool) -> bool {
            x.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_clone_bool");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_clone_bool", ChcConfig::default());

        assert_vc_structure(&vc, "probe_clone_bool", body.blocks.len());

        // Bool return type should produce bool-like state vars
        let has_bool = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool, "clone VC should have bool-like state vars");
    });
}

/// Primitive clone fallback must increment CHC fallback counter when argument
/// resolution fails.
#[test]
fn test_primitive_clone_empty_args_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_clone_fallback_site(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_clone_fallback_site");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_clone_fallback_site", ChcConfig::default());
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

        let (bb_idx, destination, target) =
            call_site.expect("expected call terminator in probe_clone_fallback_site MIR");
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
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );

        chc_ctx.codegen_call_primitive_clone_impl(
            &[],
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
        );

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one primitive clone transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "primitive clone unresolved fallback must increment CHC fallback counter"
        );
    });
}

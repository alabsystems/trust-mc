// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::codegen_ay::chc::{ChcConfig, mir_to_chc};
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::Sort;
use rustc_public::mir::{Operand, Place, TerminatorKind};
use std::sync::Arc;

#[test]
fn test_large_step_untranslatable_assert_composition_emits_error_and_successor() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_large_step_untranslatable_assert(x: u32) -> u32 {
            let y = x + 1;
            let z = y.wrapping_mul(2);
            let w = z.wrapping_add(3);
            w
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_large_step_untranslatable_assert");
        let mut body = instance.body().expect("function body");

        let assert_idx = body
            .blocks
            .iter()
            .position(|bb| matches!(bb.terminator.kind, TerminatorKind::Assert { .. }))
            .expect("probe must contain a MIR Assert terminator");

        match &mut body.blocks[assert_idx].terminator.kind {
            TerminatorKind::Assert { cond, .. } => {
                *cond = Operand::Copy(Place { local: 999usize, projection: vec![] });
            }
            other => panic!("expected Assert terminator, got {other:?}"),
        }

        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_large_step_untranslatable_assert",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        let smt = crate::codegen_ay::emit_chc(&vc_large).to_string();
        assert!(
            smt.contains("__mid_bb"),
            "large-step VC must exercise fragment composition; expected __mid_bb vars"
        );

        let error_rules = vc_large.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(error_rules > 0, "untranslatable large-step Assert must still emit an error rule");

        let successor_rules = vc_large
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && r.head.name != "error")
            .count();
        assert!(
            successor_rules > 0,
            "untranslatable large-step Assert must preserve successor reachability"
        );
    });
}

#[test]
fn test_large_step_noncopy_array_iter_composition_does_not_panic_on_late_state_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        struct NonCopyWrapper {
            value: u32,
        }

        impl NonCopyWrapper {
            fn new(v: u32) -> Self {
                Self { value: v }
            }

            fn get(&self) -> u32 {
                self.value
            }
        }

        fn probe_large_step_noncopy_array_iter() -> u32 {
            let arr = [NonCopyWrapper::new(10), NonCopyWrapper::new(20), NonCopyWrapper::new(30)];
            let mut sum = 0u32;
            for item in arr {
                sum += item.get();
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_large_step_noncopy_array_iter");
        let body = instance.body().expect("function body");

        let vc_large = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_large_step_noncopy_array_iter",
            ChcConfig { step_mode: crate::args::ChcStepMode::Large, ..ChcConfig::default() },
        );

        let smt = crate::codegen_ay::emit_chc(&vc_large).to_string();
        assert!(
            !smt.is_empty(),
            "large-step CHC emission for non-Copy array iteration should complete without panic"
        );
    });
}

#[test]
fn test_fragment_compose_snapshot_helpers_handle_late_state_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn probe_fragment_compose_late_state_vars(x: u32) -> u32 {
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fragment_compose_late_state_vars");
        let body = instance.body().expect("function body");
        let mut chc_ctx = super::ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_fragment_compose_late_state_vars",
            ChcConfig::default(),
        );

        chc_ctx.push_state_var_pair("lhs__in", "lhs__out", Sort::bitvec(32));
        chc_ctx.push_state_var_pair("flag", "flag__out", Sort::bool());

        let original_input_names: Vec<Arc<str>> =
            chc_ctx.state_var_mgr.state_vars.iter().map(|(name, _)| Arc::clone(name)).collect();
        let original_output_names: Vec<Arc<str>> = chc_ctx
            .state_var_mgr
            .output_state_vars
            .iter()
            .map(|(name, _)| Arc::clone(name))
            .collect();

        chc_ctx.fragment_mid_output_bb = Some(7);
        let late_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        chc_ctx.push_late_state_var_pair(Arc::from("late_mem"), "late_mem__out", late_sort);

        assert_eq!(
            &*chc_ctx.state_var_mgr.output_state_vars[2].0, "late_mem__mid_bb7",
            "late-created output vars should follow the active composed-block mid name"
        );

        super::set_names_to_mid(&mut chc_ctx, 7, true);
        assert_eq!(
            &*chc_ctx.state_var_mgr.state_vars[0].0, "lhs__mid_bb7",
            "input renaming should preserve the historical __in -> __mid_bb base mapping"
        );
        assert_eq!(
            &*chc_ctx.state_var_mgr.state_vars[2].0, "late_mem__mid_bb7",
            "input renaming should handle late-created vars added after the original snapshot"
        );

        super::restore_names(&mut chc_ctx, &original_input_names, true);
        super::restore_names(&mut chc_ctx, &original_output_names, false);

        assert_eq!(
            &*chc_ctx.state_var_mgr.state_vars[0].0, "lhs__in",
            "original input names should be restored from the saved snapshot"
        );
        assert_eq!(
            &*chc_ctx.state_var_mgr.output_state_vars[1].0, "flag__out",
            "original output names should be restored from the saved snapshot"
        );
        assert_eq!(
            &*chc_ctx.state_var_mgr.state_vars[2].0, "late_mem",
            "late-created input vars should restore to their base name instead of panicking"
        );
        assert_eq!(
            &*chc_ctx.state_var_mgr.output_state_vars[2].0, "late_mem__out",
            "late-created output vars should restore to the canonical __out name"
        );
    });
}

/// Part of #3696: Verify that `rebuild_entry_from_app` produces the correct
/// arity and variable names after a late state var is created and then renamed
/// by `set_names_to_mid`.
///
/// This catches the composed-fragment stale-arity bug: if `from_app` is built
/// before encoding (or only rebuilt once after the loop), late-created state
/// vars are missing from intermediate exit rules.
#[test]
fn test_rebuild_entry_from_app_captures_late_vars_after_renaming() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn probe_rebuild_entry(x: u32) -> u32 {
            if x > 0 { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rebuild_entry");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            super::super::ChcCtx::new(ctx.tcx, &body, "probe_rebuild_entry", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let entry_bb = 0;
        let from_rel = chc_ctx
            .block_relations
            .get(&entry_bb)
            .map(Arc::clone)
            .expect("entry relation must exist after declare_block_relations");

        let original_input_names: Vec<Arc<str>> =
            chc_ctx.state_var_mgr.state_vars.iter().map(|(name, _)| Arc::clone(name)).collect();
        let pre_encode_var_count = chc_ctx.state_var_mgr.state_vars.len();
        let arity_before = chc_ctx.state_var_mgr.live_state_indices[entry_bb].len();
        assert!(arity_before > 0, "entry block must have at least one live state var");

        // Simulate composition: push a late state var (as would happen during
        // encode_block_statements in a non-first block).
        chc_ctx.fragment_mid_output_bb = Some(0);
        let late_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        chc_ctx.push_late_state_var_pair(
            Arc::from("late_region_i32"),
            "late_region_i32__out",
            late_sort,
        );

        // Simulate set_names_to_mid for a subsequent block — this renames ALL
        // input vars (including the late var) to __mid_bb0 names.
        super::set_names_to_mid(&mut chc_ctx, 0, true);

        // Verify the late var was renamed by set_names_to_mid.
        let late_idx = pre_encode_var_count;
        assert!(
            chc_ctx.state_var_mgr.state_vars[late_idx].0.contains("__mid_bb"),
            "late var should have been renamed by set_names_to_mid, got: {}",
            chc_ctx.state_var_mgr.state_vars[late_idx].0,
        );

        // rebuild_entry_from_app must produce correct arity and correct names.
        let from_app = super::rebuild_entry_from_app(
            &chc_ctx,
            entry_bb,
            &from_rel,
            &original_input_names,
            pre_encode_var_count,
        );

        // Arity must include the late var.
        assert_eq!(
            from_app.args.len(),
            arity_before + 1,
            "rebuild_entry_from_app arity must include late var ({} + 1 = {}, got {})",
            arity_before,
            arity_before + 1,
            from_app.args.len(),
        );

        // Pre-existing vars must use original __in names, not __mid_bb names.
        for (i, arg) in from_app.args[..arity_before].iter().enumerate() {
            let name = format!("{}", arg);
            assert!(
                !name.contains("__mid_bb"),
                "pre-existing arg {i} should use original __in name, got: {name}"
            );
        }

        // Late var must use base name (stripped of __mid_bb), not the renamed name.
        let late_arg_name = format!("{}", from_app.args[arity_before]);
        assert!(
            !late_arg_name.contains("__mid_bb"),
            "late var arg should use base name, not __mid_bb renamed name, got: {late_arg_name}"
        );
        assert!(
            late_arg_name.contains("late_region_i32"),
            "late var arg should contain the base name 'late_region_i32', got: {late_arg_name}"
        );
    });
}

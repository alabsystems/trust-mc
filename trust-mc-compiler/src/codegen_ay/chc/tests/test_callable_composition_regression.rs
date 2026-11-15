// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A copied native borrow keeps its actual owner and observes the latest store.
use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

const SOURCE: &str = r#"
    fn increment(value: &mut i32) { *value = value.wrapping_add(1); }
    fn user_forward(mut function: Box<dyn FnMut(&mut i32)>, value: &mut i32) {
        *value = 7;
        function(value);
    }
    pub fn copied_owner_current_value_safe() {
        let mut actual = 1i32;
        let mut decoy = 41i32;
        let decoy_reference = &mut decoy;
        user_forward(Box::new(&increment), &mut actual);
        assert!(actual == 8);
        assert!(*decoy_reference == 41);
    }
    pub fn copied_owner_stale_value_bug() {
        let mut actual = 1i32;
        let mut decoy = 41i32;
        let decoy_reference = &mut decoy;
        user_forward(Box::new(&increment), &mut actual);
        assert!(*decoy_reference == 41);
        assert!(actual == 2);
    }
"#;
#[test]
fn copied_native_mutable_reference_reads_current_exact_owner() {
    with_native_box_ctx(SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for (name, expected) in
            [("copied_owner_current_value_safe", "unsat"), ("copied_owner_stale_value_bug", "sat")]
        {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            });
            let (_, body) = pass.transform_with_body_provider(
                ctx.tcx,
                instance.callee_body().unwrap(),
                instance,
                |callee| {
                    if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                        None
                    } else {
                        callee.callee_body()
                    }
                },
            );
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let verdict =
                run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "COPIED_OWNER_COMPOSITION {name}: {verdict:?}; drops={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            assert_eq!(
                verdict.as_deref(),
                Ok(expected),
                "{name}: current owner memory and same-sort decoy"
            );
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: {reasons:?}");
            assert!(reasons.is_empty(), "{name}: {reasons:?}");
        }
    });
}

#[test]
fn production_rustcall_mutable_owner_selects_memory_before_encoding() {
    with_native_box_ctx(SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for (name, expected) in
            [("copied_owner_current_value_safe", "unsat"), ("copied_owner_stale_value_bug", "sat")]
        {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            });
            let (_, body) = pass.transform_with_body_provider(
                ctx.tcx,
                instance.callee_body().unwrap(),
                instance,
                |callee| {
                    if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                        None
                    } else {
                        callee.callee_body()
                    }
                },
            );
            let harness_name = format!("rustcall_memory_preselection_{name}");
            for track_level in [crate::args::ChcTrackLevel::Reg, crate::args::ChcTrackLevel::Ptr] {
                let vc = mir_to_chc(
                    ctx.tcx,
                    &body,
                    harness_name.as_str(),
                    ChcConfig { track_level, ..ChcConfig::default() },
                );
                let verdict =
                    run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
                assert_eq!(verdict.as_deref(), Ok(expected), "{track_level:?} {name}");
                let drops = take_translation_drop_by_fn();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                assert_eq!(
                    drops.get(&harness_name).copied().unwrap_or(0),
                    0,
                    "{name}: {reasons:?}"
                );
                assert!(
                    reasons.get(&harness_name).is_none_or(|r| r.is_empty()),
                    "{name}: {reasons:?}"
                );
            }
        }
    });
}

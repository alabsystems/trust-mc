// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Real native-MIR Vec append semantics and the existing raw alias boundary.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

#[test]
fn native_vec_clear_and_truncate_do_not_treat_container_names_as_empty_drop() {
    let source = r#"
        pub struct Bomb;
        impl Drop for Bomb { fn drop(&mut self) { assert!(false); } }
        pub struct Mutex<T> { pub value: T }
        impl<T> Drop for Mutex<T> { fn drop(&mut self) { assert!(false); } }
        pub fn clear_nested(values: &mut Vec<Vec<Bomb>>) { values.clear(); }
        pub fn truncate_named(values: &mut Vec<Mutex<u64>>) { values.truncate(0); }
    "#;
    with_native_box_ctx(source, |ctx| {
        for name in ["clear_nested", "truncate_named"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (vc, _, _) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            assert!(
                reasons.get("vec_mutation_drop_effects_unmodelled").copied().unwrap_or(0) > 0,
                "actual payload/user Drop remains an obligation for {name}: {reasons:?}"
            );
            assert!(
                !vc.approximation_identity_complete,
                "unwalked Drop effects must retain their refusal"
            );
        }
    });
}

#[test]
fn native_vec_partial_remove_keeps_its_refusal_through_append() {
    let source = include_str!("../../../../../tools/soundness-duals/vec_append_transfer_dual.rs")
        .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            let name = "append_partial_remove_refusal";
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let (_, body) = FunctionInlinePass::new(InlineConfig {
                max_depth: depth,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            })
            .transform_with_body_provider(
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
            let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
            assert!(
                body.blocks.iter().any(|block| match &block.terminator.kind {
                    rustc_public::mir::TerminatorKind::Call { func, .. } =>
                        context.detect_stub(func) == Some(StubKind::VecRemove)
                            && context.detect_stub_matching(func, StubKind::is_vec_core)
                                == Some(StubKind::VecRemove),
                    _ => false,
                }),
                "the original Vec remove call must remain in the native MIR"
            );
            let (vc, _, _) = context.translate_with_diagnostics();
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            assert!(
                reasons.get("vec_mutation_effects_unmodelled").copied().unwrap_or(0) > 0,
                "partial effects must not become dead length-only havoc: {reasons:?}"
            );
            assert!(
                !vc.approximation_identity_complete,
                "an incomplete mutation cannot restore clean proof/refutation authority"
            );
        }
    });
}

#[test]
fn native_vec_append_transfers_current_elements_and_clears_source() {
    let source = include_str!("../../../../../tools/soundness-duals/vec_append_transfer_dual.rs")
        .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for name in [
                "append_literal_safe",
                "append_literal_bug",
                "append_updated_source_safe",
                "append_updated_source_bug",
                "append_empty_destination_safe",
                "append_empty_destination_bug",
                "append_cleared_source_safe",
                "append_cleared_source_bug",
                "append_truncated_source_safe",
                "append_truncated_source_bug",
                "append_buffer_alias_refusal",
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let (_, body) = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                })
                .transform_with_body_provider(
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
                let (mut vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                if name.ends_with("refusal") {
                    assert!(
                        reasons.get("vec_buffer_access_after_mutation").copied().unwrap_or(0) > 0,
                        "{name} depth={depth}: {reasons:?}"
                    );
                    assert!(
                        !vc.approximation_identity_complete,
                        "unaccounted buffer alias remains a refusal"
                    );
                    continue;
                }
                // Exercise the existing production emitter passes as well as
                // native MIR lowering. Attempt 1's raw pre-emitter Unknowns
                // remain recorded separately; every Safe/Bug oracle stays
                // strict here, including the newly added composition rows.
                let disabled =
                    crate::codegen_ay::context::chc_requires_unreduced_obligations(&vc, false)
                        || std::env::var("TRUST_MC_NO_CONST_PROP").is_ok_and(|value| value == "1");
                crate::codegen_ay::context::run_emit_time_chc_passes(&mut vc, disabled);
                let smt = crate::codegen_ay::emit_chc(&vc).to_string();
                let verdict = run_z3_on_smt2_with_timeout(&smt, 30);
                let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                eprintln!(
                    "APPEND depth={depth} {name} {verdict:?} drops={} reasons={reasons:?} guard={disabled} lambda={}",
                    diagnostics.place_translation_drop.get(), smt.contains("(lambda ")
                );
                if verdict.as_deref() != Ok(expected)
                    || !reasons.is_empty()
                    || diagnostics.place_translation_drop.get() != 0
                {
                    if let Some(dir) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") {
                        let dir = std::path::Path::new(&dir);
                        std::fs::write(dir.join(format!("{depth}-{name}.smt2")), &smt).unwrap();
                        std::fs::write(
                            dir.join(format!("{depth}-{name}.mir")),
                            format!("{body:#?}"),
                        )
                        .unwrap();
                    }
                    panic!(
                        "native append failed: depth={depth} {name} {verdict:?}, reasons={reasons:?}"
                    );
                }
            }
        }
    });
}

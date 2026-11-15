// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exercise the real preprocessing boundary before the native Box model.

use super::common::*;
use super::test_trust_box_new::{mem_config, native_box_runtime_source, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

#[test]
fn preprocessed_native_box_fixture_keeps_strict_read_write_and_drop_semantics() {
    let source = native_box_runtime_source();
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut failures = Vec::new();
        for name in [
            "boxed_scalar_read_safe",
            "boxed_scalar_wrong_value_bug",
            "boxed_array_element_read_safe",
            "boxed_array_wrong_element_bug",
            "boxed_symbolic_element_write_safe",
            "boxed_symbolic_element_wrong_value_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            });
            let (_, body) = pass.transform_with_body_provider(ctx.tcx, body, instance, |callee| {
                if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                    None
                } else {
                    callee.callee_body()
                }
            });
            assert!(
                body.blocks.iter().any(|block| matches!(
                    block.terminator.kind,
                    rustc_public::mir::TerminatorKind::Drop { .. }
                )),
                "{name}: actual Box Drop must survive preprocessing"
            );
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let result =
                run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            eprintln!(
                "PREPROCESSED_BOX {name}: {result:?}; drops={}",
                diagnostics.place_translation_drop.get()
            );
            if result.as_deref() != Ok(expected) || diagnostics.place_translation_drop.get() != 0 {
                failures.push((name, result, diagnostics.place_translation_drop.get()));
            }
        }
        assert!(failures.is_empty(), "preprocessed Box rows: {failures:?}");
    });
}

#[test]
fn thin_box_drop_cannot_silently_elide_a_real_pointee_destructor() {
    let source = r#"
        #![allow(dead_code)]
        struct Payload(u8);
        impl Drop for Payload {
            fn drop(&mut self) { assert!(self.0 == 7); }
        }
        pub fn destructor_safe() { let _value = Box::new(Payload(7)); }
        pub fn destructor_bug() { let _value = Box::new(Payload(0)); }
    "#;
    with_native_box_ctx(source, |ctx| {
        for name in ["destructor_safe", "destructor_bug"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let result =
                run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            // A recorded aggregate approximation can yield a spurious SAT
            // counterexample; the driver demotes it. It cannot excuse a false
            // UNSAT proof of the bug twin.
            let demoted_counterexample = name.ends_with("safe")
                && result.as_deref() == Ok("sat")
                && diagnostics.aggregate_encoding_gap.get() > 0;
            eprintln!(
                "DESTRUCTOR_MODEL {name}: {result:?}; drop={}; aggregate_gap={}",
                diagnostics.place_translation_drop.get(),
                diagnostics.aggregate_encoding_gap.get()
            );
            assert!(
                result.as_deref() == Ok(expected)
                    || diagnostics.place_translation_drop.get() > 0
                    || demoted_counterexample,
                "{name}: real destructor had wrong clean model: {result:?}"
            );
        }
    });
}

#[test]
fn preprocessed_native_fat_box_keeps_complete_destructors_and_successors() {
    use rustc_public::mir::{TerminatorKind, mono::Instance};
    use rustc_public::ty::{RigidTy, TyKind};

    let source = include_str!("../../../../../tools/soundness-duals/chc_native_box_drop_dual.rs")
        .replace("#[kani::proof]", "")
        .replace("let branch: bool = kani::any();", "let branch: bool = false;");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut failures = Vec::new();
        for (name, expected, has_complete_drop) in [
            ("quiet_with_loud_decoy_safe", "unsat", true),
            ("quiet_with_loud_decoy_bug", "sat", true),
            ("empty_drop_successor_bug", "sat", true),
            ("loud_effect_safe", "unsat", true),
            ("loud_effect_bug", "sat", true),
            ("user_destructor_panic_bug", "sat", true),
            ("walked_loud_effect_safe", "unsat", true),
            ("walked_loud_effect_bug", "sat", true),
            ("explicit_mem_drop_effect_safe", "unsat", true),
            ("explicit_mem_drop_effect_bug", "sat", true),
            ("user_named_drop_keeps_its_body_safe", "unsat", false),
            ("user_named_drop_keeps_its_body_bug", "sat", false),
        ] {
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
            let complete_boundary = body.blocks.iter().any(|block| match &block.terminator.kind {
                TerminatorKind::Drop { place, .. } => {
                    place.ty(body.locals()).ok().is_some_and(|ty| {
                        crate::codegen_ay::native_global_box_pointee(ctx.tcx, ty).is_some_and(
                            |inner| matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))),
                        )
                    })
                }
                TerminatorKind::Call { func, .. } => (|| {
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                        func.ty(body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    let callee = Instance::resolve(def, &args).ok()?;
                    crate::codegen_ay::native_global_dyn_box_drop_value(ctx.tcx, &callee)
                })()
                .is_some(),
                _ => false,
            });
            // The user's lookalike calls mem::forget and writes its own
            // observable value: no native drop exists for that negative control.
            assert_eq!(complete_boundary, has_complete_drop, "{name}: native drop identity");
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let result =
                run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
            eprintln!(
                "PREPROCESSED_FAT_BOX {name}: {result:?}; drops={}",
                diagnostics.place_translation_drop.get()
            );
            if result.as_deref() != Ok(expected) || diagnostics.place_translation_drop.get() != 0 {
                failures.push((name, result, diagnostics.place_translation_drop.get()));
            }
        }
        assert!(failures.is_empty(), "preprocessed fat-Box rows: {failures:?}");
    });
}

#[test]
fn preprocessed_native_box_callable_keeps_mutable_writeback() {
    let original =
        include_str!("../../../../../tools/soundness-duals/callable_reference_tuple_dual.rs");
    // These two original bodies need no arbitrary-value hook. Keep their
    // helper and assertions unchanged while using the native compiler fixture.
    let source = original
        .split("#[kani::proof]\nfn captured_reference_predicate_safe")
        .next()
        .unwrap()
        .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut failures = Vec::new();
        for depth in [0, 1, 32] {
            for (name, expected) in [
                ("boxed_callable_reference_writeback_safe", "unsat"),
                ("boxed_callable_wrong_writeback_bug", "sat"),
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let mut pass = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
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
                if let Some(dir) = std::env::var_os("MC_CALLABLE_OWNERSHIP_ARTIFACT_DIR") {
                    std::fs::write(
                        std::path::Path::new(&dir).join(format!("{name}-depth{depth}.mir")),
                        format!("{body:?}"),
                    )
                    .unwrap();
                }
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
                if let Some(dir) = std::env::var_os("MC_CALLABLE_OWNERSHIP_ARTIFACT_DIR") {
                    std::fs::write(
                        std::path::Path::new(&dir).join(format!("{name}-depth{depth}.smt2")),
                        crate::codegen_ay::emit_chc(&vc).to_string(),
                    )
                    .unwrap();
                }
                let verdict =
                    run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                eprintln!(
                    "PREPROCESSED_BOX_CALLABLE depth={depth} {name}: {verdict:?}; drops={}; reasons={reasons:?}",
                    diagnostics.place_translation_drop.get()
                );
                if depth == 32
                    && (verdict.as_deref() != Ok(expected)
                        || diagnostics.place_translation_drop.get() != 0
                        || !reasons.is_empty())
                {
                    failures.push((
                        name,
                        verdict,
                        diagnostics.place_translation_drop.get(),
                        reasons,
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "preprocessed boxed callable semantics: {failures:?}");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Original intrinsic copy bugs and their valid wrapping-pointer sibling.

use super::common::*;
use super::test_trust_box_new::mem_config;
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use trust_mc_core::PropertyKind;

fn source() -> String {
    let originals = [
        (
            include_str!(
                "../../../../../tests/expected/intrinsics/copy/copy-unreadable-src/main.rs"
            ),
            "test_copy_invalid",
            "copy_unreadable_source_bug",
        ),
        (
            include_str!(
                "../../../../../tests/expected/intrinsics/copy-nonoverlapping/copy-unreadable-src/main.rs"
            ),
            "test_copy_nonoverlapping_invalid",
            "nonoverlapping_unreadable_source_bug",
        ),
    ];
    let mut source = String::from("#![feature(core_intrinsics)]\n#![allow(dead_code)]\n");
    for (original, old_name, name) in originals {
        // Keep each original operation verbatim; only join crate attributes
        // and replace the proof registration/function name for this native test.
        source.push_str(
            &original
                .lines()
                .filter(|line| !line.trim_start().starts_with("#!["))
                .collect::<Vec<_>>()
                .join("\n")
                .replace("#[kani::proof]", "")
                .replace(old_name, name),
        );
        source.push('\n');
    }
    source.push_str(include_str!("fixtures/intrinsic_copy_wrapping.rs"));
    source
}

#[test]
fn native_intrinsic_copy_wrapping_source_bounds_preserve_oracles() {
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source(),
        &["-Cpanic=abort", "-Aunstable_imports"],
        |ctx| {
            let abstraction = StdAbstraction::resolve(ctx.tcx);
            for depth in [0, 32] {
                for (name, expected) in [
                    ("copy_unreadable_source_bug", "sat"),
                    ("nonoverlapping_unreadable_source_bug", "sat"),
                    ("copy_wrapping_valid", "unsat"),
                    ("copy_far_wrapping_refusal", "refused"),
                ] {
                    let label = format!("{name}_depth{depth}");
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
                            if native_assertion_panic_boundary(ctx.tcx, callee)
                                || abstraction.abstracts_public_instance(ctx.tcx, callee)
                            {
                                None
                            } else {
                                callee.callee_body()
                            }
                        },
                    );
                    let (vc, _, diagnostics) =
                        ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                            .translate_with_diagnostics();
                    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
                    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                        .remove(&label)
                        .unwrap_or_default();
                    if let Some(dir) = std::env::var_os("MC_INTRINSIC_COPY_ARTIFACT_DIR") {
                        let dir = std::path::Path::new(&dir);
                        std::fs::create_dir_all(dir).unwrap();
                        std::fs::write(dir.join(format!("{label}.mir")), format!("{body:#?}"))
                            .unwrap();
                        std::fs::write(dir.join(format!("{label}.smt2")), &smt).unwrap();
                        std::fs::write(
                            dir.join(format!("{label}.json")),
                            serde_json::to_vec_pretty(&serde_json::json!({
                                "name":name,"depth":depth,"expected":expected,
                                "fallbacks":diagnostics.fallback_count.get(),
                                "drops":diagnostics.place_translation_drop.get(),
                                "sound_havoc":diagnostics.sound_havoc_drop.get(),
                                "offset_provenance":diagnostics.offset_provenance_unresolved.get(),
                                "reasons":reasons,
                            }))
                            .unwrap(),
                        )
                        .unwrap();
                    }
                    if expected == "refused" {
                        assert!(
                            diagnostics.fallback_count.get() > 0
                                || diagnostics.place_translation_drop.get() > 0
                                || diagnostics.sound_havoc_drop.get() > 0,
                            "{label}: a far step must not acquire a bounded array view",
                        );
                        continue;
                    }
                    assert!(reasons.is_empty(), "{label}: {reasons:?}");
                    assert_eq!(diagnostics.fallback_count.get(), 0, "{label}");
                    assert_eq!(diagnostics.place_translation_drop.get(), 0, "{label}");
                    assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{label}");
                    assert_eq!(diagnostics.offset_provenance_unresolved.get(), 0, "{label}");
                    assert!(vc.approximation_identity_complete, "{label}");
                    let kind = if expected == "sat" {
                        PropertyKind::MemorySafety
                    } else {
                        PropertyKind::Assertion
                    };
                    assert!(vc.properties.iter().any(|property| property.kind == kind), "{label}");
                    let actual = run_z3_on_smt2_with_timeout(&smt, 60).unwrap();
                    assert_eq!(actual, expected, "{label}");
                }
            }
        },
    );
}

#[test]
fn native_intrinsic_copy_alias_counts_and_foreign_steps_have_no_static_span() {
    use super::super::codegen_ctx::types::RefTarget;
    use rustc_public::mir::{Place, Rvalue, StatementKind, TerminatorKind};

    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source(),
        &["-Cpanic=abort", "-Aunstable_imports"],
        |ctx| {
            for name in [
                "copy_alias_count_valid",
                "copy_alias_displacement_valid",
                "copy_foreign_wrapping_valid",
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let body = instance.callee_body().unwrap();
                let chc = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                let args = body
                    .blocks
                    .iter()
                    .find_map(|block| {
                        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                            return None;
                        };
                        chc.resolve_callee_path(func)
                            .filter(|path| path.contains("intrinsics::copy"))
                            .map(|_| args)
                    })
                    .expect("retain the actual intrinsic copy");
                let array = body
                    .locals()
                    .iter()
                    .enumerate()
                    .find_map(|(local, declaration)| {
                        let ty = chc.resolve_body_ty(declaration.ty);
                        (matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                            && chc.get_array_length(ty) == Some(3))
                        .then_some(local)
                    })
                    .expect("the original fixed array");
                let target = RefTarget { local: array, projections: Vec::new() };
                if name != "copy_foreign_wrapping_valid" {
                    let borrowed = body
                        .blocks
                        .iter()
                        .flat_map(|block| &block.statements)
                        .find_map(|statement| {
                            let StatementKind::Assign(_, Rvalue::AddressOf(_, place)) =
                                &statement.kind
                            else {
                                return None;
                            };
                            (place.projection.is_empty()
                                && matches!(
                                    place.ty(body.locals()).unwrap().kind(),
                                    TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))
                                ))
                            .then_some(place.local)
                        })
                        .expect("retain the integer's actual address escape");
                    assert!(
                        body.blocks.iter().flat_map(|block| &block.statements).any(
                            |statement| matches!(&statement.kind, StatementKind::Assign(place, _)
                            if matches!(place.projection.first(), Some(
                                rustc_public::mir::ProjectionElem::Deref))),
                        ),
                        "{name}: retain the actual indirect store"
                    );
                    let integer = Operand::Copy(Place { local: borrowed, projection: Vec::new() });
                    assert_eq!(chc.body_constant_int(&integer), None, "{name}: aliased integer");
                }
                if name == "copy_alias_count_valid" {
                    assert_eq!(chc.body_constant_int(&args[2]), None, "copies and casts of count");
                } else {
                    let (Operand::Copy(pointer) | Operand::Move(pointer)) = &args[0] else {
                        panic!("native pointer operand")
                    };
                    assert_eq!(
                        chc.native_array_pointer_byte_offset(pointer.local, &target),
                        None,
                        "{name}: no exact span from an aliased step or a foreign function",
                    );
                }
            }
        },
    );
}

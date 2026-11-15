// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn closed_native_empty_and_nonempty_joins_retain_guarded_successors() {
    let source = source()
        .replace("fn empty_and_loud_join_safe()", "fn empty_and_loud_join_safe(branch:bool)")
        .replace("fn empty_and_loud_join_bug()", "fn empty_and_loud_join_bug(branch:bool)")
        .replace("let branch: bool = false;", "");
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source,
        &["-Cpanic=abort"],
        |ctx| {
            for name in ["empty_and_loud_join_safe", "empty_and_loud_join_bug"] {
                let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                let (vc, _, diagnostics) = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    name,
                    ChcConfig {
                        track_level: crate::args::ChcTrackLevel::Mem,
                        ..ChcConfig::default()
                    },
                )
                .translate_with_diagnostics();
                assert_eq!(
                    diagnostics.place_translation_drop.get(),
                    0,
                    "{name}: closed typed native origins"
                );
                let (site,target)=body.blocks.iter().enumerate().find_map(|(site,block)|match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Drop{place,target,..} if place.ty(body.locals()).ok().is_some_and(|ty|matches!(ty.kind(),TyKind::RigidTy(RigidTy::Adt(def,args)) if def.is_box() && matches!(args.0.first(),Some(rustc_public::ty::GenericArgKind::Type(inner)) if matches!(inner.kind(),TyKind::RigidTy(RigidTy::Dynamic(..)))))) =>Some((site,*target)),
                _=>None,
            }).unwrap();
                let from = format!("{name}__bb{site}");
                let to = format!("{name}__bb{target}");
                let arms = vc
                    .rules
                    .iter()
                    .filter(|rule| {
                        rule.body
                            .relation
                            .as_ref()
                            .is_some_and(|relation| relation.name.as_str() == from)
                            && rule.head.name.as_str() == to
                    })
                    .collect::<Vec<_>>();
                assert_eq!(arms.len(), 2, "both actual empty and nonempty drops retain successors");
                let mut ids = HashSet::new();
                for arm in arms {
                    let guards=arm.body.constraints.iter().filter_map(|constraint|match constraint.value(){
                    ExprValue::Eq(left,right) if matches!(left.value(),ExprValue::Var{name} if name.starts_with("__vtable_sv_")) => match right.value(){ExprValue::BitVecConst{value,width:64}=>Some(value.to_string()),_=>None},
                    _=>None,
                }).collect::<Vec<_>>();
                    assert_eq!(
                        guards.len(),
                        1,
                        "every actual native drop arm has one metadata guard"
                    );
                    ids.insert(guards[0].clone());
                }
                assert_eq!(ids.len(), 2, "empty and nonempty runtime candidates remain distinct");
            }
        },
    );
}

/// Solver semantic controls for each real Boolean specialization. The strict
/// symbolic source twins remain in the runtime manifest; AY77 returned Unknown
/// on their larger memory query, which is not accepted as a proof by this test.
#[test]
fn every_concrete_join_arm_observes_its_own_destructor() {
    for branch in [false, true] {
        let source =
            source().replace("let branch: bool = false;", &format!("let branch: bool = {branch};"));
        crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
            &source,
            &["-Cpanic=abort"],
            |ctx| {
                for (name, expected) in [
                    ("empty_and_loud_join_safe", "unsat"),
                    ("empty_and_loud_join_bug", if branch { "unsat" } else { "sat" }),
                ] {
                    let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                    let (vc, _, diagnostics) = ChcCtx::new(
                        ctx.tcx,
                        &body,
                        name,
                        ChcConfig {
                            track_level: crate::args::ChcTrackLevel::Mem,
                            ..ChcConfig::default()
                        },
                    )
                    .translate_with_diagnostics();
                    let query = crate::codegen_ay::emit_chc(&vc).to_string();
                    assert_eq!(
                        run_z3_on_smt2_with_timeout(&query, 30).unwrap(),
                        expected,
                        "{name}: branch={branch}"
                    );
                    assert_eq!(
                        diagnostics.place_translation_drop.get(),
                        0,
                        "{name}: branch={branch}"
                    );
                }
            },
        );
    }
}

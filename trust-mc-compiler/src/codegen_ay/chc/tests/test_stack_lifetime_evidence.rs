// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::common::*;
use rustc_public::mir::{
    BasicBlock, Body, RawPtrKind, Rvalue, StatementKind, SwitchTargets, TerminatorKind,
};

const SOURCE: &str = r#"
    pub fn pointer(flag: bool) -> *const [u8; 2] {
        let array = [flag as u8, 2];
        &array as *const _
    }
    pub fn zero() -> *const [u8; 0] {
        let array = [];
        &array as *const _
    }
"#;

fn block(
    template: &BasicBlock,
    statements: Vec<StatementKind>,
    terminator: TerminatorKind,
) -> BasicBlock {
    let span = mir_span!(template.terminator);
    BasicBlock {
        statements: statements
            .into_iter()
            .map(|s| crate::rustc_compat::mir_statement(s, span))
            .collect(),
        terminator: crate::rustc_compat::mir_terminator(terminator, span),
    }
}

fn address(owner: usize) -> StatementKind {
    StatementKind::Assign(Place::from(0), Rvalue::AddressOf(RawPtrKind::Const, Place::from(owner)))
}

fn owner(body: &Body) -> usize {
    body.locals()
        .iter()
        .position(|l| matches!(l.ty.kind(), TyKind::RigidTy(RigidTy::Array(..))))
        .unwrap()
}

fn set_block(ctx: &mut ChcCtx<'_, '_>, index: usize) {
    ctx.current_encode_bb = index;
    ctx.liveness.dead_locals = ctx.liveness.dead_locals_at_entry[index].clone();
    ctx.liveness.maybe_dead_locals = ctx.liveness.maybe_dead_locals_at_entry[index].clone();
}

#[test]
fn test_stack_lifetime_evidence_live_dead_and_mixed_join() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut body = find_instance_by_suffix(ctx.tcx, "pointer").body().unwrap();
        let local = owner(&body);
        let template = body.blocks[0].clone();
        body.blocks = vec![
            block(&template, vec![], TerminatorKind::Goto { target: 1 }),
            block(
                &template,
                vec![StatementKind::StorageLive(local), address(local)],
                TerminatorKind::Goto { target: 2 },
            ),
            block(
                &template,
                vec![StatementKind::StorageDead(local)],
                TerminatorKind::Goto { target: 3 },
            ),
            block(&template, vec![], TerminatorKind::Return),
        ];
        let mut chc = ChcCtx::new(ctx.tcx, &body, "lifetime_linear", ChcConfig::default());
        let (must, may) = super::super::stack_storage_liveness_at_entry(&body);
        assert_eq!(must, chc.liveness.dead_locals_at_entry);
        assert_eq!(may, chc.liveness.maybe_dead_locals_at_entry);
        set_block(&mut chc, 1);
        assert_eq!(chc.stack_local_is_live(local), Some(false), "before explicit StorageLive");
        set_block(&mut chc, 2);
        assert_eq!(chc.stack_local_is_live(local), Some(true));
        set_block(&mut chc, 3);
        assert_eq!(chc.stack_local_is_live(local), Some(false));

        body.blocks = vec![
            block(
                &template,
                vec![StatementKind::StorageLive(local), address(local)],
                TerminatorKind::SwitchInt {
                    discr: Operand::Copy(Place::from(1)),
                    targets: SwitchTargets::new(vec![(0, 1)], 2),
                },
            ),
            block(
                &template,
                vec![StatementKind::StorageDead(local)],
                TerminatorKind::Goto { target: 3 },
            ),
            block(&template, vec![], TerminatorKind::Goto { target: 3 }),
            block(&template, vec![], TerminatorKind::Return),
        ];
        let mut chc = ChcCtx::new(ctx.tcx, &body, "lifetime_join", ChcConfig::default());
        set_block(&mut chc, 3);
        assert!(!chc.liveness.dead_locals.contains(&local));
        assert!(chc.liveness.maybe_dead_locals.contains(&local));
        assert_eq!(chc.stack_local_is_live(local), None);
    });
}

#[test]
fn test_stack_lifetime_evidence_refuses_cycle_and_unrolled_reactivation() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut body = find_instance_by_suffix(ctx.tcx, "pointer").body().unwrap();
        let local = owner(&body);
        let template = body.blocks[0].clone();
        for cycle in [true, false] {
            body.blocks = if cycle {
                vec![
                    block(
                        &template,
                        vec![StatementKind::StorageLive(local), address(local)],
                        TerminatorKind::Goto { target: 1 },
                    ),
                    block(
                        &template,
                        vec![],
                        TerminatorKind::SwitchInt {
                            discr: Operand::Copy(Place::from(1)),
                            targets: SwitchTargets::new(vec![(0, 0)], 2),
                        },
                    ),
                    block(&template, vec![], TerminatorKind::Return),
                ]
            } else {
                vec![
                    block(
                        &template,
                        vec![StatementKind::StorageLive(local), address(local)],
                        TerminatorKind::Goto { target: 1 },
                    ),
                    block(
                        &template,
                        vec![StatementKind::StorageDead(local)],
                        TerminatorKind::Goto { target: 2 },
                    ),
                    block(
                        &template,
                        vec![StatementKind::StorageLive(local), address(local)],
                        TerminatorKind::Goto { target: 3 },
                    ),
                    block(&template, vec![], TerminatorKind::Return),
                ]
            };
            let mut chc = ChcCtx::new(ctx.tcx, &body, "lifetime_reentry", ChcConfig::default());
            set_block(&mut chc, if cycle { 1 } else { 3 });
            assert_eq!(chc.stack_local_is_live(local), None, "cycle={cycle}");
            chc.ref_resolution.ref_targets.insert(
                0,
                crate::codegen_ay::chc::codegen_ctx::types::RefTarget::with_projections(
                    local,
                    vec![],
                ),
            );
            chc.emit_ptr_obj_valid_check(0, &HashSet::new());
            assert!(chc.diagnostics.sound_havoc_drop.get() == 0, "reentry is not sound havoc");
            assert!(
                chc.diagnostics.place_translation_drop.get() > 0,
                "reentry must prevent clean certification"
            );
        }
    });
}

#[test]
fn test_stack_lifetime_evidence_raw_deref_checks_and_zero_sized_exception() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["pointer", "zero"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let local = owner(&body);
            for state in ["live", "dead", "mixed"] {
                let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                chc.current_encode_bb = 0;
                chc.liveness.dead_locals.clear();
                chc.liveness.maybe_dead_locals.clear();
                if state == "dead" {
                    chc.liveness.dead_locals.insert(local);
                }
                if state != "live" {
                    chc.liveness.maybe_dead_locals.insert(local);
                }
                chc.ref_resolution.ref_targets.insert(
                    0,
                    crate::codegen_ay::chc::codegen_ctx::types::RefTarget::with_projections(
                        local,
                        vec![],
                    ),
                );
                chc.emit_ptr_obj_valid_check(0, &HashSet::new());
                let zero = name == "zero";
                if state == "dead" && !zero {
                    assert!(
                        chc.heap_state
                            .pending_checks
                            .iter()
                            .any(|p| matches!(p.value(), ExprValue::BoolConst(false)))
                    );
                } else {
                    assert!(chc.heap_state.pending_checks.is_empty(), "{name}/{state}");
                }
                assert_eq!(
                    chc.diagnostics.place_translation_drop.get() > 0,
                    state == "mixed" && !zero,
                    "{name}/{state}"
                );
            }
        }
    });
}

#[test]
fn test_stack_lifetime_evidence_bounds_and_unreachable_reactivation() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut body = find_instance_by_suffix(ctx.tcx, "pointer").body().unwrap();
        let local = owner(&body);
        let template = body.blocks[0].clone();
        body.blocks = vec![
            block(
                &template,
                vec![StatementKind::StorageLive(local), address(local)],
                TerminatorKind::Return,
            ),
            block(
                &template,
                vec![StatementKind::StorageLive(local), address(local)],
                TerminatorKind::Return,
            ),
        ];
        assert!(
            !super::super::reused_address_taken_locals(&body).unwrap().contains(&local),
            "an unreachable activation is not evidence of reuse"
        );
        body.blocks[0].statements = (0..262_144)
            .map(|_| {
                crate::rustc_compat::mir_statement(
                    StatementKind::Nop,
                    mir_span!(template.terminator),
                )
            })
            .collect();
        assert!(
            super::super::reused_address_taken_locals(&body).is_none(),
            "work exhaustion must retain refusal, not an empty safe set"
        );
    });
}

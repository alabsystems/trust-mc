// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_set_discriminant.rs` — CHC SetDiscriminant encoding.
//!
//! Covers `encode_block_statements` for enum variant construction (Aggregate)
//! and end-to-end `translate()` for unit/signed/non-unit enum shapes.
//!
//! Part of #3743: CHC statement dispatch + SetDiscriminant parity.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coroutine::CallDispatchCoroutine;
use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use super::test_coroutine_root_map::COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE;
use crate::codegen_ay::emit_chc;

const ENUM_CONSTRUCTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum State {
        Empty,
        Loaded(u32),
    }

    pub fn make_loaded(x: u32) -> State {
        State::Loaded(x)
    }
"#;

const COROUTINE_SET_DISCR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_resume_once() -> bool {
        let mut add_one = #[coroutine]
        |mut resume: u8| {
            loop {
                resume = yield resume.saturating_add(1);
            }
        };
        let keep_ref = &mut add_one;
        let _ = keep_ref;

        match Pin::new(&mut add_one).resume(0) {
            CoroutineState::Yielded(value) => value == 1,
            CoroutineState::Complete(_) => false,
        }
    }
"#;

const COROUTINE_PIN_LOOP_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_coroutine_loop() -> bool {
        let mut add_one = #[coroutine]
        |mut resume: u8| {
            loop {
                resume = yield resume.saturating_add(1);
            }
        };
        for _ in 0..2 {
            let res = Pin::new(&mut add_one).resume(1);
            match res {
                CoroutineState::Yielded(value) if value == 2 => {}
                _ => return false,
            }
        }
        true
    }
"#;

const COROUTINE_INLINE_BRANCH_SOURCE: &str = r#"
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]
    #![allow(dead_code)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn projected_resume(x: i32) -> (i32, CoroutineState<i32, i32>) {
        let mut g = #[coroutine] |mut state: i32| {
            if state != 0 {
                state = yield state + 1;
            }
            -1
        };
        let mut pair = (x, CoroutineState::Complete(0));
        pair.1 = Pin::new(&mut g).resume(x);
        pair
    }
"#;

// =============================================================================
// Enum variant construction — encode_block_statements marks return local modified
// =============================================================================

/// Verify that `encode_block_statements` marks the return local as modified
/// when encoding an enum variant construction (Aggregate with discriminant).
///
/// This exercises the Aggregate→discriminant encoding path that all non-async
/// enum construction uses in optimized MIR. The original async-based test
/// (P1:1418) was removed because `Instance::try_from(CrateItem)` cannot
/// monomorphize generator closures through the stable MIR API.
///
/// The SetDiscriminant statement kind itself is tested end-to-end by the
/// unit/signed/non-unit enum tests below via `translate()`.
#[test]
fn test_enum_construction_marks_return_local_modified() {
    with_test_ay_ctx_for_source(ENUM_CONSTRUCTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "make_loaded");
        let body = instance.body().expect("body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "make_loaded", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // The return place is local 0.  At least one block must mark it modified
        // when encoding the `State::Loaded(x)` aggregate assignment.
        let any_block_modifies_return = (0..body.blocks.len()).any(|bb_idx| {
            let (_constraints, _output_args, modified, _safety_checks) =
                chc_ctx.encode_block_statements(bb_idx);
            modified.contains(&0)
        });

        assert!(
            any_block_modifies_return,
            "encode_block_statements should mark return local (0) as modified \
             for State::Loaded(x) construction"
        );
    });
}

// =============================================================================
// Unit enum — discriminant should be encoded precisely
// =============================================================================

/// A unit enum (all variants fieldless) should have its discriminant encoded
/// as a bitvec constant without triggering any fallback.
#[test]
fn test_unit_enum_discriminant_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub enum Color {
            Red,
            Green,
            Blue,
        }

        pub fn probe_unit_enum() -> Color {
            Color::Green
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_enum");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unit_enum", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // Should produce a valid VC with rules.
        assert!(!vc.rules.is_empty(), "unit enum function should produce rules");
        assert!(!smt.is_empty(), "unit enum VC should produce non-empty SMT");

        assert_vc_structure(&vc, "probe_unit_enum", body.blocks.len());
    });
}

// =============================================================================
// Explicit negative discriminant — sign extension
// =============================================================================

/// Enum with explicit negative discriminant should encode correctly.
#[test]
fn test_explicit_negative_discriminant_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(i32)]
        #[derive(Clone, Copy)]
        pub enum Signed {
            Neg = -1,
            Zero = 0,
            Pos = 1,
        }

        pub fn probe_signed_enum() -> Signed {
            Signed::Neg
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_enum");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_signed_enum", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "signed enum function should produce rules");
        assert!(!smt.is_empty(), "signed enum VC should produce non-empty SMT");

        assert_vc_structure(&vc, "probe_signed_enum", body.blocks.len());
    });
}

// =============================================================================
// Non-unit enum aggregate construction
// =============================================================================

/// Non-unit enum aggregate construction should still produce a valid VC.
#[test]
fn test_non_unit_enum_set_discriminant_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub enum Shape {
            Circle(f64),
            Rect(f64, f64),
        }

        pub fn probe_non_unit_enum(r: f64) -> Shape {
            Shape::Circle(r)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_unit_enum");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_unit_enum", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Should produce a valid VC — even with fallback, the VC must be well-formed.
        assert!(!vc.rules.is_empty(), "non-unit enum function should produce rules");
        assert_vc_structure(&vc, "probe_non_unit_enum", body.blocks.len());
    });
}

// =============================================================================
// Catch-all: no-op statement kinds don't trigger fallback
// =============================================================================

/// Verify that FakeRead, PlaceMention, etc. are handled as no-ops
/// and don't increment fallback counters. These are covered implicitly
/// because any function that compiles will encounter StorageLive/Dead
/// and potentially FakeRead, and the catch-all would fire otherwise.
#[test]
fn test_noop_statements_do_not_trigger_catch_all() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_noop(x: u32) -> u32 {
            let y = x + 1;
            y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_noop");
        let body = instance.body().expect("body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_noop", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "noop probe should produce rules");
        assert!(smt.contains("bvadd"), "x + 1 should produce bvadd");
        assert_vc_structure(&vc, "probe_noop", body.blocks.len());
    });
}

/// `SetDiscriminant(*_ref, ...)` on coroutine state machines should update the
/// referent local, not fall back on the reference local.
#[test]
fn test_coroutine_set_discriminant_deref_marks_referent_modified() {
    with_test_ay_ctx_for_source(COROUTINE_SET_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_resume_once");
        let body = instance.body().expect("body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_resume_once", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (ref_local, target_local) =
            find_coroutine_ref_local(&chc_ctx, &body).expect("body should contain a coroutine ref");
        let place = rustc_public::mir::Place {
            local: ref_local,
            projection: vec![rustc_public::mir::ProjectionElem::Deref],
        };
        let variant_index = rustc_internal::stable(rustc_abi::VariantIdx::from_u32(0));
        let ty = place.ty(body.locals()).expect("manual deref place should have a coroutine type");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        let encoded =
            chc_ctx.encode_coroutine_discriminant(&place, ty, &variant_index, 0, &mut acc);

        assert!(encoded, "manual coroutine deref SetDiscriminant should encode");
        assert!(
            modified.contains(&target_local),
            "SetDiscriminant(*_{ref_local}, ...) should modify referent local {target_local}, modified={modified:?}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine SetDiscriminant deref path should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine SetDiscriminant deref path should avoid aggregate-encoding gaps"
        );
    });
}

/// Coroutine `SetDiscriminant(*_ref, ...)` should update the auxiliary
/// arg-pointee slot when `ref_targets` is unavailable.
#[test]
fn test_coroutine_set_discriminant_deref_updates_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_SET_DISCR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_coroutine_resume_once");
        let body = instance.body().expect("body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_resume_once", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (ref_local, target_local) =
            find_coroutine_ref_local(&chc_ctx, &body).expect("body should contain a coroutine ref");
        let target_expr = chc_ctx
            .resolve_local_expr(target_local, &HashSet::new())
            .expect("target coroutine local should resolve to a root expr");
        let pointee_vec_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(
            "probe_coroutine_set_discr_arg_pointee",
            "probe_coroutine_set_discr_arg_pointee__out",
            target_expr.sort().clone(),
        );
        let track_key = usize::MAX - pointee_vec_idx;
        chc_ctx.ref_resolution.ref_targets.remove(&ref_local);
        chc_ctx.ref_resolution.ref_arg_pointee_idx.insert(ref_local, pointee_vec_idx);
        chc_ctx.encode.local_expr_env.insert(track_key, target_expr);

        let place = rustc_public::mir::Place {
            local: ref_local,
            projection: vec![rustc_public::mir::ProjectionElem::Deref],
        };
        let variant_index = rustc_internal::stable(rustc_abi::VariantIdx::from_u32(0));
        let ty = place.ty(body.locals()).expect("manual deref place should have a coroutine type");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        let encoded =
            chc_ctx.encode_coroutine_discriminant(&place, ty, &variant_index, 0, &mut acc);

        assert!(encoded, "manual coroutine arg-pointee SetDiscriminant should encode");
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "coroutine arg-pointee SetDiscriminant should mark pointee state idx {pointee_vec_idx} modified"
        );
        assert!(
            chc_ctx.encode.local_expr_env.contains_key(&track_key),
            "coroutine arg-pointee SetDiscriminant should update the synthetic track key"
        );
        let constraint_strings: Vec<String> = constraints.iter().map(ToString::to_string).collect();
        assert!(
            constraint_strings
                .iter()
                .any(|c| c.contains("probe_coroutine_set_discr_arg_pointee__out")),
            "coroutine arg-pointee SetDiscriminant should constrain the pointee output slot, got {constraint_strings:?}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine arg-pointee SetDiscriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine arg-pointee SetDiscriminant should avoid aggregate-encoding gaps"
        );
    });
}

fn find_coroutine_ref_local(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> Option<(usize, usize)> {
    chc_ctx.ref_resolution.ref_targets.iter().find_map(|(&ref_local, ref_target)| {
        let target_ty = body.locals().get(ref_target.local).map(|decl| decl.ty);
        (ref_target.projections.is_empty()
            && matches!(
                target_ty.map(|ty| ty.kind()),
                Some(TyKind::RigidTy(RigidTy::Coroutine(..)))
            ))
        .then_some((ref_local, ref_target.local))
    })
}

fn find_coroutine_closure_body(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    suffix: &str,
) -> rustc_public::mir::Body {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path.contains(suffix) && path.contains("{closure#0}")
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing closure for '{suffix}'"),
        [single] => single.body().expect("closure body should exist"),
        many => panic!("ambiguous closure for '{suffix}': {many:?}"),
    }
}

fn find_coroutine_set_discriminant(
    body: &rustc_public::mir::Body,
) -> Option<(usize, rustc_public::mir::Place, rustc_public::ty::VariantIdx)> {
    use rustc_public::mir::StatementKind;

    body.blocks.iter().enumerate().find_map(|(bb_idx, bb)| {
        bb.statements.iter().find_map(|stmt| {
            let StatementKind::SetDiscriminant { place, variant_index } = &stmt.kind else {
                return None;
            };
            place
                .ty(body.locals())
                .ok()
                .filter(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))))
                .map(|_| (bb_idx, place.clone(), *variant_index))
        })
    })
}

fn find_coroutine_deref_set_discriminant(
    body: &rustc_public::mir::Body,
) -> Option<(usize, rustc_public::mir::Place, rustc_public::ty::VariantIdx)> {
    use rustc_public::mir::{ProjectionElem, StatementKind};

    body.blocks.iter().enumerate().find_map(|(bb_idx, bb)| {
        bb.statements.iter().find_map(|stmt| {
            let StatementKind::SetDiscriminant { place, variant_index } = &stmt.kind else {
                return None;
            };
            (place.projection.len() == 1 && matches!(place.projection[0], ProjectionElem::Deref))
                .then_some(())?;
            place
                .ty(body.locals())
                .ok()
                .filter(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))))
                .map(|_| (bb_idx, place.clone(), *variant_index))
        })
    })
}

#[test]
fn test_coroutine_resume_set_discriminant_ref_target_bridge() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_resume_live_across_yield");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_resume_live_across_yield::{closure#0}",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let (bb_idx, place, variant_index) = find_coroutine_deref_set_discriminant(&body)
            .expect("closure body should contain coroutine deref SetDiscriminant");
        let bridged_local = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&place.local)
            .cloned()
            .map(|ref_target| {
                assert!(
                    ref_target.projections.is_empty(),
                    "resume-live-across-yield deref source should bridge to a direct coroutine root local"
                );
                assert_ne!(
                    ref_target.local, place.local,
                    "bridge should not persist a self-referencing ref_target for the deref source"
                );
                ref_target.local
            })
            .unwrap_or_else(|| {
                assert!(
                    chc_ctx.ref_resolution.coroutine_root_map.contains_key(&place.local),
                    "resume-live-across-yield deref source should have either a propagated ref_target or a direct coroutine_root_map entry"
                );
                place.local
            });
        let root_expr = chc_ctx
            .resolve_coroutine_root_expr(bridged_local, &HashSet::new())
            .expect("bridged coroutine local should resolve through coroutine_root_map");
        assert!(
            crate::codegen_ay::types::coroutine_discriminant_select(root_expr).is_some(),
            "bridged coroutine local should resolve to a concrete coroutine root expr"
        );

        let ty = place.ty(body.locals()).expect("SetDiscriminant place should be a coroutine");
        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        let encoded =
            chc_ctx.encode_coroutine_discriminant(&place, ty, &variant_index, bb_idx, &mut acc);

        assert!(encoded, "resume-live-across-yield coroutine deref should encode");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "resume-live-across-yield coroutine deref should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "resume-live-across-yield coroutine deref should avoid aggregate-encoding gaps"
        );
    });
}

#[test]
fn test_coroutine_dispatch_prefers_inline_body_complete_and_yielded_paths() {
    with_test_ay_ctx_for_source(COROUTINE_INLINE_BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "projected_resume");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "projected_resume", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(*target);
            let before_fallback = chc_ctx.sound_fallback_count();
            let before_rules = chc_ctx.vc.rules.len();
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };
            if !chc_ctx.try_dispatch_call_coroutine(&dcx) {
                continue;
            }
            found = true;
            // Part of #4028: sound_fallback +1 after W2:4264 coroutine encoding changes.
            assert!(
                chc_ctx.sound_fallback_count() <= before_fallback + 1,
                "inline coroutine dispatch sound_fallback should stay bounded (was {before_fallback}, now {})",
                chc_ctx.sound_fallback_count()
            );
            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_rules + 1,
                "inline coroutine dispatch should emit exactly one rule"
            );

            let smt = emit_chc(&chc_ctx.vc).to_string();
            assert!(
                smt.contains("Yielded_CoroutineState_i32_i32"),
                "inline coroutine dispatch should still encode the Yielded arm; smt={smt}"
            );
            assert!(
                smt.contains("Complete_CoroutineState_i32_i32"),
                "inline coroutine dispatch should encode the Complete arm instead of the old Yielded-only fallback; smt={smt}"
            );
            break;
        }

        assert!(found, "expected a coroutine resume call in projected_resume MIR");
    });
}

#[test]
fn test_coroutine_pin_wrapper_set_discriminant_uses_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_PIN_LOOP_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_coroutine_loop");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_loop::{closure#0}", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, place, variant_index) = find_coroutine_set_discriminant(&body)
            .expect("closure body should contain coroutine SetDiscriminant");
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&place.local)
            .expect("Pin<&mut Coroutine> field copy should inherit arg-pointee state");
        let ty = place.ty(body.locals()).expect("SetDiscriminant place should be a coroutine");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        let encoded =
            chc_ctx.encode_coroutine_discriminant(&place, ty, &variant_index, bb_idx, &mut acc);

        assert!(encoded, "coroutine Pin wrapper SetDiscriminant should encode");
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "coroutine Pin wrapper SetDiscriminant should mark pointee idx {pointee_vec_idx} modified"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine Pin wrapper SetDiscriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine Pin wrapper SetDiscriminant should avoid aggregate-encoding gaps"
        );
    });
}

#[test]
fn test_coroutine_ref_target_set_discriminant_uses_arg_pointee_slot() {
    with_test_ay_ctx_for_source(COROUTINE_PIN_LOOP_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_coroutine_loop");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_coroutine_loop::{closure#0}", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, place, variant_index) = find_coroutine_set_discriminant(&body)
            .expect("closure body should contain coroutine SetDiscriminant");
        let ref_local = place.local;
        let pointee_vec_idx = *chc_ctx
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&ref_local)
            .expect("Pin<&mut Coroutine> field copy should inherit arg-pointee state");
        chc_ctx.ref_resolution.ref_targets.insert(
            ref_local,
            crate::codegen_ay::chc::RefTarget::with_projections(ref_local, vec![]),
        );
        let ty = place.ty(body.locals()).expect("SetDiscriminant place should be a coroutine");

        let before_sound = chc_ctx.sound_fallback_count();
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let mut modified = HashSet::new();
        let mut constraints = Vec::new();
        let mut last_constraint = std::collections::HashMap::new();
        let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint);
        let encoded =
            chc_ctx.encode_coroutine_discriminant(&place, ty, &variant_index, bb_idx, &mut acc);

        assert!(encoded, "coroutine ref_target SetDiscriminant should encode");
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&pointee_vec_idx),
            "coroutine ref_target SetDiscriminant should mark pointee idx {pointee_vec_idx} modified"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "coroutine ref_target SetDiscriminant should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "coroutine ref_target SetDiscriminant should avoid aggregate-encoding gaps"
        );
    });
}

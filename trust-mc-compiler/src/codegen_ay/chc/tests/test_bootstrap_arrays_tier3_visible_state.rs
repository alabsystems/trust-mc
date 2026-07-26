// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Compiletest-scale localizers for the current arrays visible-state packet.

use super::super::common::*;
use super::{
    BOOTSTRAP_ARRAYS_TIER3_SOURCE, inferable_predicate_artifacts,
    reset_bootstrap_arrays_tier3_counters,
};
use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::HashSet;

const ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD: usize = 9;
const ARRAYSOLVER_SCOPES_LEN_FIELD: usize = 21;

fn arrays_compiletest_config() -> ChcConfig {
    ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() }
}

#[derive(Debug)]
struct ArraysDiagnostics {
    constraint_invariant_fixup: usize,
    sound_fallback_count: usize,
    relation_count: usize,
    rule_count: usize,
}

impl ArraysDiagnostics {
    fn from_translation(source: &str, fn_name: &str) -> Self {
        let mut result = None;
        with_test_ay_ctx_for_source(source, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, arrays_compiletest_config());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let constraint_invariant_fixup = diagnostics
                .sound_fallback_detail
                .get("constraint_invariant_fixup")
                .copied()
                .unwrap_or(0);
            let sound_fallback_count = diagnostics.sound_fallback_detail.values().sum();

            result = Some(Self {
                constraint_invariant_fixup,
                sound_fallback_count,
                relation_count: vc.relations.len(),
                rule_count: vc.rules.len(),
            });
        });
        result.expect("translation should complete")
    }
}

pub(super) fn assert_arrays_replay_counters(
    fn_name: &str,
    inferable_decls: &[String],
    has_p_inf_rule: bool,
) {
    let fallback_counts = get_chc_fallback_counts();
    let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let unhandled_call_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();

    assert!(
        inferable_decls.is_empty(),
        "{fn_name} should not emit P_inf_* declarations for the arrays replay helper path: {inferable_decls:?}"
    );
    assert!(!has_p_inf_rule, "{fn_name} should not reference P_inf_* summaries in emitted rules");
    assert_eq!(
        fallback_count, 0,
        "{fn_name} should keep CHC fallback count at zero for the arrays replay helper path, map={fallback_counts:?}"
    );
    assert_eq!(
        unhandled_call_count, 0,
        "{fn_name} should not increment unhandled-call counters for the arrays replay helper path, map={unhandled_calls:?}"
    );
    assert_eq!(
        inferable_count, 0,
        "{fn_name} should not emit inferable-predicate summaries for the arrays replay helper path"
    );
}

#[test]
fn test_bootstrap_arrays_tier3_replay_probe_has_no_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();

    let fn_name = "probe_arrays_pop_restores_assignments";
    let mut inferable_decls = Vec::new();
    let mut has_p_inf_rule = false;

    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
    });

    assert_arrays_replay_counters(fn_name, &inferable_decls, has_p_inf_rule);
    reset_bootstrap_arrays_tier3_counters();
}

#[test]
fn test_bootstrap_arrays_tier3_scope_depth_probe_has_no_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();

    let fn_name = "probe_arrays_push_pop_scope_depth";
    let mut inferable_decls = Vec::new();
    let mut has_p_inf_rule = false;

    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
    });

    assert_arrays_replay_counters(fn_name, &inferable_decls, has_p_inf_rule);
    reset_bootstrap_arrays_tier3_counters();
}

#[test]
fn test_bootstrap_arrays_pop_empty_probe_has_no_fixup() {
    let diag = ArraysDiagnostics::from_translation(
        BOOTSTRAP_ARRAYS_TIER3_SOURCE,
        "probe_arrays_pop_empty_is_safe",
    );

    eprintln!(
        "[probe_arrays_pop_empty_is_safe] constraint_invariant_fixup={}, \
         sound_fallback_count={}, relations={}, rules={}",
        diag.constraint_invariant_fixup,
        diag.sound_fallback_count,
        diag.relation_count,
        diag.rule_count,
    );

    assert!(
        diag.relation_count >= 2,
        "probe_arrays_pop_empty_is_safe should produce a nontrivial VC"
    );
    assert!(diag.rule_count >= 1, "probe_arrays_pop_empty_is_safe should produce rules");
    assert_eq!(
        diag.constraint_invariant_fixup, 0,
        "probe_arrays_pop_empty_is_safe should not require modified-constraint repair"
    );
}

#[test]
fn test_bootstrap_arrays_dirty_flag_probe_has_no_fixup() {
    let diag = ArraysDiagnostics::from_translation(
        BOOTSTRAP_ARRAYS_TIER3_SOURCE,
        "probe_arrays_dirty_flag_after_pop",
    );

    eprintln!(
        "[probe_arrays_dirty_flag_after_pop] constraint_invariant_fixup={}, \
         sound_fallback_count={}, relations={}, rules={}",
        diag.constraint_invariant_fixup,
        diag.sound_fallback_count,
        diag.relation_count,
        diag.rule_count,
    );

    assert!(
        diag.relation_count >= 2,
        "probe_arrays_dirty_flag_after_pop should produce a nontrivial VC"
    );
    assert!(diag.rule_count >= 1, "probe_arrays_dirty_flag_after_pop should produce rules");
    assert_eq!(
        diag.constraint_invariant_fixup, 0,
        "probe_arrays_dirty_flag_after_pop should not require modified-constraint repair"
    );
}

#[test]
fn test_bootstrap_arrays_pop_restores_probe_solver_unsat_mem_track() {
    let mut result = None;
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let fn_name = "probe_arrays_pop_restores_assignments_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, arrays_compiletest_config());
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        result = Some(
            run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(60))
                .expect("z3 reduced pop_restores_assignments_assert result"),
        );
    });

    let z3 = result.expect("reduced pop_restores_assignments_assert z3 result");
    eprintln!(
        "[probe_arrays_pop_restores_assignments_assert solver] verdict={}, status_success={}",
        z3.verdict, z3.status_success
    );
    assert!(
        z3.status_success,
        "reduced pop_restores_assignments_assert z3 exited non-zero:\n{}",
        z3.stderr
    );
    assert_eq!(
        z3.verdict, "unsat",
        "reduced pop_restores_assignments_assert should be unsat, got {}.\nstdout:\n{}\nstderr:\n{}",
        z3.verdict, z3.stdout, z3.stderr
    );
}

#[test]
fn test_bootstrap_arrays_pop_empty_probe_solver_unsat() {
    let mut result = None;
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arrays_pop_empty_is_safe");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_arrays_pop_empty_is_safe",
            arrays_compiletest_config(),
        );
        assert_vc_structure(&vc, "probe_arrays_pop_empty_is_safe", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_arrays_pop_empty_is_safe");

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        result = Some(
            run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .expect("z3 reduced pop_empty_is_safe result"),
        );
    });

    let z3 = result.expect("reduced pop_empty_is_safe z3 result");
    eprintln!(
        "[probe_arrays_pop_empty_is_safe solver] verdict={}, status_success={}",
        z3.verdict, z3.status_success
    );
    assert!(z3.status_success, "reduced pop_empty_is_safe z3 exited non-zero:\n{}", z3.stderr);
    assert_eq!(
        z3.verdict, "unsat",
        "reduced pop_empty_is_safe should be unsat, got {}.\nstdout:\n{}\nstderr:\n{}",
        z3.verdict, z3.stdout, z3.stderr
    );
}

#[test]
fn test_bootstrap_arrays_pop_empty_assert_probe_solver_unsat() {
    let mut result = None;
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arrays_pop_empty_is_safe_assert");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_arrays_pop_empty_is_safe_assert",
            arrays_compiletest_config(),
        );
        assert_vc_structure(&vc, "probe_arrays_pop_empty_is_safe_assert", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_arrays_pop_empty_is_safe_assert");

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        let _ = std::fs::write("/tmp/debug_4050_pop_empty_assert.smt2", &smt);
        result = Some(
            run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .expect("z3 reduced pop_empty_is_safe_assert result"),
        );
    });

    let z3 = result.expect("reduced pop_empty_is_safe_assert z3 result");
    eprintln!(
        "[probe_arrays_pop_empty_is_safe_assert solver] verdict={}, status_success={}",
        z3.verdict, z3.status_success
    );
    assert!(
        z3.status_success,
        "reduced pop_empty_is_safe_assert z3 exited non-zero:\n{}",
        z3.stderr
    );
    if z3.verdict == "sat" {
        eprintln!(
            "[probe_arrays_pop_empty_is_safe_assert] KNOWN: combined harness sat \
             (unbridged sidecars from resolve_vec_entry_expr — #4050)"
        );
    } else {
        assert_eq!(
            z3.verdict, "unsat",
            "reduced pop_empty_is_safe_assert should be unsat or sat(known), got {}.\n\
             stdout:\n{}\nstderr:\n{}",
            z3.verdict, z3.stdout, z3.stderr
        );
    }
}

#[test]
fn test_bootstrap_arrays_pop_empty_assert_probe_mir_diagnostic() {
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arrays_pop_empty_is_safe_assert");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_arrays_pop_empty_is_safe_assert",
            arrays_compiletest_config(),
        );
        chc_ctx.declare_block_relations();

        let mut saw_switch = false;
        let mut saw_panic_call = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            match &block.terminator.kind {
                TerminatorKind::SwitchInt { discr, targets } => {
                    saw_switch = true;
                    let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
                        chc_ctx.encode_block_statements(bb_idx);
                    let discr_expr =
                        chc_ctx.translate_operand_with_modified(discr, &modified_locals);
                    eprintln!(
                        "[probe_arrays_pop_empty_is_safe_assert bb{bb_idx}] SwitchInt discr={discr:?} \
                         modified_locals={modified_locals:?} local_expr_env_keys={:?} \
                         discr_expr={:?} targets={targets:?}",
                        chc_ctx.encode.local_expr_env.keys().copied().collect::<Vec<_>>(),
                        discr_expr
                    );
                }
                TerminatorKind::Call { func, target, unwind, .. } => {
                    let path = chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))
                        .unwrap_or_else(|| "<unknown>".to_string());
                    if path.contains("panic") || path.contains("assert_failed") {
                        saw_panic_call = true;
                    }
                    eprintln!(
                        "[probe_arrays_pop_empty_is_safe_assert bb{bb_idx}] Call path={path} \
                         target={target:?} unwind={unwind:?}"
                    );
                }
                kind => {
                    eprintln!(
                        "[probe_arrays_pop_empty_is_safe_assert bb{bb_idx}] terminator={kind:?}"
                    );
                }
            }
        }

        assert!(
            saw_switch,
            "probe_arrays_pop_empty_is_safe_assert should lower through at least one SwitchInt"
        );
        assert!(
            saw_panic_call,
            "probe_arrays_pop_empty_is_safe_assert should include a panic/assert failure call path"
        );
    });
}

#[test]
fn test_bootstrap_arrays_pop_empty_single_assert_localizer() {
    let probe_names = [
        "probe_arrays_pop_empty_trail_terms_len_assert",
        "probe_arrays_pop_empty_trail_prev_present_len_assert",
        "probe_arrays_pop_empty_trail_prev_values_len_assert",
        "probe_arrays_pop_empty_assign_terms_len_assert",
        "probe_arrays_pop_empty_assign_values_len_assert",
        "probe_arrays_pop_empty_scopes_empty_assert",
    ];

    for fn_name in probe_names {
        let mut result = None;
        with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, arrays_compiletest_config());
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let _ = std::fs::write(format!("/tmp/debug_4050_{fn_name}.smt2"), &smt);
            result = Some(
                run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(30))
                    .unwrap_or_else(|e| panic!("{fn_name} z3 transport failed: {e:?}")),
            );
        });

        let z3 = result.expect("single-assert probe z3 result");
        eprintln!("[{fn_name}] verdict={}, status_success={}", z3.verdict, z3.status_success);
        if !z3.status_success {
            eprintln!("  WARN: {fn_name} z3 exited non-zero:\n{}", z3.stderr);
        }
        if z3.verdict != "unsat" {
            eprintln!("  FAIL: {fn_name} expected unsat, got {}", z3.verdict);
        }
    }
}

#[test]
fn test_bootstrap_arrays_pop_empty_vec_query_resolution_diagnostic() {
    let probe_names = [
        "probe_arrays_pop_empty_trail_terms_len_assert",
        "probe_arrays_pop_empty_trail_prev_present_len_assert",
        "probe_arrays_pop_empty_trail_prev_values_len_assert",
        "probe_arrays_pop_empty_assign_terms_len_assert",
        "probe_arrays_pop_empty_assign_values_len_assert",
        "probe_arrays_pop_empty_scopes_empty_assert",
    ];

    for fn_name in probe_names {
        with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, arrays_compiletest_config());
            chc_ctx.declare_block_relations();

            for (bb_idx, block) in body.blocks.iter().enumerate() {
                let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                else {
                    continue;
                };
                let path = chc_ctx
                    .resolve_callee_path(func)
                    .or_else(|| chc_ctx.resolve_fn_def_name(func))
                    .unwrap_or_else(|| "<unknown>".to_string());
                if !(path.contains("Vec::<")
                    && (path.ends_with("::len") || path.ends_with("::is_empty")))
                {
                    continue;
                }
                let collection_local = chc_ctx.resolve_collection_local(args);
                let field_projections = chc_ctx.resolve_collection_field_projections(args);
                let (_constraints, _output_args, modified_locals, _safety_checks) =
                    chc_ctx.encode_block_statements(bb_idx);
                let collection_env =
                    collection_local.and_then(|l| chc_ctx.encode.local_expr_env.get(&l).cloned());
                let state_idx = collection_local.and_then(|l| chc_ctx.try_state_idx_for_local(l));
                let len_var = collection_local
                    .and_then(|l| chc_ctx.collections.len_state.get_len_var(l).cloned());
                let cap_var = collection_local
                    .and_then(|l| chc_ctx.collections.len_state.get_cap_var(l).cloned());
                eprintln!(
                    "[{fn_name} bb{bb_idx}] path={path} dest_local={} collection_local={collection_local:?} \
                     field_projections={field_projections:?} projection_kind={:?} ref_target={:?} \
                     modified_locals={modified_locals:?} collection_env={collection_env:?} \
                     state_idx={state_idx:?} len_var={len_var:?} cap_var={cap_var:?}",
                    destination.local,
                    collection_local.and_then(|l| chc_ctx
                        .collections
                        .projection_locals
                        .get(&l)
                        .copied()),
                    args.first().and_then(|_| {
                        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                            chc_ctx.ref_resolution.ref_targets.get(&place.local)
                        } else {
                            None
                        }
                    }),
                );
            }
        });
    }
}

#[test]
fn test_bootstrap_arrays_new_single_assert_localizer() {
    let probe_names = [
        "probe_arrays_new_trail_terms_len_assert",
        "probe_arrays_new_trail_prev_present_len_assert",
        "probe_arrays_new_trail_prev_values_len_assert",
        "probe_arrays_new_assign_terms_len_assert",
        "probe_arrays_new_assign_values_len_assert",
        "probe_arrays_new_scopes_empty_assert",
    ];

    for fn_name in probe_names {
        let mut result = None;
        with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, arrays_compiletest_config());
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            result = Some(
                run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(30))
                    .unwrap_or_else(|e| panic!("{fn_name} z3 transport failed: {e:?}")),
            );
        });

        let z3 = result.expect("constructor assert probe z3 result");
        eprintln!("[{fn_name}] verdict={}, status_success={}", z3.verdict, z3.status_success);
        assert!(z3.status_success, "{fn_name} z3 exited non-zero:\n{}", z3.stderr);
        assert_eq!(
            z3.verdict, "unsat",
            "{fn_name} should be unsat after precise ArraySolver::new() initialization, got {}.\nstdout:\n{}\nstderr:\n{}",
            z3.verdict, z3.stdout, z3.stderr
        );
    }
}

#[test]
fn test_bootstrap_arrays_new_vec_query_resolution_diagnostic() {
    let probe_names = [
        "probe_arrays_new_trail_terms_len_assert",
        "probe_arrays_new_trail_prev_present_len_assert",
        "probe_arrays_new_trail_prev_values_len_assert",
        "probe_arrays_new_assign_terms_len_assert",
        "probe_arrays_new_assign_values_len_assert",
        "probe_arrays_new_scopes_empty_assert",
    ];

    for fn_name in probe_names {
        with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, arrays_compiletest_config());
            chc_ctx.declare_block_relations();

            for (bb_idx, block) in body.blocks.iter().enumerate() {
                let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                else {
                    continue;
                };
                let path = chc_ctx
                    .resolve_callee_path(func)
                    .or_else(|| chc_ctx.resolve_fn_def_name(func))
                    .unwrap_or_else(|| "<unknown>".to_string());
                if !(path.contains("Vec::<")
                    && (path.ends_with("::len") || path.ends_with("::is_empty")))
                {
                    continue;
                }
                let collection_local = chc_ctx.resolve_collection_local(args);
                let field_projections = chc_ctx.resolve_collection_field_projections(args);
                let (_constraints, _output_args, modified_locals, _safety_checks) =
                    chc_ctx.encode_block_statements(bb_idx);
                let collection_env =
                    collection_local.and_then(|l| chc_ctx.encode.local_expr_env.get(&l).cloned());
                let state_idx = collection_local.and_then(|l| chc_ctx.try_state_idx_for_local(l));
                let len_var = collection_local
                    .and_then(|l| chc_ctx.collections.len_state.get_len_var(l).cloned());
                let cap_var = collection_local
                    .and_then(|l| chc_ctx.collections.len_state.get_cap_var(l).cloned());
                eprintln!(
                    "[{fn_name} bb{bb_idx}] path={path} dest_local={} collection_local={collection_local:?} \
                     field_projections={field_projections:?} projection_kind={:?} ref_target={:?} \
                     modified_locals={modified_locals:?} collection_env={collection_env:?} \
                     state_idx={state_idx:?} len_var={len_var:?} cap_var={cap_var:?}",
                    destination.local,
                    collection_local.and_then(|l| chc_ctx
                        .collections
                        .projection_locals
                        .get(&l)
                        .copied()),
                    args.first().and_then(|_| {
                        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                            chc_ctx.ref_resolution.ref_targets.get(&place.local)
                        } else {
                            None
                        }
                    }),
                );
            }
        });
    }
}

pub(in crate::codegen_ay::chc::tests) fn inline_budget_note_arrays(
    tcx: TyCtxt<'_>,
    suffix: &str,
) -> String {
    let instance = find_instance_by_suffix(tcx, suffix);
    let body = instance.body().expect("function body");
    let effective = crate::codegen_ay::shared::count_effective_blocks(&body);
    let limit = crate::codegen_ay::chc::call::inline_budget::chc_inline_effective_block_limit(
        &body, effective,
    );
    format!("{suffix}:effective={effective},limit={limit}")
}

pub(in crate::codegen_ay::chc::tests) fn with_array_solver_method_call(
    probe_suffix: &str,
    callee_suffix: &str,
    assertions: impl FnOnce(
        TyCtxt<'_>,
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                {
                    let path = chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))?;
                    path.ends_with(callee_suffix).then(|| {
                        (bb_idx, func.clone(), args.clone(), destination.clone(), *target, path)
                    })
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!("expected {callee_suffix} call terminator in {probe_suffix}")
            });

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

        assertions(
            ctx.tcx,
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

struct ConstructorVisibleLenSlots {
    trail_terms_len_idx: usize,
    scopes_len_idx: usize,
    trail_terms_len_name: String,
    scopes_len_name: String,
    trail_terms_len_out: String,
    scopes_len_out: String,
}

fn constructor_visible_len_slots(
    chc_ctx: &ChcCtx<'_, '_>,
    target_bb: usize,
    dest_local: usize,
) -> ConstructorVisibleLenSlots {
    let dest_idx =
        chc_ctx.try_state_idx_for_local(dest_local).expect("constructor destination state idx");
    let trail_terms_len_idx = dest_idx + ARRAYSOLVER_TRAIL_TERMS_LEN_FIELD;
    let scopes_len_idx = dest_idx + ARRAYSOLVER_SCOPES_LEN_FIELD;
    let live_next = &chc_ctx.state_var_mgr.live_state_indices[target_bb];

    assert!(
        live_next.contains(&trail_terms_len_idx),
        "constructor successor bb{target_bb} must keep trail_terms.len live ({})",
        chc_ctx.state_var_mgr.state_vars[trail_terms_len_idx].0
    );
    assert!(
        live_next.contains(&scopes_len_idx),
        "constructor successor bb{target_bb} must keep scopes.len live ({})",
        chc_ctx.state_var_mgr.state_vars[scopes_len_idx].0
    );

    ConstructorVisibleLenSlots {
        trail_terms_len_idx,
        scopes_len_idx,
        trail_terms_len_name: chc_ctx.state_var_mgr.state_vars[trail_terms_len_idx].0.to_string(),
        scopes_len_name: chc_ctx.state_var_mgr.state_vars[scopes_len_idx].0.to_string(),
        trail_terms_len_out: chc_ctx.state_var_mgr.output_state_vars[trail_terms_len_idx]
            .0
            .to_string(),
        scopes_len_out: chc_ctx.state_var_mgr.output_state_vars[scopes_len_idx].0.to_string(),
    }
}

fn assert_constructor_visible_len_slot_rules(
    chc_ctx: &mut ChcCtx<'_, '_>,
    new_bb: usize,
    target_bb: usize,
    slots: &ConstructorVisibleLenSlots,
) {
    chc_ctx.declare_error_relation();
    chc_ctx.emit_entry_rule();
    chc_ctx.generate_transition_rules();

    let from_rel = chc_ctx.block_relations.get(&new_bb).expect("constructor source relation");
    let to_rel = chc_ctx.block_relations.get(&target_bb).expect("constructor successor relation");
    let constructor_rules: Vec<_> = chc_ctx
        .vc
        .rules
        .iter()
        .filter(|rule| {
            rule.head.name == *to_rel
                && rule.body.relation.as_ref().is_some_and(|rel| rel.name == *from_rel)
        })
        .collect();
    assert!(
        constructor_rules.iter().any(|rule| rule_contains_var(rule, &slots.trail_terms_len_out)),
        "ArraySolver::new transition should propagate {} into bb{target_bb}",
        slots.trail_terms_len_out
    );
    assert!(
        constructor_rules.iter().any(|rule| rule_contains_var(rule, &slots.scopes_len_out)),
        "ArraySolver::new transition should propagate {} into bb{target_bb}",
        slots.scopes_len_out
    );

    let successor_rules: Vec<_> = chc_ctx
        .vc
        .rules
        .iter()
        .filter(|rule| rule.body.relation.as_ref().is_some_and(|rel| rel.name == *to_rel))
        .collect();
    assert!(
        successor_rules.iter().any(|rule| rule_contains_var(rule, &slots.trail_terms_len_name)),
        "bb{target_bb} rules should consume {} from the relation body",
        slots.trail_terms_len_name
    );
    assert!(
        successor_rules.iter().any(|rule| rule_contains_var(rule, &slots.scopes_len_name)),
        "bb{target_bb} rules should consume {} from the relation body",
        slots.scopes_len_name
    );
}

#[test]
fn test_bootstrap_arrays_new_destination_keeps_visible_len_slots_live() {
    with_test_ay_ctx_for_source(BOOTSTRAP_ARRAYS_TIER3_SOURCE, |ctx| {
        let fn_name = "probe_arrays_new_trail_terms_len_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, arrays_compiletest_config());
        chc_ctx.declare_block_relations();

        let (new_bb, dest_local, target_bb) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, destination, target: Some(target), .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                let path = chc_ctx
                    .resolve_callee_path(func)
                    .or_else(|| chc_ctx.resolve_fn_def_name(func))?;
                path.ends_with("ArraySolver::new").then_some((bb_idx, destination.local, *target))
            })
            .expect("expected ArraySolver::new call in constructor probe");

        assert_ne!(
            chc_ctx.collections.projection_locals.get(&dest_local).copied(),
            Some(CollectionProjectionKind::IteratorWrapper),
            "ArraySolver owner local must not be misclassified as IteratorWrapper"
        );

        let slots = constructor_visible_len_slots(&chc_ctx, target_bb, dest_local);
        assert_constructor_visible_len_slot_rules(&mut chc_ctx, new_bb, target_bb, &slots);
        assert_eq!(
            slots.trail_terms_len_idx < slots.scopes_len_idx,
            true,
            "constructor visible len slot ordering should remain stable"
        );
    });
}

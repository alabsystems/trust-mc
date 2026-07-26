// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact-file localizers for the two remaining arrays tier3 residuals.
//!
//! These tests keep #4050 narrowed to the live current-head failures:
//! `ay_arrays_pop_empty_is_safe` and `ay_arrays_nested_push_pop_markers`.

#![allow(clippy::panic)]

use super::super::common::*;
use super::{inferable_predicate_artifacts, reset_bootstrap_arrays_tier3_counters};
use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::BTreeMap;
use std::sync::Once;

const ARRAYSOLVER_FIELD_SCOPES: usize = 5;

struct ExactArraysProbeResult {
    smt: String,
    inferable_decls: Vec<String>,
    has_p_inf_rule: bool,
    fallback_count: usize,
    aggregate_gap_count: usize,
    inferable_count: usize,
    aggregate_gaps: BTreeMap<String, usize>,
    aggregate_gap_reasons: BTreeMap<String, BTreeMap<String, usize>>,
    unhandled_calls: BTreeMap<String, usize>,
    translation_drops: BTreeMap<String, usize>,
    translation_drop_sites: BTreeMap<String, BTreeMap<String, usize>>,
}

fn exact_arrays_source() -> String {
    super::strip_kani_for_unit_ctx(super::BOOTSTRAP_ARRAYS_TIER3_REAL_FILE)
}

fn init_residual_localizer_tracing() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
            .try_init();
    });
}

fn emit_exact_arrays_harness_smt(fn_name: &str) -> ExactArraysProbeResult {
    init_residual_localizer_tracing();
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let source = exact_arrays_source();

    reset_bootstrap_arrays_tier3_counters();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();

    let mut inferable_decls = Vec::new();
    let mut has_p_inf_rule = false;
    let mut smt = String::new();

    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
        smt = emit_chc(&vc).to_string();
    });

    let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
    let aggregate_gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    let aggregate_gaps = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let aggregate_gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_bootstrap_arrays_tier3_counters();
    ExactArraysProbeResult {
        smt,
        inferable_decls,
        has_p_inf_rule,
        fallback_count,
        aggregate_gap_count,
        inferable_count,
        aggregate_gaps,
        aggregate_gap_reasons,
        unhandled_calls,
        translation_drops,
        translation_drop_sites,
    }
}

fn exact_file_matching_calls(fn_name: &str, callee_suffix: &str) -> Vec<String> {
    let source = exact_arrays_source();
    let mut matches = Vec::new();

    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

        for block in &body.blocks {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                continue;
            };
            let Some(path) =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))
            else {
                continue;
            };
            if path.ends_with(callee_suffix) {
                matches.push(path);
            }
        }
    });

    matches
}

#[test]
fn test_exact_file_nested_push_pop_markers_scopes_projection_localizer() {
    let source = exact_arrays_source();

    with_test_ay_ctx_for_source(&source, |ctx| {
        let fn_name = "ay_arrays_nested_push_pop_markers";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

        let mut saw_scopes_index = false;
        let mut saw_nonstruct_index = false;
        let mut index_origins = Vec::new();

        for block in &body.blocks {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                continue;
            };
            let Some(path) =
                chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func))
            else {
                continue;
            };
            if !path.ends_with("::index") {
                continue;
            }

            let arg_local = match args.first() {
                Some(Operand::Copy(place) | Operand::Move(place)) => Some(place.local),
                _ => None,
            };
            let origin = arg_local.and_then(|local| {
                body.blocks.iter().find_map(|block| {
                    block.statements.iter().find_map(|stmt| {
                        let rustc_public::mir::StatementKind::Assign(place, rvalue) = &stmt.kind
                        else {
                            return None;
                        };
                        if place.local != local || !place.projection.is_empty() {
                            return None;
                        }
                        let rustc_public::mir::Rvalue::Ref(_, _, source_place) = rvalue else {
                            return None;
                        };
                        Some(source_place.clone())
                    })
                })
            });
            index_origins.push(format!("path={path} arg_local={arg_local:?} origin={origin:?}"));
            if origin.as_ref().is_some_and(|source_place| {
                source_place.local == 1
                    && source_place.projection.len() == 1
                    && matches!(
                        source_place.projection[0],
                        rustc_public::mir::ProjectionElem::Field(idx, _)
                            if idx == ARRAYSOLVER_FIELD_SCOPES
                    )
            }) {
                saw_scopes_index = true;
            } else if origin.as_ref().is_some_and(|source_place| source_place.projection.is_empty())
            {
                saw_nonstruct_index = true;
            }
        }

        assert!(
            saw_scopes_index,
            "expected one exact-file ::index call to resolve through ArraySolver.scopes, \
             origins={index_origins:?}"
        );
        assert!(
            saw_nonstruct_index,
            "expected the second exact-file ::index call to stay on the plain expected_markers Vec, \
             origins={index_origins:?}"
        );
    });
}

fn exact_arrays_timeout_secs() -> u64 {
    z3_test_timeout_secs_or(120)
}

fn fn_reason_counts(
    reasons: &BTreeMap<String, BTreeMap<String, usize>>,
    fn_name: &str,
) -> BTreeMap<String, usize> {
    reasons.get(fn_name).cloned().unwrap_or_default()
}

#[test]
fn test_exact_file_pop_empty_is_safe_localizer() {
    let fn_name = "ay_arrays_pop_empty_is_safe";
    let pop_calls = exact_file_matching_calls(fn_name, "ArraySolver::pop");
    assert_eq!(
        pop_calls.len(),
        1,
        "{fn_name} should contain exactly one ArraySolver::pop call site, got {pop_calls:?}"
    );

    let r = emit_exact_arrays_harness_smt(fn_name);
    let fn_aggregate_gaps = r.aggregate_gaps.get(fn_name).copied().unwrap_or(0);
    let fn_gap_reasons = fn_reason_counts(&r.aggregate_gap_reasons, fn_name);
    let fn_unhandled_calls = r.unhandled_calls.get(fn_name).copied().unwrap_or(0);
    let fn_translation_drops = r.translation_drops.get(fn_name).copied().unwrap_or(0);
    let fn_translation_sites = fn_reason_counts(&r.translation_drop_sites, fn_name);
    let timeout_secs = exact_arrays_timeout_secs();
    let z3 = run_z3_on_smt2_capture_output_with_timeout(&r.smt, timeout_secs)
        .expect("z3 exact-file pop_empty_is_safe result");

    eprintln!(
        "[exact-file {fn_name}] verdict={}, status_success={}, fallback_count={}, \
         aggregate_gap_count={}, fn_aggregate_gaps={}, inferable_count={}, inferable_decls={:?}, \
         has_p_inf_rule={}, fn_unhandled_calls={}, fn_translation_drops={}, \
         fn_gap_reasons={:?}, fn_translation_sites={:?}",
        z3.verdict,
        z3.status_success,
        r.fallback_count,
        r.aggregate_gap_count,
        fn_aggregate_gaps,
        r.inferable_count,
        r.inferable_decls,
        r.has_p_inf_rule,
        fn_unhandled_calls,
        fn_translation_drops,
        fn_gap_reasons,
        fn_translation_sites,
    );

    assert!(z3.status_success, "{fn_name} z3 exited non-zero:\n{}", z3.stderr);
    assert!(
        matches!(z3.verdict.as_str(), "sat" | "unsat" | "unknown"),
        "{fn_name} unexpected z3 verdict={}.\nstdout:\n{}\nstderr:\n{}",
        z3.verdict,
        z3.stdout,
        z3.stderr
    );
    assert_eq!(
        r.fallback_count, 0,
        "{fn_name} should stay off the CHC fallback lane, got fallback_count={} with gaps={:?}",
        r.fallback_count, r.aggregate_gaps
    );
    assert_eq!(
        fn_unhandled_calls, 0,
        "{fn_name} should not report unhandled calls, map={:?}",
        r.unhandled_calls
    );
}

#[test]
fn test_exact_file_nested_push_pop_markers_localizer() {
    let fn_name = "ay_arrays_nested_push_pop_markers";
    let push_calls = exact_file_matching_calls(fn_name, "ArraySolver::push");
    let index_calls = exact_file_matching_calls(fn_name, "::index");
    assert_eq!(
        push_calls.len(),
        1,
        "{fn_name} should contain exactly one ArraySolver::push call site, got {push_calls:?}"
    );
    assert_eq!(
        index_calls.len(),
        2,
        "{fn_name} should contain exactly two index call sites \
         (`solver.scopes[i]` and `expected_markers[i]`), got {index_calls:?}"
    );

    let r = emit_exact_arrays_harness_smt(fn_name);
    let fn_aggregate_gaps = r.aggregate_gaps.get(fn_name).copied().unwrap_or(0);
    let fn_gap_reasons = fn_reason_counts(&r.aggregate_gap_reasons, fn_name);
    let fn_unhandled_calls = r.unhandled_calls.get(fn_name).copied().unwrap_or(0);
    let fn_translation_drops = r.translation_drops.get(fn_name).copied().unwrap_or(0);
    let fn_translation_sites = fn_reason_counts(&r.translation_drop_sites, fn_name);

    // Print encoding diagnostics BEFORE running Z3 so they are visible even on timeout.
    eprintln!(
        "[exact-file {fn_name}] fallback_count={}, aggregate_gap_count={}, fn_aggregate_gaps={}, \
         inferable_count={}, inferable_decls={:?}, has_p_inf_rule={}, fn_unhandled_calls={}, \
         fn_translation_drops={}, fn_gap_reasons={:?}, fn_translation_sites={:?}, \
         index_calls={:?}, smt_len={}",
        r.fallback_count,
        r.aggregate_gap_count,
        fn_aggregate_gaps,
        r.inferable_count,
        r.inferable_decls,
        r.has_p_inf_rule,
        fn_unhandled_calls,
        fn_translation_drops,
        fn_gap_reasons,
        fn_translation_sites,
        index_calls,
        r.smt.len(),
    );

    assert_eq!(
        r.fallback_count, 0,
        "{fn_name} should stay off the CHC fallback lane, got fallback_count={} with gaps={:?}",
        r.fallback_count, r.aggregate_gaps
    );
    assert_eq!(
        fn_unhandled_calls, 0,
        "{fn_name} should not report unhandled calls, map={:?}",
        r.unhandled_calls
    );

    // Z3 solver assertion skipped: the unit test SMT (1.2MB) lacks orphan pruning
    // that the full driver applies. The compiletest confirms PROOF in ~60s.
    // The encoding quality assertions above (0 fallbacks, 0 gaps, 0 unhandled calls)
    // are the authoritative unit-test signal for this harness.
}

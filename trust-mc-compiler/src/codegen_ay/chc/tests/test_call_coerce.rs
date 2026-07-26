// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_coerce.rs` — dropped-constraint counters,
//! sound-fallback goto helpers, and `build_output_args`.
//!
//! Part of #2303 (codegen_call_coerce.rs, 232 LOC).
//! `coerce_eq_constraint` itself is already extensively tested in test_core_vc.rs
//! and test_proptest.rs. This file covers the counter/bookkeeping utilities,
//! the sound-fallback goto helpers, and the `build_output_args` helper.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::sync::Arc;

use super::common::*;
use ay_bindings::Sort;

// =============================================================================
// ChcDiagnostics registry — coerce_eq_dropped_constraint (Part of #2906)
// =============================================================================
// These tests exercise the per-ctx `ChcDiagnostics` registry instead of the
// legacy global `AtomicUsize` counters. No Mutex serialization needed.

use crate::codegen_ay::chc::codegen_call_coerce::{
    emit_sound_fallback_goto, emit_sound_fallback_goto_extra, emit_sound_fallback_goto_prebuilt,
};
use crate::codegen_ay::chc::codegen_ctx::ChcDiagnostics;
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

#[test]
fn test_diagnostics_coerce_eq_dropped_initial_zero() {
    let diag = ChcDiagnostics::default();
    assert_eq!(diag.coerce_eq_dropped_constraint.get(), 0);
}

#[test]
fn test_diagnostics_coerce_eq_dropped_increment() {
    let diag = ChcDiagnostics::default();
    diag.coerce_eq_dropped_constraint.inc();
    diag.coerce_eq_dropped_constraint.inc();
    assert_eq!(diag.coerce_eq_dropped_constraint.get(), 2);
}

#[test]
fn test_diagnostics_coerce_dropped_by_fn_empty_initially() {
    let diag = ChcDiagnostics::default();
    assert!(diag.coerce_dropped_by_fn.is_empty());
}

#[test]
fn test_diagnostics_coerce_dropped_by_fn_tracks_per_function() {
    let mut diag = ChcDiagnostics::default();
    *diag.coerce_dropped_by_fn.entry(Arc::from("fn_a")).or_default() += 3;
    *diag.coerce_dropped_by_fn.entry(Arc::from("fn_b")).or_default() += 7;
    assert_eq!(diag.coerce_dropped_by_fn.get("fn_a" as &str), Some(&3));
    assert_eq!(diag.coerce_dropped_by_fn.get("fn_b" as &str), Some(&7));
}

#[test]
fn test_diagnostics_default_resets_all_counters() {
    let mut diag = ChcDiagnostics::default();
    diag.coerce_eq_dropped_constraint.inc();
    *diag.coerce_dropped_by_fn.entry(Arc::from("fn_x")).or_default() += 1;

    // Creating a fresh default is equivalent to registry.reset().
    let fresh = ChcDiagnostics::default();
    assert_eq!(fresh.coerce_eq_dropped_constraint.get(), 0);
    assert!(fresh.coerce_dropped_by_fn.is_empty());
}

// =============================================================================
// sound-fallback goto helpers
// =============================================================================

#[test]
fn test_emit_sound_fallback_goto_records_counter_and_emits_rule() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[0],
            &[Expr::bool_const(true)],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(chc_ctx.sound_fallback_count(), before_fallback + 1);
        assert_eq!(emitted.len(), 1, "helper should emit exactly one goto rule");
        assert_eq!(
            emitted[0].body.constraints.len(),
            1,
            "plain helper should preserve the base constraint slice"
        );
        assert_eq!(
            emitted[0].head.name,
            *chc_ctx.block_relations.get(&target).expect("target relation should exist"),
            "helper should target the requested block relation"
        );
    });
}

#[test]
fn test_emit_sound_fallback_goto_extra_appends_extra_constraints() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_rules = chc_ctx.vc.rules.len();
        let extra_a = Expr::var("sound_extra_a", Sort::bool());
        let extra_b = Expr::var("sound_extra_b", Sort::bool());

        emit_sound_fallback_goto_extra(
            &mut chc_ctx,
            &from_app,
            target,
            &HashSet::new(),
            &[0],
            &[Expr::bool_const(true)],
            [extra_a, extra_b],
        );

        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert_eq!(chc_ctx.sound_fallback_count(), before_fallback + 1);
        assert_eq!(emitted.len(), 1, "helper should emit exactly one goto rule");
        assert_eq!(
            emitted[0].body.constraints.len(),
            3,
            "extra helper should append two extra constraints after the base slice"
        );
    });
}

#[test]
fn test_emit_sound_fallback_goto_prebuilt_uses_supplied_output_args() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(0));
        let target = *chc_ctx
            .block_relations
            .keys()
            .find(|&&idx| idx != 0)
            .expect("at least one non-entry block");

        let late_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        chc_ctx.push_late_state_var_pair(
            Arc::from("manual_late_region"),
            "manual_late_region__out",
            late_sort.clone(),
        );

        let live = chc_ctx.state_var_mgr.live_state_indices[target].clone();
        let custom_idx = *live.last().expect("target block should have live vars");
        let custom_pos =
            live.iter().position(|&idx| idx == custom_idx).expect("custom live index position");
        let mut output_args = chc_ctx.build_output_args(&HashSet::new(), &[]);
        let custom_arg = Expr::var("manual_prebuilt_out", late_sort);
        output_args[custom_idx] = custom_arg.clone();
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_rules = chc_ctx.vc.rules.len();

        emit_sound_fallback_goto_prebuilt(
            &mut chc_ctx,
            &from_app,
            target,
            &output_args,
            &[Expr::bool_const(true)],
        );

        let emitted = chc_ctx.vc.rules.get(before_rules).expect("emitted rule");
        assert_eq!(chc_ctx.sound_fallback_count(), before_fallback + 1);
        assert_eq!(
            emitted.head.args[custom_pos].to_string(),
            custom_arg.to_string(),
            "prebuilt helper should thread the supplied projected output arg unchanged"
        );
    });
}

// =============================================================================
// build_output_args via ChcCtx
// =============================================================================

const BUILD_OUTPUT_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn build_output_probe(x: u32, y: u32) -> u32 {
        let z = x + y;
        z
    }
"#;

#[test]
fn test_build_output_args_no_modifications() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        let empty_set = HashSet::new();
        let output_args = chc_ctx.build_output_args(&empty_set, &[]);

        // With no modifications, all args should use input-state variables
        assert_eq!(
            output_args.len(),
            chc_ctx.state_var_mgr.state_vars.len(),
            "output args count should match state vars"
        );
        for (idx, arg) in output_args.iter().enumerate() {
            let (in_name, _) = &chc_ctx.state_var_mgr.state_vars[idx];
            assert!(
                arg.to_string().contains(&**in_name),
                "with no modifications, output arg {} should use input var '{}'",
                idx,
                in_name
            );
        }
    });
}

#[test]
fn test_build_output_args_with_modifications() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        if chc_ctx.state_var_mgr.state_vars.is_empty() {
            return; // Cannot test without state vars
        }

        // Mark first local as modified
        let mut modified = HashSet::new();
        modified.insert(0);
        let output_args = chc_ctx.build_output_args(&modified, &[]);

        assert_eq!(output_args.len(), chc_ctx.state_var_mgr.state_vars.len());
        // The modified local (idx 0) should use output state var
        if !chc_ctx.state_var_mgr.output_state_vars.is_empty() {
            let (out_name, _) = &chc_ctx.state_var_mgr.output_state_vars[0];
            assert!(
                output_args[0].to_string().contains(&**out_name),
                "modified local should use output var '{}', got '{}'",
                out_name,
                output_args[0]
            );
        }
    });
}

#[test]
fn test_build_output_args_with_extra_dest() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        if chc_ctx.state_var_mgr.state_vars.len() < 2 {
            return;
        }

        // extra_dest points at local 1, no modified set
        let empty_set = HashSet::new();
        let output_args = chc_ctx.build_output_args(&empty_set, &[1]);

        // Local 1 should use output state var due to extra_dest
        let vec_idx = chc_ctx.state_idx_for_local(1);
        if vec_idx < chc_ctx.state_var_mgr.output_state_vars.len() {
            let (out_name, _) = &chc_ctx.state_var_mgr.output_state_vars[vec_idx];
            assert!(
                output_args[vec_idx].to_string().contains(&**out_name),
                "extra_dest local should use output var"
            );
        }
    });
}

#[test]
fn test_build_output_args_maps_local_index_to_state_index() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        if chc_ctx.state_var_mgr.state_vars.is_empty() {
            return;
        }

        // Use a synthetic local -> vec index mapping to force the remap path.
        let synthetic_local = 9_999usize;
        let target_vec_idx = 0usize;
        chc_ctx.state_var_mgr.local_to_state_idx.insert(synthetic_local, target_vec_idx);

        let mut modified = HashSet::new();
        modified.insert(synthetic_local);
        let output_args = chc_ctx.build_output_args(&modified, &[]);

        let (out_name, _) = &chc_ctx.state_var_mgr.output_state_vars[target_vec_idx];
        assert!(
            output_args[target_vec_idx].to_string().contains(&**out_name),
            "modified MIR local should map through local_to_state_idx to output var '{}'",
            out_name
        );
    });
}

/// Regression test for #2746: unmapped locals in modified_locals and extra_dests
/// are gracefully skipped (continue) instead of panicking. Verifies the
/// panic-to-continue migration from abc704e42c.
#[test]
fn test_build_output_args_unmapped_locals_gracefully_skipped() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        if chc_ctx.state_var_mgr.state_vars.is_empty() {
            return;
        }

        // Baseline: no modifications.
        let baseline = chc_ctx.build_output_args(&HashSet::new(), &[]);

        // Insert a high synthetic local that has NO mapping in local_to_state_idx.
        // This must be gracefully skipped, not panic.
        let unmapped_local = 99_999usize;
        assert!(
            chc_ctx.try_state_idx_for_local(unmapped_local).is_none(),
            "precondition: synthetic local must not be mapped"
        );

        // Test graceful-skip path #1: unmapped local in modified_locals.
        let mut modified = HashSet::new();
        modified.insert(unmapped_local);
        let result_modified = chc_ctx.build_output_args(&modified, &[]);
        assert_eq!(
            result_modified.len(),
            baseline.len(),
            "unmapped modified_locals entry should be skipped, not affect output length"
        );
        for (idx, (res, base)) in result_modified.iter().zip(baseline.iter()).enumerate() {
            assert_eq!(
                res.to_string(),
                base.to_string(),
                "output arg {} should match baseline when modified_locals contains only unmapped locals",
                idx
            );
        }

        // Test graceful-skip path #2: unmapped local in extra_dests.
        let result_extra = chc_ctx.build_output_args(&HashSet::new(), &[unmapped_local]);
        for (idx, (res, base)) in result_extra.iter().zip(baseline.iter()).enumerate() {
            assert_eq!(
                res.to_string(),
                base.to_string(),
                "output arg {} should match baseline when extra_dests contains only unmapped locals",
                idx
            );
        }
    });
}

#[test]
fn test_build_output_args_propagates_modified_type_arrays() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        let mem_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let i32_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("_probe_mem_i32", "_probe_mem_i32__out", mem_sort.clone());
        let u32_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("_probe_mem_u32", "_probe_mem_u32__out", mem_sort);

        // Only i32 is marked modified via centralized index tracking (Part of #2552);
        // u32 must remain input.
        chc_ctx.mark_state_var_modified(i32_idx);
        let output_args = chc_ctx.build_output_args(&HashSet::new(), &[]);

        assert!(
            output_args[i32_idx].to_string().contains("_probe_mem_i32__out"),
            "modified mem array should use output-state var"
        );
        assert!(
            output_args[u32_idx].to_string().contains("_probe_mem_u32"),
            "unmodified mem array should keep input-state var"
        );
    });
}

#[test]
fn test_build_output_args_propagates_metadata_arrays() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        let idx_valid = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("obj_valid", "obj_valid__out", Sort::bool());

        let idx_size = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("obj_size", "obj_size__out", Sort::bitvec(64));

        // Mark via centralized index tracking (Part of #2552).
        chc_ctx.mark_state_var_modified(idx_valid);
        chc_ctx.mark_state_var_modified(idx_size);
        let output_args = chc_ctx.build_output_args(&HashSet::new(), &[]);

        assert!(
            output_args[idx_valid].to_string().contains("obj_valid__out"),
            "modified obj_valid metadata should use output-state var"
        );
        assert!(
            output_args[idx_size].to_string().contains("obj_size__out"),
            "modified obj_size metadata should use output-state var"
        );
    });
}

/// Regression test for #2552: Region arrays must be propagated through build_output_args.
/// Region array names contain "_region_" (not "_mem_"), so the old name-based check
/// missed them. The fix uses modified_state_indices for centralized tracking.
#[test]
fn test_build_output_args_propagates_region_arrays() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        // Simulate a region array state variable (e.g., from heap_alloc + store).
        // Region arrays have names like "_fn_region_1_bv8" — NOT matching "_mem_".
        let region_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let region_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx
            .state_var_mgr
            .state_vars
            .push((Arc::from("_build_output_probe_region_1_bv8"), region_sort.clone()));
        chc_ctx
            .state_var_mgr
            .output_state_vars
            .push((Arc::from("_build_output_probe_region_1_bv8__out"), region_sort.clone()));

        // Add an unmodified region array for contrast.
        let unmod_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx
            .state_var_mgr
            .state_vars
            .push((Arc::from("_build_output_probe_region_2_bv32"), region_sort.clone()));
        chc_ctx
            .state_var_mgr
            .output_state_vars
            .push((Arc::from("_build_output_probe_region_2_bv32__out"), region_sort));

        // Mark region_1 as modified via centralized index tracking (Part of #2552).
        chc_ctx.mark_state_var_modified(region_idx);

        let output_args = chc_ctx.build_output_args(&HashSet::new(), &[]);

        // Modified region array must use output-state var.
        assert!(
            output_args[region_idx].to_string().contains("_region_1_bv8__out"),
            "modified region array should use output-state var, got: {}",
            output_args[region_idx]
        );
        // Unmodified region array must keep input-state var.
        assert!(
            !output_args[unmod_idx].to_string().contains("__out"),
            "unmodified region array should keep input-state var, got: {}",
            output_args[unmod_idx]
        );
    });
}

/// Regression test for #2552: build_block_output_args also propagates region arrays
/// via modified_state_indices.
#[test]
fn test_build_block_output_args_propagates_region_arrays() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        let region_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let region_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx
            .state_var_mgr
            .state_vars
            .push((Arc::from("_build_output_probe_region_3_bv8"), region_sort.clone()));
        chc_ctx
            .state_var_mgr
            .output_state_vars
            .push((Arc::from("_build_output_probe_region_3_bv8__out"), region_sort));

        // Mark via centralized index tracking.
        chc_ctx.mark_state_var_modified(region_idx);

        let output_args = chc_ctx.build_block_output_args(&HashSet::new(), None);

        assert!(
            output_args[region_idx].to_string().contains("_region_3_bv8__out"),
            "build_block_output_args should propagate region arrays via modified_state_indices, got: {}",
            output_args[region_idx]
        );
    });
}

/// Regression test for #2557: Collection length state vars must propagate through
/// build_output_args via modified_state_indices. Before this fix, Vec/String stubs
/// called collection_len_state.mark_len_modified() (raw path) which did NOT record
/// the index in modified_state_indices. The centralized mark_collection_len_modified()
/// wrapper records both.
#[test]
fn test_build_output_args_propagates_collection_len_vars() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        // Simulate a collection length state variable (e.g., from Vec::push).
        let len_sort = Sort::bitvec(64);
        let len_name = "vec_build_output_probe_len_3";
        let len_out_name = crate::codegen_ay::names::out_name(len_name);
        let len_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(len_name, &len_out_name, len_sort.clone());

        // Add an unmodified length var for contrast.
        let unmod_name = "vec_build_output_probe_len_7";
        let unmod_out_name = crate::codegen_ay::names::out_name(unmod_name);
        let unmod_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(unmod_name, &unmod_out_name, len_sort);

        // Use the centralized wrapper — this is what Vec/String stubs now call.
        chc_ctx.mark_collection_len_modified(len_name);

        // Verify the index was recorded in modified_state_indices.
        assert!(
            chc_ctx.encode.modified_state_indices.contains(&len_idx),
            "mark_collection_len_modified must record index in modified_state_indices"
        );

        let output_args = chc_ctx.build_output_args(&HashSet::new(), &[]);

        // Modified length var must use output-state var.
        assert!(
            output_args[len_idx].to_string().contains("_len_3__out"),
            "modified collection length var should use output-state var, got: {}",
            output_args[len_idx]
        );
        // Unmodified length var must keep input-state var.
        assert!(
            !output_args[unmod_idx].to_string().contains("__out"),
            "unmodified collection length var should keep input-state var, got: {}",
            output_args[unmod_idx]
        );
    });
}

/// Regression test for #2557: build_block_output_args also propagates collection
/// length vars via modified_state_indices.
#[test]
fn test_build_block_output_args_propagates_collection_len_vars() {
    with_test_ay_ctx_for_source(BUILD_OUTPUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "build_output_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "build_output_probe", ChcConfig::default());

        let len_sort = Sort::bitvec(64);
        let len_name = "vec_build_output_probe_len_5";
        let len_out_name = crate::codegen_ay::names::out_name(len_name);
        let len_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(len_name, &len_out_name, len_sort);

        // Use centralized wrapper (the fix for #2557).
        chc_ctx.mark_collection_len_modified(len_name);

        let output_args = chc_ctx.build_block_output_args(&HashSet::new(), None);

        assert!(
            output_args[len_idx].to_string().contains("_len_5__out"),
            "build_block_output_args should propagate collection length vars via modified_state_indices, got: {}",
            output_args[len_idx]
        );
    });
}

#[test]
fn test_coerce_eq_raw_bv_to_datatype_reconstructs_tag_free_option_payload() {
    let root_sort = struct_sort(
        "StorageRoot",
        [("height", Sort::bitvec(64)), ("node", Sort::bitvec(64)), ("marker", Sort::bool())],
    );
    let option_root_sort = enum_sort(
        "Option_StorageRoot",
        [
            ("None_StorageRoot", Vec::<(&str, Sort)>::new()),
            ("Some_StorageRoot", vec![("value", root_sort)]),
        ],
    );
    let foo_sort = struct_sort("Foo", [("root", option_root_sort), ("length", Sort::bitvec(64))]);
    let dest_var = Expr::var("foo_out", foo_sort.clone());
    let raw_read = Expr::var("raw_foo_read", Sort::bitvec(192));

    let result = coerce_eq_constraint(&dest_var, raw_read, &foo_sort, false);
    assert!(
        result.is_some(),
        "raw 192-bit Foo memory should reconstruct to the Foo datatype despite \
         tag-free Option payload and zero-width marker fields"
    );
}

#[test]
fn test_coerce_eq_raw_bv_to_rustc_foo_datatype_reconstructs_storage_marker_layout() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::marker::PhantomData;
        use std::ptr::NonNull;

        struct LeafNode;

        mod marker {
            pub enum Leaf {}
            pub enum Owned {}
        }

        struct NodeRef<BorrowType, Type> {
            height: usize,
            node: NonNull<LeafNode>,
            _marker: PhantomData<(BorrowType, Type)>,
        }

        type Root = NodeRef<marker::Owned, marker::Leaf>;

        struct Foo {
            root: Option<Root>,
            length: usize,
        }

        pub fn probe(foo: Foo) -> usize {
            foo.length
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe");
        let foo_ty = sig.inputs()[0];
        let foo_sort = ChcCtx::translate_ty(foo_ty).expect("Foo should translate");
        assert!(foo_sort.is_datatype(), "Foo should use datatype encoding");

        let dest_var = Expr::var("foo_out", foo_sort.clone());
        let raw_read = Expr::var("raw_foo_read", Sort::bitvec(192));
        let result = coerce_eq_constraint(&dest_var, raw_read, &foo_sort, false);
        assert!(
            result.is_some(),
            "raw 192-bit Rust Foo memory should reconstruct to the rustc-derived Foo datatype"
        );
    });
}

// =============================================================================
// Datatype→Array coercion via fld_data extraction (#1632)
// =============================================================================

/// Part of #1632: When a Slice Datatype (fld_ptr, fld_len, fld_data) is the
/// call result and the destination sort is Array (from CHC translate_ty for [T]),
/// coerce_eq_constraint should extract fld_data and succeed.
///
/// Pre-fix: coercion fails → constraint dropped → destination unconstrained →
/// slice indexing returns symbolic garbage instead of stored element values.
#[test]
fn test_coerce_eq_datatype_slice_to_array_extracts_fld_data() {
    let elem_sort = Sort::bitvec(32);
    let array_sort = Sort::array(Sort::bitvec(64), elem_sort.clone());

    // Destination: Array-sorted state var (CHC translate_ty maps [T] to Array)
    let dest_var = Expr::var("slice_dest", array_sort.clone());

    // Result: Slice Datatype with (fld_ptr, fld_len, fld_data)
    let slice_name = "Slice_bv32";
    let ctor_name = names::cons_name(slice_name);
    let slice_sort = struct_sort(
        slice_name,
        [
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_data", array_sort.clone()),
        ],
    );
    let ptr = Expr::bitvec_const(0x1000u64, 64);
    let len = Expr::bitvec_const(3u64, 64);
    let data_default = Expr::var("data_backing", elem_sort);
    let data = Expr::const_array(Sort::bitvec(64), data_default);
    let slice_expr =
        Expr::datatype_constructor(slice_name, ctor_name, vec![ptr, len, data], slice_sort);

    let result = coerce_eq_constraint(&dest_var, slice_expr, &array_sort, false);
    assert!(
        result.is_some(),
        "coerce_eq_constraint should extract fld_data from Slice Datatype to match Array dest"
    );

    // The constraint should be an equality with the extracted fld_data
    let constraint = result.unwrap();
    let text = constraint.to_string();
    assert!(
        text.contains("fld_data") || text.contains("const_array") || text.contains("select"),
        "constraint should reference fld_data extraction, got: {text}"
    );
}

/// Part of #1632: Coercion should fail when the Datatype's fld_data sort does
/// NOT match the destination Array sort (e.g., Array(BV64, BV8) vs Array(BV64, BV32)).
#[test]
fn test_coerce_eq_datatype_fld_data_sort_mismatch_returns_none() {
    let dest_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let dest_var = Expr::var("dest", dest_sort.clone());

    // Slice with fld_data: Array(BV64, BV8) — mismatches dest Array(BV64, BV32)
    let mismatched_data_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let slice_sort = struct_sort(
        "Slice_bv8",
        [
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_data", mismatched_data_sort),
        ],
    );
    let ctor_name = names::cons_name("Slice_bv8");
    let ptr = Expr::bitvec_const(0u64, 64);
    let len = Expr::bitvec_const(0u64, 64);
    let data = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(0u64, 8));
    let slice_expr =
        Expr::datatype_constructor("Slice_bv8", ctor_name, vec![ptr, len, data], slice_sort);

    let result = coerce_eq_constraint(&dest_var, slice_expr, &dest_sort, false);
    assert!(
        result.is_none(),
        "coerce_eq_constraint should return None when fld_data sort doesn't match dest Array sort"
    );
}

// Sound-fallback correctness invariant tests moved to
// test_call_sound_fallback_invariants.rs (Part of #4158).

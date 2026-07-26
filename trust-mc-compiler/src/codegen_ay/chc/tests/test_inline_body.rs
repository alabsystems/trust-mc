// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `call/inline_body.rs`.
//!
//! Part of #4197: speculative inline rollback must restore all inline-mutated
//! transient CHC context state, not just heap updates.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_body::speculative_inline;
use crate::codegen_ay::chc::codegen_ctx::types::RefTarget;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use std::collections::HashMap;

struct BaselineState {
    update: Expr,
    modified: std::collections::HashSet<usize>,
    ref_value: Expr,
    ref_offset: Expr,
    ref_target: RefTarget,
}

fn seed_baseline_state(chc_ctx: &mut ChcCtx<'_, '_>) -> BaselineState {
    let update = Expr::bool_const(true);
    let ref_value = Expr::bitvec_const(3, POINTER_WIDTH);
    let ref_offset = Expr::bitvec_const(1, POINTER_WIDTH);
    let ref_target = RefTarget { local: 1, projections: vec![] };
    chc_ctx.heap_state.pending_updates.push(update.clone());
    chc_ctx.encode.modified_state_indices.insert(7);
    chc_ctx.ref_resolution.ref_targets.insert(1, ref_target.clone());
    chc_ctx.ref_resolution.call_forwarded_raw_ptrs.insert(1);
    chc_ctx.ref_resolution.const_ref_values.insert(1, ref_value.clone());
    chc_ctx.ref_resolution.const_ref_slice_views.insert(1, ref_value.clone());
    chc_ctx.ref_resolution.subslice_len.insert(1, ref_value.clone());
    chc_ctx.ref_resolution.subslice_offset.insert(1, ref_offset.clone());
    BaselineState {
        update,
        modified: chc_ctx.encode.modified_state_indices.clone(),
        ref_value,
        ref_offset,
        ref_target,
    }
}

fn mutate_failed_speculative_state(ctx: &mut ChcCtx<'_, '_>) -> Option<()> {
    ctx.encode.modified_state_indices.insert(99);
    ctx.heap_state.pending_updates.push(Expr::bool_const(false));
    ctx.heap_state.pending_checks.push(Expr::bool_const(false));
    ctx.heap_state.modified_arrays.insert("speculative".into());
    ctx.ref_resolution.ref_targets.insert(1, RefTarget { local: 9, projections: vec![] });
    ctx.ref_resolution.ref_targets.insert(2, RefTarget { local: 2, projections: vec![] });
    ctx.ref_resolution.call_forwarded_raw_ptrs.remove(&1);
    ctx.ref_resolution.call_forwarded_raw_ptrs.insert(2);
    ctx.ref_resolution.const_ref_values.insert(1, Expr::bitvec_const(9, POINTER_WIDTH));
    ctx.ref_resolution.const_ref_values.insert(2, Expr::bitvec_const(2, POINTER_WIDTH));
    ctx.ref_resolution.const_ref_slice_views.insert(1, Expr::bitvec_const(8, POINTER_WIDTH));
    ctx.ref_resolution.const_ref_slice_views.insert(2, Expr::bitvec_const(7, POINTER_WIDTH));
    ctx.ref_resolution.subslice_len.insert(1, Expr::bitvec_const(6, POINTER_WIDTH));
    ctx.ref_resolution.subslice_len.insert(2, Expr::bitvec_const(5, POINTER_WIDTH));
    ctx.ref_resolution.subslice_offset.insert(1, Expr::bitvec_const(4, POINTER_WIDTH));
    ctx.ref_resolution.subslice_offset.insert(2, Expr::bitvec_const(3, POINTER_WIDTH));
    None
}

fn assert_expr_entry(map: &HashMap<usize, Expr>, key: usize, expected: &Expr, label: &str) {
    assert_eq!(
        map.get(&key).unwrap_or_else(|| panic!("missing {label} entry {key}")).to_string(),
        expected.to_string(),
        "{label} should be restored for key {key}"
    );
}

fn assert_failed_heap_rollback(chc_ctx: &ChcCtx<'_, '_>, baseline: &BaselineState) {
    assert_eq!(
        chc_ctx.encode.modified_state_indices, baseline.modified,
        "failed speculative inline must restore modified_state_indices"
    );
    assert_eq!(
        chc_ctx.heap_state.pending_updates.len(),
        1,
        "failed speculative inline must discard new pending_updates"
    );
    assert_eq!(
        chc_ctx.heap_state.pending_updates[0].to_string(),
        baseline.update.to_string(),
        "failed speculative inline must preserve pre-existing pending_updates"
    );
    assert!(
        chc_ctx.heap_state.pending_checks.is_empty(),
        "failed speculative inline must discard new pending_checks"
    );
    assert!(
        chc_ctx.heap_state.modified_arrays.is_empty(),
        "failed speculative inline must discard modified array marks"
    );
}

fn assert_failed_ref_metadata_rollback(chc_ctx: &ChcCtx<'_, '_>, baseline: &BaselineState) {
    assert_eq!(
        chc_ctx.ref_resolution.ref_targets.get(&1).expect("baseline ref target").local,
        baseline.ref_target.local,
        "failed speculative inline must restore ref_targets"
    );
    assert!(chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&1));
    assert!(!chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&2));
    assert_expr_entry(
        &chc_ctx.ref_resolution.const_ref_values,
        1,
        &baseline.ref_value,
        "const_ref_values",
    );
    assert!(!chc_ctx.ref_resolution.const_ref_values.contains_key(&2));
    assert_expr_entry(
        &chc_ctx.ref_resolution.const_ref_slice_views,
        1,
        &baseline.ref_value,
        "const_ref_slice_views",
    );
    assert!(!chc_ctx.ref_resolution.const_ref_slice_views.contains_key(&2));
    assert_expr_entry(&chc_ctx.ref_resolution.subslice_len, 1, &baseline.ref_value, "subslice_len");
    assert!(!chc_ctx.ref_resolution.subslice_len.contains_key(&2));
    assert_expr_entry(
        &chc_ctx.ref_resolution.subslice_offset,
        1,
        &baseline.ref_offset,
        "subslice_offset",
    );
    assert!(!chc_ctx.ref_resolution.subslice_offset.contains_key(&2));
}

fn mutate_successful_speculative_state(ctx: &mut ChcCtx<'_, '_>) -> Option<Expr> {
    ctx.encode.modified_state_indices.insert(11);
    ctx.heap_state.pending_updates.push(Expr::bool_const(true));
    ctx.heap_state.pending_checks.push(Expr::bool_const(false));
    ctx.heap_state.modified_arrays.insert("speculative_success".into());
    ctx.ref_resolution.ref_targets.insert(4, RefTarget { local: 4, projections: vec![] });
    ctx.ref_resolution.call_forwarded_raw_ptrs.insert(4);
    ctx.ref_resolution.const_ref_values.insert(4, Expr::bitvec_const(4, POINTER_WIDTH));
    ctx.ref_resolution.const_ref_slice_views.insert(4, Expr::bitvec_const(5, POINTER_WIDTH));
    ctx.ref_resolution.subslice_len.insert(4, Expr::bitvec_const(6, POINTER_WIDTH));
    ctx.ref_resolution.subslice_offset.insert(4, Expr::bitvec_const(1, POINTER_WIDTH));
    Some(Expr::bool_const(true))
}

fn assert_successful_speculative_state(chc_ctx: &ChcCtx<'_, '_>, result: Option<Expr>) {
    assert!(result.is_some(), "successful speculative inline should return its value");
    assert!(chc_ctx.encode.modified_state_indices.contains(&11));
    assert_eq!(chc_ctx.heap_state.pending_updates.len(), 1);
    assert_eq!(
        chc_ctx.heap_state.pending_updates[0].to_string(),
        Expr::bool_const(true).to_string()
    );
    assert_eq!(chc_ctx.heap_state.pending_checks.len(), 1);
    assert!(chc_ctx.heap_state.modified_arrays.contains("speculative_success"));
    assert!(chc_ctx.ref_resolution.ref_targets.contains_key(&4));
    assert!(chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&4));
    assert!(chc_ctx.ref_resolution.const_ref_values.contains_key(&4));
    assert!(chc_ctx.ref_resolution.const_ref_slice_views.contains_key(&4));
    assert!(chc_ctx.ref_resolution.subslice_len.contains_key(&4));
    assert!(chc_ctx.ref_resolution.subslice_offset.contains_key(&4));
}

#[test]
fn test_speculative_inline_restores_transient_state_on_none() {
    with_test_ay_ctx_for_source(
        "pub fn probe_speculative_inline_restore(x: u32) -> u32 { x }",
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_speculative_inline_restore");
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_speculative_inline_restore",
                ChcConfig::default(),
            );
            let baseline = seed_baseline_state(&mut chc_ctx);

            let result = speculative_inline(&mut chc_ctx, mutate_failed_speculative_state);

            assert!(result.is_none(), "failed speculative inline should propagate None");
            assert_failed_heap_rollback(&chc_ctx, &baseline);
            assert_failed_ref_metadata_rollback(&chc_ctx, &baseline);
        },
    );
}

#[test]
fn test_speculative_inline_preserves_transient_state_on_success() {
    with_test_ay_ctx_for_source(
        "pub fn probe_speculative_inline_success(x: u32) -> u32 { x }",
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_speculative_inline_success");
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                "probe_speculative_inline_success",
                ChcConfig::default(),
            );

            let result = speculative_inline(&mut chc_ctx, mutate_successful_speculative_state);

            assert_successful_speculative_state(&chc_ctx, result);
        },
    );
}

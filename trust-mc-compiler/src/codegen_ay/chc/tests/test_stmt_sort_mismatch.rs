// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

//! Tests for SORT_MISMATCH fallback paths in `encode_block_statements`.
//!
//! These paths are soundness-critical: when `coerce_assignment_rhs_to_sort`
//! fails, we must still emit a symbolic assignment constraint and increment
//! fallback counters. Part of #2706.

use super::common::*;
use ay_bindings::Sort;

/// Source: identity function. MIR: `_0 = _1` (simple Copy, no projection,
/// no flattened tuples). We corrupt the return local's output sort.
const SOURCE_IDENTITY: &str = r#"
    #![allow(dead_code)]
    pub fn probe_sort_mismatch(x: u32) -> u32 { x }
"#;

/// Test the non-bitvec SORT_MISMATCH fallback branch.
///
/// Corrupt return local _0's output sort to an Array sort (non-bitvec).
/// Coercion fails, so codegen must:
/// 1. increment `fallback_count`
/// 2. keep the destination local in `modified`
/// 3. emit a destination equality with a fresh symbolic fallback.
#[test]
fn test_sort_mismatch_non_bitvec_uses_symbolic_fallback_constraint() {
    with_test_ay_ctx_for_source(SOURCE_IDENTITY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_sort_mismatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_sort_mismatch", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Corrupt return local _0's output sort to Array(Int, Int) (non-bitvec).
        // Using Int-indexed/valued array because BV→Array(BV,BV) is now handled
        // by #4086 coercion. Int-indexed arrays still can't be coerced from BV.
        let return_local = 0usize;
        let vec_idx = chc_ctx.state_idx_for_local(return_local);
        let original_sort = chc_ctx.state_var_mgr.output_state_vars[vec_idx].1.clone();
        assert!(
            original_sort.bitvec_width().is_some(),
            "original sort should be bitvec, got {:?}",
            original_sort
        );

        let array_sort = Sort::array(Sort::int(), Sort::int());
        let name = chc_ctx.state_var_mgr.output_state_vars[vec_idx].0.clone();
        chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (name, array_sort);

        let before = chc_ctx.sound_fallback_count();

        let (constraints, _output_args, modified, _safety_checks) =
            chc_ctx.encode_block_statements(0);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            modified.contains(&return_local),
            "non-bitvec sort mismatch should keep destination local modified via symbolic fallback"
        );

        assert!(
            after > before,
            "non-bitvec sort mismatch should increment sound_fallback_count (before={before}, after={after})"
        );

        let corrupted_name = &chc_ctx.state_var_mgr.output_state_vars[vec_idx].0;
        let has_constraint_for_corrupted =
            constraints.iter().any(|c| c.to_string().contains(&**corrupted_name));
        assert!(
            has_constraint_for_corrupted,
            "symbolic fallback should still emit equality for sort-mismatched output var '{}'",
            corrupted_name
        );

        let has_ssa_init_fallback =
            constraints.iter().any(|c| c.to_string().contains("__ssa_init_assign"));
        assert!(
            has_ssa_init_fallback,
            "non-bitvec sort mismatch should use __ssa_init_assign symbolic fallback"
        );
    });
}

/// Test the bitvec SORT_MISMATCH branch where address fallback is unavailable.
#[test]
fn test_sort_mismatch_bitvec_addr_fallback_none_uses_symbolic_fallback() {
    with_test_ay_ctx_for_source(SOURCE_IDENTITY, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_sort_mismatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_sort_mismatch", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Keep destination bitvec, but make rhs local resolve to a non-coercible sort.
        let return_local = 0usize;
        let arg_local = 1usize;
        let arg_vec_idx = chc_ctx.state_idx_for_local(arg_local);
        let arg_name = chc_ctx.state_var_mgr.state_vars[arg_vec_idx].0.clone();
        let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
        chc_ctx.state_var_mgr.state_vars[arg_vec_idx] = (arg_name, array_sort);

        let before = chc_ctx.sound_fallback_count();
        let (constraints, _output_args, modified, _safety_checks) =
            chc_ctx.encode_block_statements(0);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            modified.contains(&return_local),
            "bitvec sort mismatch should keep destination local modified via symbolic fallback"
        );

        assert!(
            after > before,
            "bitvec sort mismatch should increment sound_fallback_count (before={before}, after={after})"
        );

        let out_name =
            &chc_ctx.state_var_mgr.output_state_vars[chc_ctx.state_idx_for_local(return_local)].0;
        assert!(
            constraints.iter().any(|c| c.to_string().contains(&**out_name)),
            "bitvec sort mismatch should still emit equality for destination output var {out_name}"
        );

        assert!(
            constraints.iter().any(|c| c.to_string().contains("__ssa_init_assign")),
            "bitvec sort mismatch should use __ssa_init_assign symbolic fallback"
        );
    });
}

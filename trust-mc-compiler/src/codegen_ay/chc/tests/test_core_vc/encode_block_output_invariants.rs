// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// encode_block_statements happy path (Part of #2188)
// =============================================================================

#[test]
fn test_encode_block_statements_output_args_and_sort_invariants() {
    // (#2188) encode_block_statements output_args invariant: each block
    // produces exactly state_vars.len() output args, each with correct sort.
    // Also verifies that all emitted constraints are Bool sort.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_invariants(mut x: u32) {
            x = 42;
            let _ = x;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_invariants");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_invariants", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for bb_idx in 0..body.blocks.len() {
            let (constraints, output_args, _modified, _safety_checks) =
                chc_ctx.encode_block_statements(bb_idx);

            // Core invariant: output_args count == state_vars count
            assert_eq!(
                output_args.len(),
                chc_ctx.state_var_mgr.state_vars.len(),
                "bb{bb_idx}: output_args count should match state_vars"
            );

            // Each output arg sort should match its corresponding state var sort
            for (i, ((_name, sort), arg)) in
                chc_ctx.state_var_mgr.state_vars.iter().zip(output_args.iter()).enumerate()
            {
                assert_eq!(arg.sort(), sort, "bb{bb_idx}: output_arg[{i}] sort mismatch");
            }

            // All constraints must be Bool
            for c in &constraints {
                assert!(c.sort().is_bool(), "bb{bb_idx}: constraint should be Bool");
            }
        }
    });
}

#[test]
fn test_encode_block_statements_output_args_count_matches_state_vars() {
    // (#2188) The output_args vector must have the same length as state_vars
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_output_count(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_output_count");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_output_count", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (_constraints, output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(0);

        assert_eq!(
            output_args.len(),
            chc_ctx.state_var_mgr.state_vars.len(),
            "output_args count should match state_vars count"
        );
    });
}

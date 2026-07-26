// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// mir_to_chc pipeline: struct field reference (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_function_with_struct_generates_vc() {
    // (#2188) A function that constructs a struct should produce a valid VC
    // with relations and rules for all basic blocks. This exercises the
    // aggregate translation path (codegen_stmt_aggregate.rs).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_struct() -> (u32, u32) {
            let a: u32 = 10;
            let b: u32 = 20;
            (a, b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct", ChcConfig::default());

        let bb_count = body.blocks.len();

        // All blocks should have relations
        assert!(
            vc.relations.len() >= bb_count,
            "Should declare relations for all {} BBs, got {}",
            bb_count,
            vc.relations.len()
        );

        // Should have entry rule + at least one transition per block
        assert!(
            vc.rules.len() >= bb_count,
            "Should have rules for all {} BBs, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

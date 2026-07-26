// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// mir_to_chc pipeline: multi-block function (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_branching_function_generates_transition_rules() {
    // (#2188) A function with if/else should generate guarded transition rules
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_branching(x: u32) -> u32 {
            if x > 10 { x.wrapping_mul(2) } else { x.wrapping_add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_branching");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_branching", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(bb_count >= 3, "Branching function should have at least 3 BBs, got {bb_count}");

        // Relations = at least N block relations + error relation
        assert!(
            vc.relations.len() >= bb_count,
            "Should declare at least {} relations (one per BB + error), got {}",
            bb_count,
            vc.relations.len()
        );

        // Should have at least one guarded transition rule (SwitchInt generates guards)
        assert!(
            vc.rules.len() >= bb_count,
            "Should have at least {} rules (entry + transitions), got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

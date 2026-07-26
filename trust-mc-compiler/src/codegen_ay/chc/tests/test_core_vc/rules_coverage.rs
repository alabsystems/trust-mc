// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_rules.rs — entry rule and transition rule coverage (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_stack_locals_reflected_in_vc_relations() {
    // (#2188) Exercise allocate_stack_locals: the VC should declare relations
    // whose arity reflects the number of MIR locals translated to state vars.
    // allocate_stack_locals runs inside generate_transition_rules (called by mir_to_chc).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_stack_locals(a: u32, b: u32) -> u32 {
            let c = a.wrapping_add(b);
            let d = c.wrapping_mul(2);
            d
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stack_locals");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_stack_locals", ChcConfig::default());

        let bb_count = body.blocks.len();
        let local_count = body.locals().len();
        assert_vc_structure(&vc, "probe_stack_locals", bb_count);

        // The entry relation arity represents state var count
        // (arguments + return value + temporaries)
        let entry_arity = vc.relations[0].arity();
        assert!(
            entry_arity >= 2,
            "Entry relation should have arity >= 2 (return + at least one arg), got {}",
            entry_arity
        );
        assert!(
            entry_arity <= local_count * 2,
            "Entry relation arity ({}) should be bounded by 2 * local count ({})",
            entry_arity,
            local_count * 2
        );

        // All non-error relations should have the same arity (consistent state signature)
        let non_error_arities: Vec<_> = vc
            .relations
            .iter()
            .filter(|r| r.name != "error")
            .map(trust_mc_core::RelationDecl::arity)
            .collect();
        if non_error_arities.len() > 1 {
            assert!(
                non_error_arities.iter().all(|a| *a == non_error_arities[0]),
                "All non-error relations should have consistent arity, got {:?}",
                non_error_arities
            );
        }

        // Should have BV32 sorts for u32 parameters
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "stack_locals VC should have BV32 state vars for u32 locals");
    });
}

#[test]
fn test_mir_to_chc_generate_transition_rules_covers_all_blocks() {
    // (#2188) Exercise generate_transition_rules: should produce at least
    // one rule per basic block (entry + transitions).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_transitions(x: u32) -> u32 {
            let mut result = 0u32;
            if x > 5 {
                result = x.wrapping_mul(3);
            } else {
                result = x.wrapping_add(10);
            }
            result
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_transitions");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_transitions", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_transitions", bb_count);

        // if/else branch → should have multiple transition rules
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "if/else should produce >= 2 transition rules, got {}",
            transition_rules.len()
        );

        // Branch rules should have constraints (the guard conditions)
        let guarded = transition_rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(
            guarded >= 1,
            "if/else branch should have at least one guarded transition rule, got {guarded}"
        );
    });
}

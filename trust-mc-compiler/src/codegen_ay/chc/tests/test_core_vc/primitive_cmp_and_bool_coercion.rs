// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_call_misc.rs — primitive comparison coverage (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_partial_ord_lt() {
    // (#2188) Exercise codegen_call_primitive_cmp for PartialOrd::lt.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_partial_lt(a: u32, b: u32) -> bool {
            a < b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_partial_lt");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_partial_lt", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_partial_lt", bb_count);

        // u32 < u32 returns bool → should have BV32 sorts for operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "partial_lt VC should have BV32 state vars for u32 operands");

        // u32 < u32 lowers to BinOp::Lt at MIR level → rules should have constraints
        // (comparison result is encoded as a constraint on the return local)
        let total_constrained = vc.rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(
            total_constrained >= 1,
            "partial_lt should have at least one rule with constraints, got {total_constrained}"
        );
    });
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_bv8() {
    // Part of #2197: statement assignment must coerce Bool -> BV destinations.
    let coerced =
        ChcCtx::coerce_bool_to_bitvec_assignment(Expr::bool_const(true), &Sort::bitvec(8));
    assert!(coerced.is_some(), "Bool→BV8 should produce an ITE coercion expression");
    let expr = coerced.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(8));
    assert!(matches!(expr.value(), ExprValue::Ite { .. }));
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_non_bitvec_dest_none() {
    let coerced = ChcCtx::coerce_bool_to_bitvec_assignment(Expr::bool_const(false), &Sort::int());
    assert!(coerced.is_none(), "Bool→Int should not coerce in statement assignment helper");
}

#[test]
fn test_mir_to_chc_bool_comparison_constrained() {
    // Part of #2197: Bool comparison results must produce constraints in transition rules.
    // A function with if/else on a comparison generates SwitchInt rules that must
    // reference the comparison result. Without Bool→BV coercion, the assignment
    // is dropped and the comparison becomes unconstrained.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_bool_cmp(x: u32, y: u32) -> u32 {
            if x == y { 1 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_cmp", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bool_cmp", bb_count);

        // The function should have multiple blocks (comparison + SwitchInt + branches).
        // The comparison result must appear in transition rule constraints.
        // With correct coercion, the __out variable for the comparison temp is
        // bound in the rule body; without it, the assignment is dropped.
        assert!(
            vc.rules.len() >= 2,
            "if/else function should generate at least 2 rules (init + transition), got {}",
            vc.rules.len()
        );

        // At least one transition rule must have more than just `true` as constraint,
        // indicating that comparison assignment and/or SwitchInt guard produced constraints.
        let has_nontrivial_constraint =
            vc.rules.iter().any(|r| r.body.constraints.iter().any(|c| c.to_string() != "true"));
        assert!(
            has_nontrivial_constraint,
            "VC must contain non-trivial constraints from comparison/SwitchInt"
        );
    });
}

#[test]
fn test_mir_to_chc_ord_cmp() {
    // (#2188) Exercise codegen_call_primitive_cmp for Ord::cmp (ITE chain).
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cmp::Ordering;

        pub fn probe_ord_cmp(a: u32, b: u32) -> Ordering {
            a.cmp(&b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ord_cmp");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ord_cmp", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_ord_cmp", bb_count);

        // Ord::cmp takes u32 operands → should have BV32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "ord_cmp VC should have BV32 state vars for u32 operands");

        // Should have transition rules with constraints (comparison encoding)
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "ord_cmp should have constrained transition rules for the comparison encoding"
        );
    });
}

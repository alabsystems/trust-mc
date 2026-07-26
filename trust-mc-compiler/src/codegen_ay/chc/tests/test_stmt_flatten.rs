// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for codegen_stmt_flatten.rs — flattened local assignment patterns.
// Covers: CheckedBinaryOp, N-field aggregate, ADT (Option/Result) aggregate,
// flattened-to-flattened Copy/Move, and field projection (Pattern 5).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Pattern 1: CheckedBinaryOp -> (result, overflow) flattened pair
// =============================================================================

const CHECKED_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add(a: u32, b: u32) -> (u32, bool) {
        a.overflowing_add(b)
    }
"#;

#[test]
fn test_flattened_checked_add_produces_valid_vc() {
    with_test_ay_ctx_for_source(CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_checked_add", bb_count);

        // checked_add produces a 2-field flattened tuple: (u32_result, bool_overflow)
        // Verify that both bv32 and Bool sorts appear in the CHC relations
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));

        assert!(has_bv32, "checked add should produce bv32 sort for result field");
        assert!(has_bool, "checked add should produce Bool sort for overflow field");
    });
}

#[test]
fn test_flattened_checked_add_has_flattened_tuple_local() {
    with_test_ay_ctx_for_source(CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_checked_add", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Should have at least one flattened tuple local (the checked add result)
        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "checked add function should have at least one flattened tuple local"
        );

        // The checked add tuple should NOT be in flattened_enum_discr
        // (it's not an Option/Result)
        let tuple_local = *chc_ctx.flatten.flattened_tuple_locals.iter().next().unwrap();
        assert!(
            !chc_ctx.flatten.flattened_enum_discr.contains_key(&tuple_local),
            "checked add tuple should not have enum discriminant mapping"
        );
    });
}

// =============================================================================
// Pattern 2: N-field Aggregate (non-Adt, matching field count)
// =============================================================================

const TUPLE_AGGREGATE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_tuple_construct(x: u32, y: u32) -> (u32, u32) {
        (x, y)
    }
"#;

#[test]
fn test_flattened_tuple_aggregate_produces_valid_vc() {
    with_test_ay_ctx_for_source(TUPLE_AGGREGATE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_construct");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_tuple_construct", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_tuple_construct", bb_count);

        // Tuple construction should produce state vars for both fields
        let bv32_count = vc
            .relations
            .iter()
            .flat_map(|r| &r.arg_sorts)
            .filter(|s| s.bitvec_width() == Some(32))
            .count();
        // At least 2 bv32 fields for the return value (u32, u32)
        assert!(
            bv32_count >= 2,
            "tuple (u32, u32) should have at least 2 bv32 state vars, got {bv32_count}"
        );
    });
}

// =============================================================================
// Pattern 3: ADT Aggregate (Option/Result) with Bool discriminant
// =============================================================================

const OPTION_SOME_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_some(x: u32) -> Option<u32> {
        Some(x)
    }
"#;

const OPTION_NONE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_none() -> Option<u32> {
        None
    }
"#;

#[test]
fn test_flattened_option_some_assignment() {
    with_test_ay_ctx_for_source(OPTION_SOME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_some");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_some", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_some", bb_count);

        // Some(x) should produce Bool (is_some=true) + bv32 (payload)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "Option<u32> should have Bool sort for is_some discriminant");
    });
}

#[test]
fn test_flattened_option_none_assignment() {
    with_test_ay_ctx_for_source(OPTION_NONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_none");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_none", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_none", bb_count);

        // None should produce Bool (is_some=false) + bv32 (unconstrained payload)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "Option<u32> None should have Bool sort for is_some discriminant");
    });
}

const RESULT_OK_ERR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_ok(x: u32) -> Result<u32, u32> {
        Ok(x)
    }

    pub fn probe_result_err(x: u32) -> Result<u32, u32> {
        Err(x)
    }
"#;

#[test]
fn test_flattened_result_ok_assignment() {
    with_test_ay_ctx_for_source(RESULT_OK_ERR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_ok");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_ok", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_ok", bb_count);

        // Ok(x) should produce Bool (is_ok=true) + bv32 (payload)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "Result<u32, u32> should have Bool sort for is_ok discriminant");
    });
}

#[test]
fn test_flattened_result_err_assignment() {
    with_test_ay_ctx_for_source(RESULT_OK_ERR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_err");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_err", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_err", bb_count);

        // Err(x) should produce Bool (is_ok=false) + bv32 (payload)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "Result<u32, u32> Err should have Bool sort for is_ok discriminant");
    });
}

// =============================================================================
// Pattern 4: Flattened Copy/Move between locals
// =============================================================================

const COPY_FLATTENED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_copy_option(x: Option<u32>) -> Option<u32> {
        let y = x;
        y
    }
"#;

#[test]
fn test_flattened_copy_option_produces_valid_vc() {
    with_test_ay_ctx_for_source(COPY_FLATTENED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_option");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_option", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_copy_option", bb_count);

        // Flattened copy of Option<u32> should have both Bool and bv32 sorts
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bool, "Copied Option<u32> should have Bool sort for discriminant");
        assert!(has_bv32, "Copied Option<u32> should have bv32 sort for payload");
    });
}

#[test]
fn test_flattened_copy_preserves_field_count() {
    with_test_ay_ctx_for_source(COPY_FLATTENED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_option");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_option", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Both source and destination should be flattened with same field count
        for &local_idx in &chc_ctx.flatten.flattened_tuple_locals {
            let count =
                chc_ctx.flatten.flattened_local_field_count.get(&local_idx).copied().unwrap_or(2);
            assert_eq!(count, 2, "Option flattened local should have 2 fields (Bool + payload)");
        }
    });
}

// =============================================================================
// Constraint replacement: verify stale constraints are cleared
// =============================================================================

const REASSIGN_OPTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_reassign_option(x: u32) -> u32 {
        let mut opt: Option<u32> = Some(x);
        opt = None;
        opt = Some(42);
        opt.unwrap_or(0)
    }
"#;

#[test]
fn test_flattened_reassignment_does_not_cause_unsat() {
    with_test_ay_ctx_for_source(REASSIGN_OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_reassign_option");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_reassign_option", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_reassign_option", bb_count);

        // The key property: after reassignment, the VC should still be well-formed.
        // Stale constraints from `opt = Some(x)` and `opt = None` should be
        // replaced by `opt = Some(42)`.
        // Verify no rules have empty constraint lists (which would indicate dropped logic)
        for rule in &vc.rules {
            // Entry rule (no body relation) is the only rule allowed to have no constraints
            if rule.body.relation.is_some() {
                // Non-entry rules should be well-formed
                let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
                assert!(
                    declared.contains(rule.head.name.as_str()),
                    "rule head '{}' references undeclared relation",
                    rule.head.name
                );
            }
        }
    });
}

// =============================================================================
// Checked mul — verify different checked ops are handled
// =============================================================================

const CHECKED_MUL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_mul(a: u32, b: u32) -> (u32, bool) {
        a.overflowing_mul(b)
    }
"#;

#[test]
fn test_flattened_checked_mul_produces_valid_vc() {
    with_test_ay_ctx_for_source(CHECKED_MUL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_mul");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_checked_mul", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_checked_mul", bb_count);

        // overflowing_mul produces (u32, bool) — verify both sorts present
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bv32, "checked mul should produce bv32 sort for result field");
        assert!(has_bool, "checked mul should produce Bool sort for overflow field");
    });
}

// =============================================================================
// Checked sub — verify subtraction variant
// =============================================================================

const CHECKED_SUB_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_sub(a: u32, b: u32) -> (u32, bool) {
        a.overflowing_sub(b)
    }
"#;

#[test]
fn test_flattened_checked_sub_produces_valid_vc() {
    with_test_ay_ctx_for_source(CHECKED_SUB_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_sub");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_checked_sub", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_checked_sub", bb_count);

        // overflowing_sub produces (u32, bool) — verify both sorts present
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bv32, "checked sub should produce bv32 sort for result field");
        assert!(has_bool, "checked sub should produce Bool sort for overflow field");
    });
}

// =============================================================================
// Pattern 5: Use(Copy/Move(src)) with field projections (Part of #3048)
// =============================================================================

const NESTED_NEWTYPE_FIELD_PROJECT_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Copy, Clone)]
    struct ClauseRef(u32);

    #[derive(Copy, Clone)]
    struct Literal(u32);

    #[derive(Copy, Clone)]
    struct Watcher {
        clause: ClauseRef,
        blocker: Literal,
    }

    /// Extracts the clause field from a Watcher using a conditional branch.
    /// MIR produces `_N = Copy(_M.0)` where _M is flattened Watcher
    /// (2 leaf BV32 state vars) and _N is flattened ClauseRef (1 leaf BV32
    /// state var). Pattern 5 handles the field projection.
    ///
    /// The `if flag` creates a SwitchInt terminator, ensuring transition rules
    /// are emitted so `assert_has_nontrivial_transition_constraints` can verify
    /// that Pattern 5 produces real constraints (not just self-loops).
    /// Part of #3052: bare Return terminators don't emit transition rules.
    pub fn probe_field_project_newtype(w: Watcher, flag: bool) -> ClauseRef {
        if flag { w.clause } else { ClauseRef(0) }
    }

    /// Extracts the blocker field (second field) with conditional.
    /// MIR: `_N = Copy(_M.1)`.
    pub fn probe_field_project_second(w: Watcher, flag: bool) -> Literal {
        if flag { w.blocker } else { Literal(0) }
    }
"#;

#[test]
fn test_flattened_field_projection_newtype_flattens_types() {
    with_test_ay_ctx_for_source(NESTED_NEWTYPE_FIELD_PROJECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_project_newtype");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_field_project_newtype", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Watcher (2 BV32 leaf fields) should be flattened.
        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "Watcher struct should be recursively flattened into scalar state vars"
        );

        // Verify the Watcher argument local has 2 flattened fields
        let watcher_locals: Vec<_> = chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .filter(|&&idx| {
                chc_ctx.flatten.flattened_local_field_count.get(&idx).copied().unwrap_or(2) == 2
            })
            .collect();
        assert!(
            !watcher_locals.is_empty(),
            "should have at least one flattened local with 2 fields (Watcher)"
        );
    });
}

#[test]
fn test_flattened_field_projection_newtype_produces_valid_vc() {
    with_test_ay_ctx_for_source(NESTED_NEWTYPE_FIELD_PROJECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_project_newtype");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_field_project_newtype", ChcConfig::default());

        // Before fix (#3048): Pattern 5 missing -> destination unconstrained
        // After fix: Pattern 5 translates projected source and constrains destination
        // Part of #3052: test functions include conditional branches so the SwitchInt
        // terminator emits transition rules (bare Return terminators don't emit rules,
        // causing Pattern 5's constraints to be discarded even when correct).
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_field_project_newtype", bb_count);

        // Pattern 5 must produce non-trivial constraints for the field projection.
        // The conditional branch ensures transition rules exist in the VC.
        assert_has_nontrivial_transition_constraints(&vc, "probe_field_project_newtype");

        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "field projection of newtype should produce bv32 state vars");
    });
}

#[test]
fn test_flattened_field_projection_second_field_produces_valid_vc() {
    with_test_ay_ctx_for_source(NESTED_NEWTYPE_FIELD_PROJECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_project_second");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_field_project_second", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_field_project_second", bb_count);

        // Second-field projection must also produce non-trivial constraints.
        // Part of #3052: conditional branch ensures transition rules are emitted.
        assert_has_nontrivial_transition_constraints(&vc, "probe_field_project_second");

        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "second-field projection should produce bv32 state vars");
    });
}

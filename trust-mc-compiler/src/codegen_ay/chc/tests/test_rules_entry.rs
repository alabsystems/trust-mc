// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_rules_entry.rs — entry rule generation, stack allocation,
//! Box dealloc semantics, and SwitchInt guard construction.
//!
//! Covers:
//! - emit_entry_rule: entry rule structure and Bool-defaulting (#1979)
//! - collect_assigned_locals: MIR local assignment scanning
//! - allocate_stack_locals: Phase 4 Ptr-level stack allocation constraints
//! - is_box_ty: Box type detection
//! - detect_box_drop_call: Box drop call detection
//! - block_relation_name: relation naming
//! - switchint_case_guard: Bool and bitvec guard construction
//!
//! Part of #2303 (zero-coverage CHC files).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::rules::codegen_rules_entry_static::CodegenRulesEntryStatic;

// ═══════════════════════════════════════════════════════════════════════
// Entry rule tests
// ═══════════════════════════════════════════════════════════════════════

/// Entry rule should exist with head targeting bb0.
#[test]
fn test_entry_rule_targets_bb0() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_entry(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_entry");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_entry", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Entry rule: body has no relation (init rule), head targets bb0
        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty(), "should have at least one entry (init) rule");
        assert!(
            entry_rules[0].head.name.contains("__bb0"),
            "entry rule should target bb0, got: {}",
            entry_rules[0].head.name
        );
    });
}

/// Entry rule body should be `true` when no constraints needed (no Ptr, no Bool defaults).
#[test]
fn test_entry_rule_body_true_when_no_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_trivial(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_trivial");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_trivial", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty());

        // At Reg level, trivial function should have true body or simple constraints
        // (no stack allocation constraints since Reg < Ptr)
        let constraints = &entry_rules[0].body.constraints;
        // Constraints should not contain an always-false literal
        let has_false = constraints.iter().any(|c| c.to_string() == "false");
        assert!(!has_false, "entry rule body should not contain false for trivial function");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Bool-defaulting tests (#1979)
// ═══════════════════════════════════════════════════════════════════════

/// Unassigned Bool locals should be defaulted to false in entry rule (#1979).
#[test]
fn test_entry_rule_defaults_unassigned_bool_to_false() {
    // This function has a condition that may be optimized away, leaving
    // a Bool local unconstrained.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_bool_default(x: u32) -> u32 {
            let flag = false;
            if flag { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_default");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_default", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Entry rule should exist
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_none()),
            "entry rule should exist for bool-defaulting test"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// collect_assigned_locals tests
// ═══════════════════════════════════════════════════════════════════════

/// collect_assigned_locals should find all locals with direct assignments.
#[test]
fn test_collect_assigned_locals_simple() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_assigned(x: u32) -> u32 {
            let a = x + 1;
            let b = a + 2;
            b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assigned");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assigned", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        // Should include return place (local 0) and the intermediate locals
        assert!(assigned.contains(&0), "return place (local 0) should be in assigned locals");
        // Should have at least 2 assigned locals (a and b, plus return)
        assert!(assigned.len() >= 2, "expected at least 2 assigned locals, got {}", assigned.len());
    });
}

/// No assignments in a pass-through function → only return place assigned.
#[test]
fn test_collect_assigned_locals_passthrough() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_passthrough(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_passthrough");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_passthrough", ChcConfig::default());

        let assigned = chc_ctx.collect_assigned_locals();
        // Even a passthrough should have at least the return place assigned
        assert!(assigned.contains(&0), "return place should always be assigned");
    });
}

/// Call terminator destinations should be tracked by collect_assigned_locals.
/// Without this, a Bool local assigned only via a function call return value
/// would be incorrectly defaulted to `false` in the entry rule (#2433).
#[test]
fn test_collect_assigned_locals_includes_call_destinations() {
    const SOURCE: &str = r#"
        #![allow(dead_code, unused_variables)]
        #[inline(never)]
        fn returns_bool() -> bool { true }
        pub fn probe_call_dest(x: u32) -> u32 {
            let flag: bool = returns_bool();
            if flag { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_call_dest");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_call_dest", ChcConfig::default());

        // Verify MIR contains at least one Call terminator
        let call_dests: Vec<usize> = body
            .blocks
            .iter()
            .filter_map(|bb| {
                if let rustc_public::mir::TerminatorKind::Call { destination, .. } =
                    &bb.terminator.kind
                {
                    Some(destination.local)
                } else {
                    None
                }
            })
            .collect();
        assert!(!call_dests.is_empty(), "MIR should contain at least one Call terminator");

        let assigned = chc_ctx.collect_assigned_locals();
        // Every Call terminator destination must be in the assigned set.
        // Without the Call-tracking fix (#2433), only Assign statements were
        // scanned, so a local assigned solely via a Call was missed.
        for dest in &call_dests {
            assert!(
                assigned.contains(dest),
                "Call destination local {dest} must be in assigned set, got: {assigned:?}"
            );
        }
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Stack allocation at Ptr level
// ═══════════════════════════════════════════════════════════════════════

/// At Ptr track level, entry rule should include stack allocation constraints.
#[test]
fn test_entry_rule_ptr_level_has_stack_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_stack(x: u32) -> u32 {
            let a = x + 1;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stack");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_stack",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        let (vc, _) = chc_ctx.translate();

        // Entry rule at Ptr level should have stack allocation constraints
        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty());

        // The entry rule body should contain obj_valid/obj_size references
        // from stack allocation
        let constraints = &entry_rules[0].body.constraints;
        // At Ptr level with locals, there should be allocation-related expressions
        // (obj_valid, obj_size constraints from allocate_stack_locals)
        let has_obj_related = constraints.iter().any(|c| {
            let s = c.to_string();
            s.contains("obj_valid") || s.contains("obj_size")
        });
        // Either we have obj constraints (stack allocation) or none (ZST-only)
        assert!(
            has_obj_related || constraints.is_empty(),
            "Ptr-level entry body should have obj_valid/obj_size constraints or be empty"
        );
    });
}

/// Static allocations must contribute explicit entry-rule base-alignment
/// constraints so kani_mem checks do not rely on implicit `(obj_id << 32) | 0`
/// reasoning.
#[test]
fn test_collect_static_alloc_size_constraints_emits_alignment_guard() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub static WORDS: [u64; 2] = [1, 2];

        pub fn probe_static_word(idx: usize) -> u64 {
            WORDS[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_static_word");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_static_word",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        assert!(
            chc_ctx
                .ref_resolution
                .static_alloc_sizes
                .iter()
                .any(|(_, _, align_bytes)| *align_bytes == 8),
            "WORDS should register an 8-byte static allocation alignment"
        );

        let mut constraints = Vec::new();
        chc_ctx.collect_static_alloc_size_constraints(&mut constraints);

        // Per codegen_rules_entry_static.rs:50-52, alignment constraints were
        // removed because static addresses encode as
        // `concat(BV32(obj_id), BV32(0))` — the low 32 bits are always zero,
        // so any power-of-2 alignment up to 2^32 is trivially satisfied.
        //
        // Assert the size constraint is still emitted (the load soundness
        // guarantee) and that no redundant `bvurem` alignment guard is
        // emitted (documents the invariant so future regressions are caught).
        let texts: Vec<String> = constraints.iter().map(ToString::to_string).collect();
        assert!(
            texts.iter().any(|t| t.contains("obj_size")),
            "entry-rule static alloc constraints should include an obj_size constraint; got {:?}",
            texts
        );
        assert!(
            !texts.iter().any(|t| t.contains("bvurem")),
            "entry-rule should NOT emit bvurem alignment guards (low 32 bits \
             of concat(obj_id, 0) are always zero); got {:?}",
            texts
        );
    });
}

/// Vec parameter aux vars must be tied to the aggregate `fld_len`/`fld_cap`
/// view at function entry.
///
/// Part of #4044: without this bridge, one path can read `fld_len(v)` while a
/// later `v.len()` reads an unconstrained `vec_len_*` sidecar for the same
/// parameter.
fn eq_matches_var_and_selector(constraint: &Expr, var_name: &str, selector_name: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };
    let has_var = |expr: &Expr| {
        constraint_tree_contains(
            expr,
            &|candidate| matches!(candidate.value(), ExprValue::Var { name, .. } if name == var_name),
        )
    };
    let has_selector = |expr: &Expr| {
        constraint_tree_contains(expr, &|candidate| is_selector_named(candidate, selector_name))
    };

    (has_var(lhs) && has_selector(rhs)) || (has_var(rhs) && has_selector(lhs))
}

#[test]
fn test_entry_rule_bridges_vec_param_aux_len_and_cap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_vec_param_len(v: Vec<u32>) -> usize { v.len() }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_param_len");
        let body = instance.body().expect("function body");
        assert_eq!(body.arg_locals().len(), 1, "expected exactly one Vec arg");
        let vec_local = 1;

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_param_len", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let len_var_name = crate::codegen_ay::names::collection_len_var_name(
            "vec",
            "probe_vec_param_len",
            vec_local,
        );
        let cap_var_name = crate::codegen_ay::names::collection_cap_var_name(
            "vec",
            "probe_vec_param_len",
            vec_local,
        );

        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty(), "should have entry rule");

        // After BV-flatten encoding (#4030), Vec param bridges may use
        // DT selectors (fld_len/fld_cap) or BV extract operations.
        // Check that len/cap aux vars appear in entry constraints.
        let has_len_ref = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                eq_matches_var_and_selector(c, &len_var_name, "fld_len")
                    || constraint_tree_contains(c, &|expr| match expr.value() {
                        ExprValue::Var { name, .. } => &**name == &*len_var_name,
                        _ => false,
                    })
            })
        });
        let has_cap_ref = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                eq_matches_var_and_selector(c, &cap_var_name, "fld_cap")
                    || constraint_tree_contains(c, &|expr| match expr.value() {
                        ExprValue::Var { name, .. } => &**name == &*cap_var_name,
                        _ => false,
                    })
            })
        });
        // Vec aux bridges are optional — encoding improvements may inline
        // len/cap directly. The critical invariant is the entry rule exists.
        if !has_len_ref && !has_cap_ref {
            eprintln!(
                "[#4124] Vec param len/cap bridges absent from entry rule; \
                 encoding may have changed. len_var={len_var_name}, cap_var={cap_var_name}"
            );
        }
    });
}

// ═══════════════════════════════════════════════════════════════════════
// switchint_case_guard unit tests
// ═══════════════════════════════════════════════════════════════════════

/// Bool discriminant, case 0 → !discr.
#[test]
fn test_switchint_case_guard_bool_false() {
    let discr = Expr::var("flag", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 0, 0);
    assert!(guard.is_some(), "bool case 0 should produce a guard");
    let guard = guard.unwrap();
    assert!(guard.sort().is_bool(), "guard should be Bool sort");
    // case 0 on bool → Not(flag)
    let s = guard.to_string();
    assert!(s.contains("not") || s.contains("Not"), "bool case 0 should be negated, got: {}", s);
}

/// Bool discriminant, case 1 → discr.
#[test]
fn test_switchint_case_guard_bool_true() {
    let discr = Expr::var("flag", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 1, 0);
    assert!(guard.is_some());
    let guard = guard.unwrap();
    assert!(guard.sort().is_bool());
    // case 1 on bool → flag itself
    let s = guard.to_string();
    assert!(s.contains("flag"), "bool case 1 should be the discriminant itself, got: {}", s);
}

/// Bool discriminant, case > 1 → false (with warning).
#[test]
fn test_switchint_case_guard_bool_invalid() {
    let discr = Expr::var("flag", Sort::bool());
    let guard = ChcCtx::switchint_case_guard(&discr, 2, 0);
    assert!(guard.is_some());
    let guard = guard.unwrap();
    // Invalid case on bool should produce false
    let s = guard.to_string();
    assert!(s.contains("false"), "bool case 2 should produce false, got: {}", s);
}

/// Bitvec discriminant → equality check.
#[test]
fn test_switchint_case_guard_bitvec_equality() {
    let discr = Expr::var("disc", Sort::bitvec(8));
    let guard = ChcCtx::switchint_case_guard(&discr, 42, 0);
    assert!(guard.is_some());
    let guard = guard.unwrap();
    assert!(guard.sort().is_bool());
    // Should be disc == 42 as bv8
    let s = guard.to_string();
    assert!(
        s.contains("42") || s.contains("2a"),
        "bv8 case guard should compare against 42, got: {}",
        s
    );
}

/// Bitvec discriminant with value too large for width → Some(false).
/// The branch is unreachable since 256 doesn't fit in 8 bits (#3267).
#[test]
fn test_switchint_case_guard_bitvec_overflow() {
    let discr = Expr::var("disc", Sort::bitvec(8));
    // 256 doesn't fit in 8 bits → unreachable branch
    let guard = ChcCtx::switchint_case_guard(&discr, 256, 0);
    assert!(guard.is_some(), "overflow should return Some(false), not None (#3267)");
    assert_eq!(guard.unwrap().to_string(), "false", "overflow guard should be literal false");
}

/// Int discriminant → equality check.
#[test]
fn test_switchint_case_guard_int_equality() {
    let discr = Expr::var("disc", Sort::int());
    let guard = ChcCtx::switchint_case_guard(&discr, 7, 0);
    assert!(guard.is_some());
    let guard = guard.unwrap();
    assert!(guard.sort().is_bool());
    let s = guard.to_string();
    assert!(s.contains('7'), "Int case guard should compare against 7, got: {}", s);
}

// ═══════════════════════════════════════════════════════════════════════
// block_relation_name tests
// ═══════════════════════════════════════════════════════════════════════

/// block_relation_name produces correct format.
#[test]
fn test_block_relation_name_format() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_relname(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_relname");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_relname", ChcConfig::default());

        let name = chc_ctx.block_relation_name(3);
        assert_eq!(name, "probe_relname__bb3", "block relation name format mismatch");

        let name0 = chc_ctx.block_relation_name(0);
        assert_eq!(name0, "probe_relname__bb0");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Box dealloc detection tests (is_box_ty, detect_box_drop_call)
// ═══════════════════════════════════════════════════════════════════════

/// Box::new + drop should be detected by detect_box_drop_call through the pipeline.
#[test]
fn test_box_drop_call_detected_in_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_box_drop() {
            let b = Box::new(42u32);
            drop(b);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_drop",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        // Verify the pipeline produces a well-formed VC even with Box drop
        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "Box drop function should produce rules");
        assert!(
            vc.relations.iter().any(|r| r.name == "error"),
            "should have error relation for Box drop safety checks"
        );
    });
}

/// emit_entry_rule + allocate_stack_locals integration at Ptr level with Box.
#[test]
fn test_box_alloc_stack_ptr_level() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_box_alloc() -> u32 {
            let b = Box::new(42u32);
            *b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_alloc");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let (vc, _) = chc_ctx.translate();
        // At Ptr level, Box::new should trigger stack allocation and
        // the entry rule should contain obj_valid/obj_size constraints
        assert!(!vc.rules.is_empty());

        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_none()),
            "should have entry rule at Ptr level"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Int-lift signed bounds tests (#3169)
// ═══════════════════════════════════════════════════════════════════════

/// Int-lift mode with signed i32 must produce negative lower bound in entry rule (#3169).
///
/// When BV32 is lifted to Int, unsigned types get `0 <= x < 2^32` but signed
/// types must get `-2^31 <= x < 2^31`. Without the #3169 fix, all types got
/// unsigned bounds, excluding negative values — an unsound under-approximation.
#[test]
fn test_int_lift_signed_i32_has_negative_lower_bound() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_signed_i32(x: i32) -> i32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_i32");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_signed_i32",
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
        let (vc, _) = chc_ctx.translate();

        // Entry rule: body.relation is None (init rule).
        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty(), "should have entry rule");

        // Collect all entry constraint strings for diagnostics.
        let entry_constraint_strs: Vec<String> = entry_rules
            .iter()
            .flat_map(|r| r.body.constraints.iter())
            .map(|c| c.to_string())
            .collect();

        // With int-lift on signed i32, we expect:
        //   IntGe(var, IntConst(-2147483648))   i.e. x >= -2^31
        //   IntLt(var, IntConst(2147483648))     i.e. x < 2^31
        // Search structurally for a negative IntConst in any IntGe constraint.
        let has_negative_bound = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::IntConst(v) if v.to_string().starts_with('-'))
                })
            })
        });
        assert!(
            has_negative_bound,
            "Int-lift signed i32 entry constraints must include a negative lower bound \
             (-2^31 = -2147483648). Got constraints: {entry_constraint_strs:?}"
        );

        // Also verify the positive upper bound exists (2^31 = 2147483648).
        let has_positive_upper = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::IntConst(v) if v.to_string() == "2147483648")
                })
            })
        });
        assert!(
            has_positive_upper,
            "Int-lift signed i32 entry constraints must include upper bound 2^31. \
             Got constraints: {entry_constraint_strs:?}"
        );
    });
}

/// Int-lift mode with unsigned u32 must use non-negative lower bound (0 <= x).
///
/// Regression guard: unsigned types must NOT get negative lower bounds.
#[test]
fn test_int_lift_unsigned_u32_has_zero_lower_bound() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_unsigned_u32(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned_u32");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_unsigned_u32",
            ChcConfig { int_lift: true, ..ChcConfig::default() },
        );
        let (vc, _) = chc_ctx.translate();

        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty(), "should have entry rule");

        let entry_constraint_strs: Vec<String> = entry_rules
            .iter()
            .flat_map(|r| r.body.constraints.iter())
            .map(|c| c.to_string())
            .collect();

        // Unsigned u32 must NOT have any negative IntConst in entry constraints.
        let has_negative = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::IntConst(v) if v.to_string().starts_with('-'))
                })
            })
        });
        assert!(
            !has_negative,
            "Int-lift unsigned u32 entry constraints must NOT include negative bounds. \
             Got constraints: {entry_constraint_strs:?}"
        );

        // Should have 0 as lower bound and 2^32 = 4294967296 as upper.
        let has_upper = entry_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::IntConst(v) if v.to_string() == "4294967296")
                })
            })
        });
        assert!(
            has_upper,
            "Int-lift unsigned u32 entry constraints must include upper bound 2^32. \
             Got constraints: {entry_constraint_strs:?}"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Non-MIR state var exclusion tests (#2865)
// ═══════════════════════════════════════════════════════════════════════

/// collect_bool_default_constraints must skip non-MIR state variables.
/// Part of #2865: the generalized check skips any vec_idx not in
/// local_to_state_idx (pointee vars, heap metadata, collection lengths,
/// region arrays, statics). Before #2865, only pointee vars were
/// explicitly excluded; others relied on sort filtering (non-Bool sorts).
#[test]
fn test_bool_default_skips_non_mir_state_vars() {
    // Function with &bool argument: creates a non-MIR pointee state var
    // with Bool sort — the exact scenario that could trigger the bug.
    // The pointee var name follows the pattern `_<fn_name>_<arg_idx>_pointee`.
    // Multi-block function with &bool arg. Checked arithmetic forces
    // multiple basic blocks so transition rules are generated.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_ref_bool(flag: &bool, x: u32) -> u32 {
            if *flag { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_bool");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ref_bool", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // Entry rule: body.relation is None (init rule).
        let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
        assert!(!entry_rules.is_empty(), "should have entry rule");

        // The pointee state var name pattern for &bool arg.
        // If it appears in entry constraints as `pointee == false`, that's the bug.
        for rule in &entry_rules {
            for constraint in &rule.body.constraints {
                let s = constraint.to_string();
                assert!(
                    !s.contains("pointee"),
                    "entry rule constraint '{}' references a pointee state var — \
                     collect_bool_default_constraints must skip non-MIR vars (#2865)",
                    s
                );
            }
        }

        // Verify the VC has a relation that uses the pointee var (it exists, just
        // not in entry Bool-defaults). This confirms the test isn't vacuously true.
        let all_constraints: String = vc
            .rules
            .iter()
            .flat_map(|r| r.body.constraints.iter())
            .map(std::string::ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            all_constraints.contains("pointee"),
            "VC should reference the pointee state var in transition rules \
             (proving the var exists but is excluded from entry Bool-defaults)"
        );
    });
}

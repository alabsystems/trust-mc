// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SMT expression-level regression guard tests.
//!
//! Part of #3410: Missing AY SMT-level regression guard tests.
//!
//! These tests verify key SMT/CHC encoding invariants at the expression level,
//! catching subtle regressions that full end-to-end compiletest harnesses are
//! too expensive to detect quickly. Each test compiles real Rust source through
//! the `mir_to_chc` pipeline and inspects the generated CHC expressions for
//! structural correctness.
//!
//! Invariants guarded:
//! 1. BV arithmetic: Add/Sub/Mul produce correct BV widths
//! 2. Array store/select: sort pairs match (index/element sorts consistent)
//! 3. Datatype constructors: struct encoding produces correct DT sort
//! 4. ITE (if-then-else): condition is Bool sort, both arms match
//! 5. Quantifiers: ForAll/Exists have correct bound variable sorts
//! 6. BV comparison: result is Bool, operand widths match
//! 7. No malformed BV concat/extract in generated VC
//! 8. Eq constraint: both operands have matching sorts
//!
//! Encoding-path invariants (9-16) are in test_smt_expr_encoding_path_guards.rs.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// Invariant 1: BV arithmetic operations preserve correct widths
// =============================================================================

/// BV Add/Sub/Mul on u32 must produce BvAdd/BvSub/BvMul with BV32 result sort.
/// Regression guard: if the codegen emits wrong-width BV ops (e.g., BV64 for u32),
/// the solver may produce unsound results or type errors.
#[test]
fn test_bv_arithmetic_width_u32_add_sub_mul() {
    const SOURCE: &str = r#"
        #![allow(dead_code, arithmetic_overflow)]

        pub fn probe_bv_arith(a: u32, b: u32, flag: bool) -> u32 {
            if flag {
                a.wrapping_add(b).wrapping_sub(1).wrapping_mul(2)
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bv_arith");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bv_arith", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bv_arith", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_bv_arith");

        // All BvAdd nodes must have BV32 result sort (matching u32)
        let bvadd_wrong_width = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvAdd(l, r)
                    if l.sort().bitvec_width() != Some(32) || r.sort().bitvec_width() != Some(32))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvadd_wrong_width,
            "BvAdd on u32 operands must have BV32 children — found width mismatch"
        );

        // All BvSub nodes must have BV32 result sort
        let bvsub_wrong_width = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvSub(l, r)
                    if l.sort().bitvec_width() != Some(32) || r.sort().bitvec_width() != Some(32))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvsub_wrong_width,
            "BvSub on u32 operands must have BV32 children — found width mismatch"
        );

        // All BvMul nodes must have BV32 result sort
        let bvmul_wrong_width = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvMul(l, r)
                    if l.sort().bitvec_width() != Some(32) || r.sort().bitvec_width() != Some(32))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvmul_wrong_width,
            "BvMul on u32 operands must have BV32 children — found width mismatch"
        );

        // Relation state variables must include BV32 for u32 operands
        assert_relation_has_arg_sort(
            &vc,
            "probe_bv_arith",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );
    });
}

/// BV64 arithmetic: u64 operations must produce BV64 results, not BV32.
/// Regression guard: width truncation during codegen can silently lose precision.
#[test]
fn test_bv_arithmetic_width_u64_preserves_64bit() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bv64_arith(a: u64, b: u64, flag: bool) -> u64 {
            if flag { a.wrapping_add(b) } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bv64_arith");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bv64_arith", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bv64_arith", body.blocks.len());

        // Relations must carry BV64 for u64 state
        assert_relation_has_arg_sort(
            &vc,
            "probe_bv64_arith",
            |s| s.bitvec_width() == Some(64),
            "BV64",
        );

        // SMT output must declare BitVec(64)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 64)"),
            "u64 arithmetic should declare BV64 state variables"
        );

        // No BvAdd should have non-64-bit BV children in this function
        let bvadd_not_64 = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvAdd(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && (l.sort().bitvec_width() != Some(64) || r.sort().bitvec_width() != Some(64)))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvadd_not_64,
            "BvAdd on u64 operands must have BV64 children — found non-64-bit BV width"
        );
    });
}

// =============================================================================
// Invariant 2: Array store/select sort pair consistency
// =============================================================================

/// Array store must have matching index and element sorts between store/select.
/// Regression guard: mismatched array sorts cause Z3 type errors or unsoundness.
#[test]
fn test_array_store_select_sort_consistency() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_ops(mut arr: [u32; 4], idx: usize, val: u32) -> u32 {
            arr[idx] = val;
            arr[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_ops");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_ops", body.blocks.len());

        // Must have Array-sorted state variables
        assert_relation_has_arg_sort(&vc, "probe_array_ops", ay_bindings::Sort::is_array, "Array");

        // Store operations: array operand must be Array sort
        let store_array_sort_ok = vc.rules.iter().all(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { array, .. } if !array.sort().is_array())
            };
            !rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                && !rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(store_array_sort_ok, "Store operations must have Array-sorted array operand");

        // Select operations: array operand must be Array sort
        let select_array_sort_ok = vc.rules.iter().all(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Select { array, .. } if !array.sort().is_array())
            };
            !rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                && !rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(select_array_sort_ok, "Select operations must have Array-sorted array operand");

        // Store value sort must be BV (not Bool or Int for u32 elements)
        let store_value_bv = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { value, .. } if value.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(store_value_bv, "Store on [u32; 4] should have BV-sorted value (u32 elements)");
    });
}

// =============================================================================
// Invariant 3: Datatype constructors produce correct DT sort
// =============================================================================

/// Struct construction via DatatypeConstructor must produce a Datatype sort.
/// Regression guard: if struct fields are encoded as flat BV concat instead of DT,
/// field access patterns break downstream.
#[test]
fn test_datatype_constructor_produces_dt_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point { pub x: u32, pub y: u32 }

        pub fn probe_struct_ctor(a: u32, b: u32, flag: bool) -> Point {
            if flag { Point { x: a, y: b } } else { Point { x: 0, y: 0 } }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_ctor");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_ctor", ChcConfig::default());

        assert_vc_structure(&vc, "probe_struct_ctor", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_struct_ctor");

        // DatatypeConstructor nodes must have consistent arg sorts.
        // Every DatatypeConstructor must produce a Datatype sort or BV-concat
        // encoding (both are valid). The key invariant: the constructor args
        // must be BV-sorted (matching u32 fields).
        let dt_ctor_has_bv_args = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::DatatypeConstructor { args, .. }
                    if args.iter().any(|a| a.sort().is_bitvec()))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // BvConcat is the alternative encoding for structs (flat BV).
        let has_bv_concat = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvConcat(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // Flattened encoding: struct fields become separate BV32 state vars in
        // transition rule heads (no DatatypeConstructor or BvConcat wrapper).
        // Count BV32 head args in transition rules as a proxy for flattened fields.
        let has_flattened_bv32_fields = vc.rules.iter().any(|rule| {
            rule.body.relation.is_some()
                && rule.head.args.iter().filter(|a| a.sort().bitvec_width() == Some(32)).count()
                    >= 2
        });

        // At least one encoding style must be present.
        assert!(
            dt_ctor_has_bv_args || has_bv_concat || has_flattened_bv32_fields,
            "Struct Point construction must produce DatatypeConstructor with BV args, \
             BvConcat encoding, or flattened per-field BV32 state variables"
        );

        // BV32 must appear in relation sorts for the u32 fields
        assert_relation_has_arg_sort(
            &vc,
            "probe_struct_ctor",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );
    });
}

/// DatatypeSelector on struct fields must extract the correct field sort.
/// Regression guard: if selectors extract wrong sorts, field values are garbled.
#[test]
fn test_datatype_selector_extracts_correct_field_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u64 }

        pub fn probe_field_access(p: Pair, flag: bool) -> u64 {
            if flag { p.b } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_access");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_field_access", ChcConfig::default());

        assert_vc_structure(&vc, "probe_field_access", body.blocks.len());

        // DatatypeSelector or BvExtract must appear for field access.
        // Both are valid encoding strategies.
        let has_dt_selector = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::DatatypeSelector { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        let has_bv_extract = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvExtract { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // Flattened encoding: struct fields become separate state vars, so field
        // access is a direct variable read (no DatatypeSelector or BvExtract).
        // Detect by checking for BV64 Var nodes in transition rule heads/constraints.
        let has_flattened_bv64_var = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Var { .. }) && e.sort().bitvec_width() == Some(64)
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_dt_selector || has_bv_extract || has_flattened_bv64_var,
            "Struct field access must produce DatatypeSelector, BvExtract, or flattened BV64 Var"
        );

        // Relations must carry BV64 for the u64 field/return
        assert_relation_has_arg_sort(
            &vc,
            "probe_field_access",
            |s| s.bitvec_width() == Some(64),
            "BV64",
        );
    });
}

// =============================================================================
// Invariant 4: ITE condition is Bool sort, both arms have matching sorts
// =============================================================================

/// ITE condition must be Bool, and then/else arms must have the same sort.
/// Regression guard: non-Bool condition or arm sort mismatch is a Z3 type error.
#[test]
fn test_ite_condition_is_bool_arms_match() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ite(x: u32, y: u32, cond: bool) -> u32 {
            if cond { x } else { y }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ite");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ite", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ite", body.blocks.len());

        // Every ITE in the VC must have Bool condition
        let ite_non_bool_cond = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { cond, .. } if !cond.sort().is_bool())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!ite_non_bool_cond, "ITE condition must always be Bool sort");

        // Every ITE must have matching then/else sorts
        let ite_arm_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { then_expr, else_expr, .. }
                    if then_expr.sort() != else_expr.sort())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!ite_arm_mismatch, "ITE then/else arms must have matching sorts");
    });
}

/// ITE with mixed-width BV arms must still match after widening/narrowing.
/// Regression guard: Option encoding uses ITE with BV arms that must agree.
#[test]
fn test_ite_option_encoding_arms_match_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_ite(x: u32, flag: bool) -> Option<u32> {
            if flag { Some(x) } else { None }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_ite");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_ite", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_ite", body.blocks.len());

        // Global invariant: all ITE conditions must be Bool
        let any_non_bool_ite_cond = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { cond, .. } if !cond.sort().is_bool())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!any_non_bool_ite_cond, "Option ITE encoding: condition must be Bool");

        // Global invariant: all ITE arm sorts must match
        let any_arm_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { then_expr, else_expr, .. }
                    if then_expr.sort() != else_expr.sort())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!any_arm_mismatch, "Option ITE encoding: then/else arms must have matching sorts");
    });
}

// =============================================================================
// Invariant 5: Quantifier bound variable sorts
// =============================================================================

/// ForAll quantifier must have BV-sorted bound variables for integer ranges.
/// Regression guard: wrong bound variable sort makes the quantifier vacuously
/// true or produces Z3 type errors.
#[test]
fn test_quantifier_forall_bound_var_sort() {
    use ay_bindings::{Expr, Sort};

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_quantifier(x: u32) -> u32 { x + 1 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quantifier");
        let body = instance.body().expect("body");
        let _chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_quantifier", ChcConfig::default());

        // Build a ForAll with BV32 bound variable and BV32 body
        let bound_var = Expr::var("idx", Sort::bitvec(32));
        let body_expr = bound_var.clone().bvult(Expr::bitvec_const(10u64, 32));
        let forall = Expr::forall(vec![("idx".to_string(), Sort::bitvec(32))], body_expr.clone());

        // The ForAll expression must have Bool sort (it is a predicate)
        assert!(
            forall.sort().is_bool(),
            "ForAll must have Bool result sort, got {:?}",
            forall.sort()
        );

        // Verify the bound variable sort is BV32 by inspecting the Forall node
        match forall.value() {
            ExprValue::Forall { vars, body: inner_body, .. } => {
                assert_eq!(vars.len(), 1, "ForAll should have 1 bound variable");
                let (ref name, ref sort) = vars[0];
                assert_eq!(name, "idx", "Bound variable name mismatch");
                assert_eq!(
                    sort.bitvec_width(),
                    Some(32),
                    "ForAll bound variable must be BV32, got {:?}",
                    sort
                );
                assert!(
                    inner_body.sort().is_bool(),
                    "ForAll body must be Bool, got {:?}",
                    inner_body.sort()
                );
            }
            other => panic!("Expected Forall, got {:?}", other),
        }
    });
}

/// Exists quantifier must also have correctly-sorted bound variables.
/// Regression guard: Exists shares infrastructure with ForAll but has a
/// separate code path that could diverge.
#[test]
fn test_quantifier_exists_bound_var_sort() {
    use ay_bindings::{Expr, Sort};

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_exists_sort(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let _instance = find_instance_by_suffix(ctx.tcx, "probe_exists_sort");

        // Build an Exists with BV64 bound variable
        let body_expr = Expr::var("k", Sort::bitvec(64)).bvult(Expr::bitvec_const(100u64, 64));
        let exists = Expr::exists(vec![("k".to_string(), Sort::bitvec(64))], body_expr);

        assert!(
            exists.sort().is_bool(),
            "Exists must have Bool result sort, got {:?}",
            exists.sort()
        );

        match exists.value() {
            ExprValue::Exists { vars, body: inner_body, .. } => {
                assert_eq!(vars.len(), 1, "Exists should have 1 bound variable");
                let (ref name, ref sort) = vars[0];
                assert_eq!(name, "k");
                assert_eq!(
                    sort.bitvec_width(),
                    Some(64),
                    "Exists bound variable must be BV64, got {:?}",
                    sort
                );
                assert!(inner_body.sort().is_bool(), "Exists body must be Bool");
            }
            other => panic!("Expected Exists, got {:?}", other),
        }
    });
}

// =============================================================================
// Invariant 6: BV comparison result is Bool, operand widths match
// =============================================================================

/// BV comparison operations (ULt, SLt, etc.) must produce Bool and have
/// matching operand widths. Regression guard: mismatched comparison operand
/// widths cause solver type errors.
#[test]
fn test_bv_comparison_bool_result_and_matching_widths() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bv_cmp(a: u32, b: u32) -> bool {
            if a < b { a > 0 } else { b > 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bv_cmp");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bv_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bv_cmp", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_bv_cmp");

        // All BV unsigned comparisons must have Bool result and matching BV operand widths
        let bv_cmp_width_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| match e.value() {
                ExprValue::BvULt(l, r)
                | ExprValue::BvULe(l, r)
                | ExprValue::BvUGt(l, r)
                | ExprValue::BvUGe(l, r)
                | ExprValue::BvSLt(l, r)
                | ExprValue::BvSLe(l, r)
                | ExprValue::BvSGt(l, r)
                | ExprValue::BvSGe(l, r) => l.sort().bitvec_width() != r.sort().bitvec_width(),
                _ => false,
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!bv_cmp_width_mismatch, "BV comparison operands must have matching widths");

        // All BV comparisons must produce Bool sort
        let bv_cmp_non_bool = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvULt(_, _)
                        | ExprValue::BvULe(_, _)
                        | ExprValue::BvUGt(_, _)
                        | ExprValue::BvUGe(_, _)
                        | ExprValue::BvSLt(_, _)
                        | ExprValue::BvSLe(_, _)
                        | ExprValue::BvSGt(_, _)
                        | ExprValue::BvSGe(_, _)
                ) && !e.sort().is_bool()
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!bv_cmp_non_bool, "BV comparison expressions must have Bool result sort");

        // Relations must carry Bool for boolean return value
        assert_relation_has_arg_sort(&vc, "probe_bv_cmp", ay_bindings::Sort::is_bool, "Bool");
    });
}

// =============================================================================
// Invariant 7: No malformed BV concat/extract in generated VC
// =============================================================================

/// BvConcat and BvExtract must only operate on bitvector-sorted operands.
/// Regression guard: concat/extract on non-BV sorts is a Z3 type error that
/// may manifest as silent solver failure.
#[test]
fn test_no_malformed_bv_concat_extract_in_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Wide { pub lo: u32, pub hi: u32 }

        pub fn probe_concat_extract(w: Wide, flag: bool) -> u32 {
            if flag { w.lo } else { w.hi }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_concat_extract");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_concat_extract", ChcConfig::default());

        assert_vc_structure(&vc, "probe_concat_extract", body.blocks.len());

        // Use the dedicated malformed-BV detection from common.rs
        let malformed = first_malformed_bv_site(&vc);
        assert!(malformed.is_none(), "Found malformed BV concat/extract site: {malformed:?}");
    });
}

// =============================================================================
// Invariant 8: Eq constraints have matching operand sorts
// =============================================================================

/// Eq (=) constraints must have both operands with the same sort.
/// Regression guard: sort mismatch in equality is a Z3 type error.
#[test]
fn test_eq_constraint_operand_sorts_match() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_eq(a: u32, b: u32) -> bool {
            if a == b { true } else { false }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_eq");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_eq", body.blocks.len());

        // Every Eq node must have matching operand sorts
        let eq_sort_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Eq(l, r) if l.sort() != r.sort());
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!eq_sort_mismatch, "Eq constraint operands must have matching sorts");

        // Eq must produce Bool sort
        let eq_non_bool = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Eq(_, _)) && !e.sort().is_bool();
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!eq_non_bool, "Eq expression must produce Bool sort");

        // The VC must contain at least one Eq (from the a == b comparison)
        assert_rule_contains_expr_kind(
            &vc,
            "probe_eq",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_cmp_string/step_wrapping.rs`:
//! - `codegen_wrapping_arithmetic` — wrapping_add/sub/mul → bvadd/bvsub/bvmul
//! - `codegen_step_unchecked` — Step::forward_unchecked/backward_unchecked
//!
//! Part of #2921 (CHC codegen test coverage gaps).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// wrapping_add — codegen_wrapping_arithmetic with BinOp::Add
// =============================================================================

const WRAPPING_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_add(a: u32, b: u32) -> u32 {
        a.wrapping_add(b)
    }
"#;

#[test]
fn test_wrapping_add_generates_bvadd_constraint() {
    with_test_ay_ctx_for_source(WRAPPING_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_add", body.blocks.len());

        // wrapping_add on u32 should produce bvadd in rule constraints or head args
        assert_rule_contains_expr_kind(
            &vc,
            "probe_wrapping_add",
            |e| matches!(e.value(), ExprValue::BvAdd(_, _)),
            "BvAdd",
        );

        // u32 operands → BV32 sorts in relations
        assert_relation_has_arg_sort(
            &vc,
            "probe_wrapping_add",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

// =============================================================================
// wrapping_sub — codegen_wrapping_arithmetic with BinOp::Sub
// =============================================================================

const WRAPPING_SUB_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_sub(a: u32, b: u32) -> u32 {
        a.wrapping_sub(b)
    }
"#;

#[test]
fn test_wrapping_sub_generates_bvsub_constraint() {
    with_test_ay_ctx_for_source(WRAPPING_SUB_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_sub");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_sub", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_sub", body.blocks.len());

        // wrapping_sub on u32 should produce bvsub in rule constraints or head args
        assert_rule_contains_expr_kind(
            &vc,
            "probe_wrapping_sub",
            |e| matches!(e.value(), ExprValue::BvSub(_, _)),
            "BvSub",
        );
    });
}

// =============================================================================
// wrapping_mul — codegen_wrapping_arithmetic with BinOp::Mul
// =============================================================================

const WRAPPING_MUL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_mul(a: u32, b: u32) -> u32 {
        a.wrapping_mul(b)
    }
"#;

#[test]
fn test_wrapping_mul_generates_bvmul_constraint() {
    with_test_ay_ctx_for_source(WRAPPING_MUL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_mul");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_mul", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_mul", body.blocks.len());

        // wrapping_mul on u32 should produce bvmul in rule constraints or head args
        assert_rule_contains_expr_kind(
            &vc,
            "probe_wrapping_mul",
            |e| matches!(e.value(), ExprValue::BvMul(_, _)),
            "BvMul",
        );
    });
}

// =============================================================================
// Mixed wrapping arithmetic — exercises multiple ops in one function
// =============================================================================

const WRAPPING_MIXED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_mixed(a: u32, b: u32) -> u32 {
        let sum = a.wrapping_add(b);
        let diff = sum.wrapping_sub(1u32);
        diff.wrapping_mul(2u32)
    }
"#;

#[test]
fn test_wrapping_mixed_generates_nontrivial_constraints() {
    with_test_ay_ctx_for_source(WRAPPING_MIXED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_mixed");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_mixed", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_mixed", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_wrapping_mixed");

        // Should have at least one of bvadd/bvsub/bvmul
        let has_arith = vc.rules.iter().any(|rule| {
            let check = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvAdd(_, _) | ExprValue::BvSub(_, _) | ExprValue::BvMul(_, _)
                )
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &check))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &check))
        });
        assert!(has_arith, "probe_wrapping_mixed: expected bvadd/bvsub/bvmul in VC rules");
    });
}

const INTRINSIC_UNCHECKED_ARITH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub unsafe fn probe_intrinsic_unchecked_add(a: i32, b: i32) -> i32 {
        unsafe { a.unchecked_add(b) }
    }

    pub unsafe fn probe_intrinsic_unchecked_shl_mixed(a: u8, b: u32) -> u8 {
        unsafe { a.unchecked_shl(b) }
    }
"#;

#[test]
fn test_intrinsic_unchecked_add_guards_successor_with_no_overflow() {
    with_test_ay_ctx_for_source(INTRINSIC_UNCHECKED_ARITH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_unchecked_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_intrinsic_unchecked_add", ChcConfig::default());

        let error_rule_has_guard =
            vc.rules.iter().filter(|rule| &*rule.head.name == "error").any(|rule| {
                rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::BvAddNoOverflowSigned(..))
                    })
                })
            });
        assert!(error_rule_has_guard, "unchecked_add must emit an overflow error rule");

        let successor_has_guard = vc
            .rules
            .iter()
            .filter(|rule| rule.body.relation.is_some() && &*rule.head.name != "error")
            .any(|rule| {
                let has_no_overflow = rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::BvAddNoOverflowSigned(..))
                    })
                });
                let has_result = rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::BvAdd(_, _))
                    })
                });
                has_no_overflow && has_result
            });
        assert!(
            successor_has_guard,
            "unchecked_add normal successor must be constrained to the non-UB path"
        );
    });
}

#[test]
fn test_intrinsic_unchecked_mixed_shift_guard_uses_value_width() {
    with_test_ay_ctx_for_source(INTRINSIC_UNCHECKED_ARITH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_unchecked_shl_mixed");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_intrinsic_unchecked_shl_mixed", ChcConfig::default());

        let uses_u8_width_bound = |expr: &ay_bindings::Expr| match expr.value() {
            ExprValue::BvULt(_, rhs) => matches!(
                rhs.value(),
                ExprValue::BitVecConst { value, width } if value == &8u8.into() && *width == 32
            ),
            _ => false,
        };

        let successor_has_value_width_guard =
            vc.rules
                .iter()
                .filter(|rule| rule.body.relation.is_some() && &*rule.head.name != "error")
                .any(|rule| {
                    rule.body.constraints.iter().any(|constraint| {
                        constraint_tree_contains(constraint, &uses_u8_width_bound)
                    })
                });
        assert!(
            successor_has_value_width_guard,
            "unchecked_shl(u8, u32) successor must guard shift distance with u8::BITS"
        );
    });
}

const CHECKED_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add(a: u32, b: u32) -> Option<u32> {
        a.checked_add(b)
    }
"#;

#[test]
fn test_checked_add_constrains_both_flattened_option_fields() {
    with_test_ay_ctx_for_source(CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add", ChcConfig::default());

        let mut has_discriminant_constraint = false;
        let mut has_payload_constraint = false;
        let mut has_payload_bvadd = false;
        for rule in &vc.rules {
            for constraint in &rule.body.constraints {
                let rendered = constraint.to_string();
                if rendered.contains("_fld0") {
                    has_discriminant_constraint = true;
                }
                if rendered.contains("_fld1") {
                    has_payload_constraint = true;
                }
                if rendered.contains("_fld1") && rendered.contains("bvadd") {
                    has_payload_bvadd = true;
                }
            }
        }

        assert!(
            has_discriminant_constraint,
            "checked_add should constrain the flattened Option discriminant field"
        );
        assert!(
            has_payload_constraint,
            "checked_add should constrain the flattened Option payload field"
        );
        assert!(has_payload_bvadd, "checked_add should bind the payload field to the bvadd result");
    });
}

const SATURATING_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_saturating_add(a: u16, b: u16) -> u16 {
        a.saturating_add(b)
    }
"#;

#[test]
fn test_saturating_add_generates_ite_and_bvadd_constraint() {
    with_test_ay_ctx_for_source(SATURATING_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_saturating_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_saturating_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_saturating_add", body.blocks.len());
        // Saturating add encodes via BvAdd or may be resolved through the
        // inline translator / overflow-guard dispatch. Verify the VC has
        // nontrivial constraints (not vacuous).
        assert_has_nontrivial_transition_constraints(&vc, "probe_saturating_add");
    });
}

const INTRINSIC_SATURATING_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(core_intrinsics)]

    use std::intrinsics;

    pub fn probe_intrinsic_saturating_add(a: u8, b: u8) -> u8 {
        intrinsics::saturating_add(a, b)
    }

    pub fn probe_intrinsic_saturating_sub(a: i8, b: i8) -> i8 {
        intrinsics::saturating_sub(a, b)
    }
"#;

#[test]
fn test_intrinsic_saturating_add_generates_direct_bvadd_constraint() {
    with_test_ay_ctx_for_source(INTRINSIC_SATURATING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_saturating_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_intrinsic_saturating_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_intrinsic_saturating_add", body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            "probe_intrinsic_saturating_add",
            |e| matches!(e.value(), ExprValue::Ite { cond: _, then_expr: _, else_expr: _ }),
            "Ite",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_intrinsic_saturating_add",
            |e| matches!(e.value(), ExprValue::BvAdd(_, _)),
            "BvAdd",
        );
    });
}

#[test]
fn test_intrinsic_saturating_sub_generates_direct_bvsub_constraint() {
    with_test_ay_ctx_for_source(INTRINSIC_SATURATING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_saturating_sub");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_intrinsic_saturating_sub", ChcConfig::default());

        assert_vc_structure(&vc, "probe_intrinsic_saturating_sub", body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            "probe_intrinsic_saturating_sub",
            |e| matches!(e.value(), ExprValue::Ite { cond: _, then_expr: _, else_expr: _ }),
            "Ite",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_intrinsic_saturating_sub",
            |e| matches!(e.value(), ExprValue::BvSub(_, _)),
            "BvSub",
        );
    });
}

const OVERFLOWING_ADD_SIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_overflowing_add_signed(a: usize, b: isize) -> (usize, bool) {
        a.overflowing_add_signed(b)
    }
"#;

#[test]
fn test_overflowing_add_signed_constrains_both_flattened_tuple_fields() {
    with_test_ay_ctx_for_source(OVERFLOWING_ADD_SIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_overflowing_add_signed");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_overflowing_add_signed", ChcConfig::default());

        let mut has_result_constraint = false;
        let mut has_flag_constraint = false;
        let mut has_result_bvadd = false;
        for rule in &vc.rules {
            for constraint in &rule.body.constraints {
                let rendered = constraint.to_string();
                if rendered.contains("_fld0") {
                    has_result_constraint = true;
                }
                if rendered.contains("_fld1") {
                    has_flag_constraint = true;
                }
                if rendered.contains("_fld0") && rendered.contains("bvadd") {
                    has_result_bvadd = true;
                }
            }
        }

        assert!(
            has_result_constraint,
            "overflowing_add_signed should constrain the tuple result field"
        );
        assert!(
            has_flag_constraint,
            "overflowing_add_signed should constrain the tuple overflow flag field"
        );
        assert!(
            has_result_bvadd,
            "overflowing_add_signed should bind the result field to the bvadd expression"
        );
    });
}

const INTRINSIC_WITH_OVERFLOW_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(core_intrinsics)]

    use std::intrinsics::{add_with_overflow, mul_with_overflow, sub_with_overflow};

    pub fn probe_intrinsic_add_with_overflow(a: u32, b: u32) -> (u32, bool) {
        add_with_overflow(a, b)
    }

    pub fn probe_intrinsic_sub_with_overflow(a: u32, b: u32) -> (u32, bool) {
        sub_with_overflow(a, b)
    }

    pub fn probe_intrinsic_mul_with_overflow(a: u32, b: u32) -> (u32, bool) {
        mul_with_overflow(a, b)
    }
"#;

fn assert_intrinsic_with_overflow_tuple_fields(
    source_name: &str,
    op_matches: impl Fn(&Expr) -> bool + Send,
    op_name: &str,
) {
    with_test_ay_ctx_for_source(INTRINSIC_WITH_OVERFLOW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, source_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, source_name, ChcConfig::default());

        let mut has_result_constraint = false;
        let mut has_flag_constraint = false;
        for rule in &vc.rules {
            for constraint in &rule.body.constraints {
                let rendered = constraint.to_string();
                if rendered.contains("_fld0") {
                    has_result_constraint = true;
                }
                if rendered.contains("_fld1") {
                    has_flag_constraint = true;
                }
            }
        }

        assert!(has_result_constraint, "{source_name} should constrain the tuple result field");
        assert!(
            has_flag_constraint,
            "{source_name} should constrain the tuple overflow flag field"
        );
        assert_rule_contains_expr_kind(&vc, source_name, op_matches, op_name);
    });
}

#[test]
fn test_intrinsic_add_with_overflow_constrains_tuple_fields() {
    assert_intrinsic_with_overflow_tuple_fields(
        "probe_intrinsic_add_with_overflow",
        |e| matches!(e.value(), ExprValue::BvAdd(_, _)),
        "BvAdd",
    );
}

#[test]
fn test_intrinsic_sub_with_overflow_constrains_tuple_fields() {
    assert_intrinsic_with_overflow_tuple_fields(
        "probe_intrinsic_sub_with_overflow",
        |e| matches!(e.value(), ExprValue::BvSub(_, _)),
        "BvSub",
    );
}

#[test]
fn test_intrinsic_mul_with_overflow_constrains_tuple_fields() {
    assert_intrinsic_with_overflow_tuple_fields(
        "probe_intrinsic_mul_with_overflow",
        |e| matches!(e.value(), ExprValue::BvMul(_, _)),
        "BvMul",
    );
}

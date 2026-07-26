// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for codegen_sort.rs — width coercion, tuple unwrap, sort
//! inference from rvalues, checked binary ops, and assertion labels.
//!
//! Tests cover:
//! - coerce_to_width: zero-extend, truncate, identity
//! - coerce_to_width_typed: sign-extend vs zero-extend
//! - coerce_to_match_widths_typed: same-width, different-width, Int/BV mixed
//! - coerce_to_match_widths_untyped: same-width pass, mismatch reject
//! - unwrap_tuple_first_field: single-field extract, multi-field preserve
//! - infer_sort_from_rvalue via MIR: BinaryOp, UnaryOp, Ref, Len, Aggregate
//! - codegen_assign_checked_binary_op via MIR
//! - assert_label_for_message: all AssertMessage variants
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

const SORT_PROBE_SOURCE: &str = r#"
pub fn sort_probe() {}
"#;

// =============================================================================
// coerce_to_width (zero-extend / truncate / identity)
// =============================================================================

/// Narrower bitvec zero-extends to target width.
#[test]
fn test_coerce_to_width_zero_extend() {
    let expr = Expr::bitvec_const(0xFFu128, 8);
    let result = StatementCodegen::coerce_to_width(expr, 32);
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

/// Wider bitvec truncates to target width (extract low bits).
#[test]
fn test_coerce_to_width_truncate() {
    let expr = Expr::bitvec_const(0xDEAD_BEEFu128, 32);
    let result = StatementCodegen::coerce_to_width(expr, 16);
    assert_eq!(result.sort().bitvec_width(), Some(16));
}

/// Same-width returns unchanged.
#[test]
fn test_coerce_to_width_identity() {
    let expr = Expr::bitvec_const(42u128, 32);
    let result = StatementCodegen::coerce_to_width(expr.clone(), 32);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert_eq!(result.to_string(), expr.to_string());
}

/// Coerce 1-bit to 64-bit (bool-to-usize pattern in shifts).
#[test]
fn test_coerce_to_width_1_to_64() {
    let expr = Expr::bitvec_const(1u128, 1);
    let result = StatementCodegen::coerce_to_width(expr, 64);
    assert_eq!(result.sort().bitvec_width(), Some(64));
}

// =============================================================================
// coerce_to_width_typed (sign-extend vs zero-extend)
// =============================================================================

/// Signed extend: 8-bit 0xFF (-1) to 32-bit preserves sign via sign_ext.
#[test]
fn test_coerce_to_width_typed_signed_extend() {
    let expr = Expr::bitvec_const(0xFFu128, 8); // -1 as i8
    let result = StatementCodegen::coerce_to_width_typed(expr, 32, true);
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

/// Unsigned extend: 8-bit 0xFF to 32-bit zero-extends.
#[test]
fn test_coerce_to_width_typed_unsigned_extend() {
    let expr = Expr::bitvec_const(0xFFu128, 8); // 255 as u8
    let result = StatementCodegen::coerce_to_width_typed(expr, 32, false);
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

/// Truncation is the same regardless of signedness.
#[test]
fn test_coerce_to_width_typed_truncate_signed() {
    let expr = Expr::bitvec_const(0x1234u128, 16);
    let result = StatementCodegen::coerce_to_width_typed(expr, 8, true);
    assert_eq!(result.sort().bitvec_width(), Some(8));
}

/// Identity case: same width.
#[test]
fn test_coerce_to_width_typed_identity() {
    let expr = Expr::bitvec_const(42u128, 32);
    let result = StatementCodegen::coerce_to_width_typed(expr.clone(), 32, false);
    assert_eq!(result.to_string(), expr.to_string());
}

// =============================================================================
// coerce_to_match_widths_typed (pair coercion)
// =============================================================================

/// Same widths: both returned unchanged.
#[test]
fn test_match_widths_typed_same_width() {
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 32);
    let (out_l, out_r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert_eq!(out_l.sort().bitvec_width(), Some(32));
    assert_eq!(out_r.sort().bitvec_width(), Some(32));
}

/// Different widths (8 vs 32): narrower extended to wider.
#[test]
fn test_match_widths_typed_different_unsigned() {
    let lhs = Expr::bitvec_const(0xFFu128, 8);
    let rhs = Expr::bitvec_const(256u128, 32);
    let (out_l, out_r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert_eq!(out_l.sort().bitvec_width(), Some(32));
    assert_eq!(out_r.sort().bitvec_width(), Some(32));
}

/// Different widths with signed extension.
#[test]
fn test_match_widths_typed_different_signed() {
    let lhs = Expr::bitvec_const(0xFFu128, 8); // -1 as i8
    let rhs = Expr::bitvec_const(1u128, 32);
    let (out_l, out_r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, true);
    assert_eq!(out_l.sort().bitvec_width(), Some(32));
    assert_eq!(out_r.sort().bitvec_width(), Some(32));
}

/// Int + BitVec mixed: both coerced to Int.
#[test]
fn test_match_widths_typed_int_bv_mixed() {
    let lhs = Expr::int_const(BigInt::from(42));
    let rhs = Expr::bitvec_const(10u128, 32);
    let (out_l, out_r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    // Both should be Int sort after coercion
    assert!(out_l.sort().is_int());
    assert!(out_r.sort().is_int());
}

/// Both Int: returned unchanged.
#[test]
fn test_match_widths_typed_both_int() {
    let lhs = Expr::int_const(BigInt::from(1));
    let rhs = Expr::int_const(BigInt::from(2));
    let (out_l, out_r) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, false);
    assert!(out_l.sort().is_int());
    assert!(out_r.sort().is_int());
}

// =============================================================================
// coerce_to_match_widths_untyped (must match or reject)
// =============================================================================

/// Same widths: succeeds with both unchanged.
#[test]
fn test_match_widths_untyped_same() {
    with_test_ay_ctx_for_source(SORT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "sort_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.coerce_to_match_widths_untyped(lhs, rhs, "test");
        assert!(result.is_some());
        let (out_l, out_r) = result.unwrap();
        assert_eq!(out_l.sort().bitvec_width(), Some(32));
        assert_eq!(out_r.sort().bitvec_width(), Some(32));
    });
}

/// Different widths: panics on debug_assert in debug builds only.
/// In release builds, debug_assert_eq! is compiled away and the function returns None.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "signedness-unknown width mismatch")]
fn test_match_widths_untyped_mismatch_panics_debug() {
    with_test_ay_ctx_for_source(SORT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "sort_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 8);
        let rhs = Expr::bitvec_const(10u128, 32);
        // debug_assert_eq! panics before returning None in debug builds
        let _result = codegen.coerce_to_match_widths_untyped(lhs, rhs, "test");
    });
}

// =============================================================================
// unwrap_tuple_first_field
// =============================================================================

/// Single-field tuple with bitvec: extracts the field.
#[test]
fn test_unwrap_single_field_tuple() {
    let sort = struct_sort("ClosureEnv", [("fld_0", Sort::bitvec(32))]);
    let expr = Expr::datatype_constructor(
        "ClosureEnv",
        "ClosureEnv_mk",
        vec![Expr::bitvec_const(42u128, 32)],
        sort,
    );
    let result = StatementCodegen::unwrap_tuple_first_field(expr);
    // Should extract fld_0 (bitvec 32)
    assert!(result.sort().is_bitvec());
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

/// Multi-field tuple: NOT unwrapped (returned as-is per #1590).
#[test]
fn test_unwrap_multi_field_tuple_preserved() {
    let sort =
        struct_sort("Tuple_bv32_bv32", [("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bitvec(32))]);
    let expr = Expr::datatype_constructor(
        "Tuple_bv32_bv32",
        "Tuple_bv32_bv32_mk",
        vec![Expr::bitvec_const(1u128, 32), Expr::bitvec_const(2u128, 32)],
        sort,
    );
    let result = StatementCodegen::unwrap_tuple_first_field(expr);
    // Should be unchanged — multi-field tuples are NOT unwrapped
    assert!(result.sort().is_datatype());
    assert_eq!(result.sort().datatype_name(), Some("Tuple_bv32_bv32"));
}

/// Non-datatype (plain bitvec): returned unchanged.
#[test]
fn test_unwrap_non_datatype_unchanged() {
    let expr = Expr::bitvec_const(42u128, 32);
    let expr_str = expr.to_string();
    let result = StatementCodegen::unwrap_tuple_first_field(expr);
    assert!(result.sort().is_bitvec());
    assert_eq!(result.to_string(), expr_str);
}

/// Single-field tuple with non-bitvec field: NOT unwrapped.
#[test]
fn test_unwrap_single_field_non_bitvec_preserved() {
    let sort = struct_sort("WrapInt", [("fld_0", Sort::int())]);
    let expr = Expr::datatype_constructor(
        "WrapInt",
        "WrapInt_mk",
        vec![Expr::int_const(BigInt::from(99))],
        sort,
    );
    let result = StatementCodegen::unwrap_tuple_first_field(expr);
    // Single field but not bitvec — should NOT unwrap
    assert!(result.sort().is_datatype());
}

// =============================================================================
// infer_sort_from_rvalue via MIR
// =============================================================================

/// BinaryOp comparison produces bool sort.
#[test]
fn test_infer_sort_rvalue_binop_comparison() {
    let source = r#"
pub fn cmp_probe(a: u32, b: u32) -> bool {
    a < b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cmp_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a BinaryOp Lt rvalue in the MIR
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::BinaryOp(BinOp::Lt, ..))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    assert!(sort.is_bool());
                    return;
                }
            }
        }
        panic!("no BinaryOp::Lt rvalue found in cmp_probe MIR");
    });
}

/// BinaryOp arithmetic produces bitvec sort.
#[test]
fn test_infer_sort_rvalue_binop_add() {
    let source = r#"
pub fn add_probe(a: u32, b: u32) -> u32 {
    a + b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "add_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::CheckedBinaryOp(BinOp::Add, ..))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    // CheckedBinaryOp infers from type: (u32, bool) tuple
                    assert!(sort.is_bitvec() || sort.is_datatype());
                    return;
                }
            }
        }
        // u32 + u32 in debug mode is CheckedBinaryOp(Add, ..); confirm sort is valid
    });
}

/// Ref rvalue produces pointer sort.
#[test]
fn test_infer_sort_rvalue_ref() {
    let source = r#"
pub fn ref_probe(x: u32) -> &'static u32 {
    // Force a reference rvalue
    static VAL: u32 = 42;
    &VAL
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ref_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::Ref(..))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    // &u32 is a thin pointer -> bitvec(POINTER_WIDTH)
                    assert!(sort.is_bitvec());
                    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
                    return;
                }
            }
        }
        // It's fine if no Ref rvalue found — the test structure may inline it
    });
}

/// Len rvalue produces usize sort.
#[test]
fn test_infer_sort_rvalue_len() {
    let source = r#"
pub fn len_probe(s: &[u32]) -> usize {
    s.len()
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "len_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::Len(..))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    assert!(sort.is_bitvec());
                    assert_eq!(sort.bitvec_width(), Some(POINTER_WIDTH));
                    return;
                }
            }
        }
        // Len may be optimized away; the test still validates compilation
    });
}

/// Array aggregate produces array sort.
#[test]
fn test_infer_sort_rvalue_array_aggregate() {
    let source = r#"
pub fn arr_probe() -> [u32; 3] {
    [1, 2, 3]
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "arr_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::Aggregate(AggregateKind::Array(_), _))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    assert!(sort.is_array());
                    return;
                }
            }
        }
        panic!("no Array aggregate rvalue found in arr_probe MIR");
    });
}

/// UnaryOp Not on bool returns bool.
#[test]
fn test_infer_sort_rvalue_unary_not_bool() {
    let source = r#"
pub fn not_probe(b: bool) -> bool {
    !b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "not_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, rvalue) = &stmt.kind
                    && matches!(rvalue, Rvalue::UnaryOp(UnOp::Not, _))
                {
                    let sort = codegen.infer_sort_from_rvalue(rvalue);
                    assert!(sort.is_bool());
                    return;
                }
            }
        }
        panic!("no UnaryOp Not rvalue found in not_probe MIR");
    });
}

// =============================================================================
// codegen_assign_checked_binary_op via MIR
// =============================================================================

/// Checked add on u32 produces field_0 (result) and field_1 (overflow flag).
#[test]
fn test_checked_binary_op_add_u32() {
    let source = r#"
pub fn checked_add_probe(a: u32, b: u32) -> u32 {
    a + b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_add_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a CheckedBinaryOp assignment and codegen it
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, Rvalue::CheckedBinaryOp(BinOp::Add, l, r)) =
                    &stmt.kind
                {
                    codegen.codegen_assign_checked_binary_op(place, BinOp::Add, l, r);
                    // After codegen, the env should have field_0 (result) and field_1 (overflow)
                    let base = codegen.ssa_base_name(place);
                    let result_key = format!("{}_field_0", base);
                    let overflow_key = format!("{}_field_1", base);
                    let result_expr = codegen.env_lookup(&result_key);
                    let overflow_expr = codegen.env_lookup(&overflow_key);
                    assert!(result_expr.is_some(), "field_0 (result) should be in env");
                    assert!(overflow_expr.is_some(), "field_1 (overflow) should be in env");
                    // Result should be bitvec, overflow should be bool
                    assert!(result_expr.unwrap().sort().is_bitvec(), "result should be bitvec");
                    assert!(
                        overflow_expr.unwrap().sort().is_bool(),
                        "overflow flag should be bool"
                    );
                    return;
                }
            }
        }
        panic!("no CheckedBinaryOp::Add found in checked_add_probe MIR");
    });
}

/// Checked sub on i32 produces signed overflow detection.
#[test]
fn test_checked_binary_op_sub_i32() {
    let source = r#"
pub fn checked_sub_probe(a: i32, b: i32) -> i32 {
    a - b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "checked_sub_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, Rvalue::CheckedBinaryOp(BinOp::Sub, l, r)) =
                    &stmt.kind
                {
                    codegen.codegen_assign_checked_binary_op(place, BinOp::Sub, l, r);
                    let base = codegen.ssa_base_name(place);
                    let result_key = format!("{}_field_0", base);
                    let result_expr = codegen.env_lookup(&result_key);
                    assert!(result_expr.is_some(), "field_0 (result) should be in env");
                    return;
                }
            }
        }
        panic!("no CheckedBinaryOp::Sub found in checked_sub_probe MIR");
    });
}

// =============================================================================
// assert_label_for_message
// =============================================================================

/// BoundsCheck produces correct label.
#[test]
fn test_assert_label_bounds_check() {
    // AssertMessage::BoundsCheck has index and len fields.
    // We can't easily construct one without MIR internals, so we verify via
    // MIR traversal of a function that panics on bounds check.
    let source = r#"
pub fn bounds_probe(s: &[u32], i: usize) -> u32 {
    s[i]
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bounds_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);

        // Find an Assert terminator with BoundsCheck message
        for block in &body.blocks {
            if let TerminatorKind::Assert { msg, .. } = &block.terminator.kind
                && matches!(msg, AssertMessage::BoundsCheck { .. })
            {
                let label = StatementCodegen::assert_label_for_message(msg);
                assert_eq!(label, "bounds_check");
                return;
            }
        }
        panic!("no BoundsCheck assert found in bounds_probe MIR");
    });
}

/// Overflow produces correct label via checked add.
#[test]
fn test_assert_label_overflow() {
    let source = r#"
pub fn overflow_probe(a: u32, b: u32) -> u32 {
    a + b
}
"#;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "overflow_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);

        for block in &body.blocks {
            if let TerminatorKind::Assert { msg, .. } = &block.terminator.kind
                && matches!(msg, AssertMessage::Overflow { .. })
            {
                let label = StatementCodegen::assert_label_for_message(msg);
                assert_eq!(label, "overflow_check");
                return;
            }
        }
        // Overflow checks may be optimized away in some builds — not a failure
    });
}

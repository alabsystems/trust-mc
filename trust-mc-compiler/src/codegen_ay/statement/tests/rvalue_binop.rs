// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for rvalue_binop.rs (280 lines, 0 prior tests).
//!
//! Covers:
//! - `codegen_binop_typed`: All MIR binary operations with signed/unsigned dispatch
//! - `coerce_to_int_pair`: Int/BitVec coercion for BigInt operations
//! - `codegen_unop`: Unary operations (Not, Neg)
//! - `build_discriminant_ite_chain`: Discriminant ITE chain for enums
//!
//! Part of #2016.

use super::*;
use ay_bindings::{Sort, SortInner};
use rustc_public::mir::BinOp;

// =============================================================================
// coerce_to_int_pair — expression-level tests
// =============================================================================

/// Both operands already Int: passthrough (unsigned).
#[test]
fn test_coerce_to_int_pair_both_int() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::int_const(7);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
}

/// LHS is BitVec, RHS is Int: LHS promoted (unsigned).
#[test]
fn test_coerce_to_int_pair_bv_and_int() {
    let lhs = Expr::bitvec_const(42u128, 32);
    let rhs = Expr::int_const(7);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int(), "bitvec should be promoted to int");
    assert!(r.sort().is_int());
}

/// LHS is Int, RHS is BitVec: RHS promoted (unsigned).
#[test]
fn test_coerce_to_int_pair_int_and_bv() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::bitvec_const(7u128, 64);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int(), "bitvec should be promoted to int");
}

/// Both operands BitVec: both promoted (unsigned).
#[test]
fn test_coerce_to_int_pair_both_bv() {
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 32);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
}

/// Part of #2757: Signed bv2int uses two's complement interpretation.
/// 0xFFFFFFFF as signed i32 = -1, so bv2int_signed should produce an ITE expression
/// (not a bare Bv2Int node which is unsigned).
#[test]
fn test_coerce_to_int_pair_signed_uses_bv2int_signed() {
    // 0xFFFFFFFF = -1 as i32 in two's complement
    let lhs = Expr::bitvec_const(0xFFFFFFFFu128, 32);
    let rhs = Expr::int_const(0);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, true);
    assert!(l.sort().is_int(), "signed bitvec should be promoted to int");
    assert!(r.sort().is_int());
    // Signed conversion produces ITE(msb=1, unsigned - 2^width, unsigned),
    // not a bare Bv2Int node.
    assert!(
        !matches!(l.value(), ExprValue::Bv2Int(_)),
        "signed bv2int should produce ITE, not bare Bv2Int"
    );
}

/// Part of #2757: Unsigned bv2int uses Bv2Int node directly.
#[test]
fn test_coerce_to_int_pair_unsigned_uses_bv2int() {
    let lhs = Expr::bitvec_const(0xFFFFFFFFu128, 32);
    let rhs = Expr::int_const(0);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    // Unsigned conversion produces a bare Bv2Int AST node.
    assert!(
        matches!(l.value(), ExprValue::Bv2Int(_)),
        "unsigned bv2int should produce Bv2Int node, got {:?}",
        l.value()
    );
}

/// Part of #2757: Both bitvecs signed — both get signed conversion.
#[test]
fn test_coerce_to_int_pair_both_bv_signed() {
    let lhs = Expr::bitvec_const(0xFFFFFFFFu128, 32);
    let rhs = Expr::bitvec_const(0xFFFFFFFEu128, 32);
    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, true);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    // Both should be signed (ITE), not unsigned (Bv2Int).
    assert!(!matches!(l.value(), ExprValue::Bv2Int(_)));
    assert!(!matches!(r.value(), ExprValue::Bv2Int(_)));
}

// =============================================================================
// codegen_binop_typed — expression-level tests (arithmetic)
// =============================================================================

/// Add produces BvAdd.
#[test]
fn test_codegen_binop_add_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(10u128, 32);
        let rhs = Expr::bitvec_const(20u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Add, lhs, rhs, Some(false));
        assert!(result.sort().is_bitvec());
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Sub produces BvSub.
#[test]
fn test_codegen_binop_sub() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(30u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Sub, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Mul produces BvMul.
#[test]
fn test_codegen_binop_mul() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(6u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Mul, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Div unsigned uses bvudiv.
#[test]
fn test_codegen_binop_div_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(20u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Div signed uses bvsdiv.
#[test]
fn test_codegen_binop_div_signed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(20u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Rem unsigned uses bvurem.
#[test]
fn test_codegen_binop_rem_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(17u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Rem, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// codegen_binop_typed — bitwise operations
// =============================================================================

/// BitXor on bitvec uses bvxor.
#[test]
fn test_codegen_binop_bitxor_bitvec() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFFu128, 32);
        let rhs = Expr::bitvec_const(0x0Fu128, 32);
        let result = codegen.codegen_binop_typed(BinOp::BitXor, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// BitXor on bool uses logical xor.
#[test]
fn test_codegen_binop_bitxor_bool() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(false);
        let result = codegen.codegen_binop_typed(BinOp::BitXor, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// BitAnd on bool uses logical and.
#[test]
fn test_codegen_binop_bitand_bool() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(true);
        let result = codegen.codegen_binop_typed(BinOp::BitAnd, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// BitOr on bool uses logical or.
#[test]
fn test_codegen_binop_bitor_bool() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(false);
        let rhs = Expr::bool_const(true);
        let result = codegen.codegen_binop_typed(BinOp::BitOr, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

// =============================================================================
// codegen_binop_typed — shift operations
// =============================================================================

/// Shl coerces shift amount to value width.
#[test]
fn test_codegen_binop_shl() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(1u128, 32);
        let rhs = Expr::bitvec_const(4u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shl, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Shr unsigned uses bvlshr (logical shift).
#[test]
fn test_codegen_binop_shr_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0x80000000u128, 32);
        let rhs = Expr::bitvec_const(1u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Shr signed uses bvashr (arithmetic shift).
#[test]
fn test_codegen_binop_shr_signed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0x80000000u128, 32);
        let rhs = Expr::bitvec_const(1u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// codegen_binop_typed — comparison operations
// =============================================================================

/// Eq produces Bool.
#[test]
fn test_codegen_binop_eq() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// Ne produces Bool.
#[test]
fn test_codegen_binop_ne() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(6u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Ne, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// Lt unsigned uses bvult.
#[test]
fn test_codegen_binop_lt_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(3u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// Lt signed uses bvslt.
#[test]
fn test_codegen_binop_lt_signed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(3u128, 32);
        let rhs = Expr::bitvec_const(5u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(true));
        assert!(result.sort().is_bool());
    });
}

/// Eq with mixed Int/BitVec promotes both to Int.
#[test]
fn test_codegen_binop_eq_int_bv_mixed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(42);
        let rhs = Expr::bitvec_const(42u128, 64);
        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// Lt with mixed Int/BitVec promotes both to Int.
#[test]
fn test_codegen_binop_lt_int_bv_mixed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(10);
        let rhs = Expr::bitvec_const(20u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

/// Cmp produces bitvec(32) three-way comparison to match sort_inference.rs (#2771).
#[test]
fn test_codegen_binop_cmp_unsigned() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Cmp with Int operands uses int_lt/eq chain, returns bitvec(32) (#2771).
#[test]
fn test_codegen_binop_cmp_int_mixed() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(5);
        let rhs = Expr::int_const(10);
        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Offset fallback: byte-level addition.
#[test]
fn test_codegen_binop_offset() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
        let rhs = Expr::bitvec_const(4u128, POINTER_WIDTH);
        let result = codegen.codegen_binop_typed(BinOp::Offset, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

// =============================================================================
// codegen_unop — expression-level tests
// =============================================================================

/// Not on bool produces logical negation.
#[test]
fn test_codegen_unop_not_bool() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let operand = Expr::bool_const(true);
        let result = codegen.codegen_unop(rustc_public::mir::UnOp::Not, operand);
        assert!(result.sort().is_bool());
    });
}

/// Not on bitvec produces bitwise complement.
#[test]
fn test_codegen_unop_not_bitvec() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let operand = Expr::bitvec_const(0xFFu128, 32);
        let result = codegen.codegen_unop(rustc_public::mir::UnOp::Not, operand);
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

/// Neg produces bitvec negation.
#[test]
fn test_codegen_unop_neg() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let operand = Expr::bitvec_const(42u128, 32);
        let result = codegen.codegen_unop(rustc_public::mir::UnOp::Neg, operand);
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

// =============================================================================
// build_discriminant_ite_chain — expression-level tests
// =============================================================================

/// Helper to extract constructors from a datatype sort.
fn get_constructors(sort: &Sort) -> Vec<ay_bindings::DatatypeConstructor> {
    match sort.inner() {
        SortInner::Datatype(dt) => dt.constructors.clone(),
        _ => panic!("expected datatype sort"),
    }
}

/// Single constructor: returns 0.
#[test]
fn test_build_discriminant_ite_chain_single_constructor() {
    let sort = struct_sort("Wrapper", [("fld_inner", Sort::bitvec(32))]);
    let constructors = get_constructors(&sort);

    let expr = Expr::var("w", sort);
    let discrim = StatementCodegen::build_discriminant_ite_chain("Wrapper", &constructors, &expr);
    assert_eq!(discrim.sort().bitvec_width(), Some(32));
}

/// Two constructors (like Option): ITE selecting 0 or 1.
#[test]
fn test_build_discriminant_ite_chain_two_constructors() {
    let sort = enum_sort(
        "MyEnum",
        [
            ("MyEnum_A", vec![("fld_x", Sort::bitvec(32))]),
            ("MyEnum_B", vec![("fld_y", Sort::bitvec(64))]),
        ],
    );
    let constructors = get_constructors(&sort);
    assert_eq!(constructors.len(), 2);

    let expr = Expr::var("e", sort);
    let discrim = StatementCodegen::build_discriminant_ite_chain("MyEnum", &constructors, &expr);
    // Result should be bitvec(32) with ITE structure
    assert_eq!(discrim.sort().bitvec_width(), Some(32));
}

/// Three constructors: nested ITE chain.
#[test]
fn test_build_discriminant_ite_chain_three_constructors() {
    let sort = enum_sort(
        "Triple",
        [
            ("Triple_A", vec![]),
            ("Triple_B", vec![("fld_x", Sort::bitvec(32))]),
            ("Triple_C", vec![("fld_y", Sort::bitvec(64))]),
        ],
    );
    let constructors = get_constructors(&sort);
    assert_eq!(constructors.len(), 3);

    let expr = Expr::var("t", sort);
    let discrim = StatementCodegen::build_discriminant_ite_chain("Triple", &constructors, &expr);
    assert_eq!(discrim.sort().bitvec_width(), Some(32));
}

// =============================================================================
// codegen_binop_typed — default signedness (None)
// =============================================================================

/// When is_signed is None for Shr, defaults to unsigned (logical shift) — the safe
/// fallback because bvashr on an unsigned operand silently corrupts high bits.
#[test]
fn test_codegen_binop_default_signedness() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Shr with None signedness defaults to logical shift (unsigned)
        let lhs = Expr::bitvec_const(0x80000000u128, 32);
        let rhs = Expr::bitvec_const(1u128, 32);
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, None);
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(
            matches!(result.value(), ExprValue::BvLShr(_, _)),
            "None signedness must produce BvLShr (unsigned), got {:?}",
            result.value()
        );
    });
}

/// Le/Ge/Gt comparisons produce Bool.
#[test]
fn test_codegen_binop_le_ge_gt() {
    with_test_ay_ctx_for_source("pub fn probe(x: u32) -> u32 { x }", |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let a = Expr::bitvec_const(10u128, 32);
        let b = Expr::bitvec_const(20u128, 32);

        let le = codegen.codegen_binop_typed(BinOp::Le, a.clone(), b.clone(), Some(false));
        assert!(le.sort().is_bool());

        let ge = codegen.codegen_binop_typed(BinOp::Ge, a.clone(), b.clone(), Some(false));
        assert!(ge.sort().is_bool());

        let gt = codegen.codegen_binop_typed(BinOp::Gt, a, b, Some(true));
        assert!(gt.sort().is_bool());
    });
}

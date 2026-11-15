// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for arithmetic_checks.rs — overflow, div-by-zero, shift, offset,
//! and negation safety checks.
//!
//! Each function in arithmetic_checks.rs emits verification conditions via
//! `record_violation_guarded`. Tests verify that calling a production function
//! increases the violation count in `ctx.bmc_vc.violations` by the expected
//! amount.
//!
//! Part of #2615.

use super::*;

use crate::codegen_ay::provenance::{Loc, Val};

const ARITH_PROBE_SOURCE: &str = r#"
pub fn probe(x: u32, y: u32) -> u32 { x.wrapping_add(y) }
"#;

// =============================================================================
// overflow_check — returns Option<(Expr, &str)> for overflow-checkable ops
// =============================================================================

/// overflow_check for signed Add returns Some with a Bool no-overflow expression.
#[test]
fn test_overflow_check_signed_add_returns_some() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = codegen.overflow_check(BinOp::Add, &lhs, &rhs, true);

        assert!(result.is_some(), "signed Add should be overflow-checkable");
        let (expr, label) = result.unwrap();
        assert!(expr.sort().is_bool(), "overflow check must return Bool");
        assert_eq!(label, "overflow_check_add");
    });
}

/// overflow_check for unsigned Sub returns Some with underflow check.
#[test]
fn test_overflow_check_unsigned_sub_returns_some() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = codegen.overflow_check(BinOp::Sub, &lhs, &rhs, false);

        assert!(result.is_some(), "unsigned Sub should be overflow-checkable");
        let (expr, label) = result.unwrap();
        assert!(expr.sort().is_bool());
        assert_eq!(label, "overflow_check_sub");
    });
}

/// overflow_check for signed Mul returns Some.
#[test]
fn test_overflow_check_signed_mul_returns_some() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(16));
        let rhs = Expr::var("b", Sort::bitvec(16));
        let result = codegen.overflow_check(BinOp::Mul, &lhs, &rhs, true);

        assert!(result.is_some(), "signed Mul should be overflow-checkable");
        let (expr, label) = result.unwrap();
        assert!(expr.sort().is_bool());
        assert_eq!(label, "overflow_check_mul");
    });
}

/// overflow_check for signed Div produces INT_MIN/-1 guard.
#[test]
fn test_overflow_check_signed_div_int_min_guard() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = codegen.overflow_check(BinOp::Div, &lhs, &rhs, true);

        assert!(result.is_some(), "signed Div should produce INT_MIN/-1 overflow guard");
        let (expr, label) = result.unwrap();
        assert!(expr.sort().is_bool());
        assert_eq!(label, "overflow_check_div");
    });
}

/// overflow_check for signed Rem also produces INT_MIN/-1 guard (same path).
#[test]
fn test_overflow_check_signed_rem_int_min_guard() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(8));
        let rhs = Expr::var("b", Sort::bitvec(8));
        let result = codegen.overflow_check(BinOp::Rem, &lhs, &rhs, true);

        assert!(result.is_some(), "signed Rem should produce INT_MIN/-1 overflow guard");
        let (_, label) = result.unwrap();
        // `%` has its own label for Kani message parity (b2d2dca93).
        assert_eq!(label, "overflow_check_rem");
    });
}

/// overflow_check returns None for non-overflow-checkable ops (bitwise, comparison).
#[test]
fn test_overflow_check_bitwise_returns_none() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));

        assert!(
            codegen.overflow_check(BinOp::BitAnd, &lhs, &rhs, false).is_none(),
            "BitAnd cannot overflow"
        );
        assert!(
            codegen.overflow_check(BinOp::BitOr, &lhs, &rhs, false).is_none(),
            "BitOr cannot overflow"
        );
        assert!(
            codegen.overflow_check(BinOp::BitXor, &lhs, &rhs, false).is_none(),
            "BitXor cannot overflow"
        );
    });
}

/// overflow_check returns None for unsigned Div (div-by-zero handled separately).
#[test]
fn test_overflow_check_unsigned_div_returns_none() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));

        assert!(
            codegen.overflow_check(BinOp::Div, &lhs, &rhs, false).is_none(),
            "unsigned Div cannot overflow (div-by-zero checked elsewhere)"
        );
    });
}

/// overflow_check coerces mismatched widths before checking (8-bit + 32-bit).
#[test]
fn test_overflow_check_width_mismatch_coercion() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(8));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = codegen.overflow_check(BinOp::Add, &lhs, &rhs, false);

        assert!(result.is_some(), "width mismatch should be coerced, not rejected");
        let (expr, _) = result.unwrap();
        assert!(expr.sort().is_bool());
    });
}

#[test]
fn test_coerce_int_bitvec_mixed_drops_bitvec_width() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let int_lhs = Expr::var("bigint_val", Sort::int());
        let bv_rhs = Expr::bitvec_const(0xFFFF_FFFFu64, 32);
        let (coerced_lhs, coerced_rhs) =
            StatementCodegen::coerce_to_match_widths_typed(int_lhs, bv_rhs, true);

        assert!(coerced_lhs.sort().is_int(), "mixed Int/BV coercion should keep lhs as Int");
        assert_eq!(
            coerced_lhs.sort().bitvec_width(),
            None,
            "Int sort should report no bitvec width"
        );
        assert!(coerced_rhs.sort().is_int(), "mixed Int/BV coercion should convert rhs to Int");

        let overflow = codegen.overflow_check(BinOp::Div, &coerced_lhs, &coerced_rhs, true);
        assert!(
            overflow.is_none(),
            "signed Div overflow check should fail closed for Int-sort operands"
        );
    });
}

// =============================================================================
// emit_overflow_check — records violation when overflow is possible
// =============================================================================

/// emit_overflow_check for Add records exactly one violation.
#[test]
fn test_emit_overflow_check_records_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        codegen.emit_overflow_check(BinOp::Add, &lhs, &rhs, true);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "emit_overflow_check for Add should record one violation"
        );
    });
}

/// emit_overflow_check for BitAnd is a no-op (no violation recorded).
#[test]
fn test_emit_overflow_check_noop_for_bitwise() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        codegen.emit_overflow_check(BinOp::BitAnd, &lhs, &rhs, false);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before,
            "emit_overflow_check for BitAnd should not record any violation"
        );
    });
}

// =============================================================================
// emit_division_by_zero_check — records violation for divisor == 0
// =============================================================================

/// emit_division_by_zero_check records exactly one violation.
#[test]
fn test_emit_division_by_zero_check_records_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let divisor = Expr::var("d", Sort::bitvec(32));
        codegen.emit_division_by_zero_check(&divisor, "test_div_zero");

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "emit_division_by_zero_check should record one violation"
        );
    });
}

/// emit_division_by_zero_check with non-bitvec sort is a no-op.
#[test]
fn test_emit_division_by_zero_check_noop_for_non_bitvec() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let divisor = Expr::var("d", Sort::int());
        codegen.emit_division_by_zero_check(&divisor, "test_div_zero_int");

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before,
            "emit_division_by_zero_check should be no-op for Int sort"
        );
    });
}

// =============================================================================
// emit_shift_distance_check — excessive shift and negative shift violations
// =============================================================================

/// emit_shift_distance_check with unsigned distance records one violation
/// (excessive shift only, no negative check).
#[test]
fn test_emit_shift_distance_check_unsigned_one_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let value = Expr::var("v", Sort::bitvec(32));
        let distance = Expr::var("d", Sort::bitvec(32));
        codegen.emit_shift_distance_check(&value, &distance, Some(false));

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "unsigned shift distance check should record one violation (excessive shift)"
        );
    });
}

/// emit_shift_distance_check with signed distance records two violations
/// (excessive shift + negative shift).
#[test]
fn test_emit_shift_distance_check_signed_two_violations() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let value = Expr::var("v", Sort::bitvec(64));
        let distance = Expr::var("d", Sort::bitvec(32));
        codegen.emit_shift_distance_check(&value, &distance, Some(true));

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 2,
            "signed shift distance check should record two violations (excessive + negative)"
        );
    });
}

/// emit_shift_distance_check with non-bitvec value is a no-op.
#[test]
fn test_emit_shift_distance_check_noop_for_non_bitvec() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let value = Expr::var("v", Sort::int());
        let distance = Expr::var("d", Sort::bitvec(32));
        codegen.emit_shift_distance_check(&value, &distance, Some(false));

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before,
            "shift distance check should be no-op when value is non-bitvec"
        );
    });
}

// =============================================================================
// emit_offset_overflow_check — pointer offset with 3 checks
// =============================================================================

/// emit_offset_overflow_check with pointee_size > 1 records 3 violations
/// (value bounds, byte multiply overflow, result wraparound).
#[test]
fn test_emit_offset_overflow_check_nonzst_three_violations() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let ptr = Loc::of_address(Expr::var("p", Sort::bitvec(POINTER_WIDTH)));
        let count = Val::of_value(Expr::var("c", Sort::bitvec(POINTER_WIDTH)));
        codegen.emit_offset_overflow_check(&ptr, &count, 8); // u64 pointee

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 3,
            "offset check with size>1 should record 3 violations \
             (value bounds, byte multiply overflow, result wraparound)"
        );
    });
}

/// emit_offset_overflow_check with pointee_size == 1 records 2 violations
/// (value bounds, result wraparound — no multiply overflow needed).
#[test]
fn test_emit_offset_overflow_check_size1_two_violations() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let ptr = Loc::of_address(Expr::var("p", Sort::bitvec(POINTER_WIDTH)));
        let count = Val::of_value(Expr::var("c", Sort::bitvec(POINTER_WIDTH)));
        codegen.emit_offset_overflow_check(&ptr, &count, 1); // u8 pointee

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 2,
            "offset check with size==1 should record 2 violations \
             (value bounds, result wraparound — no multiply overflow)"
        );
    });
}

/// emit_offset_overflow_check with ZST (pointee_size == 0) records 1 violation
/// (value bounds only — no byte/result checks for ZST).
#[test]
fn test_emit_offset_overflow_check_zst_one_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let ptr = Loc::of_address(Expr::var("p", Sort::bitvec(POINTER_WIDTH)));
        let count = Val::of_value(Expr::var("c", Sort::bitvec(POINTER_WIDTH)));
        codegen.emit_offset_overflow_check(&ptr, &count, 0); // ZST

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "offset check for ZST should record 1 violation (value bounds only)"
        );
    });
}

/// emit_offset_overflow_check with non-bitvec ptr is a no-op.
#[test]
fn test_emit_offset_overflow_check_noop_for_non_bitvec_ptr() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let ptr = Loc::of_address(Expr::var("p", Sort::int()));
        let count = Val::of_value(Expr::var("c", Sort::bitvec(64)));
        codegen.emit_offset_overflow_check(&ptr, &count, 8);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before,
            "offset check should be no-op when ptr is non-bitvec"
        );
    });
}

/// extra_pointer_checks adds a provenance-invalid violation even for ZST offset ops.
#[test]
fn test_emit_offset_overflow_check_zst_extra_checks_adds_provenance_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let ptr = Loc::of_address(Expr::var("p", Sort::bitvec(POINTER_WIDTH)));
        let count = Val::of_value(Expr::var("c", Sort::bitvec(POINTER_WIDTH)));
        codegen.emit_offset_overflow_check(&ptr, &count, 0);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 2,
            "ZST offset check with extra_pointer_checks should record value-bounds and provenance violations"
        );

        let last_violation = codegen.ctx.bmc_vc.violations.last().expect("provenance violation");
        let rendered = last_violation.condition.to_string();
        // heap_is_allocated uses array-backed allocation map; rendered form may
        // contain "obj_valid" or an Array select expression depending on the
        // heap model version.
        assert!(
            rendered.contains("obj_valid")
                || rendered.contains("select")
                || rendered.contains("bvudiv"),
            "extra_pointer_checks provenance violation should reference heap validity: {rendered}"
        );
    });
}

// =============================================================================
// emit_neg_overflow_check — INT_MIN negation overflow
// =============================================================================

/// emit_neg_overflow_check records exactly one violation.
#[test]
fn test_emit_neg_overflow_check_records_violation() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let violations_before = codegen.ctx.bmc_vc.violations.len();

        let operand = Expr::var("x", Sort::bitvec(32));
        codegen.emit_neg_overflow_check(&operand);

        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before + 1,
            "emit_neg_overflow_check should record one violation"
        );
    });
}

// =============================================================================
// Unchecked operation variants — same predicate as the safe operator, own label
// =============================================================================

/// AddUnchecked uses the same overflow check as Add.
#[test]
fn test_overflow_check_add_unchecked_same_as_add() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));

        let add_result = codegen.overflow_check(BinOp::Add, &lhs, &rhs, false);
        let unchecked_result = codegen.overflow_check(BinOp::AddUnchecked, &lhs, &rhs, false);

        // Same predicate, distinct labels: the safe operator's overflow is a
        // Rust panic (`overflow_check_add`, driver class `overflow`), the
        // unchecked one UB of an unsafe intrinsic (`unchecked_add_overflow`,
        // Kani's `arithmetic_overflow`, never gated). One shared label let a
        // `#[kani::should_panic]` harness bank the UB as its panic.
        let (add_expr, add_label) = add_result.expect("Add is overflow-checkable");
        let (unchecked_expr, unchecked_label) =
            unchecked_result.expect("AddUnchecked is overflow-checkable");
        assert_eq!(add_expr, unchecked_expr);
        assert_eq!(add_label, "overflow_check_add");
        assert_eq!(unchecked_label, "unchecked_add_overflow");
    });
}

/// SubUnchecked uses the same overflow check as Sub.
#[test]
fn test_overflow_check_sub_unchecked_same_as_sub() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));

        let sub_result = codegen.overflow_check(BinOp::Sub, &lhs, &rhs, true);
        let unchecked_result = codegen.overflow_check(BinOp::SubUnchecked, &lhs, &rhs, true);

        let (sub_expr, sub_label) = sub_result.expect("Sub is overflow-checkable");
        let (unchecked_expr, unchecked_label) =
            unchecked_result.expect("SubUnchecked is overflow-checkable");
        assert_eq!(sub_expr, unchecked_expr);
        assert_eq!(sub_label, "overflow_check_sub");
        assert_eq!(unchecked_label, "unchecked_sub_overflow");
    });
}

/// MulUnchecked uses the same overflow check as Mul.
#[test]
fn test_overflow_check_mul_unchecked_same_as_mul() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::var("a", Sort::bitvec(64));
        let rhs = Expr::var("b", Sort::bitvec(64));

        let mul_result = codegen.overflow_check(BinOp::Mul, &lhs, &rhs, false);
        let unchecked_result = codegen.overflow_check(BinOp::MulUnchecked, &lhs, &rhs, false);

        let (mul_expr, mul_label) = mul_result.expect("Mul is overflow-checkable");
        let (unchecked_expr, unchecked_label) =
            unchecked_result.expect("MulUnchecked is overflow-checkable");
        assert_eq!(mul_expr, unchecked_expr);
        assert_eq!(mul_label, "overflow_check_mul");
        assert_eq!(unchecked_label, "unchecked_mul_overflow");
    });
}

/// The intercepted `<int>::unchecked_{add,sub,mul}` methods reach
/// `codegen_unchecked_arith` as the plain `BinOp::Add`/`Sub`/`Mul`
/// (`dispatch_arithmetic`). Their overflow is UB: it records the unchecked
/// label under the ungated UB kind, and `--no-overflow-checks` keeps it (the
/// check has no assume half, so gating dropped the only check of the UB).
#[test]
fn test_codegen_unchecked_arith_records_unchecked_label_ungated() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        ctx.config.overflow_checks = false;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        for (op, label) in [
            (BinOp::Add, "unchecked_add_overflow"),
            (BinOp::Sub, "unchecked_sub_overflow"),
            (BinOp::Mul, "unchecked_mul_overflow"),
        ] {
            let before = codegen.ctx.bmc_vc.violations.len();
            let result = codegen.codegen_unchecked_arith(
                &[local_operand(1), local_operand(2)],
                &local_place(0),
                Some(1),
                op,
            );
            assert_eq!(result, Some(1), "{label}");
            assert_eq!(
                codegen.ctx.bmc_vc.violations.len(),
                before + 1,
                "{label} must survive --no-overflow-checks"
            );
            let violation = codegen.ctx.bmc_vc.violations.last().expect("unchecked overflow check");
            assert_eq!(violation.kind, trust_mc_core::PropertyKind::UndefinedBehavior, "{label}");
            let prefix = format!("ay_violation_{label}_");
            assert!(
                violation.smt_var.as_deref().is_some_and(|name| name.starts_with(&prefix)),
                "{label}: got {:?}",
                violation.smt_var
            );
        }
    });
}

/// The smt names of the violations recorded since `before`.
fn violation_vars_since(codegen: &StatementCodegen<'_, '_, '_>, before: usize) -> Vec<String> {
    codegen.ctx.bmc_vc.violations[before..]
        .iter()
        .map(|v| v.smt_var.clone().unwrap_or_default())
        .collect()
}

/// An `unchecked_shl`/`unchecked_shr` past the width (or by a negative signed
/// distance) is UB of an unsafe intrinsic: its checks carry the unchecked
/// labels and the ungated UB kind, so `--no-overflow-checks` keeps them. On the
/// shared `shift_distance_check` labels the flag dropped the only check of the
/// UB.
#[test]
fn test_emit_shift_distance_check_records_unchecked_labels_ungated() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        ctx.config.overflow_checks = false;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let before = codegen.ctx.bmc_vc.violations.len();
        let value = Expr::var("v", Sort::bitvec(64));
        let distance = Expr::var("d", Sort::bitvec(32));
        codegen.emit_shift_distance_check(&value, &distance, Some(true));

        let vars = violation_vars_since(&codegen, before);
        assert_eq!(vars.len(), 2, "both sub-checks survive --no-overflow-checks: {vars:?}");
        assert!(vars[0].starts_with("ay_violation_unchecked_shift_distance_check_"), "{vars:?}");
        assert!(
            vars[1].starts_with("ay_violation_unchecked_shift_distance_check_negative_"),
            "{vars:?}"
        );
        for v in &codegen.ctx.bmc_vc.violations[before..] {
            assert_eq!(v.kind, trust_mc_core::PropertyKind::UndefinedBehavior);
        }
    });
}

/// The SIMD lane shift checks (Kani's compiler writes them) and the MIR
/// `Assert(Overflow(Shl|Shr))` checks (enabled at the terminator) keep the
/// `shift_distance_check` labels and record under `CheckGate::Always`: the
/// label's gated kind does not drop them under `--no-overflow-checks`.
#[test]
fn test_simd_and_mir_assert_shift_checks_survive_no_overflow_checks() {
    with_test_ay_ctx_for_source(ARITH_PROBE_SOURCE, |mut ctx| {
        ctx.config.overflow_checks = false;
        let instance = find_instance_by_suffix(&ctx, "probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let value = Expr::var("v", Sort::bitvec(32));
        let distance = Expr::var("d", Sort::bitvec(32));
        let before = codegen.ctx.bmc_vc.violations.len();
        codegen.emit_shift_distance_check_named(&value, &distance, Some(true), Some("simd_shl"));
        let vars = violation_vars_since(&codegen, before);
        assert_eq!(vars.len(), 2, "SIMD shift checks survive the flag: {vars:?}");
        assert!(vars[0].starts_with("ay_violation_shift_distance_check_"), "{vars:?}");
        assert!(vars[1].starts_with("ay_violation_shift_distance_check_negative_"), "{vars:?}");

        let before = codegen.ctx.bmc_vc.violations.len();
        codegen.emit_mir_assert_shift_distance_check(
            &value,
            &distance,
            Some(false),
            "attempt to shift left with overflow",
        );
        let vars = violation_vars_since(&codegen, before);
        assert_eq!(vars.len(), 1, "the enabled MIR Assert's check is recorded: {vars:?}");
        assert!(vars[0].starts_with("ay_violation_shift_distance_check_"), "{vars:?}");
    });
}

const SIGNED_ARITH_PROBE_SOURCE: &str = r#"
pub fn probe_signed(x: i32, y: i32) -> i32 { x.wrapping_add(y) }
"#;

/// An intercepted `unchecked_div`/`unchecked_rem` reaches
/// `codegen_unchecked_arith` as `BinOp::Div`/`Rem`. Its signed `MIN / -1` is
/// UB: the operator-level `binop_*` labels (ungated UB kind), never the MIR
/// `Assert`'s gated panic label `overflow_check_div`/`_rem`.
#[test]
fn test_codegen_unchecked_div_rem_records_binop_overflow_label() {
    with_test_ay_ctx_for_source(SIGNED_ARITH_PROBE_SOURCE, |mut ctx| {
        ctx.config.overflow_checks = false;
        let instance = find_instance_by_suffix(&ctx, "probe_signed");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        for (op, zero, overflow) in [
            (BinOp::Div, "unchecked_div_by_zero", "binop_div_overflow"),
            (BinOp::Rem, "unchecked_div_by_zero", "binop_rem_overflow"),
        ] {
            let before = codegen.ctx.bmc_vc.violations.len();
            let result = codegen.codegen_unchecked_arith(
                &[local_operand(1), local_operand(2)],
                &local_place(0),
                Some(1),
                op,
            );
            assert_eq!(result, Some(1), "{op:?}");
            let vars = violation_vars_since(&codegen, before);
            assert_eq!(vars.len(), 2, "{op:?}: divisor and MIN / -1, got {vars:?}");
            assert!(vars[0].starts_with(&format!("ay_violation_{zero}_")), "{op:?}: {vars:?}");
            assert!(vars[1].starts_with(&format!("ay_violation_{overflow}_")), "{op:?}: {vars:?}");
            for v in &codegen.ctx.bmc_vc.violations[before..] {
                assert_eq!(v.kind, trust_mc_core::PropertyKind::UndefinedBehavior, "{op:?}");
            }
        }
    });
}

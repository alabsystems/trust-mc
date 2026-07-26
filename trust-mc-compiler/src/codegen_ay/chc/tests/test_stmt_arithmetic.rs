// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Tests for codegen_stmt_arithmetic.rs — translate_binop, translate_checked_binop,
// translate_unop, translate_cast, coerce_shift_amount, coerce_arithmetic_operands.
//
// Part of #2188: CHC module test coverage.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// coerce_shift_amount — delegates to coerce_bitvec_width_safe
// =============================================================================

#[test]
fn test_coerce_shift_amount_narrower_extends() {
    // u64 << u32: the u32 shift amount should be zero-extended to 64 bits
    let shift_amt = Expr::bitvec_const(3u128, 32);
    let coerced = ChcCtx::coerce_shift_amount(shift_amt, 64);
    assert_eq!(
        coerced.sort().bitvec_width(),
        Some(64),
        "shift amount should be extended to target width"
    );
    assert!(
        coerced.to_string().contains("zero_extend"),
        "narrower shift should use zero_extend (unsigned): {}",
        coerced
    );
}

#[test]
fn test_coerce_shift_amount_wider_truncates() {
    // u8 << u32: the u32 shift amount should be truncated to 8 bits
    let shift_amt = Expr::bitvec_const(3u128, 32);
    let coerced = ChcCtx::coerce_shift_amount(shift_amt, 8);
    assert_eq!(
        coerced.sort().bitvec_width(),
        Some(8),
        "shift amount should be truncated to target width"
    );
    assert!(coerced.to_string().contains("extract"), "wider shift should use extract: {}", coerced);
}

#[test]
fn test_coerce_shift_amount_same_width_noop() {
    // u32 << u32: same width, no coercion needed
    let shift_amt = Expr::bitvec_const(3u128, 32);
    let coerced = ChcCtx::coerce_shift_amount(shift_amt.clone(), 32);
    assert_eq!(
        coerced.to_string(),
        shift_amt.to_string(),
        "same-width shift should pass through unchanged"
    );
}

#[test]
fn test_coerce_shift_amount_non_bitvec_passthrough() {
    // Int sort should pass through unchanged
    let int_expr = Expr::int_const(5);
    let coerced = ChcCtx::coerce_shift_amount(int_expr.clone(), 32);
    assert_eq!(
        coerced.to_string(),
        int_expr.to_string(),
        "non-bitvec should pass through unchanged"
    );
}

// =============================================================================
// coerce_arithmetic_operands — mixed-width arithmetic coercion
// =============================================================================

#[test]
fn test_coerce_arithmetic_operands_mixed_width_unsigned() {
    // u64 + u32: both should be coerced to 64-bit (max width), unsigned
    let lhs = Expr::bitvec_const(100u128, 64);
    let rhs = Expr::bitvec_const(50u128, 32);
    let (lhs_coerced, rhs_coerced) = ChcCtx::coerce_arithmetic_operands(lhs, rhs, false);
    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(64));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(64));
    assert!(
        rhs_coerced.to_string().contains("zero_extend"),
        "unsigned coercion should use zero_extend: {}",
        rhs_coerced
    );
}

#[test]
fn test_coerce_arithmetic_operands_mixed_width_signed() {
    // i64 + i32: both should be coerced to 64-bit (max width), signed
    let lhs = Expr::bitvec_const(100u128, 64);
    let rhs = Expr::bitvec_const(0xFFFFFFFFu128, 32); // -1 as i32
    let (lhs_coerced, rhs_coerced) = ChcCtx::coerce_arithmetic_operands(lhs, rhs, true);
    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(64));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(64));
    assert!(
        rhs_coerced.to_string().contains("sign_extend"),
        "signed coercion should use sign_extend: {}",
        rhs_coerced
    );
}

#[test]
fn test_coerce_arithmetic_operands_same_width_noop() {
    // u32 + u32: same width, no coercion needed
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 32);
    let (lhs_coerced, rhs_coerced) =
        ChcCtx::coerce_arithmetic_operands(lhs.clone(), rhs.clone(), false);
    assert_eq!(lhs_coerced.to_string(), lhs.to_string());
    assert_eq!(rhs_coerced.to_string(), rhs.to_string());
}

#[test]
fn test_coerce_arithmetic_operands_non_bitvec_passthrough() {
    // Int + Int: non-bitvec passthrough
    let lhs = Expr::int_const(10);
    let rhs = Expr::int_const(20);
    let (lhs_coerced, rhs_coerced) =
        ChcCtx::coerce_arithmetic_operands(lhs.clone(), rhs.clone(), false);
    assert_eq!(lhs_coerced.to_string(), lhs.to_string());
    assert_eq!(rhs_coerced.to_string(), rhs.to_string());
}

#[test]
fn test_coerce_arithmetic_operands_rhs_wider() {
    // u8 + u32: lhs should be extended to 32-bit
    let lhs = Expr::bitvec_const(5u128, 8);
    let rhs = Expr::bitvec_const(10u128, 32);
    let (lhs_coerced, rhs_coerced) = ChcCtx::coerce_arithmetic_operands(lhs, rhs, false);
    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(32));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(32));
    assert!(
        lhs_coerced.to_string().contains("zero_extend"),
        "narrower lhs should be zero-extended: {}",
        lhs_coerced
    );
}

// =============================================================================
// MIR-driven: translate_binop via mir_to_chc pipeline
// =============================================================================

#[test]
fn test_mir_to_chc_checked_add_produces_overflow_flag() {
    // Checked addition should produce a tuple (result, overflow_flag).
    // This exercises translate_checked_binop in codegen_stmt_arithmetic.rs.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_checked_add(a: u32, b: u32) -> (u32, bool) {
            a.overflowing_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add", ChcConfig::default());

        // Should produce rules and relations
        assert!(!vc.rules.is_empty(), "checked add should produce CHC rules");
        assert!(!vc.relations.is_empty(), "checked add should produce CHC relations");

        // Emit SMT and verify it's valid (contains bvadd for the arithmetic)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd") || smt.contains("BitVec"),
            "checked add should use bitvector arithmetic: {}...",
            &smt[..smt.len().min(2000)]
        );
    });
}

#[test]
fn test_mir_to_chc_negation_produces_valid_chc() {
    // Unary negation should produce valid CHC with bitvec state variables.
    // This exercises the negation path through the CHC pipeline.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_negate(x: i32) -> i32 {
            let y = -x;
            y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_negate");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_negate", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "negation should produce CHC rules");
        assert!(!vc.relations.is_empty(), "negation should declare relations");

        // Verify structural properties
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "should have error relation");

        // Semantic: negation of i32 produces a checked overflow guard comparing
        // against i32::MIN (#x80000000), since -i32::MIN overflows.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("#x80000000"),
            "i32 negation should check i32::MIN overflow guard (#x80000000), got: {}",
            &smt[..smt.len().min(1000)]
        );
    });
}

#[test]
fn test_mir_to_chc_bitwise_not_produces_valid_chc() {
    // Bitwise NOT should produce valid CHC with bitvec operations.
    // This exercises the UnOp::Not path through the CHC pipeline.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bitwise_not(x: u32) -> u32 {
            let y = !x;
            y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bitwise_not");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bitwise_not", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "bitwise not should produce CHC rules");
        assert!(!vc.relations.is_empty(), "bitwise not should declare relations");

        // Should have at least entry bb0 + one transition
        let has_bb0 = vc.relations.iter().any(|r| r.name.contains("__bb0"));
        assert!(has_bb0, "should have bb0 entry relation");

        // Semantic: bitwise NOT on u32 should have BitVec 32 state variables
        // for the input and output.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("BitVec 32"),
            "u32 bitwise NOT VC should declare BitVec 32 sorts, full output: {}",
            smt
        );
    });
}

#[test]
fn test_mir_to_chc_cast_widening_valid_chc() {
    // Cast from u8 to u32 exercises translate_cast widening path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cast_widen(x: u8) -> u32 {
            x as u32
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_widen");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_cast_widen", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "cast should produce CHC rules");
        assert!(!vc.relations.is_empty(), "cast should declare relations");

        // Verify input and output sorts differ (u8 → u32 means 8-bit input, 32-bit output)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("BitVec 8") && smt.contains("BitVec 32"),
            "widening cast should have both 8-bit and 32-bit sorts: {}...",
            &smt[..smt.len().min(800)]
        );
    });
}

#[test]
fn test_mir_to_chc_cast_narrowing_valid_chc() {
    // Cast from u32 to u8 exercises translate_cast truncation path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cast_narrow(x: u32) -> u8 {
            x as u8
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_narrow");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_cast_narrow", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "cast should produce CHC rules");

        // Verify both bit widths present (32-bit input, 8-bit output)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("BitVec 8") && smt.contains("BitVec 32"),
            "narrowing cast should have both 8-bit and 32-bit sorts: {}...",
            &smt[..smt.len().min(800)]
        );
    });
}

#[test]
fn test_mir_to_chc_shift_left_mixed_width_valid_chc() {
    // u64 << u32 exercises coerce_shift_amount through mir_to_chc.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_shl(x: u64, amt: u32) -> u64 {
            x << (amt & 0x3F)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shl");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_shl", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "shift should produce CHC rules");

        // Verify mixed-width operands present (64-bit and 32-bit)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("BitVec 64") && smt.contains("BitVec 32"),
            "mixed-width shift should have both 64-bit and 32-bit sorts: {}...",
            &smt[..smt.len().min(800)]
        );
    });
}

#[test]
fn test_mir_to_chc_three_way_cmp_produces_ordering() {
    // BinOp::Cmp produces Ordering (Less/Equal/Greater) as bitvec values.
    // This exercises the Cmp arm of translate_binop.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cmp(a: u32, b: u32) -> core::cmp::Ordering {
            a.cmp(&b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cmp");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_cmp", ChcConfig::default());

        // Cmp should produce valid CHC
        assert!(!vc.rules.is_empty(), "cmp should produce CHC rules");
        assert!(!vc.relations.is_empty(), "cmp should produce CHC relations");

        // Semantic: three-way comparison produces ite (if-then-else) to select
        // between Less/Equal/Greater Ordering values using bvult/bvugt.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("ite") || smt.contains("bvult") || smt.contains("bvugt"),
            "three-way cmp should use ite/bvult/bvugt for ordering, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

// =============================================================================
// translate_binop: Int-sort arithmetic through solver
// =============================================================================

#[test]
fn test_int_add_semantics_via_solver() {
    // Verify Int-sort addition semantics (BigInt path) via Z3 solver.
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("sum", Sort::int()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let sum = Expr::var("sum", Sort::int());

    // Entry: x=100 ∧ y=200 → bb0(x, y)
    vc.add_rule(Rule::init(
        x.clone().eq(Expr::int_const(100)).and(y.clone().eq(Expr::int_const(200))),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    // Transition: bb0(x, y) ∧ sum=(x+y) → bb1(sum)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![sum.clone().eq(x.int_add(y))],
        ),
        RelationApp::new("bb1", vec![sum.clone()]),
    ));

    // Error: bb1(sum) ∧ sum!=300 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![sum.clone()])),
            vec![sum.eq(Expr::int_const(300)).not()],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();

    // Verify the SMT contains Int-sort arithmetic
    assert!(smt.contains("Int"), "should use Int sort for BigInt path");

    // Z3 should prove this unsat (100 + 200 == 300).
    // Fail closed if z3 is unavailable instead of silently skipping.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Checked binop overflow semantics
// =============================================================================

#[test]
fn test_checked_add_unsigned_overflow_via_solver() {
    // Unsigned add: MAX_U32 + 1 should overflow.
    // Verifies translate_checked_binop unsigned overflow path.
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("result", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("overflow", Sort::bool()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32), Sort::bool()]));

    let result = Expr::var("result", Sort::bitvec(32));
    let overflow = Expr::var("overflow", Sort::bool());

    let max_u32 = Expr::bitvec_const(0xFFFFFFFFu128, 32);
    let one = Expr::bitvec_const(1u128, 32);

    // Compute: result = MAX + 1 (wrapping), overflow = result < MAX
    let wrapped = max_u32.clone().bvadd(one);
    let overflow_flag = wrapped.clone().bvult(max_u32);

    // Entry: result=wrapped ∧ overflow=flag → bb0(result, overflow)
    vc.add_rule(Rule::init(
        result.clone().eq(wrapped).and(overflow.clone().eq(overflow_flag)),
        RelationApp::new("bb0", vec![result.clone(), overflow.clone()]),
    ));

    // Error: bb0(result, overflow) ∧ !overflow → error()
    // Should NOT be reachable because overflow IS true for MAX+1
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![result, overflow.clone()])),
            vec![overflow.not()],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();
    assert!(smt.contains("bvadd"), "should contain bvadd for checked add");
    assert!(smt.contains("bvult"), "should contain bvult for overflow check");

    // Z3 should prove this unsat (overflow IS true for MAX+1, so !overflow is unreachable).
    assert_z3_result(&smt, "unsat");
}

#[test]
fn test_checked_add_unsigned_no_overflow_via_solver() {
    // Negative case: 1 + 1 should NOT overflow.
    // Verifies that bvadd_no_overflow yields SAT for small values.
    // Part of P1:763 directive: negative-case coverage.
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("result", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("overflow", Sort::bool()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32), Sort::bool()]));

    let result = Expr::var("result", Sort::bitvec(32));
    let overflow = Expr::var("overflow", Sort::bool());

    let one_a = Expr::bitvec_const(1u128, 32);
    let one_b = Expr::bitvec_const(1u128, 32);

    // Compute: result = 1 + 1 (wrapping), overflow = result < 1
    let wrapped = one_a.clone().bvadd(one_b);
    let overflow_flag = wrapped.clone().bvult(one_a);

    // Entry: result=wrapped ∧ overflow=flag → bb0(result, overflow)
    vc.add_rule(Rule::init(
        result.clone().eq(wrapped).and(overflow.clone().eq(overflow_flag)),
        RelationApp::new("bb0", vec![result.clone(), overflow.clone()]),
    ));

    // Error: bb0(result, overflow) ∧ overflow → error()
    // Should NOT be reachable because overflow IS false for 1+1
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![result, overflow.clone()])),
            vec![overflow],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();
    assert!(smt.contains("bvadd"), "should contain bvadd for checked add");
    assert!(smt.contains("bvult"), "should contain bvult for overflow check");

    // Z3 should prove this unsat (1+1 does NOT overflow, so overflow is unreachable).
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// coerce_eq_operands — Bool↔BV and BV width mismatch coercion for BinOp::Eq/Ne
// Part of #2244: Sort mismatch panics in equality comparisons
// =============================================================================

#[test]
fn test_coerce_eq_operands_same_sort_noop() {
    let a = Expr::bitvec_const(1u64, 32);
    let b = Expr::bitvec_const(2u64, 32);
    let (l, r) = ChcCtx::coerce_eq_operands(a.clone(), b.clone(), false);
    assert_eq!(*l.sort(), *a.sort());
    assert_eq!(*r.sort(), *b.sort());
}

#[test]
fn test_coerce_eq_operands_bool_vs_bv32() {
    // Part of #2244: flattened enum discriminant (Bool) compared to BV32 field
    let bool_expr = Expr::bool_const(true);
    let bv32_expr = Expr::bitvec_const(1u64, 32);
    let (l, r) = ChcCtx::coerce_eq_operands(bool_expr, bv32_expr, false);
    assert_eq!(
        *l.sort(),
        *r.sort(),
        "coerced operands must have same sort: lhs={:?} rhs={:?}",
        l.sort(),
        r.sort()
    );
    assert!(l.sort().is_bitvec(), "Bool should be coerced to bitvec");
    assert_eq!(l.sort().bitvec_width(), Some(32));
}

#[test]
fn test_coerce_eq_operands_bv32_vs_bool() {
    // Reverse direction: BV32 lhs, Bool rhs
    let bv32_expr = Expr::bitvec_const(1u64, 32);
    let bool_expr = Expr::bool_const(false);
    let (l, r) = ChcCtx::coerce_eq_operands(bv32_expr, bool_expr, false);
    assert_eq!(
        *l.sort(),
        *r.sort(),
        "coerced operands must have same sort: lhs={:?} rhs={:?}",
        l.sort(),
        r.sort()
    );
    assert!(r.sort().is_bitvec(), "Bool should be coerced to bitvec");
    assert_eq!(r.sort().bitvec_width(), Some(32));
}

#[test]
fn test_coerce_eq_operands_bv_width_mismatch() {
    // BV32 vs BV64 — should coerce both to BV64
    let bv32 = Expr::bitvec_const(1u64, 32);
    let bv64 = Expr::bitvec_const(2u64, 64);
    let (l, r) = ChcCtx::coerce_eq_operands(bv32, bv64, false);
    assert_eq!(*l.sort(), *r.sort(), "coerced operands must have same sort");
    assert_eq!(l.sort().bitvec_width(), Some(64), "should widen to max width");
    assert_eq!(r.sort().bitvec_width(), Some(64));
}

#[test]
fn test_coerce_eq_operands_bv_width_mismatch_signed() {
    // BV8 vs BV32 with signed=true — should sign-extend BV8 to BV32
    let bv8 = Expr::bitvec_const(0xFFu64, 8); // i8(-1)
    let bv32 = Expr::bitvec_const(0xFFFFFFFFu64, 32); // i32(-1)
    let (l, r) = ChcCtx::coerce_eq_operands(bv8, bv32, true);
    assert_eq!(*l.sort(), *r.sort(), "coerced operands must have same sort");
    assert_eq!(l.sort().bitvec_width(), Some(32));
    // Sign-extended i8(-1) should equal i32(-1)
    let expected_lhs = Expr::bitvec_const(0xFFu64, 8).sign_extend(24);
    assert_eq!(l, expected_lhs, "signed extension should sign-extend i8(-1) to i32(-1)");
}

#[test]
fn test_coerce_eq_operands_bool_vs_bv1() {
    // Bool vs BV1 — should coerce Bool to BV1
    let bool_expr = Expr::bool_const(true);
    let bv1 = Expr::bitvec_const(1u64, 1);
    let (l, r) = ChcCtx::coerce_eq_operands(bool_expr, bv1, false);
    assert_eq!(*l.sort(), *r.sort());
    assert_eq!(l.sort().bitvec_width(), Some(1));
}

#[test]
fn test_coerce_eq_operands_incompatible_passthrough() {
    // Int vs BV — cannot coerce, should pass through unchanged
    let int_expr = Expr::int_const(42);
    let bv32 = Expr::bitvec_const(42u64, 32);
    let (l, r) = ChcCtx::coerce_eq_operands(int_expr, bv32, false);
    // Sorts remain different — caller must handle via return None
    assert!(l.sort().is_int());
    assert!(r.sort().is_bitvec());
}

// =============================================================================
// coerce_bitwise_operands — BV width normalization for bitwise ops
// Part of proof_coverage: no direct tests existed
// =============================================================================

#[test]
fn test_coerce_bitwise_operands_same_width_noop() {
    let a = Expr::bitvec_const(0xffu64, 8);
    let b = Expr::bitvec_const(0x0fu64, 8);
    let (l, r) = ChcCtx::coerce_bitwise_operands(a, b, false);
    assert_eq!(l.sort().bitvec_width(), Some(8));
    assert_eq!(r.sort().bitvec_width(), Some(8));
}

#[test]
fn test_coerce_bitwise_operands_width_mismatch() {
    let bv8 = Expr::bitvec_const(0xffu64, 8);
    let bv32 = Expr::bitvec_const(0xffu64, 32);
    let (l, r) = ChcCtx::coerce_bitwise_operands(bv8, bv32, false);
    assert_eq!(l.sort().bitvec_width(), Some(32), "should widen to max width for bitwise");
    assert_eq!(r.sort().bitvec_width(), Some(32));
}

#[test]
fn test_coerce_bitwise_operands_non_bv_passthrough() {
    let bool_a = Expr::bool_const(true);
    let bool_b = Expr::bool_const(false);
    let (l, r) = ChcCtx::coerce_bitwise_operands(bool_a, bool_b, false);
    assert!(l.sort().is_bool(), "non-BV should pass through unchanged");
    assert!(r.sort().is_bool());
}

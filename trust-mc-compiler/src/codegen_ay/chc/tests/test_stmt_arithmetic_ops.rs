// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_arithmetic_ops.rs` — checked arithmetic,
//! unary ops, PtrMetadata, and cast operations.
//!
//! Part of #2303 (codegen_stmt_arithmetic_ops.rs, 388 LOC, zero dedicated coverage).
//! Covers:
//! - `translate_checked_binop`: checked add/sub/mul with overflow tuples
//! - `translate_checked_binop_flat`: flat overflow pair output (#2214)
//! - `translate_unop`: Not/Neg operations
//! - `translate_cast`: bitvec width extension/truncation/sign-handling (#673)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// Checked addition with overflow detection
// =============================================================================

/// Branching forces multi-BB MIR so the VC contains transition rules with
/// non-trivial constraints. Single-expression calls compile to init+call-only rules.
const CHECKED_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add(a: u32, b: u32, flag: bool) -> (u32, bool) {
        if flag { a.overflowing_add(b) } else { (0, false) }
    }
"#;

/// Checked unsigned add encodes BV32 state for u32 operands and Bool for overflow flag.
/// `overflowing_add` lowers as a CheckedBinOp call — the addition flows through
/// state-variable sorts (BV32/Bool), not as BvAdd in constraint bodies.
#[test]
fn test_checked_add_unsigned_generates_vc() {
    with_test_ay_ctx_for_source(CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_add", body.blocks.len());

        // Semantic: relations must carry BV32 for u32 operands/result
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "checked u32 add VC should have BV32-sorted relation args");

        // Semantic: relations must carry Bool for the overflow flag (fld1)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "checked add VC should have Bool-sorted relation args for overflow");

        // SMT output must declare BitVec(32) state variables for the addition operands
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)"),
            "checked u32 add should declare BV32 state variables: {}...",
            &smt[..smt.len().min(500)]
        );

        // Semantic: checked add produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_checked_add");
        // Note: overflowing_add lowers as a CheckedBinOp call in MIR — the addition
        // result flows through state-variable assignments (head args), not as a BvAdd
        // constraint in rule bodies. The checked-add semantics are validated above via
        // sort-level checks: BV32 for u32 operands and Bool for the overflow flag.
        // SwitchInt branching scaffold produces the Not constraint verified here.
        // See #2910 for analysis of what this assertion actually verifies.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_add",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not (SwitchInt branch guard)",
        );
    });
}

// =============================================================================
// Checked signed subtraction
// =============================================================================

const CHECKED_SUB_SIGNED_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_sub_signed(a: i32, b: i32, flag: bool) -> (i32, bool) {
        if flag { a.overflowing_sub(b) } else { (0, false) }
    }
"#;

/// Checked signed subtraction encodes BV32 for i32 operands and Bool for overflow.
#[test]
fn test_checked_sub_signed_generates_vc() {
    with_test_ay_ctx_for_source(CHECKED_SUB_SIGNED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_sub_signed");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_sub_signed", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_sub_signed", body.blocks.len());

        // Semantic: relations must carry BV32 for i32 operands
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "checked i32 sub VC should have BV32-sorted relation args");

        // Semantic: overflow flag requires Bool sort in relations
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "checked sub VC should have Bool-sorted args for overflow flag");

        // SMT output must reference both BV32 (i32 values) and Bool (overflow flag)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 32)") && smt.contains("Bool"),
            "checked i32 sub should declare BV32 + Bool state: {}...",
            &smt[..smt.len().min(500)]
        );

        // Semantic: checked sub produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_checked_sub_signed");
        // Same pattern as checked_add: overflowing_sub flows through state-variable
        // sorts, not as BvSub in constraint bodies. Not comes from SwitchInt scaffold.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_sub_signed",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not (SwitchInt branch guard)",
        );

        // Semantic: the else branch returns (0, false) — a BitVecConst should
        // appear as a constant assignment in the false-branch rule head args.
        // The zero constant (BV32 0) validates that the else-branch encoding
        // emits concrete constants, not just unconstrained variables.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_sub_signed",
            |e| matches!(e.value(), ExprValue::BitVecConst { width: 32, .. }),
            "BitVecConst(bv32) (else-branch constant return)",
        );
    });
}

// =============================================================================
// Checked unsigned multiplication
// =============================================================================

const CHECKED_MUL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_mul(a: u64, b: u64, flag: bool) -> (u64, bool) {
        if flag { a.overflowing_mul(b) } else { (0, false) }
    }
"#;

/// Checked unsigned multiplication encodes BV64 for u64 operands and Bool for overflow.
#[test]
fn test_checked_mul_unsigned_generates_vc() {
    with_test_ay_ctx_for_source(CHECKED_MUL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_mul");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_mul", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_mul", body.blocks.len());

        // Semantic: relations must carry BV64 for u64 operands/result
        let has_bv64 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(has_bv64, "checked u64 mul VC should have BV64-sorted relation args");

        // Semantic: overflow flag requires Bool sort
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "checked mul VC should have Bool-sorted args for overflow flag");

        // SMT output must declare BitVec(64) state variables
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(_ BitVec 64)"),
            "checked u64 mul should declare BV64 state variables: {}...",
            &smt[..smt.len().min(500)]
        );

        // Semantic: checked mul produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_checked_mul");
        // Same pattern as checked_add: overflowing_mul flows through state-variable
        // sorts, not as BvMul in constraint bodies. Not comes from SwitchInt scaffold.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_mul",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not (SwitchInt branch guard)",
        );
    });
}

// =============================================================================
// Unary Not (multi-block sources to force transition rules)
// =============================================================================

/// Bool NOT uses branching to guarantee multi-BB MIR with transition constraints.
/// Single-block `!x` would produce only an init rule (Return terminator emits no
/// successor rule), so we force SwitchInt via `if` to exercise the negation path.
const UNARY_NOT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_bool_not(x: bool) -> bool {
        if x { !x } else { true }
    }

    pub fn probe_bitwise_not(a: u32) -> u32 {
        if a > 0 { !a } else { 0 }
    }
"#;

/// Bool NOT generates a VC with logical negation (not) in branch guard constraints.
#[test]
fn test_bool_not_generates_vc() {
    with_test_ay_ctx_for_source(UNARY_NOT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_not");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_not", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bool_not", body.blocks.len());

        // Semantic: the SwitchInt on a bool produces (not ...) guard constraints
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(not "),
            "bool NOT with branch should encode (not ...) in CHC output: {}...",
            &smt[..smt.len().min(500)]
        );
        // Relations must have Bool sort for the bool input/output
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "bool NOT VC should have Bool-sorted relation args");

        // Semantic: bool NOT produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_bool_not");
        // Semantic: branch guard uses Not for bool negation
        assert_rule_contains_expr_kind(
            &vc,
            "probe_bool_not",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not",
        );
    });
}

/// Bitwise NOT on u32 generates a VC with bvnot in transition constraints.
#[test]
fn test_bitwise_not_generates_vc() {
    with_test_ay_ctx_for_source(UNARY_NOT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bitwise_not");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bitwise_not", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bitwise_not", body.blocks.len());

        // Semantic: bitwise NOT on u32 must produce bvnot in transition constraints
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvnot"),
            "bitwise NOT on u32 should encode bvnot: {}...",
            &smt[..smt.len().min(500)]
        );
        // Must have BV32-sorted relation arguments for u32 state
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 bitwise NOT VC should have BV32-sorted relation args");

        // Semantic: bitwise NOT produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_bitwise_not");
        // Semantic: bitwise NOT produces BvNot expression in constraint tree
        assert_rule_contains_expr_kind(
            &vc,
            "probe_bitwise_not",
            |e| matches!(e.value(), ExprValue::BvNot(_)),
            "BvNot",
        );
    });
}

// =============================================================================
// Unary Neg
// =============================================================================

/// Signed negation uses branching to ensure multi-BB MIR with transition constraints.
const UNARY_NEG_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_neg_i32(x: i32) -> i32 {
        if x > 0 { -x } else { x }
    }

    pub fn probe_neg_f32(x: f32, flag: bool) -> f32 {
        if flag { -x } else { x }
    }

    pub fn probe_neg_f64(x: f64, flag: bool) -> f64 {
        if flag { -x } else { x }
    }
"#;

/// Signed negation generates a VC with bvneg in transition constraints.
#[test]
fn test_neg_i32_generates_vc() {
    with_test_ay_ctx_for_source(UNARY_NEG_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_neg_i32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_neg_i32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_neg_i32", body.blocks.len());

        // Semantic: i32 negation produces bvneg in the CHC transition constraints
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvneg"),
            "i32 negation should encode bvneg: {}...",
            &smt[..smt.len().min(500)]
        );
        // BV32-sorted relations for i32 state variables
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "i32 negation VC should have BV32-sorted relation args");

        // Semantic: negation produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_neg_i32");
        // Semantic: i32 negation produces BvNeg expression in constraint tree
        assert_rule_contains_expr_kind(
            &vc,
            "probe_neg_i32",
            |e| matches!(e.value(), ExprValue::BvNeg(_)),
            "BvNeg",
        );
    });
}

fn assert_float_neg_uses_bvxor(fn_name: &str, expected_width: u32) {
    with_test_ay_ctx_for_source(UNARY_NEG_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let has_expected_bv = vc
            .relations
            .iter()
            .any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(expected_width)));
        assert!(has_expected_bv, "{fn_name} should have BV{expected_width}-sorted relation args");

        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "{fn_name} should have Bool-sorted relation args for the branch flag");

        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |e| matches!(e.value(), ExprValue::BvXor(_, _)),
            "BvXor",
        );

        let has_bvneg = vc.rules.iter().any(|rule| {
            let in_body = rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::BvNeg(_)))
            });
            let in_head = rule.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| matches!(e.value(), ExprValue::BvNeg(_)))
            });
            in_body || in_head
        });
        assert!(!has_bvneg, "{fn_name} should encode float negation without bvneg");
    });
}

#[test]
fn test_neg_f32_generates_bvxor_vc() {
    assert_float_neg_uses_bvxor("probe_neg_f32", 32);
}

#[test]
fn test_neg_f64_generates_bvxor_vc() {
    assert_float_neg_uses_bvxor("probe_neg_f64", 64);
}

// =============================================================================
// Cast: widening and truncation
// =============================================================================

/// Cast sources use branching to guarantee multi-BB MIR with transition constraints.
/// Single-block casts produce only init + Return (no transition rules containing
/// the cast operation), so we force SwitchInt control flow around the cast.
const CAST_WIDEN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_u8_to_u32(x: u8, flag: bool) -> u32 {
        if flag { x as u32 } else { 0 }
    }

    pub fn probe_i8_to_i32(x: i8, flag: bool) -> i32 {
        if flag { x as i32 } else { 0 }
    }

    pub fn probe_u32_to_u8(x: u32, flag: bool) -> u8 {
        if flag { x as u8 } else { 0 }
    }
"#;

/// Zero-extending cast (u8 -> u32) generates a VC with zero_extend in transition rules.
#[test]
fn test_cast_u8_to_u32_generates_vc() {
    with_test_ay_ctx_for_source(CAST_WIDEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u8_to_u32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_u8_to_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_u8_to_u32", body.blocks.len());

        // Semantic: u8 -> u32 widening uses zero_extend (24 extra bits)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("zero_extend"),
            "u8->u32 cast should encode zero_extend: {}...",
            &smt[..smt.len().min(500)]
        );
        // Must have BV8 inputs and BV32 outputs in relation sorts
        let has_bv8 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(8)));
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv8, "u8->u32 cast VC should have BV8-sorted relation args");
        assert!(has_bv32, "u8->u32 cast VC should have BV32-sorted relation args");

        // Semantic: zero-extension produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_u8_to_u32");
        // Semantic: zero-extension produces BvZeroExtend in constraint tree
        assert_rule_contains_expr_kind(
            &vc,
            "probe_u8_to_u32",
            |e| matches!(e.value(), ExprValue::BvZeroExtend { .. }),
            "BvZeroExtend",
        );
    });
}

/// Sign-extending cast (i8 -> i32) generates a VC with sign_extend in transition rules.
#[test]
fn test_cast_i8_to_i32_generates_vc() {
    with_test_ay_ctx_for_source(CAST_WIDEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_i8_to_i32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_i8_to_i32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_i8_to_i32", body.blocks.len());

        // Semantic: i8 -> i32 widening uses sign_extend (24 extra bits)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("sign_extend"),
            "i8->i32 cast should encode sign_extend: {}...",
            &smt[..smt.len().min(500)]
        );

        // Semantic: sign-extension produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_i8_to_i32");
        // Semantic: sign-extension produces BvSignExtend in constraint tree
        assert_rule_contains_expr_kind(
            &vc,
            "probe_i8_to_i32",
            |e| matches!(e.value(), ExprValue::BvSignExtend { .. }),
            "BvSignExtend",
        );
    });
}

/// Truncating cast (u32 -> u8) generates a VC with extract in transition rules.
#[test]
fn test_cast_u32_to_u8_generates_vc() {
    with_test_ay_ctx_for_source(CAST_WIDEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u32_to_u8");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_u32_to_u8", ChcConfig::default());

        assert_vc_structure(&vc, "probe_u32_to_u8", body.blocks.len());

        // Semantic: u32 -> u8 truncation uses extract to keep low 8 bits
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("extract"),
            "u32->u8 truncation should encode extract: {}...",
            &smt[..smt.len().min(500)]
        );

        // Semantic: truncation produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_u32_to_u8");
        // Semantic: truncation produces BvExtract in constraint tree
        assert_rule_contains_expr_kind(
            &vc,
            "probe_u32_to_u8",
            |e| matches!(e.value(), ExprValue::BvExtract { .. }),
            "BvExtract",
        );
    });
}

// =============================================================================
// Cast: bool conversions (with branching for multi-BB MIR)
// =============================================================================

const CAST_BOOL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_bool_to_u32(x: bool, flag: bool) -> u32 {
        if flag { x as u32 } else { 0 }
    }
"#;

/// Bool-to-bitvec cast generates a VC with ite (if-then-else) for bool-to-BV conversion.
#[test]
fn test_cast_bool_to_u32_generates_vc() {
    with_test_ay_ctx_for_source(CAST_BOOL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_to_u32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_to_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bool_to_u32", body.blocks.len());

        // Semantic: bool -> u32 uses ite(bool, #b1, #b0) then zero_extend
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("ite"),
            "bool->u32 cast should encode ite for bool-to-bitvec: {}...",
            &smt[..smt.len().min(500)]
        );
        // Relations must have Bool sort (for bool input) and BV32 sort (for u32 output)
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bool, "bool->u32 cast VC should have Bool-sorted relation args");
        assert!(has_bv32, "bool->u32 cast VC should have BV32-sorted relation args");

        // Semantic: bool-to-bitvec cast produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_bool_to_u32");
        // Semantic: bool-to-bitvec cast uses Ite for conditional conversion
        assert_rule_contains_expr_kind(
            &vc,
            "probe_bool_to_u32",
            |e| matches!(e.value(), ExprValue::Ite { .. }),
            "Ite",
        );
    });
}

// =============================================================================
// Combined checked arithmetic with branching
// =============================================================================

const CHECKED_ADD_BRANCH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add_branch(a: u32, b: u32) -> u32 {
        match a.checked_add(b) {
            Some(result) => result,
            None => 0,
        }
    }
"#;

/// Checked add with match on overflow generates a VC with BV32 state and SwitchInt branches.
#[test]
fn test_checked_add_branch_generates_vc() {
    with_test_ay_ctx_for_source(CHECKED_ADD_BRANCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_branch");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add_branch", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_add_branch", body.blocks.len());

        // Semantic: relations must carry BV32 for u32 operands and result
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "checked_add branch VC should have BV32-sorted relation args");

        // The match on Some/None produces multiple transition rules (>= 3:
        // init + checked binop BB + at least 2 branch arms for Some/None)
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 3,
            "checked_add with match should produce >= 3 transition rules \
             (checked binop + Some arm + None arm), got {transition_rules}"
        );

        // Transition rules should have non-empty constraints encoding the branch conditions
        let constrained_transitions = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_transitions >= 2,
            "checked_add branch should have >= 2 constrained transition rules \
             (branch guard constraints), got {constrained_transitions}"
        );

        // Semantic: checked_add with branch produces non-trivial transition constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_checked_add_branch");
        // Same pattern as checked_add above: arithmetic flows through state-variable
        // sorts. Not comes from SwitchInt scaffold.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_add_branch",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not (SwitchInt branch guard)",
        );

        // Semantic: checked_add produces BvAdd in constraint tree for the addition itself
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_add_branch",
            |e| matches!(e.value(), ExprValue::BvAdd(_, _)),
            "BvAdd (checked addition arithmetic)",
        );

        // Semantic: Bool sort present for the overflow discriminant from checked_add
        assert_relation_has_arg_sort(
            &vc,
            "probe_checked_add_branch",
            ay_bindings::Sort::is_bool,
            "Bool (overflow flag from checked_add)",
        );
    });
}

// =============================================================================
// Unsigned remainder simplification
// =============================================================================

const UNSIGNED_REM_POW2_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_unsigned_rem_pow2(a: u32, flag: bool) -> u32 {
        if flag { a % 8 } else { a }
    }
"#;

#[test]
fn test_unsigned_rem_power_of_two_uses_bitmask() {
    with_test_ay_ctx_for_source(UNSIGNED_REM_POW2_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsigned_rem_pow2");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_unsigned_rem_pow2", ChcConfig::default());

        assert_vc_structure(&vc, "probe_unsigned_rem_pow2", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_unsigned_rem_pow2");

        assert_rule_contains_expr_kind(
            &vc,
            "probe_unsigned_rem_pow2",
            |e| {
                matches!(
                    e.value(),
                    ExprValue::BvAnd(_, rhs)
                        if matches!(
                            rhs.value(),
                            ExprValue::BitVecConst { value, width }
                                if *value == 7u8.into() && *width == 32
                        )
                )
            },
            "BvAnd(_, 7)",
        );

        let has_bvurem = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| matches!(e.value(), ExprValue::BvURem(_, _)))
            }) || rule.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| matches!(e.value(), ExprValue::BvURem(_, _)))
            })
        });
        assert!(!has_bvurem, "unsigned `% 8` should lower without bvurem");
    });
}

// =============================================================================
// translate_cast: fallback counter for unsupported sort/width combinations
// Part of #2783: ensure record_fallback() sites have dedicated tests.
// =============================================================================

/// translate_cast increments fallback_count when the source expression has
/// a sort that cannot be meaningfully cast (Real, Array, Datatype sorts).
///
/// Production site: codegen_stmt_arithmetic_ops.rs line 388 — `self.record_fallback()`
/// in the catch-all arm of the (src_sort, target_width) match.
#[test]
fn test_translate_cast_unsupported_sort_increments_fallback_counter() {
    // Use a function with a cast so we get a valid ChcCtx with locals,
    // then inject a Real-sort state var to force the unsupported-sort fallback.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cast_fallback(x: u8, flag: bool) -> u32 {
            if flag { x as u32 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cast_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the Cast rvalue to get the target type and source operand
        let mut cast_info = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _lhs,
                    rustc_public::mir::Rvalue::Cast(_, operand, target_ty),
                ) = &stmt.kind
                {
                    cast_info = Some((operand.clone(), *target_ty));
                    break;
                }
            }
            if cast_info.is_some() {
                break;
            }
        }
        let (operand, target_ty) = cast_info.expect("expected Cast rvalue in MIR");

        // Inject a Real-sort expression for the source operand's local.
        // This simulates a scenario where the operand resolves to an unsupported
        // sort (e.g., from BigRational or a pass-through from an unknown type).
        if let Operand::Copy(ref place) | Operand::Move(ref place) = operand {
            let local = place.local;
            if let Some(vec_idx) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local).copied() {
                // Replace the state var sort with Real
                let name = chc_ctx.state_var_mgr.state_vars[vec_idx].0.clone();
                chc_ctx.state_var_mgr.state_vars[vec_idx] =
                    (name.clone(), ay_bindings::Sort::real());
                chc_ctx.state_var_mgr.output_state_vars[vec_idx] =
                    (name, ay_bindings::Sort::real());
            }
        }

        let modified = HashSet::<usize>::new();
        let before = chc_ctx.fallback_count;
        let result = chc_ctx.translate_cast(&operand, target_ty, &modified);
        let after = chc_ctx.fallback_count;

        // translate_cast should still return Some (pass-through) but increment fallback
        assert!(
            result.is_some(),
            "translate_cast with unsupported sort should return Some (pass-through expression)"
        );
        assert!(
            after > before,
            "translate_cast should increment fallback_count for unsupported sort \
             (before={before}, after={after})"
        );
    });
}

/// Negative: translate_cast does NOT increment fallback_count for valid
/// bitvec-to-bitvec casts.
#[test]
fn test_translate_cast_valid_bitvec_does_not_increment_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cast_ok(x: u8, flag: bool) -> u32 {
            if flag { x as u32 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_ok");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cast_ok", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut cast_info = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _lhs,
                    rustc_public::mir::Rvalue::Cast(_, operand, target_ty),
                ) = &stmt.kind
                {
                    cast_info = Some((operand.clone(), *target_ty));
                    break;
                }
            }
            if cast_info.is_some() {
                break;
            }
        }
        let (operand, target_ty) = cast_info.expect("expected Cast rvalue in MIR");
        let modified = HashSet::<usize>::new();

        let before = chc_ctx.fallback_count;
        let result = chc_ctx.translate_cast(&operand, target_ty, &modified);
        let after = chc_ctx.fallback_count;

        assert!(result.is_some(), "translate_cast with valid u8->u32 cast should return Some");
        assert_eq!(
            after, before,
            "translate_cast with valid bitvec cast should NOT increment fallback_count"
        );
    });
}

/// Regression guard (#2876 post-OI4): pointer-wrapper ADTs (NonNull/Box) are
/// translated to pointer-width bitvectors by `translate_ty`, so cast target
/// width inference must not fall back.
#[test]
fn test_translate_cast_pointer_wrapper_targets_use_translate_ty_width() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;

        use alloc::boxed::Box;
        use core::ptr::NonNull;

        pub fn probe_cast_pointer_wrapper_widths(
            x: u8,
            nn: NonNull<u8>,
            bx: Box<[u8]>,
        ) -> u8 {
            let _ = nn;
            let _ = bx;
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_pointer_wrapper_widths");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_cast_pointer_wrapper_widths", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut src_local_u8: Option<usize> = None;
        let mut target_nonnull = None;
        let mut target_box = None;
        for (local_idx, local_decl) in body.local_decls() {
            match local_decl.ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Uint(
                    rustc_public::ty::UintTy::U8,
                )) if src_local_u8.is_none() => {
                    src_local_u8 = Some(local_idx);
                }
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                    if def.trimmed_name() == "NonNull" =>
                {
                    target_nonnull = Some(local_decl.ty);
                }
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                    if def.trimmed_name() == "Box" =>
                {
                    target_box = Some(local_decl.ty);
                }
                _ => {}
            }
        }

        let src_local_u8 = src_local_u8.expect("expected u8 local");
        let target_nonnull = target_nonnull.expect("expected NonNull local type");
        let target_box = target_box.expect("expected Box local type");
        let src_operand = rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: src_local_u8,
            projection: vec![],
        });
        let modified = HashSet::<usize>::new();

        let before = chc_ctx.fallback_count;
        let cast_nonnull = chc_ctx.translate_cast(&src_operand, target_nonnull, &modified);
        let mid = chc_ctx.fallback_count;
        let cast_box = chc_ctx.translate_cast(&src_operand, target_box, &modified);
        let after = chc_ctx.fallback_count;

        assert!(
            cast_nonnull.is_some(),
            "cast to NonNull target should be translated via pointer-width bitvec"
        );
        assert!(
            cast_box.is_some(),
            "cast to Box target should be translated via pointer-width bitvec"
        );
        assert_eq!(
            cast_nonnull.and_then(|e| e.sort().bitvec_width()),
            Some(crate::codegen_ay::types::POINTER_WIDTH)
        );
        assert_eq!(
            cast_box.and_then(|e| e.sort().bitvec_width()),
            Some(crate::codegen_ay::types::POINTER_WIDTH)
        );
        assert_eq!(
            mid, before,
            "cast to NonNull target should not trigger fallback_count increment"
        );
        assert_eq!(after, before, "cast to Box target should not trigger fallback_count increment");
    });
}

/// Regression guard (#4030): `&raw const (*wide_ptr)` must preserve the
/// existing wide BV128 pointer value instead of collapsing to an address-only
/// lane in Mem mode.
#[test]
fn test_translate_addressof_raw_slice_pointer_keeps_wide_bv_width() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cast_raw_slice_pointer(arr: &[u8; 4]) -> *const [u8] {
            let slice: &[u8] = &arr[1..3];
            slice as *const [u8]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cast_raw_slice_pointer");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_cast_raw_slice_pointer", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut addressof_place = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _lhs,
                    rustc_public::mir::Rvalue::AddressOf(_, place),
                ) = &stmt.kind
                    && place.projection.len() == 1
                    && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
                {
                    addressof_place = Some(place.clone());
                    break;
                }
            }
            if addressof_place.is_some() {
                break;
            }
        }

        let place = addressof_place.expect("expected &raw const (*wide_ptr) in MIR");
        let modified = HashSet::<usize>::new();
        let before = chc_ctx.fallback_count;
        let result = chc_ctx
            .translate_ref_or_addressof(&place, true, &modified)
            .expect("wide raw slice pointer AddressOf should translate");
        let after = chc_ctx.fallback_count;

        assert_eq!(
            result.sort().bitvec_width(),
            Some(2 * crate::codegen_ay::types::POINTER_WIDTH),
            "&raw const (*slice_ptr) should stay wide (data + metadata), got {:?}",
            result.sort()
        );
        assert_eq!(
            after, before,
            "wide raw slice pointer AddressOf should not trigger fallback_count increment"
        );
    });
}

/// Regression guard (#3262): repr enum cast extension with known signedness
/// must NOT trigger the signedness fallback counter. Before #3262, all enums
/// had unknown cast signedness, causing fallback. After #3262, `#[repr(u8)]`
/// enums correctly report `Some(false)` (unsigned).
#[test]
fn test_translate_cast_extension_repr_enum_no_signedness_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(u8)]
        enum Tiny {
            A = 1,
            B = 2,
        }

        pub fn probe_enum_cast_extension(flag: bool) -> u32 {
            let e = if flag { Tiny::A } else { Tiny::B };
            e as u32
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_cast_extension");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_enum_cast_extension", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut enum_local = None;
        let mut target_ty = None;
        for (local_idx, local_decl) in body.local_decls() {
            match local_decl.ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                    if def.trimmed_name() == "Tiny" =>
                {
                    enum_local = Some(local_idx);
                }
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Uint(
                    rustc_public::ty::UintTy::U32,
                )) if target_ty.is_none() => {
                    target_ty = Some(local_decl.ty);
                }
                _ => {}
            }
        }
        let operand = Operand::Copy(rustc_public::mir::Place {
            local: enum_local.expect("expected Tiny local in MIR"),
            projection: vec![],
        });
        let target_ty = target_ty.expect("expected u32 local type");

        // Force the enum source local expression to BV8 so translate_cast takes
        // the extension path (BV8 -> BV32). Signedness is now known (unsigned)
        // thanks to #3262 enum repr awareness.
        if let Operand::Copy(ref place) | Operand::Move(ref place) = operand {
            let local = place.local;
            if let Some(vec_idx) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local).copied() {
                let name = chc_ctx.state_var_mgr.state_vars[vec_idx].0.clone();
                let bv8 = ay_bindings::Sort::bitvec(8);
                chc_ctx.state_var_mgr.state_vars[vec_idx] = (name.clone(), bv8.clone());
                chc_ctx.state_var_mgr.output_state_vars[vec_idx] = (name, bv8);
            }
        }

        // #3262: repr enums now have known signedness — should be Some(false) for #[repr(u8)]
        assert_eq!(
            chc_ctx.operand_signedness_for_cast(&operand),
            Some(false),
            "#[repr(u8)] enum should have known unsigned cast signedness after #3262"
        );
        let sf_before = crate::codegen_ay::shared::get_signedness_fallback_count();
        let modified = HashSet::<usize>::new();
        let cast = chc_ctx.translate_cast(&operand, target_ty, &modified);
        let sf_after = crate::codegen_ay::shared::get_signedness_fallback_count();

        assert!(cast.is_some(), "enum cast extension should produce an expression");
        assert_eq!(
            cast.and_then(|expr| expr.sort().bitvec_width()),
            Some(32),
            "enum cast extension should produce BV32 after widening"
        );
        assert_eq!(
            sf_after, sf_before,
            "repr enum cast with known signedness must NOT increment signedness fallback counter"
        );
    });
}

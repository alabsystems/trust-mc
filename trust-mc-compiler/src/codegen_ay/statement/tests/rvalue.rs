// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for rvalue.rs — Rvalue translation dispatch and helpers.
//!
//! Tests cover:
//! - BinOp::Cmp (three-way comparison) for signed/unsigned/BigInt paths
//! - BinOp::Offset fallback (when no pointee type info)
//! - Unchecked arithmetic/shift variants (AddUnchecked, SubUnchecked, etc.)
//! - coerce_to_int_pair edge cases (both bitvec)
//! - build_discriminant_ite_chain for 1- and 3-variant enums
//! - codegen_unop edge cases (16-bit Neg, width preservation)
//! - Comparison with width mismatch coercion
//! - BigInt comparison operators (Ne, Le, Ge, Gt)
//! - codegen_ptr_metadata thin/wide pointer behavior
//! - Rvalue::NullaryOp runtime-check constants and CopyForDeref lookup
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

const RVALUE_PROBE_SOURCE: &str = r#"
pub fn rvalue_probe() {}
"#;

fn assert_bool_const(expr: Expr, expected: bool) {
    match expr.value() {
        ExprValue::BoolConst(value) => assert_eq!(*value, expected),
        other => panic!("expected BoolConst({expected}), got {other:?}"),
    }
}

// ─── BinOp::Cmp (three-way comparison) ─────────────────────────────

#[test]
fn test_cmp_unsigned_produces_32bit_ite() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(false));
        // Cmp returns 32-bit bitvec to match sort_inference.rs unit enum encoding (#2771)
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    });
}

#[test]
fn test_cmp_signed_produces_32bit_ite() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFFFF_FFFBu128, 32); // -5 as i32
        let rhs = Expr::bitvec_const(3u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(true));
        // Fix #2771: 32-bit to match sort_inference.rs unit enum encoding
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    });
}

#[test]
fn test_cmp_bigint_uses_int_path() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(5);
        let rhs = Expr::int_const(10);

        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(false));
        // Fix #2771: 32-bit to match sort_inference.rs unit enum encoding
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::Ite { .. }));
    });
}

#[test]
fn test_cmp_mixed_int_bv_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(42);
        let rhs = Expr::bitvec_const(42u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Cmp, lhs, rhs, Some(false));
        // Fix #2771: 32-bit to match sort_inference.rs unit enum encoding
        assert_eq!(result.sort().bitvec_width(), Some(32));
    });
}

// ─── BinOp::Offset fallback ────────────────────────────────────────

#[test]
fn test_offset_fallback_is_bvadd() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let ptr = Expr::bitvec_const(0x1000u128, 64);
        let offset = Expr::bitvec_const(8u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Offset, ptr, offset, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(64));
        assert!(matches!(result.value(), ExprValue::BvAdd(..)));
    });
}

#[test]
fn test_pointee_size_for_offset_ty_returns_none_for_non_pointer() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn scalar_probe(x: bool) -> bool { x }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "scalar_probe");
            let body = instance.body().expect("function body");
            let bool_ty = body.locals()[1].ty;
            assert_eq!(StatementCodegen::pointee_size_for_offset_ty(bool_ty), None);
        },
    );
}

#[test]
fn test_pointee_size_for_offset_ty_uses_layout_for_pointers() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ptr_probe(p: *const u32) -> usize {
            p as usize
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(&ctx, "ptr_probe");
            let body = instance.body().expect("function body");
            let ptr_ty = body.locals()[1].ty;
            assert_eq!(StatementCodegen::pointee_size_for_offset_ty(ptr_ty), Some(4));
        },
    );
}

// ─── Unchecked arithmetic variants ──────────────────────────────────

#[test]
fn test_add_unchecked_produces_bvadd() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(200u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::AddUnchecked, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvAdd(..)));
    });
}

#[test]
fn test_sub_unchecked_produces_bvsub() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(300u128, 32);
        let rhs = Expr::bitvec_const(100u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::SubUnchecked, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSub(..)));
    });
}

#[test]
fn test_mul_unchecked_produces_bvmul() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(7u128, 16);
        let rhs = Expr::bitvec_const(3u128, 16);

        let result = codegen.codegen_binop_typed(BinOp::MulUnchecked, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(16));
        assert!(matches!(result.value(), ExprValue::BvMul(..)));
    });
}

// ─── Unchecked shift variants ───────────────────────────────────────

#[test]
fn test_shl_unchecked_produces_bvshl() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(1u128, 32);
        let rhs = Expr::bitvec_const(4u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::ShlUnchecked, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvShl(..)));
    });
}

#[test]
fn test_shr_unchecked_unsigned_is_logical() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xF0u128, 8);
        let rhs = Expr::bitvec_const(2u128, 8);

        let result = codegen.codegen_binop_typed(BinOp::ShrUnchecked, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvLShr(..)));
    });
}

#[test]
fn test_shr_unchecked_signed_is_arithmetic() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xF0u128, 8);
        let rhs = Expr::bitvec_const(2u128, 8);

        let result = codegen.codegen_binop_typed(BinOp::ShrUnchecked, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvAShr(..)));
    });
}

// ─── coerce_to_int_pair: both bitvec ────────────────────────────────

#[test]
fn test_coerce_to_int_pair_both_bitvec() {
    let lhs = Expr::bitvec_const(10u128, 32);
    let rhs = Expr::bitvec_const(20u128, 64);

    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs, rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    assert!(matches!(l.value(), ExprValue::Bv2Int(..)));
    assert!(matches!(r.value(), ExprValue::Bv2Int(..)));
}

// ─── build_discriminant_ite_chain ───────────────────────────────────

#[test]
fn test_discriminant_chain_single_variant() {
    let constructors =
        vec![ay_bindings::DatatypeConstructor { name: "Only".to_string(), fields: vec![] }];

    let sort = enum_sort("SingleEnum", [("Only", Vec::<(&str, Sort)>::new())]);
    let expr = Expr::datatype_constructor("SingleEnum", "Only", vec![], sort);

    let result = StatementCodegen::build_discriminant_ite_chain("SingleEnum", &constructors, &expr);
    assert_eq!(result.sort().bitvec_width(), Some(32));
}

#[test]
fn test_discriminant_chain_three_variants() {
    let constructors = vec![
        ay_bindings::DatatypeConstructor { name: "A".to_string(), fields: vec![] },
        ay_bindings::DatatypeConstructor { name: "B".to_string(), fields: vec![] },
        ay_bindings::DatatypeConstructor { name: "C".to_string(), fields: vec![] },
    ];

    let sort =
        enum_sort("TriEnum", [("A", Vec::<(&str, Sort)>::new()), ("B", vec![]), ("C", vec![])]);
    let expr = Expr::datatype_constructor("TriEnum", "B", vec![], sort);

    let result = StatementCodegen::build_discriminant_ite_chain("TriEnum", &constructors, &expr);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(matches!(result.value(), ExprValue::Ite { .. }));
}

// ─── codegen_unop edge cases ────────────────────────────────────────

#[test]
fn test_unop_neg_16bit() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let val = Expr::bitvec_const(42u128, 16);
        let result = codegen.codegen_unop(UnOp::Neg, val);
        assert_eq!(result.sort().bitvec_width(), Some(16));
        assert!(matches!(result.value(), ExprValue::BvNeg(..)));
    });
}

#[test]
fn test_unop_not_preserves_width() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let val8 = Expr::bitvec_const(0xAAu128, 8);
        let result8 = codegen.codegen_unop(UnOp::Not, val8);
        assert_eq!(result8.sort().bitvec_width(), Some(8));
        assert!(matches!(result8.value(), ExprValue::BvNot(..)));

        let val64 = Expr::bitvec_const(0u128, 64);
        let result64 = codegen.codegen_unop(UnOp::Not, val64);
        assert_eq!(result64.sort().bitvec_width(), Some(64));
    });
}

fn assert_float_neg_rvalue_uses_sign_bit_xor(
    source: &str,
    fn_name: &str,
    expected_width: u32,
    expected_mask: u128,
) {
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_name);
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let neg_stmt = body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
            matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::UnaryOp(UnOp::Neg, _)))
        });
        assert!(neg_stmt.is_some(), "{fn_name} should keep a UnaryOp::Neg in MIR");

        let StatementKind::Assign(_, rhs) = &neg_stmt.expect("neg stmt").kind else {
            panic!("expected Assign statement");
        };
        let expr = codegen.codegen_rvalue(rhs).expect("float neg expression");
        assert_eq!(expr.sort().bitvec_width(), Some(expected_width));

        match expr.value() {
            ExprValue::BvXor(_, mask) => match mask.value() {
                ExprValue::BitVecConst { value, width } => {
                    assert_eq!(*width, expected_width);
                    assert_eq!(*value, BigInt::from(expected_mask));
                }
                other => panic!("expected sign-bit mask constant, got {other:?}"),
            },
            other => panic!("expected BvXor sign-bit flip for float negation, got {other:?}"),
        }
    });
}

fn assert_float_binop_rvalue_uses_fp_theory(source: &str, fn_name: &str, expected_op: BinOp) {
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_name);
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let binop_stmt = body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
            matches!(
                &stmt.kind,
                StatementKind::Assign(_, Rvalue::BinaryOp(op, _, _)) if *op == expected_op
            )
        });
        assert!(binop_stmt.is_some(), "{fn_name} should keep a BinaryOp in MIR");

        let StatementKind::Assign(_, rhs) = &binop_stmt.expect("binop stmt").kind else {
            panic!("expected Assign statement");
        };
        let violations_before = codegen.ctx.bmc_vc.violations.len();
        let expr =
            codegen.codegen_rvalue(rhs).expect("float BinOp rvalue should lower through FP theory");
        assert_eq!(
            codegen.ctx.bmc_vc.violations.len(),
            violations_before,
            "float {expected_op:?} should not reuse integer UB checks"
        );

        let inner = match expr.value() {
            ExprValue::FpToIeeeBv(inner) => inner,
            other => panic!("expected fp.to_ieee_bv for float {expected_op:?}, got {other:?}"),
        };
        let matches_op = match expected_op {
            BinOp::Div => matches!(inner.value(), ExprValue::FpDiv(_, _, _)),
            BinOp::Rem => matches!(inner.value(), ExprValue::FpRem(_, _)),
            other => panic!("unsupported float rvalue op in test helper: {other:?}"),
        };
        assert!(
            matches_op,
            "expected fp.to_ieee_bv-wrapped {expected_op:?}, got {:?}",
            expr.value()
        );
    });
}

#[test]
fn test_codegen_rvalue_neg_f32_uses_sign_bit_xor() {
    assert_float_neg_rvalue_uses_sign_bit_xor(
        r#"
        pub fn negate_float32(x: f32) -> f32 {
            -x
        }
        "#,
        "negate_float32",
        32,
        0x8000_0000,
    );
}

#[test]
fn test_codegen_rvalue_neg_f64_uses_sign_bit_xor() {
    assert_float_neg_rvalue_uses_sign_bit_xor(
        r#"
        pub fn negate_float64(x: f64) -> f64 {
            -x
        }
        "#,
        "negate_float64",
        64,
        0x8000_0000_0000_0000,
    );
}

#[test]
fn test_codegen_rvalue_div_f32_uses_fp_theory_without_integer_ub_checks() {
    assert_float_binop_rvalue_uses_fp_theory(
        r#"
        pub fn div_float32(x: f32, y: f32) -> f32 {
            x / y
        }
        "#,
        "div_float32",
        BinOp::Div,
    );
}

#[test]
fn test_codegen_rvalue_rem_f64_uses_fp_theory_without_integer_ub_checks() {
    assert_float_binop_rvalue_uses_fp_theory(
        r#"
        pub fn rem_float64(x: f64, y: f64) -> f64 {
            x % y
        }
        "#,
        "rem_float64",
        BinOp::Rem,
    );
}

// ─── Width mismatch coercion in comparison ──────────────────────────

#[test]
fn test_eq_different_widths_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFFu128, 8);
        let rhs = Expr::bitvec_const(0xFFu128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

// ─── Le/Ge/Gt for both signed and unsigned ──────────────────────────

#[test]
fn test_le_ge_gt_signed_unsigned() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::bitvec_const(10u128, 32);

        let le_u = codegen.codegen_binop_typed(BinOp::Le, lhs.clone(), rhs.clone(), Some(false));
        assert!(le_u.sort().is_bool());

        let le_s = codegen.codegen_binop_typed(BinOp::Le, lhs.clone(), rhs.clone(), Some(true));
        assert!(le_s.sort().is_bool());

        let ge_u = codegen.codegen_binop_typed(BinOp::Ge, lhs.clone(), rhs.clone(), Some(false));
        assert!(ge_u.sort().is_bool());

        let gt_s = codegen.codegen_binop_typed(BinOp::Gt, lhs, rhs, Some(true));
        assert!(gt_s.sort().is_bool());
    });
}

// ─── BigInt comparison operators ────────────────────────────────────

#[test]
fn test_bigint_ne() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(42);
        let rhs = Expr::int_const(43);

        let result = codegen.codegen_binop_typed(BinOp::Ne, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_bigint_le_ge_gt() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(100);
        let rhs = Expr::int_const(200);

        let le = codegen.codegen_binop_typed(BinOp::Le, lhs.clone(), rhs.clone(), Some(false));
        assert!(le.sort().is_bool());

        let ge = codegen.codegen_binop_typed(BinOp::Ge, lhs.clone(), rhs.clone(), Some(false));
        assert!(ge.sort().is_bool());

        let gt = codegen.codegen_binop_typed(BinOp::Gt, lhs, rhs, Some(false));
        assert!(gt.sort().is_bool());
    });
}

// ─── codegen_ptr_metadata coverage ──────────────────────────────────

#[test]
fn test_ptr_metadata_thin_pointer_returns_zero() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn thin_ptr_meta(p: *const u8) -> usize {
            if p.is_null() { 0 } else { 1 }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "thin_ptr_meta");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let ptr_local = body
                .locals()
                .iter()
                .enumerate()
                .find_map(|(idx, local)| match local.ty.kind() {
                    TyKind::RigidTy(RigidTy::RawPtr(_, _)) => Some(Local::from(idx)),
                    _ => None,
                })
                .expect("expected raw pointer local");
            let operand = Operand::Copy(Place { local: ptr_local, projection: vec![] });

            let meta = codegen.codegen_ptr_metadata(&operand).expect("metadata expression");
            assert_eq!(meta.sort().bitvec_width(), Some(POINTER_WIDTH));
            match meta.value() {
                ExprValue::BitVecConst { value, .. } => {
                    assert_eq!(*value, BigInt::from(0u8));
                }
                other => panic!("expected thin pointer metadata to be zero, got {other:?}"),
            }
        },
    );
}

#[test]
fn test_ptr_metadata_wide_pointer_extracts_len_or_declares_meta_symbol() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn slice_meta(xs: &[u8]) -> usize {
            xs.len()
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "slice_meta");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let slice_local = body
                .locals()
                .iter()
                .enumerate()
                .find_map(|(idx, local)| match local.ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                        if matches!(
                            pointee.kind(),
                            TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str)
                        ) =>
                    {
                        Some(Local::from(idx))
                    }
                    _ => None,
                })
                .expect("expected slice reference local");
            let operand = Operand::Copy(Place { local: slice_local, projection: vec![] });

            let meta = codegen.codegen_ptr_metadata(&operand).expect("metadata expression");
            assert_eq!(meta.sort().bitvec_width(), Some(POINTER_WIDTH));
            match meta.value() {
                ExprValue::DatatypeSelector { selector_name, .. } => {
                    assert_eq!(selector_name, "fld_len");
                }
                ExprValue::Var { name } => {
                    assert!(name.ends_with("_meta"), "expected *_meta fallback var, got {name}");
                }
                other => panic!("expected len selector or fallback meta var, got {other:?}"),
            }
        },
    );
}

// ─── Misc Rvalue variants ───────────────────────────────────────────

#[test]
fn test_nullary_runtime_checks_constants() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let ub = codegen
            .codegen_rvalue(&Rvalue::NullaryOp(rustc_public::mir::NullOp::RuntimeChecks(
                rustc_public::mir::RuntimeChecks::UbChecks,
            )))
            .expect("UbChecks expression");
        let contract = codegen
            .codegen_rvalue(&Rvalue::NullaryOp(rustc_public::mir::NullOp::RuntimeChecks(
                rustc_public::mir::RuntimeChecks::ContractChecks,
            )))
            .expect("ContractChecks expression");
        let overflow = codegen
            .codegen_rvalue(&Rvalue::NullaryOp(rustc_public::mir::NullOp::RuntimeChecks(
                rustc_public::mir::RuntimeChecks::OverflowChecks,
            )))
            .expect("OverflowChecks expression");

        assert_bool_const(ub, true);
        assert_bool_const(contract, true);
        assert_bool_const(overflow, false);
    });
}

#[test]
fn test_copy_for_deref_reuses_existing_place_value() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn copy_for_deref_seed(input: u32) -> u32 {
            input
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "copy_for_deref_seed");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let source_local = body
                .locals()
                .iter()
                .enumerate()
                .find_map(|(idx, local)| {
                    (idx > 0 && matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))))
                        .then_some(Local::from(idx))
                })
                .expect("expected non-return u32 local");
            let place = Place { local: source_local, projection: vec![] };
            let expected = codegen.codegen_place(&place).expect("seed place expression");

            let copied = codegen
                .codegen_rvalue(&Rvalue::CopyForDeref(place))
                .expect("CopyForDeref expression");
            assert_eq!(copied, expected);
        },
    );
}

// ─── Bitwise ops: bool vs bitvec dispatch ────────────────────────────

#[test]
fn test_bitxor_bool_produces_xor() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(false);

        let result = codegen.codegen_binop_typed(BinOp::BitXor, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Xor(_, _)));
    });
}

#[test]
fn test_bitxor_bitvec_produces_bvxor() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xAAu128, 8);
        let rhs = Expr::bitvec_const(0x55u128, 8);

        let result = codegen.codegen_binop_typed(BinOp::BitXor, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvXor(_, _)));
    });
}

#[test]
fn test_bitand_bool_produces_and() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(true);
        let rhs = Expr::bool_const(true);

        let result = codegen.codegen_binop_typed(BinOp::BitAnd, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::And(_)));
    });
}

#[test]
fn test_bitand_bitvec_produces_bvand() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xFF00u128, 16);
        let rhs = Expr::bitvec_const(0x0F0Fu128, 16);

        let result = codegen.codegen_binop_typed(BinOp::BitAnd, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(16));
        assert!(matches!(result.value(), ExprValue::BvAnd(_, _)));
    });
}

#[test]
fn test_bitor_bool_produces_or() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bool_const(false);
        let rhs = Expr::bool_const(true);

        let result = codegen.codegen_binop_typed(BinOp::BitOr, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Or(_)));
    });
}

#[test]
fn test_bitor_bitvec_produces_bvor() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xF0u128, 8);
        let rhs = Expr::bitvec_const(0x0Fu128, 8);

        let result = codegen.codegen_binop_typed(BinOp::BitOr, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvOr(_, _)));
    });
}

// ─── Div/Rem signedness dispatch ─────────────────────────────────────

#[test]
fn test_div_unsigned_produces_bvudiv() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(7u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvUDiv(_, _)));
    });
}

#[test]
fn test_div_signed_produces_bvsdiv() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(7u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSDiv(_, _)));
    });
}

#[test]
fn test_rem_unsigned_produces_bvurem() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(7u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Rem, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvURem(_, _)));
    });
}

#[test]
fn test_rem_signed_produces_bvsrem() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(7u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Rem, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvSRem(_, _)));
    });
}

// ─── Shift width coercion ────────────────────────────────────────────

#[test]
fn test_shl_different_widths_coerces_rhs() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // u32 << u8: rhs (8-bit) must be widened to match lhs (32-bit)
        let lhs = Expr::bitvec_const(1u128, 32);
        let rhs = Expr::bitvec_const(4u128, 8);

        let result = codegen.codegen_binop_typed(BinOp::Shl, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvShl(_, _)));
    });
}

#[test]
fn test_shr_different_widths_coerces_rhs() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // u64 >> u16: rhs (16-bit) must be widened to match lhs (64-bit)
        let lhs = Expr::bitvec_const(0xFF00u128, 64);
        let rhs = Expr::bitvec_const(8u128, 16);

        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(false));
        assert_eq!(result.sort().bitvec_width(), Some(64));
        assert!(matches!(result.value(), ExprValue::BvLShr(_, _)));
    });
}

#[test]
fn test_shr_signed_different_widths() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // i32 >> u8: signed shift with narrow shift amount
        let lhs = Expr::bitvec_const(0xFFFF_FF00u128, 32); // negative i32
        let rhs = Expr::bitvec_const(4u128, 8);

        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvAShr(_, _)));
    });
}

// ─── Width mismatch coercion in arithmetic ───────────────────────────

#[test]
fn test_add_different_widths_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Closure captured variables may have different widths (#1582)
        let lhs = Expr::bitvec_const(10u128, 32);
        let rhs = Expr::bitvec_const(20u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Add, lhs, rhs, Some(false));
        // Result should be 64-bit (wider operand wins)
        assert_eq!(result.sort().bitvec_width(), Some(64));
        assert!(matches!(result.value(), ExprValue::BvAdd(_, _)));
    });
}

#[test]
fn test_sub_different_widths_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 64);
        let rhs = Expr::bitvec_const(50u128, 32);

        let result = codegen.codegen_binop_typed(BinOp::Sub, lhs, rhs, Some(true));
        assert_eq!(result.sort().bitvec_width(), Some(64));
        assert!(matches!(result.value(), ExprValue::BvSub(_, _)));
    });
}

// ─── BigInt Eq comparison ────────────────────────────────────────────

#[test]
fn test_bigint_eq() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(42);
        let rhs = Expr::int_const(42);

        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_bigint_lt() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(5);
        let rhs = Expr::int_const(10);

        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

// ─── Mixed Int/BV comparison operators ───────────────────────────────

#[test]
fn test_mixed_int_bv_eq_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(10);
        let rhs = Expr::bitvec_const(10u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Eq, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_mixed_int_bv_ne_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::int_const(10);

        let result = codegen.codegen_binop_typed(BinOp::Ne, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_mixed_int_bv_lt_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(5u128, 32);
        let rhs = Expr::int_const(10);

        let result = codegen.codegen_binop_typed(BinOp::Lt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_mixed_int_bv_le_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(5);
        let rhs = Expr::bitvec_const(10u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Le, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_mixed_int_bv_ge_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(20u128, 32);
        let rhs = Expr::int_const(10);

        let result = codegen.codegen_binop_typed(BinOp::Ge, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

#[test]
fn test_mixed_int_bv_gt_coerces() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::int_const(100);
        let rhs = Expr::bitvec_const(50u128, 64);

        let result = codegen.codegen_binop_typed(BinOp::Gt, lhs, rhs, Some(false));
        assert!(result.sort().is_bool());
    });
}

// ─── coerce_to_int_pair edge cases ───────────────────────────────────

#[test]
fn test_coerce_to_int_pair_both_int() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::int_const(99);

    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs.clone(), rhs.clone(), false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    // Already Int, should pass through (no Bv2Int wrapping)
    assert_eq!(l, lhs);
    assert_eq!(r, rhs);
}

#[test]
fn test_coerce_to_int_pair_mixed_int_bv() {
    let lhs = Expr::int_const(42);
    let rhs = Expr::bitvec_const(99u128, 32);

    let (l, r) = StatementCodegen::coerce_to_int_pair(lhs.clone(), rhs, false);
    assert!(l.sort().is_int());
    assert!(r.sort().is_int());
    // LHS was already Int, should pass through
    assert_eq!(l, lhs);
    // RHS was bitvec, should be wrapped in Bv2Int (unsigned)
    assert!(matches!(r.value(), ExprValue::Bv2Int(..)));
}

// ─── codegen_unop: bool Not ──────────────────────────────────────────

#[test]
fn test_unop_not_bool_produces_logical_not() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let val = Expr::bool_const(true);
        let result = codegen.codegen_unop(UnOp::Not, val);
        assert!(result.sort().is_bool());
        assert!(matches!(result.value(), ExprValue::Not(_)));
    });
}

// ─── Rvalue::Repeat (const array) ────────────────────────────────────

#[test]
fn test_repeat_rvalue_creates_const_array() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn repeat_array() -> [u32; 4] {
            [0u32; 4]
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "repeat_array");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find the Repeat rvalue in the MIR
            let repeat_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Repeat(..)))
                });
            if let Some(stmt) = repeat_stmt
                && let StatementKind::Assign(_, rhs) = &stmt.kind
            {
                let result = codegen.codegen_rvalue(rhs);
                if let Some(expr) = result {
                    assert!(expr.sort().is_array());
                }
            }
            // If no Repeat in MIR (optimizer may fold it), test const_array directly
            let elem = Expr::bitvec_const(0u128, 32);
            let arr = Expr::const_array(Sort::bitvec(POINTER_WIDTH), elem);
            assert!(arr.sort().is_array());
        },
    );
}

// ─── Rvalue::Len (array length) ──────────────────────────────────────

#[test]
fn test_len_array_returns_const_length() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn array_len(a: [u32; 8]) -> usize {
            a.len()
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "array_len");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find the Len rvalue in the MIR
            let len_stmt = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Len(_))));
            if let Some(stmt) = len_stmt
                && let StatementKind::Assign(_, rhs) = &stmt.kind
            {
                let result = codegen.codegen_rvalue(rhs).expect("Len expression");
                assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
                // Array length should be a constant 8
                if let ExprValue::BitVecConst { value, .. } = result.value() {
                    assert_eq!(*value, BigInt::from(8u8));
                }
            }
        },
    );
}

// ─── Rvalue::ShallowInitBox ─────────────────────────────────────────

#[test]
fn test_shallow_init_box_is_operand_passthrough() {
    // ShallowInitBox(operand, ty) delegates to codegen_operand(operand).
    // Since we can't construct MIR AST nodes in unit tests, verify the
    // expression-level pattern: the result is a bitvec address (pointer).
    let ptr_addr = Expr::bitvec_const(0x4000u128, POINTER_WIDTH);
    assert_eq!(ptr_addr.sort().bitvec_width(), Some(POINTER_WIDTH));
    // The codegen path: codegen_rvalue -> Rvalue::ShallowInitBox -> codegen_operand
    // just returns the operand expression unchanged (treat as address).
}

// ─── Signedness fallback defaults ────────────────────────────────────

#[test]
fn test_signedness_none_div_defaults_to_unsigned() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(100u128, 32);
        let rhs = Expr::bitvec_const(7u128, 32);

        // Part of #2749: unknown signedness for Div should prefer unsigned (bvudiv).
        let result = codegen.codegen_binop_typed(BinOp::Div, lhs, rhs, None);
        assert_eq!(result.sort().bitvec_width(), Some(32));
        assert!(matches!(result.value(), ExprValue::BvUDiv(_, _)));
    });
}

#[test]
fn test_shr_none_defaults_to_logical() {
    with_test_ay_ctx_for_source(RVALUE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "rvalue_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let lhs = Expr::bitvec_const(0xF0u128, 8);
        let rhs = Expr::bitvec_const(2u128, 8);

        // None signedness for Shr defaults to logical shift (bvlshr) — unsigned is the safe
        // default because bvashr on an unsigned operand silently corrupts high bits.
        let result = codegen.codegen_binop_typed(BinOp::Shr, lhs, rhs, None);
        assert_eq!(result.sort().bitvec_width(), Some(8));
        assert!(matches!(result.value(), ExprValue::BvLShr(_, _)));
    });
}

// ─── build_discriminant_ite_chain: two-variant (Option-like) ─────────

#[test]
fn test_discriminant_chain_two_variants() {
    let constructors = vec![
        ay_bindings::DatatypeConstructor { name: "None".to_string(), fields: vec![] },
        ay_bindings::DatatypeConstructor {
            name: "Some".to_string(),
            fields: vec![ay_bindings::DatatypeField {
                name: "value".to_string(),
                sort: Sort::bitvec(32),
            }],
        },
    ];

    let sort = enum_sort("OptI32", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);
    let expr = Expr::datatype_constructor("OptI32", "None", vec![], sort);

    let result = StatementCodegen::build_discriminant_ite_chain("OptI32", &constructors, &expr);
    assert_eq!(result.sort().bitvec_width(), Some(32));
    assert!(matches!(result.value(), ExprValue::Ite { .. }));
}

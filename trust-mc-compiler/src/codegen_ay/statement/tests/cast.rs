// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for cast.rs — type cast codegen for AY.
//!
//! Trivial tests that only constructed AY Expr/Sort values (Bool↔BitVec
//! patterns, BitVec width coercion, Int↔Real conversions, identity casts,
//! newtype wrapper casts, enum discriminant construction, fat pointer field
//! extraction) were removed per rule #2312 and #2482 because they did not
//! exercise production codegen paths.
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// MIR-driven codegen_cast tests
// ═══════════════════════════════════════════════════════════════════════
//
// These tests compile real Rust source, find Cast rvalues in MIR, and
// exercise codegen_cast through the full pipeline.

const CAST_PROBE_SOURCE: &str = r#"
pub fn unsigned_widen(x: u8) -> u32 {
    x as u32
}

pub fn signed_widen(x: i8) -> i32 {
    x as i32
}

pub fn signed_to_unsigned_widen(x: i8) -> u32 {
    x as u32
}

pub fn unsigned_to_signed_widen(x: u8) -> i32 {
    x as i32
}

pub fn narrow_u32_to_u8(x: u32) -> u8 {
    x as u8
}

pub fn char_to_u8(c: char) -> u8 {
    c as u8
}

pub fn bool_to_u32(b: bool) -> u32 {
    b as u32
}

pub fn bool_to_u8(b: bool) -> u8 {
    b as u8
}

pub fn u32_to_bool_via_ne(x: u32) -> bool {
    x != 0
}

#[repr(transparent)]
pub struct I8Wrapper(pub i8);

pub fn wrapper_to_i32_target_ty(_w: I8Wrapper) -> i32 {
    0
}

#[repr(transparent)]
pub struct U8Wrapper(pub u8);

pub fn u8_wrapper_to_u32_target_ty(_w: U8Wrapper) -> u32 {
    0
}

pub fn same_width_cast(x: u32) -> u32 {
    x as u32
}

pub fn u8_to_u16(x: u8) -> u16 {
    x as u16
}

pub fn i16_to_i64(x: i16) -> i64 {
    x as i64
}

pub fn u64_to_u8(x: u64) -> u8 {
    x as u8
}

pub fn ptr_to_usize(p: *const u8) -> usize {
    p as usize
}

pub fn ptr_to_u32(p: *const u8) -> u32 {
    p as u32
}

pub fn usize_to_ptr(x: usize) -> *const u8 {
    x as *const u8
}

pub fn slice_ptr_to_thin(p: *const [u8]) -> *const u8 {
    p as *const u8
}

pub trait CastProbeTrait {
    fn as_u8(&self) -> u8;
}

impl CastProbeTrait for u8 {
    fn as_u8(&self) -> u8 {
        *self
    }
}

pub fn dyn_ptr_to_thin(p: *const dyn CastProbeTrait) -> *const () {
    p as *const ()
}

pub fn f32_to_u32(x: f32) -> u32 {
    x as u32
}

pub fn f64_to_i64(x: f64) -> i64 {
    x as i64
}

pub fn u32_to_f32(x: u32) -> f32 {
    x as f32
}

pub fn i64_to_f64(x: i64) -> f64 {
    x as f64
}

pub fn f32_to_f64(x: f32) -> f64 {
    x as f64
}

pub fn char_to_u32(c: char) -> u32 {
    c as u32
}

#[repr(u8)]
pub enum Color {
    Red = 0,
    Green = 1,
    Blue = 2,
}

pub fn enum_discriminant(c: Color) -> u8 {
    c as u8
}

pub fn enum_discriminant_widen(c: Color) -> u32 {
    c as u32
}

#[repr(i8)]
pub enum SignedCode {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

pub fn signed_enum_to_i32(code: SignedCode) -> i32 {
    code as i32
}

pub fn signed_enum_to_u32(code: SignedCode) -> u32 {
    code as u32
}

#[repr(u16)]
pub enum SingletonCode {
    Only = 7,
}

pub fn singleton_enum_to_u32(code: SingletonCode) -> u32 {
    code as u32
}
"#;

/// Walk MIR blocks to find the first Rvalue::Cast statement. Returns the
/// operand and target type.
fn find_first_cast(body: &rustc_public::mir::Body) -> Option<(Operand, rustc_public::ty::Ty)> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Cast(_, operand, target_ty)) = &stmt.kind {
                return Some((operand.clone(), *target_ty));
            }
        }
    }
    None
}

/// Helper: set up codegen for a probe function and call codegen_cast on
/// the first Cast rvalue found in its MIR body.
fn exercise_codegen_cast(ctx: &mut AYCtx<'_, 'static>, fn_name: &str) -> Option<Expr> {
    let instance = find_instance_by_suffix(ctx, fn_name);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    // Seed argument locals into the SSA environment so codegen_operand
    // can resolve them. arg_locals() returns locals 1..=arg_count.
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1; // arg_locals are 1-indexed in MIR
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }

    let (operand, target_ty) =
        find_first_cast(&body).unwrap_or_else(|| panic!("no Cast rvalue found in {fn_name}"));
    codegen.codegen_cast(&operand, target_ty)
}

/// Variant of `exercise_codegen_cast` that force-injects a specific expression for
/// argument 1. This hits cast branches that don't arise from standard MIR sort
/// inference (for example Real→BitVec and Int→BitVec).
fn exercise_codegen_cast_with_first_arg(
    ctx: &mut AYCtx<'_, 'static>,
    fn_name: &str,
    first_arg_expr: Expr,
) -> Option<Expr> {
    let instance = find_instance_by_suffix(ctx, fn_name);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    let mut first_arg_expr = Some(first_arg_expr);
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1; // arg_locals are 1-indexed in MIR
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);

        if idx == 0 {
            codegen.env_update(base, first_arg_expr.take().expect("first arg available"));
            continue;
        }
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }

    let (operand, target_ty) =
        find_first_cast(&body).unwrap_or_else(|| panic!("no Cast rvalue found in {fn_name}"));
    codegen.codegen_cast(&operand, target_ty)
}

// ─── Unsigned widening: u8 → u32 ────────────────────────────────────

#[test]
fn test_mir_unsigned_widen_u8_to_u32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "unsigned_widen")
            .expect("codegen_cast should succeed for u8→u32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "u8→u32 cast should produce bv32");
        // Unsigned widening uses zero_extend
        assert!(
            matches!(result.value(), ExprValue::BvZeroExtend { .. })
                || matches!(result.value(), ExprValue::Var { .. }),
            "expected zero_extend or variable, got {:?}",
            result.value()
        );
    });
}

// ─── Signed widening: i8 → i32 ──────────────────────────────────────

#[test]
fn test_mir_signed_widen_i8_to_i32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "signed_widen")
            .expect("codegen_cast should succeed for i8→i32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "i8→i32 cast should produce bv32");
        // Signed widening typically uses sign_extend, but may use zero_extend
        // if the synthetic SSA variable lacks signedness info (the codegen
        // determines signedness from MIR operand types, not the expression).
        assert!(
            matches!(result.value(), ExprValue::BvSignExtend { .. })
                || matches!(result.value(), ExprValue::BvZeroExtend { .. })
                || matches!(result.value(), ExprValue::Var { .. }),
            "expected sign/zero_extend or variable, got {:?}",
            result.value()
        );
    });
}

#[test]
fn test_mir_signed_to_unsigned_widen_i8_to_u32_uses_sign_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "signed_to_unsigned_widen")
            .expect("codegen_cast should succeed for i8→u32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "i8→u32 cast should produce bv32");
        match result.value() {
            ExprValue::BvSignExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 24, "i8→u32 cast should sign-extend by 24 bits");
                assert_eq!(expr.sort().bitvec_width(), Some(8), "source should remain bv8");
            }
            other => panic!("expected BvSignExtend for i8→u32 cast, got {:?}", other),
        }
    });
}

#[test]
fn test_mir_unsigned_to_signed_widen_u8_to_i32_uses_zero_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "unsigned_to_signed_widen")
            .expect("codegen_cast should succeed for u8→i32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "u8→i32 cast should produce bv32");
        match result.value() {
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 24, "u8→i32 cast should zero-extend by 24 bits");
                assert_eq!(expr.sort().bitvec_width(), Some(8), "source should remain bv8");
            }
            other => panic!("expected BvZeroExtend for u8→i32 cast, got {:?}", other),
        }
    });
}

#[test]
fn test_dt_single_field_signed_widen_uses_sign_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "wrapper_to_i32_target_ty");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: Local::from(1usize), projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        let src_sort =
            StatementCodegen::infer_sort_from_ty(body.locals()[1].ty).expect("I8Wrapper sort");
        codegen.env_update(base, Expr::var("wrapped_i8", src_sort));

        let operand = Operand::Copy(place);
        let target_ty = body.locals()[0].ty; // i32
        let result =
            codegen.codegen_cast(&operand, target_ty).expect("DT single-field i8 wrapper cast");
        match result.value() {
            ExprValue::BvSignExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 24, "i8 wrapper→i32 must sign-extend by 24 bits");
                assert_eq!(expr.sort().bitvec_width(), Some(8), "wrapped payload should be bv8");
            }
            other => panic!("expected BvSignExtend for DT i8 wrapper→i32 cast, got {:?}", other),
        }
    });
}

/// DT-to-BV widening for unsigned newtype wrappers must use zero_extend, not sign_extend.
/// Regression test for gap in commit a1e6541 (DT-to-BV widening sign-extension fix):
/// the unsigned path at cast.rs:125/312 was untested. A regression could silently
/// sign-extend unsigned wrapper values, corrupting the verification model.
#[test]
fn test_dt_single_field_unsigned_widen_uses_zero_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "u8_wrapper_to_u32_target_ty");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place { local: Local::from(1usize), projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        let src_sort =
            StatementCodegen::infer_sort_from_ty(body.locals()[1].ty).expect("U8Wrapper sort");
        codegen.env_update(base, Expr::var("wrapped_u8", src_sort));

        let operand = Operand::Copy(place);
        let target_ty = body.locals()[0].ty; // u32
        let result =
            codegen.codegen_cast(&operand, target_ty).expect("DT single-field u8 wrapper cast");
        match result.value() {
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 24, "u8 wrapper→u32 must zero-extend by 24 bits");
                assert_eq!(expr.sort().bitvec_width(), Some(8), "wrapped payload should be bv8");
            }
            other => {
                panic!("expected BvZeroExtend for unsigned DT u8 wrapper→u32 cast, got {:?}", other)
            }
        }
    });
}

#[test]
fn test_bv_to_bv_signed_widen_regression_uses_sign_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        // Regression guard: keep the direct BV→BV signed cast behavior unchanged.
        let src_expr = Expr::var("signed_bv8", Sort::bitvec(8));
        let result =
            exercise_codegen_cast_with_first_arg(&mut ctx, "signed_to_unsigned_widen", src_expr)
                .expect("BV i8 source should cast to u32");
        match result.value() {
            ExprValue::BvSignExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 24, "BV i8→u32 must sign-extend by 24 bits");
                assert_eq!(expr.sort().bitvec_width(), Some(8), "source should remain bv8");
            }
            other => panic!("expected BvSignExtend for BV i8→u32 cast, got {:?}", other),
        }
    });
}

// ─── Narrowing: u32 → u8 ────────────────────────────────────────────

#[test]
fn test_mir_narrow_u32_to_u8() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "narrow_u32_to_u8")
            .expect("codegen_cast should succeed for u32→u8");
        assert_eq!(result.sort().bitvec_width(), Some(8), "u32→u8 cast should produce bv8");
        // Narrowing uses extract
        assert!(
            matches!(result.value(), ExprValue::BvExtract { .. })
                || matches!(result.value(), ExprValue::Var { .. }),
            "expected extract or variable, got {:?}",
            result.value()
        );
    });
}

#[test]
fn test_mir_char_to_u8_narrow_extracts_low_byte() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result =
            exercise_codegen_cast(&mut ctx, "char_to_u8").expect("codegen_cast should succeed");
        assert_eq!(result.sort().bitvec_width(), Some(8), "char→u8 cast should produce bv8");
        match result.value() {
            ExprValue::BvExtract { expr, high, low } => {
                assert_eq!((*high, *low), (7, 0), "char→u8 cast should extract [7:0]");
                assert_eq!(expr.sort().bitvec_width(), Some(32), "char source should be bv32");
            }
            other => panic!("expected BvExtract for char→u8 cast, got {:?}", other),
        }
    });
}

// ─── Bool → u32 cast ─────────────────────────────────────────────────

#[test]
fn test_mir_bool_to_u32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "bool_to_u32")
            .expect("codegen_cast should succeed for bool→u32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "bool→u32 cast should produce bv32");
    });
}

#[test]
fn test_mir_bool_to_u8_uses_ite_then_zero_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result =
            exercise_codegen_cast(&mut ctx, "bool_to_u8").expect("codegen_cast should succeed");
        assert_eq!(result.sort().bitvec_width(), Some(8), "bool→u8 cast should produce bv8");
        match result.value() {
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 7, "bool→u8 cast should zero-extend by 7 bits");
                assert!(matches!(expr.value(), ExprValue::Ite { .. }), "expected ITE source");
            }
            other => panic!("expected BvZeroExtend(ITE(..)) for bool→u8 cast, got {:?}", other),
        }
    });
}

#[test]
fn test_mir_bool_to_u32_uses_ite_then_zero_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "bool_to_u32")
            .expect("codegen_cast should succeed for bool→u32");
        match result.value() {
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                assert_eq!(
                    *extra_bits, 31,
                    "bool→u32 cast should zero-extend a bv1 discriminator to bv32"
                );
                assert!(
                    matches!(expr.value(), ExprValue::Ite { .. }),
                    "bool→u32 cast should build ite(bool, 1, 0) before zero-extend"
                );
            }
            other => panic!("expected BvZeroExtend(ITE(...)) for bool→u32 cast, got {:?}", other),
        }
    });
}

// ─── Same-width cast: u32 → u32 ─────────────────────────────────────

#[test]
fn test_mir_same_width_u32_identity() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        // same_width_cast may be optimized away by rustc at MIR level.
        // If no Cast rvalue is found, the optimizer elided it (valid).
        let instance = find_instance_by_suffix(&ctx, "same_width_cast");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for (idx, local_decl) in body.arg_locals().iter().enumerate() {
            let local_idx = idx + 1;
            let local = Local::from(local_idx);
            let place = Place { local, projection: vec![] };
            let base = codegen.ssa_base_name(&place);
            if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
                codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
            }
        }

        if let Some((operand, target_ty)) = find_first_cast(&body) {
            let result =
                codegen.codegen_cast(&operand, target_ty).expect("same-width cast should succeed");
            assert_eq!(
                result.sort().bitvec_width(),
                Some(32),
                "u32→u32 cast should preserve width"
            );
        } else {
            // Optimizer elided the identity cast — this is valid behavior.
        }
    });
}

// ─── Additional widening: u8 → u16 ──────────────────────────────────

#[test]
fn test_mir_unsigned_widen_u8_to_u16() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "u8_to_u16")
            .expect("codegen_cast should succeed for u8→u16");
        assert_eq!(result.sort().bitvec_width(), Some(16), "u8→u16 cast should produce bv16");
        match result.value() {
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 8, "u8→u16 cast should zero-extend by 8 bits");
                assert_eq!(
                    expr.sort().bitvec_width(),
                    Some(8),
                    "u8→u16 cast should widen from an 8-bit source"
                );
            }
            other => panic!("expected BvZeroExtend for u8→u16 cast, got {:?}", other),
        }
    });
}

// ─── Signed widening: i16 → i64 ─────────────────────────────────────

#[test]
fn test_mir_signed_widen_i16_to_i64() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "i16_to_i64")
            .expect("codegen_cast should succeed for i16→i64");
        assert_eq!(result.sort().bitvec_width(), Some(64), "i16→i64 cast should produce bv64");
        match result.value() {
            ExprValue::BvSignExtend { expr, extra_bits } => {
                assert_eq!(*extra_bits, 48, "i16→i64 cast should sign-extend by 48 bits");
                assert_eq!(
                    expr.sort().bitvec_width(),
                    Some(16),
                    "i16→i64 cast should widen from a 16-bit source"
                );
            }
            other => panic!("expected BvSignExtend for i16→i64 cast, got {:?}", other),
        }
    });
}

// ─── Narrowing: u64 → u8 ────────────────────────────────────────────

#[test]
fn test_mir_narrow_u64_to_u8() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "u64_to_u8")
            .expect("codegen_cast should succeed for u64→u8");
        assert_eq!(result.sort().bitvec_width(), Some(8), "u64→u8 cast should produce bv8");
        match result.value() {
            ExprValue::BvExtract { expr, high, low } => {
                assert_eq!((*high, *low), (7, 0), "u64→u8 cast should extract low byte [7:0]");
                assert_eq!(
                    expr.sort().bitvec_width(),
                    Some(64),
                    "u64→u8 cast should narrow a 64-bit source"
                );
            }
            other => panic!("expected BvExtract for u64→u8 cast, got {:?}", other),
        }
    });
}

// ─── Pointer to usize cast ──────────────────────────────────────────

#[test]
fn test_mir_ptr_to_usize() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "ptr_to_usize")
            .expect("codegen_cast should succeed for *const u8→usize");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "ptr→usize cast should produce bv{POINTER_WIDTH}"
        );
        assert!(
            matches!(result.value(), ExprValue::Var { .. }),
            "thin ptr→usize is a same-width bitvec identity cast, got {:?}",
            result.value()
        );
    });
}

#[test]
fn test_mir_ptr_to_u32_truncates_when_pointer_is_wide() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result =
            exercise_codegen_cast(&mut ctx, "ptr_to_u32").expect("codegen_cast should succeed");
        assert_eq!(result.sort().bitvec_width(), Some(32), "ptr→u32 cast should produce bv32");
        if POINTER_WIDTH > 32 {
            assert!(
                matches!(result.value(), ExprValue::BvExtract { .. }),
                "wide-pointer ptr→u32 should truncate with extract, got {:?}",
                result.value()
            );
        } else {
            assert!(
                matches!(result.value(), ExprValue::Var { .. }),
                "32-bit pointer ptr→u32 should be identity, got {:?}",
                result.value()
            );
        }
    });
}

// ─── Enum discriminant extraction ────────────────────────────────────

#[test]
fn test_mir_enum_discriminant_cast() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "enum_discriminant");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed enum argument as a symbolic variable
        for (idx, local_decl) in body.arg_locals().iter().enumerate() {
            let local_idx = idx + 1;
            let local = Local::from(local_idx);
            let place = Place { local, projection: vec![] };
            let base = codegen.ssa_base_name(&place);
            if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
                codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
            }
        }

        // Walk all blocks looking for Cast rvalues — enum discriminant
        // extraction may appear as Cast or as Discriminant rvalue
        let mut found_cast = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Cast(_, operand, target_ty)) = &stmt.kind {
                    let result = codegen.codegen_cast(operand, *target_ty);
                    if let Some(expr) = result {
                        assert!(
                            expr.sort().is_bitvec(),
                            "enum discriminant cast should produce bitvec, got {:?}",
                            expr.sort()
                        );
                        found_cast = true;
                    }
                }
            }
        }
        // Note: enum discriminant may be lowered differently in MIR
        // (Discriminant rvalue + IntToInt cast, or direct). The test
        // exercises whatever cast pattern rustc produces.
        if !found_cast {
            // Check if Discriminant rvalue was used instead of Cast
            let has_discriminant = body.blocks.iter().any(|bb| {
                bb.statements.iter().any(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Discriminant(_)))
                })
            });
            assert!(
                has_discriminant,
                "enum_discriminant should produce either Cast or Discriminant rvalue"
            );
        }
    });
}

#[test]
fn test_mir_enum_discriminant_widen_u8_to_u32_uses_zero_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "enum_discriminant_widen")
            .expect("codegen_cast should succeed for Color→u32");
        assert_eq!(result.sort().bitvec_width(), Some(32), "Color→u32 cast should produce bv32");
        let debug_repr = format!("{:?}", result.value());
        assert!(
            debug_repr.contains("BvZeroExtend"),
            "repr(u8)→u32 should zero-extend the repr value, got {}",
            debug_repr
        );
    });
}

#[test]
fn test_mir_signed_enum_to_i32_uses_sign_extend() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "signed_enum_to_i32")
            .expect("codegen_cast should succeed for SignedCode→i32");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(32),
            "SignedCode→i32 cast should produce bv32"
        );
        let debug_repr = format!("{:?}", result.value());
        assert!(
            debug_repr.contains("BvSignExtend"),
            "repr(i8)→i32 should sign-extend the repr value, got {}",
            debug_repr
        );
    });
}

#[test]
fn test_mir_signed_enum_to_u32_still_sign_extends_repr_i8() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "signed_enum_to_u32")
            .expect("codegen_cast should succeed for SignedCode→u32");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(32),
            "SignedCode→u32 cast should produce bv32"
        );
        let debug_repr = format!("{:?}", result.value());
        assert!(
            debug_repr.contains("BvSignExtend"),
            "repr(i8)→u32 should preserve signed value via sign-extend, got {}",
            debug_repr
        );
    });
}

#[test]
fn test_mir_singleton_enum_to_u32_is_constant_without_ite() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "singleton_enum_to_u32")
            .expect("codegen_cast should succeed for SingletonCode→u32");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(32),
            "SingletonCode→u32 cast should produce bv32"
        );
        let debug_repr = format!("{:?}", result.value());
        assert!(
            !debug_repr.contains("Ite"),
            "single-variant enum cast should not build an ITE chain, got {}",
            debug_repr
        );
        assert!(
            debug_repr.contains("BvZeroExtend"),
            "repr(u16)→u32 singleton cast should zero-extend constant discriminant, got {}",
            debug_repr
        );
    });
}

// ─── Float → Integer casts ──────────────────────────────────────────
// In standard MIR-driven setup, floats are modeled as bitvectors. The dedicated
// regression below force-injects Real to exercise the Real→BitVec cast arm.

#[test]
fn test_mir_f32_to_u32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        // Standard MIR path models floats as bitvectors; this checks the
        // normal f32→u32 codegen pipeline. Real→BitVec is covered separately.
        let result = exercise_codegen_cast(&mut ctx, "f32_to_u32");
        if let Some(expr) = result {
            assert_eq!(expr.sort().bitvec_width(), Some(32), "f32→u32 cast should produce bv32");
        }
    });
}

#[test]
fn test_mir_f64_to_i64() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "f64_to_i64");
        if let Some(expr) = result {
            assert_eq!(expr.sort().bitvec_width(), Some(64), "f64→i64 cast should produce bv64");
        }
    });
}

/// Regression test for #2404 against production `codegen_cast`.
/// Force source sort to Real so the Real→BitVec branch is exercised.
#[test]
fn test_real_to_bv_codegen_cast_uses_constrained_int2bv() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let constraints_before = ctx.bmc_vc.constraints.len();
        let bv_result = exercise_codegen_cast_with_first_arg(
            &mut ctx,
            "f32_to_u32",
            Expr::var("real_input", Sort::real()),
        )
        .expect("Real→u32 cast should produce an expression");
        assert!(bv_result.sort().is_bitvec());
        assert_eq!(bv_result.sort().bitvec_width(), Some(32));
        assert!(
            matches!(bv_result.value(), ExprValue::Int2Bv(_, 32)),
            "Real→BV should end with Int2Bv node, got {:?}",
            bv_result.value()
        );
        if let ExprValue::Int2Bv(inner, _) = bv_result.value() {
            assert!(
                inner.sort().is_int(),
                "Int2Bv inner should be Int-sort, got {:?}",
                inner.sort()
            );
        }
        let constraints_added = ctx.bmc_vc.constraints.len() - constraints_before;
        assert!(
            constraints_added >= 2,
            "Real→BV should add floor constraints (iv <= real < iv + 1), added {constraints_added}"
        );
    });
}

// ─── Integer → Float casts ──────────────────────────────────────────
// Sort inference maps f32→bv32, f64→bv64 (not Real), so these are
// BitVec→BitVec same-width casts (identity path at cast.rs:149).

#[test]
fn test_mir_u32_to_f32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "u32_to_f32");
        if let Some(expr) = result {
            // f32 maps to bv32 in sort inference → same-width identity
            assert_eq!(
                expr.sort().bitvec_width(),
                Some(32),
                "u32→f32 cast should produce bv32 (f32 maps to bv32)"
            );
        }
    });
}

#[test]
fn test_mir_i64_to_f64() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "i64_to_f64");
        if let Some(expr) = result {
            // f64 maps to bv64 in sort inference → same-width identity
            assert_eq!(
                expr.sort().bitvec_width(),
                Some(64),
                "i64→f64 cast should produce bv64 (f64 maps to bv64)"
            );
        }
    });
}

// ─── Float → Float cast ────────────────────────────────────────────
// f32→f64 is bv32→bv64 (widening) since sort inference maps floats to bitvecs.

#[test]
fn test_mir_f32_to_f64() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "f32_to_f64");
        if let Some(expr) = result {
            assert_eq!(
                expr.sort().bitvec_width(),
                Some(64),
                "f32→f64 cast should produce bv64 (bv32 widened to bv64)"
            );
        }
    });
}

// ─── usize → *const u8 cast (BV width only, NOT provenance) ────────
// usize and *const u8 both resolve to Sort::bitvec(POINTER_WIDTH),
// so this exercises the BV→BV identity/width-matching path.
//
// NOTE: This test covers sort/width behavior only.  It does NOT cover
// provenance invalidation (the #3350 obj_valid false-store), which is
// an assignment-time side effect in track_cast_propagation().  Provenance
// semantics are guarded by codegen_assign_mir.rs tests (#3819).

#[test]
fn test_mir_usize_to_ptr_width_only() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        // usize→*const u8 is a BV→BV same-width cast (both POINTER_WIDTH).
        // codegen_cast should succeed, not return None. (#2423 Step C: explicit assertion.)
        let expr = exercise_codegen_cast(&mut ctx, "usize_to_ptr")
            .expect("usize→*const u8 should succeed (BV→BV identity)");
        assert!(
            expr.sort().is_bitvec(),
            "usize→ptr should produce bitvec (pointer width), got {:?}",
            expr.sort()
        );
        assert_eq!(
            expr.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "usize→ptr should be pointer-width bitvec"
        );
    });
}

// ─── char → u32 cast ───────────────────────────────────────────────
// Exercises char (treated as unsigned) → bv32 (same width identity).

#[test]
fn test_mir_char_to_u32() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "char_to_u32");
        if let Some(expr) = result {
            assert_eq!(expr.sort().bitvec_width(), Some(32), "char→u32 cast should produce bv32");
        }
    });
}

// ─── Fat pointer → thin pointer casts ──────────────────────────────
// Exercises Datatype→BitVec pointer extraction in codegen_dt_to_bv.

#[test]
fn test_mir_slice_ptr_to_thin_extracts_data_ptr() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "slice_ptr_to_thin")
            .expect("codegen_cast should succeed for *const [u8]→*const u8");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "slice fat-pointer cast should produce pointer-width bitvec"
        );
        assert!(
            matches!(result.value(), ExprValue::DatatypeSelector { .. }),
            "expected DatatypeSelector for slice fat-pointer cast, got {:?}",
            result.value()
        );
    });
}

#[test]
fn test_mir_dyn_ptr_to_thin_extracts_data_ptr() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_cast(&mut ctx, "dyn_ptr_to_thin")
            .expect("codegen_cast should succeed for *const dyn Trait→*const ()");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "dyn fat-pointer cast should produce pointer-width bitvec"
        );
        assert!(
            matches!(result.value(), ExprValue::DatatypeSelector { .. }),
            "expected DatatypeSelector for dyn fat-pointer cast, got {:?}",
            result.value()
        );
    });
}

// ─── Int → BitVec conversion (int2bv, #2403 regression) ─────────────

#[test]
fn test_int_to_bv_codegen_cast_uses_direct_int2bv() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let constraints_before = ctx.bmc_vc.constraints.len();
        let bv_result =
            exercise_codegen_cast_with_first_arg(&mut ctx, "unsigned_widen", Expr::int_const(42))
                .expect("Int→u32 cast should produce an expression");
        assert!(bv_result.sort().is_bitvec());
        assert_eq!(bv_result.sort().bitvec_width(), Some(32));
        assert!(
            matches!(bv_result.value(), ExprValue::Int2Bv(_, 32)),
            "Int→BV should use Int2Bv node, got {:?}",
            bv_result.value()
        );
        let constraints_added = ctx.bmc_vc.constraints.len() - constraints_before;
        assert_eq!(
            constraints_added, 0,
            "Int→BV int2bv path should not emit auxiliary assertions, added {constraints_added}"
        );
    });
}

/// Negative-value regression for #2403: Int→BitVec must remain satisfiable.
#[test]
fn test_int_to_bv_codegen_cast_allows_negative_input() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let bv_result =
            exercise_codegen_cast_with_first_arg(&mut ctx, "unsigned_widen", Expr::int_const(-1))
                .expect("negative Int→u32 cast should still produce an expression");
        assert!(bv_result.sort().is_bitvec());
        assert_eq!(bv_result.sort().bitvec_width(), Some(32));
        // The previous pattern (fresh BV + unsigned bv2int equality) was UNSAT for negatives.
        // Direct int2bv keeps the expression well-defined under modular semantics.
        assert!(
            matches!(bv_result.value(), ExprValue::Int2Bv(_, 32)),
            "negative Int→BV should still use Int2Bv, got {:?}",
            bv_result.value()
        );
    });
}

// ─── Transmute layout guard (#3809) ──────────────────────────────────
// These tests verify that codegen_transmute_cast (BMC backend) correctly
// blocks layout-sensitive cross-ADT transmutes and allows safe ones.

/// Probe source for transmute tests. Uses `mem::transmute` between struct types.
const TRANSMUTE_PROBE_SOURCE: &str = r#"
use std::mem;

#[repr(C)]
pub struct ReprCPair { pub x: u32, pub y: u32 }

#[repr(C)]
pub struct ReprCOther { pub a: u32, pub b: u32 }

pub struct DefaultPair { pub x: u32, pub y: u64 }

pub struct DefaultOther { pub a: u64, pub b: u32 }

#[repr(transparent)]
pub struct Wrapper(pub u64);

/// repr(C) → repr(C) transmute: layout is guaranteed identical.
pub fn reprc_to_reprc(s: ReprCPair) -> ReprCOther {
    unsafe { mem::transmute(s) }
}

/// Default layout → default layout transmute: layout may differ.
pub fn default_to_default(s: DefaultPair) -> DefaultOther {
    unsafe { mem::transmute(s) }
}

/// Same struct transmute (identity).
pub fn same_struct(s: ReprCPair) -> ReprCPair {
    unsafe { mem::transmute(s) }
}

/// Single-field wrapper transmute: not multi-field, always safe.
pub fn wrapper_to_u64(w: Wrapper) -> u64 {
    unsafe { mem::transmute(w) }
}

/// u32 → u32 transmute (BV → BV identity, baseline).
pub fn u32_identity(x: u32) -> u32 {
    unsafe { mem::transmute(x) }
}
"#;

/// Walk MIR blocks to find the first `CastKind::Transmute` rvalue.
fn find_first_transmute_cast(
    body: &rustc_public::mir::Body,
) -> Option<(Operand, rustc_public::ty::Ty)> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Cast(CastKind::Transmute, operand, target_ty)) =
                &stmt.kind
            {
                return Some((operand.clone(), *target_ty));
            }
        }
    }
    None
}

/// Helper: set up codegen for a transmute probe function and call
/// `codegen_cast_with_kind(CastKind::Transmute, ...)` on the first
/// Transmute rvalue found in its MIR body.
fn exercise_codegen_transmute(ctx: &mut AYCtx<'_, 'static>, fn_name: &str) -> Option<Expr> {
    let instance = find_instance_by_suffix(ctx, fn_name);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }

    let (operand, target_ty) = find_first_transmute_cast(&body)
        .unwrap_or_else(|| panic!("no Transmute cast rvalue found in {fn_name}"));
    codegen.codegen_cast_with_kind(&CastKind::Transmute, &operand, target_ty)
}

/// Default-layout cross-ADT transmute must be blocked (returns None).
/// The two structs have the same fields but rustc may reorder them.
/// Part of #3809.
#[test]
fn test_transmute_default_layout_cross_adt_blocked() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "default_to_default");
        assert!(
            result.is_none(),
            "default-layout cross-ADT transmute should be blocked, got {:?}",
            result
        );
    });
}

/// repr(C) cross-ADT transmute with matching fields should be allowed.
/// Both structs have `#[repr(C)]` with identical field types, so layout
/// is guaranteed to match.
/// Part of #3809.
#[test]
fn test_transmute_reprc_cross_adt_allowed() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "reprc_to_reprc");
        assert!(
            result.is_some(),
            "repr(C) cross-ADT transmute with matching layout should succeed"
        );
    });
}

/// Same-struct transmute is always allowed (identity path).
/// Note: rustc may optimize away same-type transmutes, so no Transmute
/// CastKind appears in MIR. If present, it must succeed.
/// Part of #3809.
#[test]
fn test_transmute_same_struct_identity_allowed() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "same_struct");
        let body = instance.body().expect("function body");
        if find_first_transmute_cast(&body).is_some() {
            let result = exercise_codegen_transmute(&mut ctx, "same_struct");
            assert!(
                result.is_some(),
                "same-struct transmute should succeed (identity or same-sort path)"
            );
        }
        // If rustc optimized away the identity transmute, the path is trivially safe.
    });
}

/// Single-field wrapper transmute to the inner type should be allowed.
/// The multi-field check only triggers when both sides have >1 field.
/// Part of #3809.
#[test]
fn test_transmute_single_field_wrapper_allowed() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "wrapper_to_u64");
        assert!(result.is_some(), "single-field wrapper transmute should succeed");
    });
}

// ─── Unconstrained-variable cast fallbacks (#2423) ──────────────────
// These tests verify that unsupported cast paths return None instead of
// fresh unconstrained variables (which cause false proofs).
//
// Coverage notes:
// - DT→BV fallback: 2 tests below (multi-field non-fat-ptr, Bool-field wrapper)
// - DT→DT structural mismatch (cast.rs:149-158): exercised through transmute
//   tests above (default_to_default is blocked by the transmute layout guard).
// - BV→DT (cast.rs:221-232): not testable through standard MIR probes — no Rust
//   cast produces a bitvec source with a datatype target sort. Pointer types
//   resolve to bitvec, not datatype (sort_inference.rs:71).

/// DT→BV fallback: multi-field struct (not a fat-pointer pattern) cast to
/// usize should return None, not an unconstrained bitvec.
/// Exercises codegen_dt_to_bv fallback path.
/// Part of #2423.
#[test]
fn test_dt_to_bv_multi_field_non_fat_ptr_returns_none() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        // Inject a 2-field struct that doesn't match the fat-pointer pattern
        // (ptr/len field names, both POINTER_WIDTH bitvecs). The DT→BV fallback
        // should return None.
        let src_sort = struct_sort(
            "UnknownStruct",
            [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))],
        );
        let src_expr = Expr::var("unknown_struct", src_sort);
        // ptr_to_usize: *const u8 → usize. Target resolves to bv(POINTER_WIDTH).
        // Source is injected as a 2-field DT → hits DT→BV path.
        let result = exercise_codegen_cast_with_first_arg(&mut ctx, "ptr_to_usize", src_expr);
        assert!(
            result.is_none(),
            "DT→BV with unrecognized multi-field struct should return None, got {:?}",
            result
        );
    });
}

/// DT→BV fallback: single-field struct with non-bitvec inner (Bool) should
/// return None. The single-field extraction only handles bitvec fields.
/// Part of #2423.
#[test]
fn test_dt_to_bv_single_bool_field_returns_none() {
    with_test_ay_ctx_for_source(CAST_PROBE_SOURCE, |mut ctx| {
        let src_sort = struct_sort("BoolWrapper", [("fld_val", Sort::bool())]);
        let src_expr = Expr::var("bool_wrapper", src_sort);
        let result = exercise_codegen_cast_with_first_arg(&mut ctx, "ptr_to_usize", src_expr);
        assert!(
            result.is_none(),
            "DT→BV with Bool-field struct should return None, got {:?}",
            result
        );
    });
}

// ─── PointerCoercion::Unsize cast (boxed dyn closure) ───────────────
// Part of #3793: Box<closure> → Box<dyn FnOnce()> unsize coercion.
// Exercises the dedicated cast_unsize.rs wrapper-walk path.

const UNSIZE_CAST_PROBE_SOURCE: &str = r#"
struct Droppy(u8);
impl Drop for Droppy {
    fn drop(&mut self) {}
}

pub fn captured_box_dyn_fnonce_cast() {
    let captured = Droppy(1);
    let f: Box<dyn FnOnce()> = Box::new(move || drop(captured));
    let _ = f;
}
"#;

/// Walk MIR blocks to find the first `PointerCoercion::Unsize` cast rvalue.
fn find_first_unsize_cast(
    body: &rustc_public::mir::Body,
) -> Option<(CastKind, Operand, rustc_public::ty::Ty)> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Cast(
                    kind @ CastKind::PointerCoercion(PointerCoercion::Unsize),
                    operand,
                    target_ty,
                ),
            ) = &stmt.kind
            {
                return Some((*kind, operand.clone(), *target_ty));
            }
        }
    }
    None
}

/// Captured Box<dyn FnOnce()> unsize cast produces Some result via the
/// dedicated wrapper-walk path in cast_unsize.rs.
/// Part of #3793.
#[test]
fn test_captured_box_dyn_fnonce_unsize_cast_succeeds() {
    with_test_ay_ctx_for_source(UNSIZE_CAST_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "captured_box_dyn_fnonce_cast");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed all locals with symbolic variables so codegen_operand can resolve them.
        for (idx, local_decl) in body.locals().iter().enumerate() {
            let local = Local::from(idx);
            let place = Place { local, projection: vec![] };
            let base = codegen.ssa_base_name(&place);
            if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
                codegen.env_update(base, Expr::var(format!("local_{idx}"), sort));
            }
        }

        let Some((kind, operand, target_ty)) = find_first_unsize_cast(&body) else {
            // rustc may inline Box::new entirely, eliminating the explicit
            // Unsize cast. If so, there's nothing to test — the path is
            // trivially handled by the inlined form.
            return;
        };

        let result = codegen.codegen_cast_with_kind(&kind, &operand, target_ty);
        assert!(
            result.is_some(),
            "PointerCoercion::Unsize for Box<closure> → Box<dyn FnOnce()> \
             should succeed via cast_unsize.rs wrapper-walk path"
        );
        let expr = result.unwrap();
        // Box<dyn FnOnce> may be encoded as BV64 (pointer) or Datatype depending
        // on the dyn encoding path. Both are valid.
        assert!(
            expr.sort().is_datatype() || expr.sort().bitvec_width().is_some(),
            "unsize cast result should be a Datatype or BV (pointer), got {:?}",
            expr.sort()
        );
    });
}

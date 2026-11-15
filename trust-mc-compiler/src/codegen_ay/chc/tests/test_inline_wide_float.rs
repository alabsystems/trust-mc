// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real MIR types drive the inline evaluator: unsupported numeric casts must
//! decline, while IEEE negation and existing supported conversions stay exact.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_shared::{PlaceResolver, inline_rvalue_to_expr};
use rustc_public::mir::{CastKind, Rvalue, StatementKind, UnOp};
use std::collections::HashMap;

const SOURCE: &str = r#"
#![feature(f16, f128)]
#![allow(dead_code)]
pub fn neg16(x: f16) -> f16 { -x }
pub fn neg32(x: f32) -> f32 { -x }
pub fn neg64(x: f64) -> f64 { -x }
pub fn neg128(x: f128) -> f128 { -x }
pub fn neg_int(x: i32) -> i32 { -x }
pub fn int16(x: i32) -> f16 { x as f16 }
pub fn int128(x: i32) -> f128 { x as f128 }
pub fn from16to32(x: f16) -> f32 { x as f32 }
pub fn from16to64(x: f16) -> f64 { x as f64 }
pub fn from16to128(x: f16) -> f128 { x as f128 }
pub fn from128to16(x: f128) -> f16 { x as f16 }
pub fn from128to32(x: f128) -> f32 { x as f32 }
pub fn from128to64(x: f128) -> f64 { x as f64 }
pub fn from32to16(x: f32) -> f16 { x as f16 }
pub fn from32to128(x: f32) -> f128 { x as f128 }
pub fn from64to16(x: f64) -> f16 { x as f16 }
pub fn from64to128(x: f64) -> f128 { x as f128 }
pub fn int32(x: i32) -> f32 { x as f32 }
pub fn int64(x: i32) -> f64 { x as f64 }
pub fn from32to64(x: f32) -> f64 { x as f64 }
pub fn from64to32(x: f64) -> f32 { x as f32 }
pub fn from16toint(x: f16) -> i32 { x as i32 }
pub fn from32toint(x: f32) -> i32 { x as i32 }
pub fn from64toint(x: f64) -> i32 { x as i32 }
pub fn from128toint(x: f128) -> i32 { x as i32 }
pub fn int_widen(x: i32) -> i64 { x as i64 }
pub fn bits16(x: f16) -> u16 { unsafe { core::mem::transmute(x) } }
pub fn bits128(x: f128) -> u128 { unsafe { core::mem::transmute(x) } }
pub fn same16(x: f16) -> f16 { x as f16 }
pub fn same128(x: f128) -> f128 { x as f128 }
"#;

fn operation(body: &rustc_public::mir::Body) -> (usize, Rvalue, usize) {
    let ops: Vec<_> = body
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter_map(|stmt| {
            let StatementKind::Assign(dest, rvalue) = &stmt.kind else { return None };
            let operand = match rvalue {
                Rvalue::UnaryOp(UnOp::Neg, operand) | Rvalue::Cast(_, operand, _) => operand,
                _ => return None,
            };
            let (Operand::Copy(src) | Operand::Move(src)) = operand else { return None };
            assert!(src.projection.is_empty());
            Some((dest.local, rvalue.clone(), src.local))
        })
        .collect();
    assert_eq!(ops.len(), 1, "expected one numeric operation in {body:?}");
    ops.into_iter().next().unwrap()
}

fn evaluate(ctx: &mut ChcCtx<'_, '_>, body: &rustc_public::mir::Body, input: Expr) -> Option<Expr> {
    let (dest, rvalue, src) = operation(body);
    let values = HashMap::from([(src, input)]);
    let fields = HashMap::new();
    inline_rvalue_to_expr(
        ctx,
        &rvalue,
        &values,
        &PlaceResolver::FieldMap(&fields),
        body.locals(),
        Some(dest),
    )
}

fn bits(expr: Expr) -> u128 {
    let (value, _) = crate::codegen_ay::float_arithmetic::eval_bv_expr(&expr);
    u128::try_from(value).unwrap()
}

#[test]
fn inline_wide_float_negation_matches_ieee_bit_patterns() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let cases: &[(&str, u32, &[(u128, u128)])] = &[
            (
                "neg16",
                16,
                &[
                    (0x3c00, 0xbc00),
                    (0, 0x8000),
                    (0x8000, 0),
                    (1, 0x8001),
                    (0x7c00, 0xfc00),
                    (0x7e35, 0xfe35),
                ],
            ),
            (
                "neg32",
                32,
                &[
                    (1.5f32.to_bits() as u128, (-1.5f32).to_bits() as u128),
                    (0, 0x80000000),
                    (0x7fc01234, 0xffc01234),
                ],
            ),
            (
                "neg64",
                64,
                &[
                    (1.5f64.to_bits() as u128, (-1.5f64).to_bits() as u128),
                    (0, 0x8000000000000000),
                    (0x7ff8000000001234, 0xfff8000000001234),
                ],
            ),
            (
                "neg128",
                128,
                &[
                    (0x3fff0000000000000000000000000000, 0xbfff0000000000000000000000000000),
                    (0, 0x80000000000000000000000000000000),
                    (0x80000000000000000000000000000000, 0),
                    (1, 0x80000000000000000000000000000001),
                    (0x7fff0000000000000000000000000000, 0xffff0000000000000000000000000000),
                    (0x7fff8000000000000000000000001234, 0xffff8000000000000000000000001234),
                ],
            ),
        ];
        for &(name, width, samples) in cases {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            for &(input, expected) in samples {
                assert_eq!(
                    bits(evaluate(&mut chc, &body, Expr::bitvec_const(input, width)).unwrap()),
                    expected,
                    "{name} input={input:x}"
                );
            }
            assert!(
                evaluate(&mut chc, &body, Expr::bitvec_const(0u32, width + 1)).is_none(),
                "wrong width: {name}"
            );
            assert!(
                evaluate(&mut chc, &body, Expr::int_const(1)).is_none(),
                "integer-sort float: {name}"
            );
            // The statement evaluator must use the same IEEE operation.
            chc.collect_state_vars();
            let (_, rvalue, _) = operation(&body);
            let stmt = chc.translate_rvalue_with_modified(&rvalue, &HashSet::new(), None).unwrap();
            assert!(stmt.to_string().contains("bvxor"), "statement {name}: {stmt}");
        }
        let body = find_instance_by_suffix(ctx.tcx, "neg_int").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "neg_int", ChcConfig::default());
        assert_eq!(
            bits(evaluate(&mut chc, &body, Expr::bitvec_const(3u32, 32)).unwrap()),
            0xffff_fffd
        );
    });
}

#[test]
fn inline_wide_float_unsupported_casts_decline_instead_of_coercing_bits() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, width) in [
            ("int16", 32),
            ("int128", 32),
            ("from16to32", 16),
            ("from16to64", 16),
            ("from16to128", 16),
            ("from128to16", 128),
            ("from128to32", 128),
            ("from128to64", 128),
            ("from32to16", 32),
            ("from32to128", 32),
            ("from64to16", 64),
            ("from64to128", 64),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            assert!(
                evaluate(&mut chc, &body, Expr::bitvec_const(3u32, width)).is_none(),
                "unsupported cast admitted: {name}"
            );
        }
    });
}

#[test]
fn inline_wide_float_supported_casts_keep_numeric_semantics() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, width, input, expected) in [
            ("int32", 32, 3u128, 0x40400000),
            ("int64", 32, 3, 0x4008000000000000),
            ("from32to64", 32, 0x3fc00000, 0x3ff8000000000000),
            ("from64to32", 64, 0x3ff8000000000000, 0x3fc00000),
            ("from16toint", 16, 0x3e00, 1),
            ("from32toint", 32, 0x3fc00000, 1),
            ("from64toint", 64, 0x3ff8000000000000, 1),
            ("from128toint", 128, 0x3fff8000000000000000000000000000, 1),
            ("from16toint", 16, 0x7c00, 0x7fffffff),
            ("from128toint", 128, 0x7fff8000000000000000000000001234, 0),
            ("int_widen", 32, 3, 3),
            ("bits16", 16, 0x3c00, 0x3c00),
            (
                "bits128",
                128,
                0x3fff0000000000000000000000000000,
                0x3fff0000000000000000000000000000,
            ),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            assert_eq!(
                bits(evaluate(&mut chc, &body, Expr::bitvec_const(input, width)).unwrap()),
                expected,
                "{name}"
            );
        }
    });
}

#[test]
fn inline_wide_float_declines_record_fail_closed_diagnostics() {
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    assert_eq!(
        fallback_soundness("inline_float_operation_unmodeled"),
        FallbackSoundness::FailClose
    );
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, value) in [
            ("int16", Expr::bitvec_const(3u32, 32)),
            ("from128to32", Expr::bitvec_const(0u32, 128)),
            ("int32", Expr::bitvec_const(1u32, 33)),
            ("from16toint", Expr::bitvec_const(1u32, 17)),
            ("from32to64", Expr::bool_const(true)),
            ("neg16", Expr::int_const(1)),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            assert_eq!(chc.diagnostics.place_translation_drop.get(), 0);
            assert!(evaluate(&mut chc, &body, value).is_none(), "{name}");
            assert_eq!(chc.diagnostics.place_translation_drop.get(), 1, "{name}");
            assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0, "{name}");
            assert_eq!(chc.vc.accounted_approximations, 0, "{name}");
        }
    });
}

#[test]
fn inline_wide_float_same_type_casts_preserve_exact_identity() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, width, input) in
            [("same16", 16, 0xfe35u128), ("same128", 128, 0xffff8000000000000000000000001234)]
        {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let rvalue = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|stmt| {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else { return None };
                    (place.local == 0).then_some(rvalue)
                })
                .expect("same-type function return assignment");
            let operand = match rvalue {
                Rvalue::Use(operand, ..) | Rvalue::Cast(CastKind::FloatToFloat, operand, _) => {
                    operand
                }
                _ => panic!("unexpected same-type MIR: {rvalue:?}"),
            };
            println!("{name} actual return MIR: {rvalue:?}");
            let source_ty = operand.ty(body.locals()).unwrap();
            let target_ty = body.locals()[0].ty;
            assert_eq!(source_ty, target_ty);
            let (Operand::Copy(place) | Operand::Move(place)) = operand else {
                panic!("same-type input must be a parameter");
            };
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let values = HashMap::from([(place.local, Expr::bitvec_const(input, width))]);
            let fields = HashMap::new();
            let resolver = PlaceResolver::FieldMap(&fields);
            let actual =
                inline_rvalue_to_expr(&mut chc, rvalue, &values, &resolver, body.locals(), Some(0))
                    .unwrap();
            assert_eq!(bits(actual), input);
            // MIR may simplify the identity to Use. Also pin the retained-cast
            // form using those same compiler-supplied, exactly equal types.
            let retained = Rvalue::Cast(CastKind::FloatToFloat, operand.clone(), target_ty);
            let actual = inline_rvalue_to_expr(
                &mut chc,
                &retained,
                &values,
                &resolver,
                body.locals(),
                Some(0),
            )
            .unwrap();
            assert_eq!(bits(actual), input);
            assert_eq!(chc.diagnostics.place_translation_drop.get(), 0);
            let wrong_width = HashMap::from([(place.local, Expr::bitvec_const(input, width + 1))]);
            assert!(
                inline_rvalue_to_expr(
                    &mut chc,
                    &retained,
                    &wrong_width,
                    &resolver,
                    body.locals(),
                    Some(0)
                )
                .is_none()
            );
            assert_eq!(chc.diagnostics.place_translation_drop.get(), 1);
        }
    });
}

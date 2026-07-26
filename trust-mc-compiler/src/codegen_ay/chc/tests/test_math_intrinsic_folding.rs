// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC math intrinsic detection (Part of #3373).
//!
//! Covers:
//! - `detect_math_intrinsic()` suffix matching for all f32/f64 intrinsics
//! - f32/f64 suffix list parity validation

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::chc::codegen_call_cmp_string::math::{
    F32_SUFFIXES, F64_SUFFIXES, detect_math_intrinsic, normalize_to_intrinsic_suffix,
};
use crate::codegen_ay::chc::codegen_call_cmp_string::math_const::{
    try_extract_const_f32, try_extract_const_f32_with_ctx,
};
use crate::codegen_ay::float_arithmetic::bv_float_binop_chc;
use ay_bindings::Expr;
use rustc_public::mir::BinOp;

const LOCAL_EXPR_ENV_CONST_SOURCE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(internal_features)]
    #![allow(dead_code)]

    pub unsafe fn probe_sqrt_two_hop() -> f32 {
        let first = 4.0_f32;
        let second = first;
        let third = second;
        core::intrinsics::sqrtf32(third)
    }
"#;

const METHOD_FORM_MATH_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_method_sqrt_const() -> f32 {
        let positive = 4.0_f32;
        positive.sqrt()
    }
"#;

const SQRT_ASSERTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_sqrt_assertion() {
        let positive = 4.0_f32;
        let abs_difference = (positive.sqrt() - 2.0).abs();
        assert!(abs_difference <= f32::EPSILON);
    }

    pub fn probe_negative_zero_sqrt_eq() {
        let negative_zero = -0.0_f32;
        assert!(negative_zero.sqrt() == negative_zero);
    }

    pub fn probe_full_sqrt_harness_shape() {
        let positive = 4.0_f32;
        let negative_zero = -0.0_f32;
        let abs_difference = (positive.sqrt() - 2.0).abs();
        assert!(abs_difference <= f32::EPSILON);
        assert!(negative_zero.sqrt() == negative_zero);
    }
"#;

fn reset_math_translation_drop_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
}

// =============================================================================
// detect_math_intrinsic tests
// =============================================================================

#[test]
fn test_detect_f32_floor() {
    assert_eq!(detect_math_intrinsic("std::intrinsics::floorf32"), Some(true));
}

#[test]
fn test_detect_f64_floor() {
    assert_eq!(detect_math_intrinsic("std::intrinsics::floorf64"), Some(false));
}

#[test]
fn test_detect_all_f32_suffixes() {
    for suffix in F32_SUFFIXES {
        let path = format!("core::intrinsics::{suffix}");
        assert_eq!(
            detect_math_intrinsic(&path),
            Some(true),
            "f32 suffix '{suffix}' should be detected as f32"
        );
    }
}

#[test]
fn test_detect_all_f64_suffixes() {
    for suffix in F64_SUFFIXES {
        let path = format!("core::intrinsics::{suffix}");
        assert_eq!(
            detect_math_intrinsic(&path),
            Some(false),
            "f64 suffix '{suffix}' should be detected as f64"
        );
    }
}

#[test]
fn test_detect_non_math_returns_none() {
    assert_eq!(detect_math_intrinsic("std::mem::size_of"), None);
    assert_eq!(detect_math_intrinsic("core::intrinsics::add_with_overflow"), None);
    assert_eq!(detect_math_intrinsic(""), None);
    assert_eq!(detect_math_intrinsic("floorf32_extra"), None);
    assert_eq!(detect_math_intrinsic("core::f32::math::asin"), None);
}

#[test]
fn test_detect_bare_suffix() {
    assert_eq!(detect_math_intrinsic("sqrtf32"), Some(true));
    assert_eq!(detect_math_intrinsic("sqrtf64"), Some(false));
}

// =============================================================================
// Method-call form detection tests (Part of #3688)
// =============================================================================

#[test]
fn test_detect_method_call_trunc_f32() {
    // MIR-inlined fract() produces this call path for trunc.
    assert_eq!(detect_math_intrinsic("core::f32::math::trunc"), Some(true));
}

#[test]
fn test_detect_method_call_trunc_f64() {
    assert_eq!(detect_math_intrinsic("core::f64::math::trunc"), Some(false));
}

#[test]
fn test_detect_method_call_floor_f32() {
    assert_eq!(detect_math_intrinsic("core::f32::math::floor"), Some(true));
}

#[test]
fn test_detect_method_call_ceil_f64() {
    assert_eq!(detect_math_intrinsic("core::f64::math::ceil"), Some(false));
}

#[test]
fn test_detect_method_call_abs_f32() {
    assert_eq!(detect_math_intrinsic("core::f32::math::abs"), Some(true));
}

#[test]
fn test_detect_method_call_exp_f32() {
    assert_eq!(detect_math_intrinsic("core::f32::math::exp"), Some(true));
}

#[test]
fn test_detect_method_call_log10_f64() {
    assert_eq!(detect_math_intrinsic("core::f64::math::log10"), Some(false));
}

#[test]
fn test_detect_method_call_mul_add_f32() {
    assert_eq!(detect_math_intrinsic("core::f32::math::mul_add"), Some(true));
}

#[test]
fn test_detect_method_call_powi_f64() {
    assert_eq!(detect_math_intrinsic("core::f64::math::powi"), Some(false));
}

#[test]
fn test_normalize_method_call_trunc_f32() {
    assert_eq!(
        normalize_to_intrinsic_suffix("core::f32::math::trunc"),
        Some("truncf32".to_string())
    );
}

#[test]
fn test_normalize_method_call_trunc_f64() {
    assert_eq!(
        normalize_to_intrinsic_suffix("core::f64::math::trunc"),
        Some("truncf64".to_string())
    );
}

#[test]
fn test_normalize_method_call_exp_f32() {
    assert_eq!(normalize_to_intrinsic_suffix("core::f32::math::exp"), Some("expf32".to_string()));
}

#[test]
fn test_normalize_method_call_mul_add_f64() {
    assert_eq!(
        normalize_to_intrinsic_suffix("core::f64::math::mul_add"),
        Some("fmaf64".to_string())
    );
}

#[test]
fn test_normalize_intrinsic_form_returns_none() {
    // Intrinsic form doesn't need normalization.
    assert_eq!(normalize_to_intrinsic_suffix("std::intrinsics::truncf32"), None);
}

#[test]
fn test_normalize_unrelated_path_returns_none() {
    assert_eq!(normalize_to_intrinsic_suffix("std::mem::size_of"), None);
    assert_eq!(normalize_to_intrinsic_suffix("core::f32::math::asin"), None);
}

#[test]
fn test_f32_f64_suffix_lists_same_length() {
    assert_eq!(
        F32_SUFFIXES.len(),
        F64_SUFFIXES.len(),
        "f32 and f64 suffix lists should have the same number of entries"
    );
}

#[test]
fn test_f32_f64_suffix_parity() {
    for f32_suffix in F32_SUFFIXES {
        let f64_equivalent = f32_suffix.replace("f32", "f64");
        assert!(
            F64_SUFFIXES.contains(&f64_equivalent.as_str()),
            "f32 suffix '{f32_suffix}' has no f64 counterpart '{f64_equivalent}'"
        );
    }
}

#[test]
fn test_try_extract_const_f32_with_ctx_reads_local_expr_env_for_two_hop_copy() {
    with_test_ay_ctx_for_source(LOCAL_EXPR_ENV_CONST_SOURCE, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "probe_sqrt_two_hop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_sqrt_two_hop", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let operand = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. }
                    if chc_ctx
                        .resolve_callee_path(func)
                        .as_deref()
                        .is_some_and(|path| path.contains("sqrtf32")) =>
                {
                    Some(args.first().expect("sqrtf32 arg"))
                }
                _ => None,
            })
            .expect("sqrtf32 call terminator");

        let env_bits = 9.0_f32.to_bits();
        assert_ne!(
            try_extract_const_f32(operand, &body),
            Some(env_bits),
            "the local_expr_env sentinel should differ from the raw MIR baseline"
        );

        let local = match operand {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place) => {
                place.local
            }
            _ => panic!("expected local operand for sqrtf32 argument"),
        };
        let modified_locals = HashSet::from([local]);
        chc_ctx.encode.local_expr_env.insert(local, Expr::bitvec_const(env_bits as u128, 32));

        assert_eq!(
            try_extract_const_f32_with_ctx(&mut chc_ctx, operand, &modified_locals),
            Some(env_bits),
            "CHC math constant extraction should prioritize local_expr_env over the raw MIR fallback"
        );
    });
}

#[test]
fn test_math_dispatch_constant_folds_two_hop_copy_via_local_expr_env() {
    with_test_ay_ctx_for_source(LOCAL_EXPR_ENV_CONST_SOURCE, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "probe_sqrt_two_hop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_sqrt_two_hop", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && chc_ctx
                    .resolve_callee_path(func)
                    .as_deref()
                    .is_some_and(|path| path.contains("sqrtf32"))
            {
                found = true;
                let arg_local = match args.first().expect("sqrtf32 arg") {
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place) => place.local,
                    _ => panic!("expected local operand for sqrtf32 argument"),
                };
                let modified_locals = HashSet::from([arg_local]);
                chc_ctx
                    .encode
                    .local_expr_env
                    .insert(arg_local, Expr::bitvec_const(4.0_f32.to_bits() as u128, 32));

                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };

                assert!(
                    chc_ctx.try_dispatch_call_math_intrinsic(&dcx),
                    "sqrtf32 call should be handled by the CHC math intrinsic path"
                );
                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "same-block constant input should avoid range-axiom fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "constant-folded sqrtf32 should emit one CHC transition rule"
                );
                break;
            }
        }

        assert!(found, "expected sqrtf32 call terminator in probe_sqrt_two_hop");
    });
}

#[test]
fn test_math_dispatch_method_form_sqrt_constant_folds_without_sound_fallback() {
    with_test_ay_ctx_for_source(METHOD_FORM_MATH_SOURCE, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "probe_method_sqrt_const");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_method_sqrt_const", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && chc_ctx
                    .resolve_callee_path(func)
                    .as_deref()
                    .is_some_and(|path| path.contains("sqrt"))
            {
                found = true;
                let arg_local = match args.first().expect("sqrt arg") {
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place) => place.local,
                    _ => panic!("expected local operand for sqrt argument"),
                };
                let modified_locals = HashSet::from([arg_local]);
                let from_rel =
                    chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
                let output_args: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                    .collect();
                let from_app = RelationApp::new(&from_rel, output_args);
                let stmt_constraints = [Expr::bool_const(true)];
                let target_opt = Some(*target);
                let before = chc_ctx.sound_fallback_count();
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app: &from_app,
                    stmt_constraints: &stmt_constraints,
                    modified_locals: &modified_locals,
                    callee_path: None,
                };

                assert!(
                    chc_ctx.try_dispatch_call_math_intrinsic(&dcx),
                    "method-form sqrt dispatch should be handled by the math intrinsic path"
                );
                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "method-form sqrt dispatch should constant-fold the concrete input"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "method-form sqrt dispatch should emit one CHC transition rule"
                );
                break;
            }
        }

        assert!(found, "expected method-form sqrt call terminator");
    });
}

fn assert_no_math_translation_drops(fn_name: &str) {
    let translation_drops = take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
    let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "{fn_name} should not record translation drops, drops={translation_drops:?}, sites={translation_sites:?}, place_count={place_drop_count}, constant_count={constant_drop_count}"
    );
    assert!(
        !translation_sites.contains_key(fn_name),
        "{fn_name} should not record translation-drop site reasons, sites={translation_sites:?}"
    );
}

#[test]
fn test_mir_to_chc_sqrt_assertion_pipeline_has_clean_translation_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_math_translation_drop_metadata();

    with_test_ay_ctx_for_source(SQRT_ASSERTION_SOURCE, |ctx| {
        let fn_name = "probe_sqrt_assertion";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
    });

    assert_no_math_translation_drops("probe_sqrt_assertion");
}

#[test]
fn test_bv_float_binop_chc_normalizes_negative_zero_constants() {
    let f32_result = bv_float_binop_chc(
        BinOp::Mul,
        Expr::bitvec_const(0xBF80_0000u64, 32),
        Expr::bitvec_const(0x0000_0000u64, 32),
        32,
    )
    .expect("f32 constant fold should succeed");
    assert_eq!(
        f32_result,
        Expr::bitvec_const(0x0000_0000u64, 32),
        "(-1.0f32) * 0.0f32 should normalize to +0.0 bits in CHC constant folding"
    );

    let f64_result = bv_float_binop_chc(
        BinOp::Mul,
        Expr::bitvec_const(0xBFF0_0000_0000_0000u64, 64),
        Expr::bitvec_const(0x0000_0000_0000_0000u64, 64),
        64,
    )
    .expect("f64 constant fold should succeed");
    assert_eq!(
        f64_result,
        Expr::bitvec_const(0x0000_0000_0000_0000u64, 64),
        "(-1.0f64) * 0.0f64 should normalize to +0.0 bits in CHC constant folding"
    );
}

#[test]
fn test_bv_float_binop_chc_returns_none_for_symbolic_operands() {
    use ay_bindings::Sort;
    let sym = Expr::var("sym_f32", Sort::bitvec(32));
    let one = Expr::bitvec_const(0x3F80_0000u64, 32);

    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem] {
        assert!(
            bv_float_binop_chc(op, sym.clone(), one.clone(), 32).is_none(),
            "symbolic LHS for {op:?} must fail closed in CHC encoding"
        );
        assert!(
            bv_float_binop_chc(op, one.clone(), sym.clone(), 32).is_none(),
            "symbolic RHS for {op:?} must fail closed in CHC encoding"
        );
        assert!(
            bv_float_binop_chc(op, sym.clone(), sym.clone(), 32).is_none(),
            "both-symbolic for {op:?} must fail closed in CHC encoding"
        );
    }
}

#[test]
fn test_bv_float_binop_chc_returns_none_for_unsupported_widths() {
    // f16 (16-bit) and f128 (128-bit) constants have no native host
    // representation, so we cannot constant-fold precisely. Fail closed
    // rather than approximate via f32/f64.
    let lhs_16 = Expr::bitvec_const(0x3C00u64, 16); // 1.0_f16
    let rhs_16 = Expr::bitvec_const(0x4000u64, 16); // 2.0_f16
    assert!(bv_float_binop_chc(BinOp::Add, lhs_16, rhs_16, 16).is_none());

    let lhs_128 = Expr::bitvec_const(1u128, 128);
    let rhs_128 = Expr::bitvec_const(2u128, 128);
    assert!(bv_float_binop_chc(BinOp::Add, lhs_128, rhs_128, 128).is_none());
}

#[test]
fn test_mir_to_chc_negative_zero_sqrt_eq_has_clean_translation_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_math_translation_drop_metadata();

    with_test_ay_ctx_for_source(SQRT_ASSERTION_SOURCE, |ctx| {
        let fn_name = "probe_negative_zero_sqrt_eq";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
    });

    assert_no_math_translation_drops("probe_negative_zero_sqrt_eq");
}

#[test]
fn test_mir_to_chc_full_sqrt_harness_shape_has_clean_translation_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_math_translation_drop_metadata();

    with_test_ay_ctx_for_source(SQRT_ASSERTION_SOURCE, |ctx| {
        let fn_name = "probe_full_sqrt_harness_shape";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
    });

    assert_no_math_translation_drops("probe_full_sqrt_harness_shape");
}

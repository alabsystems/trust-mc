// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven regression tests for symbolic CHC math intrinsic dispatch.
//!
//! Part of #3750.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;

const ROUNDING_INTRINSIC_SOURCE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]

    pub unsafe fn probe_floor(x: f32) -> f32 {
        core::intrinsics::floorf32(x)
    }

    pub unsafe fn probe_floor_f64(x: f64) -> f64 {
        core::intrinsics::floorf64(x)
    }

    pub unsafe fn probe_ceil(x: f32) -> f32 {
        core::intrinsics::ceilf32(x)
    }

    pub unsafe fn probe_ceil_f64(x: f64) -> f64 {
        core::intrinsics::ceilf64(x)
    }

    pub unsafe fn probe_trunc(x: f32) -> f32 {
        core::intrinsics::truncf32(x)
    }

    pub unsafe fn probe_trunc_f64(x: f64) -> f64 {
        core::intrinsics::truncf64(x)
    }

    pub unsafe fn probe_round(x: f32) -> f32 {
        core::intrinsics::roundf32(x)
    }

    pub unsafe fn probe_round_f64(x: f64) -> f64 {
        core::intrinsics::roundf64(x)
    }

    pub unsafe fn probe_round_ties_even(x: f32) -> f32 {
        core::intrinsics::round_ties_even_f32(x)
    }

    pub unsafe fn probe_round_ties_even_f64(x: f64) -> f64 {
        core::intrinsics::round_ties_even_f64(x)
    }
"#;

const FP_ROUNDING_MODE_TOKENS: &[&str] = &[
    "fp.roundToIntegral",
    "roundTowardZero",
    "roundTowardNegative",
    "roundTowardPositive",
    "roundNearestTiesToAway",
    "roundNearestTiesToEven",
];

fn with_symbolic_rounding_dispatch(
    fn_name: &str,
    intrinsic_fragment: &str,
    assertions: impl FnOnce(&str) + Send,
) {
    with_test_ay_ctx_for_source(ROUNDING_INTRINSIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && chc_ctx
                    .resolve_callee_path(func)
                    .as_deref()
                    .is_some_and(|path| path.contains(intrinsic_fragment))
            {
                found = true;
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
                let modified_locals = HashSet::new();
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
                    "{intrinsic_fragment} dispatch should be handled by the math intrinsic path"
                );
                assert_eq!(
                    chc_ctx.sound_fallback_count(),
                    before,
                    "{intrinsic_fragment} dispatch should not record a sound fallback"
                );
                assert_eq!(
                    chc_ctx.vc.rules.len(),
                    1,
                    "{intrinsic_fragment} dispatch should emit one CHC rule"
                );

                let smt = emit_chc(&chc_ctx.vc).to_string();
                assertions(&smt);
                break;
            }
        }

        assert_mir_pattern_found(found, intrinsic_fragment);
    });
}

fn assert_pure_bv_rounding_encoding(smt: &str, intrinsic_name: &str) {
    for token in FP_ROUNDING_MODE_TOKENS {
        assert!(
            !smt.contains(token),
            "{intrinsic_name} should avoid FP rounding-mode token '{token}', got: {smt}"
        );
    }

    assert!(
        smt.contains("bvshl") || smt.contains("bvlshr"),
        "{intrinsic_name} should emit BV shifts for mantissa masking/increment logic, got: {smt}"
    );
    assert!(
        smt.contains("ite"),
        "{intrinsic_name} should emit ITE structure for special/sub-one/normal cases, got: {smt}"
    );
}

#[test]
fn test_symbolic_rounding_intrinsics_use_pure_bv_chc_encoding() {
    for (fn_name, intrinsic_fragment) in [
        ("probe_floor", "floorf32"),
        ("probe_floor_f64", "floorf64"),
        ("probe_ceil", "ceilf32"),
        ("probe_ceil_f64", "ceilf64"),
        ("probe_trunc", "truncf32"),
        ("probe_trunc_f64", "truncf64"),
        ("probe_round", "roundf32"),
        ("probe_round_f64", "roundf64"),
        ("probe_round_ties_even", "round_ties_even_f32"),
        ("probe_round_ties_even_f64", "round_ties_even_f64"),
    ] {
        with_symbolic_rounding_dispatch(fn_name, intrinsic_fragment, |smt| {
            assert_pure_bv_rounding_encoding(smt, intrinsic_fragment);
        });
    }
}

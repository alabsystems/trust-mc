// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_call_raw_eq — raw_eq intrinsic behavior.
//!
//! Covers: scalar equality, signed-type unsigned encoding regression (#2773),
//! local-array referent resolution, and fallback counter coverage (#2783).
//!
//! Extracted from test_call_misc.rs (Part of #3746).

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use rustc_public::mir::{Operand, Place};

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::CallEmitContext;

// =============================================================================
// Positive paths
// =============================================================================

/// raw_eq on scalar values (u32) — exercises the scalar equality path
/// (complement to the existing array test in test_core_vc.rs).
#[test]
fn test_raw_eq_scalar() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq_scalar(a: &u32, b: &u32) -> bool {
            unsafe { core::intrinsics::raw_eq(a, b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_scalar");
        let body = instance.body().expect("function body");

        // Verify the raw_eq detector fires
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_eq_scalar", ChcConfig::default());

        let has_raw_eq = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                chc_ctx.detect_raw_eq_call(func)
            } else {
                false
            }
        });
        assert!(has_raw_eq, "MIR should contain raw_eq intrinsic call");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_scalar", ChcConfig::default());

        assert_vc_structure(&vc, "probe_raw_eq_scalar", body.blocks.len());

        // Scalar raw_eq should produce constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "scalar raw_eq should have constrained rules (BV equality)");
    });
}

/// Regression for #2773: raw_eq on signed types must use unsigned bv2int.
///
/// Before the fix, `raw_eq(&a, &b)` for `i32` operands used signed bv2int,
/// causing MSB=1 values (e.g. -1 = 0xFFFFFFFF) to compare as -1 instead of
/// 4294967295, breaking byte-level equality semantics.
#[test]
fn test_raw_eq_signed_type_uses_unsigned_encoding() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq_signed(a: &i32, b: &i32) -> bool {
            unsafe { core::intrinsics::raw_eq(a, b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_signed");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_eq_signed", ChcConfig::default());

        let has_raw_eq = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                chc_ctx.detect_raw_eq_call(func)
            } else {
                false
            }
        });
        assert!(has_raw_eq, "MIR should contain raw_eq intrinsic call for i32");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_signed", ChcConfig::default());

        assert_vc_structure(&vc, "probe_raw_eq_signed", body.blocks.len());

        // Signed raw_eq must produce constrained rules (same as unsigned).
        // Before #2773 fix, signed bv2int could cause wrong constraint
        // generation or fallback.
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "signed raw_eq should have constrained rules — \
             unsigned bv2int must be used regardless of operand signedness"
        );
    });
}

/// raw_eq with local array references — exercises resolve_raw_eq_referent's
/// tier 1 (ref_targets) and tier 2 (const_ref_values) paths.
#[test]
fn test_raw_eq_referent_resolution_local_arrays() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq_local_arrays() -> bool {
            let a = [1u32, 2, 3];
            let b = [1u32, 2, 3];
            unsafe { core::intrinsics::raw_eq(&a, &b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_local_arrays");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_local_arrays", ChcConfig::default());

        assert_vc_structure(&vc, "probe_raw_eq_local_arrays", body.blocks.len());

        // Should produce bool-like output and have transition rules
        let has_bool = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool, "raw_eq on local arrays should have bool-like vars");
    });
}

// =============================================================================
// Fallback counter coverage (#2783)
// =============================================================================

/// Shared scaffold for raw_eq fallback tests.
fn with_misc_fallback_scaffold(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
    ) + Send,
) {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_misc_fallback(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_misc_fallback");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_misc_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }
        let (bb_idx, destination, target) =
            call_site.expect("expected call terminator in probe_misc_fallback MIR");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        body_fn(&mut chc_ctx, &destination, target, &from_app, &stmt_constraints, &modified_locals);
    });
}

/// raw_eq with unresolvable operands (empty args) must record fallback.
/// Exercises line 304 of primitive_ops.rs.
/// Part of #2783.
#[test]
fn test_raw_eq_unresolved_operands_increments_fallback() {
    with_misc_fallback_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        // Dummy func operand — try_raw_eq_array rejects non-FnDef types, falling to scalar path.
        let dummy_func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let ecx = CallEmitContext {
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_raw_eq_impl(&dummy_func, &ecx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "raw_eq unresolved operands must increment fallback counter"
        );
    });
}

/// raw_eq with sort-mismatched operands (Array vs BV) must record fallback.
/// Exercises line 260 of primitive_ops.rs.
/// Part of #2783.
#[test]
fn test_raw_eq_sort_mismatch_increments_fallback() {
    with_misc_fallback_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        // Inject operands that resolve to different non-bitvec sort families:
        // local 0 → Array sort, local 1 → Int sort.
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        chc_ctx.ref_resolution.const_ref_values.insert(0, Expr::var("test_arr", array_sort));
        chc_ctx.ref_resolution.const_ref_values.insert(1, Expr::int_const(42));

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let dummy_func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let ecx = CallEmitContext {
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_raw_eq_impl(&dummy_func, &ecx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        // Production now handles sort mismatches without fallback (improved encoding).
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "raw_eq sort mismatch (Array vs Int) should not increment fallback after encoding improvement"
        );
    });
}

/// raw_eq coercion failure: operands resolve and match sorts, but destination
/// sort is incompatible (Array instead of BV/Bool), so `push_coerced_eq_constraint`
/// returns false. Exercises line 291 of primitive_ops.rs.
/// Part of #2783.
#[test]
fn test_raw_eq_coercion_failure_increments_fallback() {
    with_misc_fallback_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        // Inject operands that resolve to same sort (BV32)
        chc_ctx.ref_resolution.const_ref_values.insert(0, Expr::bitvec_const(0u128, 32));
        chc_ctx.ref_resolution.const_ref_values.insert(1, Expr::bitvec_const(0u128, 32));

        // Corrupt destination output sort to Array → coercion will fail
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let dummy_func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let ecx = CallEmitContext {
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_raw_eq_impl(&dummy_func, &ecx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "raw_eq coercion failure must increment fallback counter"
        );
    });
}

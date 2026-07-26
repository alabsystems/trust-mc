// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `record_fallback()` paths in `primitive_ops.rs`.
//!
//! Covers `codegen_call_primitive_clone_impl`, `codegen_call_slice_stub_parity_impl`,
//! and `codegen_call_raw_eq_impl`. Each test forces a specific fallback path
//! and asserts that `sound_fallback_count()` increments.
//!
//! Part of #2783 (primitive_ops record_fallback test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::{CallEmitContext, ChcCallContext};

/// Minimal Rust source providing a call site for scaffold extraction.
const SCAFFOLD_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x + 1 }

    pub fn probe_primitive_ops_fallback(x: u32) -> u32 {
        helper(x)
    }
"#;

/// Extracts call-site scaffold from MIR: ChcCtx, destination, target,
/// from_app, stmt_constraints, modified_locals, bb_idx.
fn with_call_scaffold(
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize, // bb_idx
    ) + Send,
) {
    with_test_ay_ctx_for_source(SCAFFOLD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_primitive_ops_fallback");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_primitive_ops_fallback", ChcConfig::default());
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
            call_site.expect("expected call terminator in probe_primitive_ops_fallback MIR");
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        body(
            &mut chc_ctx,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
        );
    });
}

// =============================================================================
// codegen_call_primitive_clone_impl — 1 fallback site (line 69)
// =============================================================================

/// When the clone operand cannot be resolved (bogus local), primitive clone
/// must record a fallback and emit an unconstrained transition.
#[test]
fn test_primitive_clone_unresolved_operand_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        // Operand referencing a nonexistent local
        let bogus_args = [Operand::Copy(Place { local: 997usize, projection: vec![] })];
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        chc_ctx.codegen_call_primitive_clone_impl(
            &bogus_args,
            destination,
            target,
            from_app,
            sc,
            ml,
        );

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "primitive clone unresolved operand must increment fallback counter"
        );
    });
}

// =============================================================================
// codegen_call_slice_stub_parity_impl — 4 testable fallback sites
// =============================================================================

/// SlicePartialEqEqual with mismatched sorts (neither bitvec nor equal) must
/// record fallback. Exercises line 141.
#[test]
fn test_slice_stub_equality_sort_mismatch_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        // Inject locals with incompatible sorts: one Int, one Array
        let idx_lhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", ay_bindings::Sort::int());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx_lhs);
        let idx_rhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(
            "test_rhs",
            "test_rhs_out",
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32)),
        );
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx_rhs);

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::SlicePartialEqEqual,
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert!(
            chc_ctx.sound_fallback_count() > 0,
            "slice equality sort mismatch must increment fallback counter"
        );
    });
}

/// SlicePartialEqEqual with unresolvable operands (bogus locals) must record
/// fallback. Exercises line 175.
#[test]
fn test_slice_stub_equality_unresolved_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        let bogus_args = [
            Operand::Copy(Place { local: 998usize, projection: vec![] }),
            Operand::Copy(Place { local: 999usize, projection: vec![] }),
        ];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::SlicePartialEqEqual,
            args: &bogus_args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "unresolved slice equality must increment fallback counter"
        );
    });
}

/// SliceIndexIndex over-approximation must record fallback. Exercises line 186.
#[test]
fn test_slice_stub_index_overapprox_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice index over-approximation must increment fallback counter"
        );
    });
}

/// Unexpected StubKind catch-all must record fallback. Exercises line 192.
#[test]
fn test_slice_stub_unexpected_stubkind_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        let args = [Operand::Copy(Place { local: 0usize, projection: vec![] })];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        // Use a StubKind not routed by this function
        let cx = ChcCallContext {
            stub: StubKind::VecPush,
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "unexpected StubKind must increment fallback counter"
        );
    });
}

// =============================================================================
// codegen_call_slice_stub_parity_impl — additional fallback sites
// Part of #2783: slice record_fallback test coverage gap
// =============================================================================

/// SliceIndexIndex with insufficient args (<2) must record fallback.
/// Exercises codegen_call_slice.rs line 207.
#[test]
fn test_slice_index_insufficient_args_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        // Pass only 1 arg — codegen_call_slice_index_impl requires >= 2.
        let args = [Operand::Copy(Place { local: 0usize, projection: vec![] })];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice index with insufficient args must increment fallback counter"
        );
    });
}

/// SliceIndexIndex with zero args must record fallback.
/// Exercises codegen_call_slice.rs line 207.
#[test]
fn test_slice_index_zero_args_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        let args: &[Operand] = &[];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::IndexIndex,
            args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice index with zero args must increment fallback counter"
        );
    });
}

/// emit_slice_index_zst sort mismatch must record fallback when the
/// destination output sort is incompatible with Unit constructor.
/// Exercises codegen_call_slice.rs line 354.
///
/// Uses the generic scaffold with a `&[()]`-typed operand to trigger the ZST
/// detection path, then corrupts the destination output sort so Unit coercion fails.
#[test]
fn test_slice_index_zst_sort_mismatch_increments_fallback() {
    const ZST_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_slice_fallback(s: &[()], idx: usize) -> usize {
            idx
        }
    "#;

    with_test_ay_ctx_for_source(ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_slice_fallback");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_zst_slice_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("bb0 relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();
        let destination = Place { local: 0usize, projection: vec![] };

        // Build args: local 1 is &[()], local 2 is usize (idx).
        // chc_slice_elem_ty inspects the operand's type via body.locals().
        // local 1 has type &[()] → element type () is ZST.
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 2usize, projection: vec![] }),
        ];

        // Corrupt the destination output sort to Array so that
        // push_coerced_eq_constraint(Unit, Array) fails → line 354.
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        if chc_ctx.state_var_mgr.output_state_vars.len() > dest_vec_idx {
            let (out_name, _out_sort) =
                chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].clone();
            chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx] = (
                out_name,
                ay_bindings::Sort::array(
                    ay_bindings::Sort::bitvec(32),
                    ay_bindings::Sort::bitvec(32),
                ),
            );
        }

        let before = chc_ctx.sound_fallback_count();
        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &args,
            destination: &destination,
            target: 0usize, // target bb
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            after > before,
            "ZST slice index sort mismatch must increment fallback counter \
             (before={before}, after={after})"
        );
    });
}

// =============================================================================
// codegen_call_raw_eq_impl — 3 testable fallback sites
// =============================================================================

/// raw_eq sort mismatch (incompatible non-bitvec sorts) must record fallback.
/// Exercises line 260.
#[test]
fn test_raw_eq_sort_mismatch_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        // Inject locals with incompatible sorts
        let idx_lhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", ay_bindings::Sort::int());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx_lhs);
        let idx_rhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair(
            "test_rhs",
            "test_rhs_out",
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32)),
        );
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx_rhs);

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];
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

        assert!(
            chc_ctx.sound_fallback_count() > 0,
            "raw_eq sort mismatch must increment fallback counter"
        );
    });
}

/// raw_eq coercion failure (successful equality but output sort incompatible)
/// must record fallback. Exercises line 291.
#[test]
fn test_raw_eq_coercion_failure_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        // Inject matching bitvec locals so equality succeeds
        let idx_lhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", ay_bindings::Sort::bitvec(32));
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx_lhs);
        let idx_rhs = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_rhs", "test_rhs_out", ay_bindings::Sort::bitvec(32));
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx_rhs);

        // Corrupt destination output sort to array (incompatible with bool/bv result)
        let dest_vec_idx = chc_ctx.state_idx_for_local(destination.local);
        let (dest_name, _dest_sort) = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].clone();
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx] = (
            dest_name,
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32)),
        );
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];
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

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "raw_eq coercion failure must increment fallback counter"
        );
    });
}

/// raw_eq unresolved operands (bogus locals) must record fallback.
/// Exercises line 304.
#[test]
fn test_raw_eq_unresolved_operands_increments_fallback() {
    with_call_scaffold(|chc_ctx, destination, target, from_app, sc, ml, _bb_idx| {
        let bogus_args = [
            Operand::Copy(Place { local: 998usize, projection: vec![] }),
            Operand::Copy(Place { local: 999usize, projection: vec![] }),
        ];
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let dummy_func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let ecx = CallEmitContext {
            args: &bogus_args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_raw_eq_impl(&dummy_func, &ecx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "raw_eq unresolved operands must increment fallback counter"
        );
    });
}

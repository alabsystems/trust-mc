// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `record_fallback()` paths in `codegen_call_slice.rs`.
//!
//! Each test forces a specific fail-open path and asserts that `record_fallback()`
//! was called (via `sound_fallback_count()` field). Without these, a regression removing
//! any `record_fallback()` call is invisible to the test suite.
//!
//! Part of #2783 (codegen_call_slice record_fallback test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use rustc_public::mir::{Operand, Place};

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;

/// Minimal Rust source providing a call site for scaffold extraction.
const FALLBACK_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x + 1 }

    pub fn probe_slice_fallback(x: u32) -> u32 {
        helper(x)
    }
"#;

const SLICE_FIRST_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_zero_len_array_first(empty_array: &[u8; 0]) -> Option<&u8> {
        empty_array.first()
    }

    pub fn probe_zst_array_first(zst_array: &[(); 10]) -> Option<&()> {
        zst_array.first()
    }
"#;

/// Extracts call-site scaffold from MIR and invokes `body` with a ready-to-use
/// `ChcCtx`, destination, target, from_app, stmt_constraints, and modified_locals.
fn with_slice_scaffold(
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Place,
        usize, // target
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
    ) + Send,
) {
    with_test_ay_ctx_for_source(FALLBACK_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_fallback");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_slice_fallback", ChcConfig::default());
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
            call_site.expect("expected call terminator in probe_slice_fallback MIR");
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

        body(&mut chc_ctx, &destination, target, &from_app, &stmt_constraints, &modified_locals);
    });
}

fn with_slice_first_scaffold(
    fn_name: &str,
    body: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
    ) + Send,
) {
    with_test_ay_ctx_for_source(SLICE_FIRST_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            if chc_ctx.detect_stub_matching(func, |stub| matches!(stub, StubKind::SliceFirst))
                != Some(StubKind::SliceFirst)
            {
                continue;
            }
            call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
            break;
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected SliceFirst call in probe");
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
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
        );
    });
}

// =============================================================================
// Test 1: Slice equality sort mismatch — one operand is Array, other is Bool
// Exercises line 153 of codegen_call_slice.rs
// =============================================================================

/// When two resolved operands have incompatible non-bitvec sorts (Array vs Bool),
/// the eq comparison branch falls through to the `else` sort-mismatch path and
/// must record a fallback.
#[test]
fn test_slice_eq_sort_mismatch_increments_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        // Inject locals 0 and 1 with different non-bitvec sorts
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));
        let bool_sort = ay_bindings::Sort::bool();

        let idx0 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", array_sort.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx0);
        chc_ctx.encode.local_expr_env.insert(0, Expr::var("test_lhs", array_sort));

        let idx1 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_rhs", "test_rhs_out", bool_sort.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx1);
        chc_ctx.encode.local_expr_env.insert(1, Expr::var("test_rhs", bool_sort));

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
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

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice equality sort mismatch must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 1b: Slice equality Array vs BV — reinterpret coercion avoids fallback
// Part of #3951: BV→Array coercion for slice literal vs Vec data.
// =============================================================================

/// When one operand is Array(BV64→BV32) and the other is BV128 (= 4 × BV32),
/// `reinterpret_fixed_layout_expr` coerces the BV to a matching Array, and
/// the equality does NOT fall back. This exercises the #3951 fix.
#[test]
fn test_slice_eq_bv_to_array_coercion_avoids_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let array_sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(32));
        // BV128 = 4 × BV32 elements — reinterpretable as Array(BV64, BV32).
        let bv128_sort = ay_bindings::Sort::bitvec(128);

        let idx0 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", array_sort.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx0);
        chc_ctx.encode.local_expr_env.insert(0, Expr::var("test_lhs", array_sort));

        let idx1 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_rhs", "test_rhs_out", bv128_sort.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx1);
        chc_ctx.encode.local_expr_env.insert(1, Expr::var("test_rhs", bv128_sort));

        // Need a destination state var for the eq result (bool-width BV).
        let dest_idx = chc_ctx.state_var_mgr.state_vars.len();
        let dest_sort = ay_bindings::Sort::bitvec(8);
        chc_ctx.push_state_var_pair("test_dest", "test_dest_out", dest_sort);
        chc_ctx.state_var_mgr.local_to_state_idx.insert(destination.local, dest_idx);

        let args = [
            Operand::Copy(Place { local: 0usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
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

        assert!(chc_ctx.vc.rules.len() > before_rules, "expected at least one rule emitted");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "BV128 → Array(BV64,BV32) coercion should avoid fallback (Part of #3951)"
        );
    });
}

// =============================================================================
// Test 2: Slice index with unresolvable operands (non-empty args)
// Exercises line 320 of codegen_call_slice.rs
// =============================================================================

/// When slice index is called with >=2 args but both operands point to locals
/// that cannot be resolved (no local_expr_env, no state var mapping), the index
/// path falls through to the constrained symbolic fallback and must record it.
#[test]
fn test_slice_index_unresolvable_operands_increments_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        // Use local 1 (parameter x: u32, exists in MIR) but strip its CHC-level
        // mappings so translate_operand_with_modified / resolve_ref_or_const_referent
        // return None. Both args reference the same local — it only needs to be
        // unresolvable, not distinct.
        chc_ctx.encode.local_expr_env.remove(&1);
        chc_ctx.state_var_mgr.local_to_state_idx.remove(&1);
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
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

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice index with unresolvable operands must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 3: Slice index with IndexIndex variant (same path as SliceIndexIndex)
// Exercises line 320 via IndexIndex variant
// =============================================================================

/// Same unresolvable path but via `IndexIndex` variant — both StubKind variants
/// route to the same `codegen_call_slice_index_impl` and must both record fallback.
#[test]
fn test_index_index_unresolvable_operands_increments_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        // Use local 1 (parameter x: u32, exists in MIR) but strip its CHC-level
        // mappings so translate_operand_with_modified / resolve_ref_or_const_referent
        // return None. Both args reference the same local — it only needs to be
        // unresolvable, not distinct.
        chc_ctx.encode.local_expr_env.remove(&1);
        chc_ctx.state_var_mgr.local_to_state_idx.remove(&1);
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
        ];

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::IndexIndex,
            args: &args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "IndexIndex with unresolvable operands must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 4: ZST slice index with destination sort mismatch
// Exercises line 354 of codegen_call_slice.rs (emit_slice_index_zst fallback)
// =============================================================================

/// When ZST element detection succeeds but the destination output sort is
/// incompatible with the Unit constructor (e.g., Array sort), the ZST path
/// falls through to the sort-mismatch fallback in `emit_slice_index_zst`.
#[test]
fn test_slice_index_zst_sort_mismatch_increments_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, _ml| {
        // We need the ZST path to trigger but the output slot to have an
        // incompatible sort. The ZST path requires chc_slice_elem_ty to return
        // a ZST type, which requires the first operand to be a slice/array ref.
        // Since we can't easily construct typed MIR operands, we instead call
        // emit_slice_index_zst directly (it's the inner function that records
        // the fallback at line 354).
        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);

        // Set the destination output sort to Array (incompatible with Unit struct)
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(32), ay_bindings::Sort::bitvec(32));

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let new_output_args = chc_ctx.build_output_args(&HashSet::new(), &[dest_local]);
        chc_ctx.emit_slice_index_zst(dest_local, target, from_app, sc, &new_output_args);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "ZST slice index with sort mismatch must increment fallback counter"
        );
    });
}

// =============================================================================
// Test 5: Slice equality with both operands resolvable to same sort — no fallback
// Negative test: verifies the happy path does NOT increment sound_fallback_count()
// =============================================================================

/// When both operands resolve to the same bitvec sort, slice equality should
/// produce a constrained rule without incrementing the fallback counter.
#[test]
fn test_slice_eq_same_sort_no_fallback() {
    with_slice_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let bv32 = ay_bindings::Sort::bitvec(32);

        let idx0 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_lhs", "test_lhs_out", bv32.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(0, idx0);
        chc_ctx.encode.local_expr_env.insert(0, Expr::var("test_lhs", bv32.clone()));

        let idx1 = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("test_rhs", "test_rhs_out", bv32.clone());
        chc_ctx.state_var_mgr.local_to_state_idx.insert(1, idx1);
        chc_ctx.encode.local_expr_env.insert(1, Expr::var("test_rhs", bv32));

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

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "slice equality with matching sorts should NOT increment fallback counter"
        );
    });
}

#[test]
fn test_slice_first_zero_len_flattened_enum_without_tuple_marker_no_fallback() {
    with_slice_first_scaffold(
        "probe_zero_len_array_first",
        |chc_ctx, args, destination, target, from_app, sc, ml| {
            let dest_local = destination.local;
            let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
            assert!(
                chc_ctx.flatten.flattened_tuple_locals.remove(&dest_local),
                "precondition: slice::first result local should start flattened"
            );
            assert!(
                chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1.is_bool(),
                "precondition: flattened Option result should expose a Bool discriminant slot"
            );
            chc_ctx.flatten.flattened_local_field_count.insert(dest_local, 2);
            chc_ctx.flatten.flattened_enum_discr.entry(dest_local).or_insert((1, 0));

            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

            let cx = ChcCallContext {
                stub: StubKind::SliceFirst,
                args,
                destination,
                target,
                from_app,
                stmt_constraints: sc,
                modified_locals: ml,
            };
            chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "slice::first should still emit a rule when only the tuple-local marker is absent"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "zero-length slice::first should not fall back when flattened enum metadata remains"
            );
        },
    );
}

#[test]
fn test_slice_first_zst_flattened_enum_without_tuple_marker_no_fallback() {
    with_slice_first_scaffold(
        "probe_zst_array_first",
        |chc_ctx, args, destination, target, from_app, sc, ml| {
            let dest_local = destination.local;
            let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
            assert!(
                chc_ctx.flatten.flattened_tuple_locals.remove(&dest_local),
                "precondition: slice::first result local should start flattened"
            );
            assert!(
                chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1.is_bool(),
                "precondition: flattened Option result should expose a Bool discriminant slot"
            );
            chc_ctx.flatten.flattened_local_field_count.insert(dest_local, 2);
            chc_ctx.flatten.flattened_enum_discr.entry(dest_local).or_insert((1, 0));

            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

            let cx = ChcCallContext {
                stub: StubKind::SliceFirst,
                args,
                destination,
                target,
                from_app,
                stmt_constraints: sc,
                modified_locals: ml,
            };
            chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "slice::first should still emit a rule when only the tuple-local marker is absent"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "non-empty ZST slice::first should not fall back when flattened enum metadata remains"
            );
        },
    );
}

// =============================================================================
// Slice fallback counter coverage (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

/// SlicePartialEqEqual unresolved fallback must increment CHC fallback counter.
#[test]
fn test_slice_partial_eq_empty_args_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_slice_eq_fallback(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_eq_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_slice_eq_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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
            call_site.expect("expected call terminator in probe_slice_eq_fallback MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );

        let cx = ChcCallContext {
            stub: StubKind::SlicePartialEqEqual,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one slice-eq transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "SlicePartialEqEqual unresolved fallback must increment CHC fallback counter"
        );
    });
}

/// Slice index over-approximation fallback must increment CHC fallback counter.
#[test]
fn test_slice_index_stub_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_slice_index_fallback(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_index_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_slice_index_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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
            call_site.expect("expected call terminator in probe_slice_index_fallback MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one slice-index transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "slice-index over-approximation must increment CHC fallback counter"
        );
    });
}

/// Unexpected non-slice stub routed into slice handler must increment CHC
/// fallback counter.
#[test]
fn test_slice_stub_unexpected_variant_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_slice_unexpected_stub(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_unexpected_stub");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_slice_unexpected_stub", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
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
            call_site.expect("expected call terminator in probe_slice_unexpected_stub MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: fallback counter should start at zero"
        );

        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one slice fallback transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "unexpected stub in slice handler must increment CHC fallback counter"
        );
    });
}

/// SlicePartialEqEqual with sort-mismatched operands (Array vs Int) must
/// record fallback. Part of #2783.
#[test]
fn test_slice_partial_eq_sort_mismatch_increments_fallback() {
    with_misc_fallback_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
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

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        // Production now handles sort mismatches without fallback (improved encoding).
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "SlicePartialEqEqual sort mismatch should not increment fallback after encoding improvement"
        );
    });
}

/// IndexIndex over-approximation fallback must increment CHC fallback counter.
/// Part of #2783.
#[test]
fn test_index_index_stub_increments_sound_fallback_counter() {
    with_misc_fallback_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

        let cx = ChcCallContext {
            stub: StubKind::IndexIndex,
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_stub_parity_impl(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "IndexIndex over-approximation must increment CHC fallback counter"
        );
    });
}

/// Shared scaffold for slice/raw_eq fallback tests.
fn with_misc_fallback_scaffold(
    body_fn: impl FnOnce(&mut ChcCtx<'_, '_>, &Place, usize, &RelationApp, &[Expr], &HashSet<usize>)
    + Send,
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

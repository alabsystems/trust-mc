// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for Range-based slice indexing in `codegen_call_slice_range.rs`.
//!
//! Covers `is_range_type_operand`, `is_range_inclusive_operand`, `operand_local`,
//! and fallback/happy paths in `codegen_call_slice_range_index`.
//!
//! Part of #3339 (zero test coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use rustc_public::mir::{Operand, Place, ProjectionElem};

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;

/// Minimal probe: plain `u32 -> u32` function providing a call site scaffold.
const RANGE_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x + 1 }

    pub fn probe_range(x: u32) -> u32 {
        helper(x)
    }
"#;

/// Source with Range<usize> type for `is_range_type_operand` tests.
const RANGE_TYPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_range_type(s: &[u8]) -> &[u8] {
        &s[1..3]
    }
"#;

/// Isolated range-index fragments from `tests/trust_mc/PointerComparison/ptr_comparison.rs`.
/// These exclude the pointer-comparison helper calls so the test can localize
/// whether remaining `call_dispatch_fallback` drops still come from the
/// slice-range path itself.
const PTR_COMPARISON_RANGE_ONLY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_box_slice_range_only() {
        let obj = Box::new([0u16, 10]);
        let _first: *const [u16] = &obj[1..2];
        let _second: *const [u16] = &obj[1..2];
    }

    pub fn probe_slice_len_range_only() {
        let array = [0u8; 10];
        let _first: *const [u8] = &array[0..2];
        let _second: *const [u8] = &array[0..4];
        let _third: *const [u8] = &array[4..6];
        let _fourth: *const [u8] = &array[4..5];
        let _fifth: *const [u8] = &array[4..];
    }
"#;

const PTR_COMPARISON_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/PointerComparison/ptr_comparison.rs");

fn strip_ptr_comparison_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(
        source.len()
            + "#![allow(dead_code)]\n#![allow(ambiguous_wide_pointer_comparisons)]\n".len(),
    );
    result.push_str("#![allow(dead_code)]\n");
    result.push_str("#![allow(ambiguous_wide_pointer_comparisons)]\n");
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[cfg_attr(kani,") || trimmed.starts_with("// kani-expect:") {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

/// Scaffold: build a ChcCtx with declared block relations and extract call-site
/// components ready for testing individual call handlers.
fn with_range_scaffold(
    body_fn: impl FnOnce(&mut ChcCtx<'_, '_>, &Place, usize, &RelationApp, &[Expr], &HashSet<usize>)
    + Send,
) {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, "probe_range", ChcConfig::default());
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
            call_site.expect("expected call terminator in probe_range MIR");
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

        body_fn(&mut chc_ctx, &destination, target, &from_app, &stmt_constraints, &modified_locals);
    });
}

/// Scaffold using the real `&s[1..3]` MIR so tests can exercise range recovery
/// from aggregate constants instead of synthetic flattened state.
fn with_real_range_type_scaffold(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
    ) + Send,
) {
    with_test_ay_ctx_for_source(RANGE_TYPE_SOURCE, |ctx| {
        use rustc_public::mir::TerminatorKind;

        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_type");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, "probe_range_type", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            let TerminatorKind::Call { args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                continue;
            };
            if args.len() == 2 && ChcCtx::is_range_type_operand(&args[1], mir_body.locals()) {
                call_site = Some((bb_idx, args, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected slice range call terminator in probe_range_type MIR");
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

        body_fn(
            &mut chc_ctx,
            args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
        );
    });
}

fn seed_u8_slice_backing(chc_ctx: &mut ChcCtx<'_, '_>, local: usize) {
    let base = Expr::const_array(
        ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
        Expr::bitvec_const(0u64, 8),
    );
    let data = base
        .store(
            Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(10u64, 8),
        )
        .store(
            Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(20u64, 8),
        )
        .store(
            Expr::bitvec_const(2u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(30u64, 8),
        )
        .store(
            Expr::bitvec_const(3u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(40u64, 8),
        );
    chc_ctx.ref_resolution.const_ref_values.insert(local, data);
    chc_ctx
        .ref_resolution
        .subslice_len
        .insert(local, Expr::bitvec_const(4u64, crate::codegen_ay::types::POINTER_WIDTH));
    chc_ctx.ref_resolution.subslice_offset.remove(&local);
}

fn reset_slice_range_dispatch_metadata() {
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_slice_rebase_source_index_uses_raw_offset_for_first_element() {
    let offset = Expr::var("slice_offset", crate::codegen_ay::types::ptr_sort());
    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);

    let src_idx = ChcCtx::slice_rebase_source_index(&offset, zero, 0);

    assert_eq!(src_idx, offset, "the first rebased element must select at offset, not offset + 0");
}

#[test]
fn test_slice_rebase_source_index_adds_offset_for_later_elements() {
    let offset = Expr::var("slice_offset", crate::codegen_ay::types::ptr_sort());
    let one = Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH);

    let src_idx = ChcCtx::slice_rebase_source_index(&offset, one, 1);

    assert!(
        matches!(src_idx.value(), ay_bindings::ExprValue::BvAdd(_, _)),
        "later rebased elements should still select at offset + index"
    );
}

// =============================================================================
// operand_local tests
// =============================================================================

/// Copy of a bare local returns Some(local index).
#[test]
fn test_operand_local_copy_bare_returns_some() {
    let place = Place { local: 5usize, projection: vec![] };
    let op = Operand::Copy(place);
    assert_eq!(ChcCtx::operand_local(&op), Some(5));
}

/// Move of a bare local returns Some(local index).
#[test]
fn test_operand_local_move_bare_returns_some() {
    let place = Place { local: 3usize, projection: vec![] };
    let op = Operand::Move(place);
    assert_eq!(ChcCtx::operand_local(&op), Some(3));
}

/// Copy with projection returns None.
#[test]
fn test_operand_local_copy_with_projection_returns_none() {
    let place = Place { local: 5usize, projection: vec![ProjectionElem::Deref] };
    let op = Operand::Copy(place);
    assert_eq!(ChcCtx::operand_local(&op), None);
}

/// Move with projection returns None.
#[test]
fn test_operand_local_move_with_projection_returns_none() {
    let place = Place { local: 7usize, projection: vec![ProjectionElem::Deref] };
    let op = Operand::Move(place);
    assert_eq!(ChcCtx::operand_local(&op), None);
}

// =============================================================================
// is_range_type_operand tests (requires real MIR context)
// =============================================================================

/// `is_range_type_operand` returns false for non-Range types (u32).
#[test]
fn test_is_range_type_operand_false_for_u32() {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range");
        let mir_body = instance.body().expect("function body");

        // Local 1 is the parameter x: u32.
        let place = Place { local: 1usize, projection: vec![] };
        let op = Operand::Copy(place);
        assert!(
            !ChcCtx::is_range_type_operand(&op, mir_body.locals()),
            "u32 operand should not be detected as Range type"
        );
        assert!(
            !ChcCtx::is_range_inclusive_operand(&op, mir_body.locals()),
            "u32 operand should not be detected as RangeInclusive type"
        );
    });
}

/// `is_range_type_operand` detects Range<usize> locals in slice indexing MIR.
#[test]
fn test_is_range_type_operand_detects_range_in_mir() {
    with_test_ay_ctx_for_source(RANGE_TYPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range_type");
        let mir_body = instance.body().expect("function body");

        // Scan all locals for Range-typed ones.
        let mut found_range = false;
        for (idx, local) in mir_body.locals().iter().enumerate() {
            let ty = local.ty;
            if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)) =
                ty.kind()
            {
                if def.trimmed_name() == "Range" {
                    let place = Place { local: idx, projection: vec![] };
                    let op = Operand::Copy(place);
                    assert!(
                        ChcCtx::is_range_type_operand(&op, mir_body.locals()),
                        "Local {} has Range type but is_range_type_operand returned false",
                        idx
                    );
                    assert!(
                        !ChcCtx::is_range_inclusive_operand(&op, mir_body.locals()),
                        "Range (not Inclusive) local should return false for is_range_inclusive"
                    );
                    found_range = true;
                }
            }
        }

        assert!(found_range, "Expected at least one Range<usize> local in probe_range_type MIR");
    });
}

/// Real MIR aggregate range locals should lower without flattened field state
/// when bounds are recoverable from the aggregate constructor itself.
#[test]
fn test_range_index_mir_constant_bounds_do_not_require_flattened_state() {
    with_real_range_type_scaffold(|chc_ctx, args, destination, target, from_app, sc, ml| {
        let (slice_arg, index_arg) = chc_ctx.split_chc_slice_index_args(args);
        let slice_local =
            ChcCtx::operand_local(slice_arg).expect("slice receiver should be a local");
        let index_arg = index_arg.expect("slice range call should have an index arg");
        let range_local = ChcCtx::operand_local(index_arg).expect("range index should be a local");

        seed_u8_slice_backing(chc_ctx, slice_local);
        chc_ctx.state_var_mgr.local_to_state_idx.remove(&range_local);
        assert!(
            chc_ctx.flattened_local_field_expr(range_local, 0, ml).is_none(),
            "test precondition: start should not be available from flattened state"
        );
        assert!(
            chc_ctx.flattened_local_field_expr(range_local, 1, ml).is_none(),
            "test precondition: end should not be available from flattened state"
        );

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.sound_fallback_count();
        let dest_local = destination.local;

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, slice_arg, index_arg, false);

        assert!(chc_ctx.vc.rules.len() > before_rules, "expected range codegen to emit rules");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "MIR aggregate bounds should avoid sound fallback without flattened state"
        );

        let subslice_len = chc_ctx
            .ref_resolution
            .subslice_len
            .get(&dest_local)
            .expect("successful range lowering should record subslice_len");
        assert_eq!(
            subslice_len.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "successful range lowering should record a pointer-width subslice_len"
        );
    });
}

#[test]
fn test_ptr_comparison_range_only_detects_index_stubs() {
    with_test_ay_ctx_for_source(PTR_COMPARISON_RANGE_ONLY_SOURCE, |ctx| {
        for (fn_name, expected_count) in
            [("probe_box_slice_range_only", 2usize), ("probe_slice_len_range_only", 5usize)]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

            let detected = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    rustc_public::mir::TerminatorKind::Call { func, .. } => {
                        chc_ctx.detect_stub(func)
                    }
                    _ => None,
                })
                .filter(|stub| matches!(stub, StubKind::IndexIndex | StubKind::SliceIndexIndex))
                .count();

            assert_eq!(
                detected, expected_count,
                "{fn_name} should classify every ptr_comparison-style range index call as a slice stub"
            );
        }
    });
}

#[test]
fn test_ptr_comparison_range_only_stays_off_call_dispatch_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(PTR_COMPARISON_RANGE_ONLY_SOURCE, |ctx| {
        for fn_name in ["probe_box_slice_range_only", "probe_slice_len_range_only"] {
            reset_slice_range_dispatch_metadata();

            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, _diagnostics) = chc_ctx.translate_with_diagnostics();
            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
            let call_dispatch_fallbacks = fn_sites
                .iter()
                .filter(|(reason, _)| *reason == "call_dispatch_fallback")
                .map(|(_, count)| *count)
                .sum::<usize>();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            assert_eq!(
                call_dispatch_fallbacks, 0,
                "{fn_name} should keep isolated range-only ptr_comparison fragments off call_dispatch_fallback, sites={fn_sites:?}"
            );
        }
    });
}

// =============================================================================
// codegen_call_slice_range_index fallback path tests
// =============================================================================

/// When the index operand is not a bare local (has projection), the range
/// indexing path falls through to the "index not a bare local" fallback.
#[test]
fn test_range_index_not_bare_local_increments_fallback() {
    with_range_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let dest_local = destination.local;

        let slice_op = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let index_op =
            Operand::Copy(Place { local: 2usize, projection: vec![ProjectionElem::Deref] });

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[slice_op.clone(), index_op.clone()],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, &slice_op, &index_op, false);

        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "expected at least one fallback rule emitted"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "non-bare-local index must record sound fallback"
        );
    });
}

/// When the index is a bare local but no flattened field state vars exist
/// (flattened_local_field_expr returns None), the range indexing path
/// takes the "cannot extract Range fields" fallback.
#[test]
fn test_range_index_no_flattened_fields_increments_fallback() {
    with_range_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let dest_local = destination.local;

        let slice_op = Operand::Copy(Place { local: 1usize, projection: vec![] });
        // Local 99 has no state var mapping, so flattened_local_field_expr returns None.
        let index_op = Operand::Copy(Place { local: 99usize, projection: vec![] });

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[slice_op.clone(), index_op.clone()],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, &slice_op, &index_op, false);

        assert!(chc_ctx.vc.rules.len() > before_rules, "expected fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "missing flattened Range fields must record sound fallback"
        );
    });
}

/// When Range fields exist and coerce to pointer width, the happy path emits
/// bounds guard rules (reversed range -> error) plus a transition rule.
#[test]
fn test_range_index_happy_path_emits_bounds_guards() {
    with_range_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let dest_local = destination.local;

        // Create 2 state var slots for Range start/end and map local 10.
        let bv_sort = ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH);
        let base_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("range_start_0", "range_start_0_out", bv_sort.clone());
        chc_ctx.push_state_var_pair("range_end_0", "range_end_0_out", bv_sort);
        chc_ctx.state_var_mgr.local_to_state_idx.insert(10, base_idx);

        let slice_op = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let index_op = Operand::Copy(Place { local: 10usize, projection: vec![] });

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[slice_op.clone(), index_op.clone()],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, &slice_op, &index_op, false);

        // At minimum: reversed-range guard (start > end -> error) + output rule.
        let new_rule_count = chc_ctx.vc.rules.len() - before_rules;
        assert!(
            new_rule_count >= 2,
            "expected at least 2 rules (reversed guard + output), got {}",
            new_rule_count
        );

        let has_error_rule = chc_ctx.vc.rules.iter().any(|r| r.head.name.contains("error"));
        assert!(has_error_rule, "expected error rule for reversed-range bounds guard");
    });
}

/// Inclusive range (RangeInclusive) also emits bounds guard rules.
#[test]
fn test_range_index_inclusive_emits_rules() {
    with_range_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let dest_local = destination.local;

        let bv_sort = ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH);
        let base_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("range_start_1", "range_start_1_out", bv_sort.clone());
        chc_ctx.push_state_var_pair("range_end_1", "range_end_1_out", bv_sort);
        chc_ctx.state_var_mgr.local_to_state_idx.insert(10, base_idx);

        let slice_op = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let index_op = Operand::Copy(Place { local: 10usize, projection: vec![] });

        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[slice_op.clone(), index_op.clone()],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, &slice_op, &index_op, true);

        let new_rule_count = chc_ctx.vc.rules.len() - before_rules;
        assert!(
            new_rule_count >= 2,
            "inclusive range should emit bounds guard + output rules, got {}",
            new_rule_count
        );
    });
}

/// When Range fields have non-bitvec sort (Bool), coerce_to_pointer_width fails,
/// triggering the start-coerce fallback path.
#[test]
fn test_range_index_start_coerce_fail_increments_fallback() {
    with_range_scaffold(|chc_ctx, destination, target, from_app, sc, ml| {
        let dest_local = destination.local;

        // Bool sort is not bitvec -- coerce_to_pointer_width returns None.
        let bool_sort = ay_bindings::Sort::bool();
        let base_idx = chc_ctx.state_var_mgr.state_vars.len();
        chc_ctx.push_state_var_pair("range_start_2", "range_start_2_out", bool_sort.clone());
        chc_ctx.push_state_var_pair("range_end_2", "range_end_2_out", bool_sort);
        chc_ctx.state_var_mgr.local_to_state_idx.insert(10, base_idx);

        let slice_op = Operand::Copy(Place { local: 1usize, projection: vec![] });
        let index_op = Operand::Copy(Place { local: 10usize, projection: vec![] });

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition");

        let cx = ChcCallContext {
            stub: StubKind::SliceIndexIndex,
            args: &[slice_op.clone(), index_op.clone()],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_slice_range_index(&cx, dest_local, &slice_op, &index_op, false);

        assert!(chc_ctx.vc.rules.len() > before_rules, "expected fallback rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "non-bitvec Range start field must trigger coerce fallback"
        );
    });
}

// =============================================================================
// Full check_box_comparison pattern — diagnostic for sfb=1 source
// =============================================================================

/// Mirrors `check_box_comparison` from `tests/trust_mc/PointerComparison/ptr_comparison.rs`
/// including the `compare_equal` helper, to identify which call in the full
/// harness generates the remaining sound_fallback after D1 signedness fix.
///
/// Part of #4030.
const PTR_CMP_FULL_BOX_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cmp::*;

    fn compare_equal<T: ?Sized>(obj1: *const T, obj2: *const T) {
        assert_eq!(obj1.cmp(&obj2), Ordering::Equal);
        assert!(obj1 <= obj2);
        assert!(obj1 >= obj2);
        assert!(obj1 == obj2);
        assert!(!(obj1 > obj2));
        assert!(!(obj1 < obj2));
        assert!(!(obj1 != obj2));
        assert_eq!(obj1.min(obj2), obj1);
        assert_eq!(obj1.max(obj2), obj1);
    }

    pub fn probe_full_box_comparison() {
        let obj = Box::new([0u16, 10]);
        let first: *const [u16] = &obj[1..2];
        let second: *const [u16] = &obj[1..2];
        assert_eq!(second as *const (), first as *const (), "Expected same data address");
        compare_equal(first, second);
    }
"#;

#[test]
fn test_full_box_comparison_fallback_reasons() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(PTR_CMP_FULL_BOX_SOURCE, |ctx| {
        let fn_name = "probe_full_box_comparison";
        reset_slice_range_dispatch_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let compare_equal_sites =
            translation_sites.get("compare_equal").cloned().unwrap_or_default();

        // Diagnostic: print all fallback reasons for inspection.
        let total_sfb = diagnostics.fallback_count.get();
        let all_reasons: Vec<_> = fn_sites.iter().collect();

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        // The isolated range-only probe has 0 call_dispatch_fallback (confirmed
        // by test_ptr_comparison_range_only_stays_off_call_dispatch_fallback).
        // This test documents which specific reason generates the remaining
        // sound_fallback in the full harness pattern.
        //
        // Expected: sfb comes from fn_inline processing of compare_equal,
        // not from Range extraction or Box::new.
        let call_dispatch_fallbacks: usize = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum();
        let inline_fallbacks: usize = fn_sites
            .iter()
            .filter(|(reason, _)| reason.starts_with("fn_inline"))
            .map(|(_, count)| *count)
            .sum();

        // Record for diagnostic visibility (test output on failure shows these).
        eprintln!(
            "{fn_name}: total_sfb={total_sfb}, call_dispatch_fallback={call_dispatch_fallbacks}, \
             inline_fallbacks={inline_fallbacks}, all_reasons={all_reasons:?}, \
             compare_equal_sites={compare_equal_sites:?}, translation_sites={translation_sites:?}"
        );
    });
}

#[test]
fn test_ptr_comparison_exact_file_box_slice_fallback_reasons() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    let source = strip_ptr_comparison_for_unit_ctx(PTR_COMPARISON_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        for fn_name in ["check_box_comparison", "check_slice_data_ptr"] {
            reset_slice_range_dispatch_metadata();

            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
            let compare_equal_sites =
                translation_sites.get("compare_equal").cloned().unwrap_or_default();
            let fallback_counts = get_chc_fallback_counts();
            let fn_drop_reasons = drop_fallback_reasons.get(fn_name).cloned().unwrap_or_default();

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            eprintln!(
                "[exact-file ptr_comparison] {fn_name}: fallback_count(fn)={}, \
                 diagnostics_fallback_count={}, fn_drop_reasons={fn_drop_reasons:?}, fn_sites={fn_sites:?}, \
                 compare_equal_sites={compare_equal_sites:?}, fallback_counts={fallback_counts:?}, \
                 drop_fallback_reasons={drop_fallback_reasons:?}, translation_sites={translation_sites:?}",
                fallback_counts.get(fn_name).copied().unwrap_or(0),
                diagnostics.fallback_count.get(),
            );
        }
    });
}

#[test]
fn test_ptr_comparison_exact_file_slice_len_proves() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    let source = strip_ptr_comparison_for_unit_ctx(PTR_COMPARISON_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_name = "check_slice_len";
        reset_slice_range_dispatch_metadata();

        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks: usize = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should stay off call_dispatch_fallback after the ptr-comparison recovery, sites={fn_sites:?}"
        );
        assert_eq!(
            diagnostics.inferable_predicate.get(),
            0,
            "{fn_name} should not rely on inferable summaries"
        );
        assert_z3_result(&smt, "unsat");
    });
}

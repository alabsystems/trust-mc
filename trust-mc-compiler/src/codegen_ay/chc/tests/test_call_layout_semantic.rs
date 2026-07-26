// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for layout-construction semantics — LayoutArray, LayoutNew,
//! LayoutForValueRaw, LayoutFromSizeAlign (checked and unchecked).
//!
//! Part of #1739 / #2303. Extracted from test_call_misc.rs (Part of #3746).

#![allow(clippy::unwrap_used)]

use super::common::*;
use super::test_call_alloc_layout_helpers::{
    collect_layout_extra_stubs, has_constraint_with_fragments, transition_constraint_texts,
    with_misc_usize_call_scaffold,
};
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;

// =============================================================================
// LayoutArray
// =============================================================================

/// Find the first basic block containing a call to the given `StubKind`,
/// returning `(bb_idx, destination_local, target_bb)`.
fn find_stub_call_terminator(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    matcher: fn(StubKind) -> bool,
    expected_stub: StubKind,
) -> (usize, rustc_public::mir::Local, usize) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, matcher) == Some(expected_stub)
            {
                Some((bb_idx, destination.local, *target))
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("expected {:?} call terminator", expected_stub))
}

#[test]
fn test_layout_array_semantic_payload_not_unconstrained() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_array_semantic_payload(n: usize) -> usize {
            let layout = Layout::array::<u32>(n).unwrap();
            layout.size()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_array_semantic_payload");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_layout_array_semantic_payload",
            ChcConfig::default(),
        );
        let layout_stubs = collect_layout_extra_stubs(&chc_ctx, &body);
        assert!(
            layout_stubs.contains(&StubKind::LayoutArray),
            "expected LayoutArray stub in MIR; got {:?}",
            layout_stubs
        );

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_layout_array_semantic_payload", ChcConfig::default());
        assert_vc_structure(&vc, "probe_layout_array_semantic_payload", body.blocks.len());

        let constraints = transition_constraint_texts(&vc);
        assert!(!constraints.is_empty(), "layout array should emit constrained transitions");
        assert!(
            has_constraint_with_fragments(&constraints, &["(concat", "(bvmul"]),
            "expected semantic LayoutArray encoding with concat(bvmul(size, n), align); constraints: {:?}",
            constraints
        );
        assert!(
            has_constraint_with_fragments(&constraints, &["_fld1__out", "(concat", "(bvmul"]),
            "expected flattened LayoutArray Result payload (_fld1) to be constrained; constraints: {:?}",
            constraints
        );
    });
}

#[test]
fn test_layout_array_semantic_payload_not_unconstrained_mem_track() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_array_semantic_payload_mem(n: usize) -> usize {
            let layout = Layout::array::<u32>(n).unwrap();
            layout.size()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_array_semantic_payload_mem");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_layout_array_semantic_payload_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert_vc_structure(&vc, "probe_layout_array_semantic_payload_mem", body.blocks.len());

        let constraints = transition_constraint_texts(&vc);
        assert!(
            has_constraint_with_fragments(&constraints, &["_fld1__out", "(concat", "(bvmul"]),
            "expected flattened LayoutArray Result payload (_fld1) to be constrained in mem track; constraints: {:?}",
            constraints
        );
    });
}

#[test]
fn test_layout_array_call_rule_does_not_flip_unrelated_later_local_to_output() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub unsafe fn probe_layout_array_rule_alias_regression(_n: usize) -> i32 {
            let layout = std::alloc::Layout::new::<i32>();
            let ptr = unsafe { std::alloc::alloc(layout) } as *mut i32;
            unsafe { ptr.write(42) };
            let new_layout = std::alloc::Layout::array::<i32>(2).unwrap();
            let new_ptr =
                unsafe { std::alloc::realloc(ptr as *mut u8, layout, new_layout.size()) }
                    as *mut i32;
            unsafe { new_ptr.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_array_rule_alias_regression");
        let body = instance.body().expect("function body");
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_layout_array_rule_alias_regression", config);
        chc_ctx.declare_block_relations();

        let (bb_idx, dest_local, target_bb) = find_stub_call_terminator(
            &chc_ctx,
            &body,
            StubKind::is_layout_extra,
            StubKind::LayoutArray,
        );

        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let alias_local = dest_vec_idx + 1;
        let alias_vec_idx = chc_ctx
            .try_state_idx_for_local(alias_local)
            .expect("expected later MIR local whose index overlaps LayoutArray payload slot");
        assert_ne!(
            alias_vec_idx,
            dest_vec_idx + 1,
            "test requires vec-slot overlap with a distinct later local"
        );

        let alias_in_name = chc_ctx.state_var_mgr.state_vars[alias_vec_idx].0.to_string();
        let alias_out_name = chc_ctx.state_var_mgr.output_state_vars[alias_vec_idx].0.to_string();
        let payload_out_name =
            chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx + 1].0.to_string();
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let to_rel = chc_ctx.block_relations.get(&target_bb).expect("target relation").clone();

        let vc = mir_to_chc(ctx.tcx, &body, "probe_layout_array_rule_alias_regression", config);

        let rule = vc
            .rules
            .iter()
            .find(|rule| {
                rule.body.relation.as_ref().is_some_and(|rel| rel.name == from_rel)
                    && rule.head.name == to_rel
                    && rule_contains_var(rule, &payload_out_name)
            })
            .expect("expected LayoutArray transition rule with flattened payload constraint");

        assert!(
            rule_contains_var(rule, &alias_in_name),
            "layout rule should carry the later local through as an input var"
        );
        assert!(
            !rule_contains_var(rule, &alias_out_name),
            "layout rule must not flip an unrelated later local to __out"
        );
    });
}

// =============================================================================
// LayoutFromSizeAlignUnchecked
// =============================================================================

#[test]
fn test_layout_from_size_align_unchecked_semantic_payload_not_unconstrained() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub unsafe fn probe_layout_from_size_align_unchecked_semantic_payload(
            size: usize,
            align: usize,
        ) -> usize {
            let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
            layout.align()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(
            ctx.tcx,
            "probe_layout_from_size_align_unchecked_semantic_payload",
        );
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_layout_from_size_align_unchecked_semantic_payload",
            ChcConfig::default(),
        );
        let layout_stubs = collect_layout_extra_stubs(&chc_ctx, &body);
        assert!(
            layout_stubs.contains(&StubKind::LayoutFromSizeAlignUnchecked),
            "expected LayoutFromSizeAlignUnchecked stub in MIR; got {:?}",
            layout_stubs
        );

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_layout_from_size_align_unchecked_semantic_payload",
            ChcConfig::default(),
        );
        assert_vc_structure(
            &vc,
            "probe_layout_from_size_align_unchecked_semantic_payload",
            body.blocks.len(),
        );

        let constraints = transition_constraint_texts(&vc);
        assert!(
            !constraints.is_empty(),
            "layout from_size_align should emit constrained transitions"
        );
        assert!(
            has_constraint_with_fragments(&constraints, &["(concat"]),
            "expected semantic LayoutFromSizeAlignUnchecked concat(size, align) constraint; constraints: {:?}",
            constraints
        );
    });
}

// =============================================================================
// LayoutNew
// =============================================================================

#[test]
fn test_layout_new_semantic_payload_not_unconstrained() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_new_semantic_payload() -> usize {
            let layout = Layout::new::<u16>();
            layout.align()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_new_semantic_payload");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_layout_new_semantic_payload", ChcConfig::default());
        let layout_stubs = collect_layout_extra_stubs(&chc_ctx, &body);

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_layout_new_semantic_payload", ChcConfig::default());
        assert_vc_structure(&vc, "probe_layout_new_semantic_payload", body.blocks.len());

        let constraints = transition_constraint_texts(&vc);
        assert!(!constraints.is_empty(), "layout new path should emit transition constraints");

        if layout_stubs.contains(&StubKind::LayoutNew) {
            assert!(
                has_constraint_with_fragments(&constraints, &["(concat"]),
                "expected semantic LayoutNew concat(size, align) constraint; constraints: {:?}",
                constraints
            );
        }
    });
}

// =============================================================================
// Unit-level semantic impl tests (via scaffold)
// =============================================================================

/// LayoutNew semantic handler should emit a concrete `concat(size, align)`
/// payload instead of leaving destination unconstrained.
#[test]
fn test_layout_semantic_impl_layout_new_emits_concat_constraint() {
    with_misc_usize_call_scaffold(|chc_ctx, func, _args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::LayoutNew,
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule = chc_ctx.vc.rules.last().expect("expected emitted LayoutNew rule");
        assert!(
            rule.body.constraints.len() > sc.len(),
            "LayoutNew semantic path should add at least one equality constraint"
        );
        let has_concat = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::BvConcat(_, _))
            })
        });
        assert!(
            has_concat,
            "LayoutNew semantic path should construct layout as concat(size, align)"
        );
    });
}

/// LayoutForValueRaw semantic handler should emit a concrete `concat(size, align)`
/// payload, same as LayoutNew (regression test for #3184: LayoutForValueRaw was
/// previously routed to unconstrained stub, causing false CTREX).
#[test]
fn test_layout_semantic_impl_layout_for_value_raw_emits_concat_constraint() {
    with_misc_usize_call_scaffold(|chc_ctx, func, _args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::LayoutForValueRaw,
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule = chc_ctx.vc.rules.last().expect("expected emitted LayoutForValueRaw rule");
        assert!(
            rule.body.constraints.len() > sc.len(),
            "LayoutForValueRaw semantic path should add at least one equality constraint"
        );
        let has_concat = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::BvConcat(_, _))
            })
        });
        assert!(
            has_concat,
            "LayoutForValueRaw semantic path should construct layout as concat(size, align)"
        );
    });
}

/// LayoutFromSizeAlignUnchecked with missing args should fail closed to
/// unconstrained destination update (no semantic concat constraint).
#[test]
fn test_layout_semantic_impl_from_size_align_unchecked_missing_args_falls_back_unconstrained() {
    with_misc_usize_call_scaffold(|chc_ctx, func, _args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::LayoutFromSizeAlignUnchecked,
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule = chc_ctx
            .vc
            .rules
            .last()
            .expect("expected emitted LayoutFromSizeAlignUnchecked fallback rule");
        assert_eq!(
            rule.body.constraints.len(),
            sc.len(),
            "missing-args fallback should not add semantic constraints"
        );
        let has_semantic_constraint = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::BvConcat(_, _) | ExprValue::Eq(_, _))
            })
        });
        assert!(
            !has_semantic_constraint,
            "missing-args fallback should avoid semantic layout constraints"
        );
    });
}

// =============================================================================
// Overflow guard tests (#3408)
// =============================================================================

/// Part of #3408: LayoutArray semantic handler must emit an overflow guard
/// (bvudiv-based) constraint when type_size > 0. This ensures the Ok path
/// only fires when `size_of::<T>() * n` does not wrap (checked_mul semantics).
#[test]
fn test_layout_array_overflow_guard_emits_bvudiv() {
    with_misc_usize_call_scaffold(|chc_ctx, func, args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::LayoutArray,
            args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "expected at least one transition rule for LayoutArray"
        );
        let rule = chc_ctx.vc.rules.last().expect("expected emitted LayoutArray rule");

        // The overflow guard is: bvudiv(bvmul(size, n), size) == n.
        // Verify BvUDiv appears in the emitted constraints.
        let has_overflow_guard = rule.body.constraints.iter().any(|c| {
            constraint_tree_contains(c, &|expr| matches!(expr.value(), ExprValue::BvUDiv(_, _)))
        });
        assert!(
            has_overflow_guard,
            "LayoutArray must emit overflow guard (bvudiv check for checked_mul)"
        );
    });
}

/// Part of #3408: LayoutArrayInner semantic handler must emit an overflow guard
/// using `size_nonzero => (total / size == n)` when element size is symbolic.
#[test]
fn test_layout_array_inner_overflow_guard_emits_bvudiv() {
    with_misc_usize_call_scaffold(|chc_ctx, func, args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        // LayoutArrayInner takes 3 args: (elem_size, align, count).
        // Duplicate the scaffold's arg to fill all 3 slots.
        let triple_args: Vec<_> = args.iter().cycle().take(3).cloned().collect();

        let cx = ChcCallContext {
            stub: StubKind::LayoutArrayInner,
            args: &triple_args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "expected at least one transition rule for LayoutArrayInner"
        );
        let rule = chc_ctx.vc.rules.last().expect("expected emitted LayoutArrayInner rule");

        // The overflow guard is: size_nonzero => (bvudiv(total, size) == n).
        // Verify BvUDiv appears in the emitted constraints.
        let has_overflow_guard = rule.body.constraints.iter().any(|c| {
            constraint_tree_contains(c, &|expr| matches!(expr.value(), ExprValue::BvUDiv(_, _)))
        });
        assert!(
            has_overflow_guard,
            "LayoutArrayInner must emit overflow guard (bvudiv check for checked_mul)"
        );
    });
}

// =============================================================================
// LayoutFromSizeAlign — checked variant (#3641)
// =============================================================================

/// `Layout::from_size_align(size, align)` should be routed through the semantic
/// layout path and emit a `concat(size, align)` constraint, achieving parity
/// with `LayoutFromSizeAlignUnchecked`.
#[test]
fn test_layout_from_size_align_checked_semantic_payload_not_unconstrained() {
    // Use symbolic args so concat is visible in constraints (constant args fold
    // concat into a single BitVecConst, hiding the concat node).
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::Layout;

        pub fn probe_layout_from_size_align_checked(
            size: usize,
            align: usize,
        ) -> usize {
            let layout = Layout::from_size_align(size, align).unwrap();
            layout.align()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_layout_from_size_align_checked");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_layout_from_size_align_checked",
            ChcConfig::default(),
        );
        let layout_stubs = collect_layout_extra_stubs(&chc_ctx, &body);
        // Checked from_size_align should be detected as a layout stub. It may
        // lower to LayoutFromSizeAlign or LayoutFromSizeAlignUnchecked depending
        // on MIR inlining depth.
        let has_from_size_align = layout_stubs.iter().any(|s| {
            matches!(s, StubKind::LayoutFromSizeAlign | StubKind::LayoutFromSizeAlignUnchecked)
        });
        assert!(
            has_from_size_align,
            "expected LayoutFromSizeAlign or LayoutFromSizeAlignUnchecked stub in MIR; got {:?}",
            layout_stubs
        );

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_layout_from_size_align_checked",
            ChcConfig::default(),
        );
        assert_vc_structure(&vc, "probe_layout_from_size_align_checked", body.blocks.len());

        let constraints = transition_constraint_texts(&vc);
        assert!(
            !constraints.is_empty(),
            "checked from_size_align should emit constrained transitions"
        );
        // With symbolic args, the semantic path emits concat(size, align) or
        // extract operations on the packed bv128 layout — either proves the
        // layout is being semantically constructed (not left unconstrained).
        let has_semantic_layout = has_constraint_with_fragments(&constraints, &["(concat"])
            || has_constraint_with_fragments(&constraints, &["extract"]);
        assert!(
            has_semantic_layout,
            "expected semantic LayoutFromSizeAlign concat or extract constraint; constraints: {:?}",
            constraints
        );
    });
}

/// LayoutFromSizeAlign with missing args should fail closed (sound fallback).
#[test]
fn test_layout_semantic_impl_from_size_align_checked_missing_args_falls_back_unconstrained() {
    with_misc_usize_call_scaffold(|chc_ctx, func, _args, destination, target, from_app, sc, ml| {
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::LayoutFromSizeAlign,
            args: &[],
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_layout_semantic_impl(func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule =
            chc_ctx.vc.rules.last().expect("expected emitted LayoutFromSizeAlign fallback rule");
        assert_eq!(
            rule.body.constraints.len(),
            sc.len(),
            "missing-args fallback should not add semantic constraints"
        );
        let has_semantic_constraint = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::BvConcat(_, _) | ExprValue::Eq(_, _))
            })
        });
        assert!(
            !has_semantic_constraint,
            "missing-args fallback should avoid semantic layout constraints"
        );
    });
}

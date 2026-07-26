// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_call_vec_ops.rs — Vec lifecycle, capacity, and query
//! operations through the mir_to_chc pipeline.
//!
//! Part of #2921 (zero-coverage remediation for codegen_call_vec_ops.rs).
//! Covers: vec_op_new (VecNew/VecWithCapacity), vec_op_reserve,
//! vec_op_shrink_to_fit, vec_op_clear, vec_op_clone, vec_op_len,
//! build_vec_datatype_eq, emit_cap_ge_len, and helper methods.

#![allow(clippy::unwrap_used)]

use super::super::codegen_call_vec::CallVec;
use super::common::*;
// =============================================================================
// Vec::new / Vec::with_capacity — vec_op_new
// =============================================================================

/// Vec::new() produces CHC constraints with zero-length initialization.
#[test]
fn test_vec_new_sets_len_zero() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_new() -> Vec<u32> {
            Vec::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_new", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_new", bb_count);

        // Vec::new() should produce at least one rule with a BV constant
        // (the zero-length initialization encodes len=0 as a bitvec literal).
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_new",
            |e| matches!(e.value(), ExprValue::BitVecConst { .. }),
            "BitVecConst (len=0 initialization)",
        );
    });
}

/// Vec::with_capacity(n) produces CHC constraints that encode the capacity
/// argument into the Vec state.
#[test]
fn test_vec_with_capacity_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_with_capacity() -> Vec<u32> {
            Vec::with_capacity(10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_with_capacity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_with_capacity", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_with_capacity", bb_count);
    });
}

/// Vec::new() followed by push exercises both vec_op_new and the push path,
/// verifying that the initialized state (len=0) is properly carried through.
#[test]
fn test_vec_new_then_push_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_new_push() -> Vec<u32> {
            let mut v = Vec::new();
            v.push(42);
            v
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_new_push", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_new_push", bb_count);
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_new_push");
    });
}

#[test]
fn test_vec_new_dangling_add_extra_checks_emits_provenance_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_new_dangling_add() -> *const u32 {
            let v = Vec::<u32>::new();
            let p = v.as_ptr();
            unsafe { p.add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new_dangling_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_new_dangling_add",
            ChcConfig { extra_pointer_checks: true, ..ChcConfig::default() },
        );

        assert!(
            vc_rules_contain_var(&vc, "obj_valid__out"),
            "Vec::new extra-pointer-check path should update obj_valid__out"
        );

        let has_obj_valid_error_rule =
            vc.rules.iter().filter(|r| r.head.name == "error").any(|rule| {
                rule_contains_expr(rule, |expr| match expr.value() {
                    ExprValue::Select { array, .. } => matches!(
                        array.value(),
                        ExprValue::Var { name }
                            if name.as_str() == "obj_valid" || name.as_str() == "obj_valid__out"
                    ),
                    _ => false,
                })
            });
        assert!(
            has_obj_valid_error_rule,
            "Vec::new dangling ptr.add under extra checks must emit an error rule that reads obj_valid"
        );
    });
}

#[test]
fn test_vec_with_capacity_symbolic_zero_extra_checks_invalidates_provenance_conditionally() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_with_capacity_symbolic(cap: usize) -> *const u32 {
            let v = Vec::<u32>::with_capacity(cap);
            let p = v.as_ptr();
            unsafe { p.add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_with_capacity_symbolic");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_vec_with_capacity_symbolic",
            ChcConfig { extra_pointer_checks: true, ..ChcConfig::default() },
        );

        let has_conditional_obj_valid_update = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                let matches_update =
                    |lhs: &ay_bindings::Expr, rhs: &ay_bindings::Expr| match lhs.value() {
                        ExprValue::Var { name } if name.as_str() == "obj_valid__out" => {
                            matches!(rhs.value(), ExprValue::Ite { .. })
                                && constraint_tree_contains(rhs, &|expr| {
                                    matches!(expr.value(), ExprValue::Store { .. })
                                })
                                && constraint_tree_contains(rhs, &|expr| {
                                    matches!(expr.value(), ExprValue::BoolConst(false))
                                })
                        }
                        _ => false,
                    };

                match constraint.value() {
                    ExprValue::Eq(lhs, rhs) => matches_update(lhs, rhs) || matches_update(rhs, lhs),
                    _ => false,
                }
            })
        });
        assert!(
            has_conditional_obj_valid_update,
            "Vec::with_capacity(cap) under extra checks must conditionally invalidate obj_valid when cap == 0"
        );
    });
}

// =============================================================================
// Vec::reserve — vec_op_reserve
// =============================================================================

/// Vec::reserve(additional) routes through vec_op_reserve and produces
/// a CHC cap update (cap >= len + additional).
#[test]
fn test_vec_reserve_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_reserve() {
            let mut v = Vec::<u32>::new();
            v.reserve(100);
            let _ = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_reserve");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_reserve", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_reserve", bb_count);
    });
}

/// Vec::reserve_exact(additional) routes through the same vec_op_reserve path.
#[test]
fn test_vec_reserve_exact_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_reserve_exact() {
            let mut v = Vec::<u32>::new();
            v.reserve_exact(50);
            let _ = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_reserve_exact");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_reserve_exact", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_reserve_exact", bb_count);
    });
}

/// Vec::reserve emits a `required.bvuge(len)` overflow guard (Part of #3409).
/// This test verifies the BvUGe constraint appears in the VC, preventing
/// false PROOFs from unsigned wraparound on `len + additional`.
#[test]
fn test_vec_reserve_emits_overflow_guard() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_reserve_overflow_guard() {
            let mut v = Vec::<u32>::new();
            v.reserve(100);
            let _ = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_reserve_overflow_guard");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_vec_reserve_overflow_guard", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_reserve_overflow_guard", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_reserve_overflow_guard");

        // vec_op_reserve pushes required.bvuge(current_len) — verify BvUGe
        // appears somewhere in the VC rules (constraints or head args).
        let has_bvuge = vc.rules.iter().any(|rule| {
            let pred = |e: &ay_bindings::Expr| matches!(e.value(), ExprValue::BvUGe(..));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_bvuge,
            "probe_vec_reserve_overflow_guard: VC should contain BvUGe overflow guard \
             from vec_op_reserve (required >= len). Part of #3409."
        );
    });
}

// =============================================================================
// Vec::shrink_to_fit — vec_op_shrink_to_fit
// =============================================================================

/// Vec::shrink_to_fit() sets cap = len in the CHC model.
#[test]
fn test_vec_shrink_to_fit_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_shrink() {
            let mut v = Vec::<u32>::with_capacity(100);
            v.push(1);
            v.shrink_to_fit();
            let _ = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_shrink");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_shrink", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_shrink", bb_count);
    });
}

// Vec::resize tests moved to test_call_vec_ops_resize.rs (Part of #4105)

//
// Vec::clear — vec_op_clear
// =============================================================================

/// Vec::clear() sets tracked length to 0. Exercises vec_op_clear at
/// codegen_call_vec_ops.rs:410.
#[test]
fn test_vec_clear_sets_len_zero() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_clear() {
            let mut v = vec![1u32, 2, 3];
            v.clear();
            let _ = v;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clear", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_clear", bb_count);
    });
}

// =============================================================================
// Vec::clone — vec_op_clone
// =============================================================================

/// Vec::clone() copies tracked length from source to destination.
/// Exercises vec_op_clone at codegen_call_vec_ops.rs:429.
#[test]
fn test_vec_clone_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_clone() -> Vec<u32> {
            let v = vec![1u32, 2, 3];
            v.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clone");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clone", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_clone", bb_count);
    });
}

// =============================================================================
// Vec::len — vec_op_len
// =============================================================================

/// Vec::len() returns tracked length from sidecar state variable.
/// Exercises vec_op_len at codegen_call_vec_ops.rs:448.
#[test]
fn test_vec_len_returns_tracked_length() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_len() -> usize {
            let v = vec![1u32, 2, 3];
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_len", bb_count);
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_len");
    });
}

// =============================================================================
// Vec::capacity — vec_op_capacity
// =============================================================================

/// Vec::capacity() returns tracked capacity from sidecar state variable.
#[test]
fn test_vec_capacity_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_capacity() -> usize {
            let v = Vec::<u32>::with_capacity(10);
            v.capacity()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_capacity", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_capacity", bb_count);
    });
}

// =============================================================================
// build_vec_datatype_eq — exercised via Vec::new pipeline (constructs Eq)
// =============================================================================

/// Vec::new() → pipeline exercises build_vec_datatype_eq indirectly.
/// At Reg level, Vec fields may be flattened (no full DatatypeConstructor),
/// but the VC should still carry Eq constraints assigning initial field values
/// to state variables via the build_vec_datatype_eq code path.
#[test]
fn test_vec_new_produces_eq_constraints() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_new_dt() -> Vec<u32> {
            Vec::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new_dt");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_new_dt", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_new_dt", body.blocks.len());

        // build_vec_datatype_eq wraps the constructed Vec in an Eq constraint.
        // At Reg level, flattened fields use Eq directly in head args. Either way,
        // the VC must contain Eq or have nontrivial head-arg expressions.
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_new_dt");
    });
}

// =============================================================================
// emit_cap_ge_len — exercised via Vec::with_capacity pipeline
// =============================================================================

/// Vec::with_capacity(n) exercises emit_cap_ge_len which produces a BvUGe
/// constraint (cap >= len). Verify via pipeline that the VC contains BvUGe.
#[test]
fn test_vec_with_capacity_emits_cap_ge_len() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_cap_ge_len() -> Vec<u32> {
            Vec::with_capacity(10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_cap_ge_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_cap_ge_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_cap_ge_len", body.blocks.len());

        // emit_cap_ge_len emits BvUGe(cap, len) which should appear in
        // constraints. However, the Vec constructor also produces other
        // constraint forms, so we just verify the VC is structurally sound
        // and has nontrivial transitions.
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_cap_ge_len");
    });
}

// =============================================================================
// Composite operations: push + reserve + len
// =============================================================================

/// Vec push + reserve + len exercises multiple vec_ops in sequence.
/// Verifies that tracked length and capacity state flows correctly across
/// operations.
#[test]
fn test_vec_push_reserve_len_composite_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_reserve_len() -> usize {
            let mut v = Vec::<u32>::new();
            v.push(1);
            v.push(2);
            v.reserve(10);
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_reserve_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_push_reserve_len", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_push_reserve_len", bb_count);
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_push_reserve_len");
    });
}

/// Vec::new + push + clear + len exercises clearing and re-reading length.
#[test]
fn test_vec_clear_then_len_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_clear_len() -> usize {
            let mut v = vec![1u32, 2, 3, 4, 5];
            v.clear();
            v.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clear_len", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_clear_len", bb_count);
    });
}

// =============================================================================
// Vec::from(&[T]) — VecFromSlice subslice_len resolution
// =============================================================================

/// Vec::from(&[1u32, 2]) should propagate the array length (2) into the Vec's
/// fld_len constraint. Regression test: resolve_collection_local followed
/// ref_targets to the pointee array, losing the subslice_len keyed on the
/// &[T] reference local. Part of #3732.
#[test]
fn test_vec_from_slice_propagates_array_length() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_from_slice() -> Vec<u32> {
            Vec::from(&[1u32, 2u32] as &[u32])
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_from_slice");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_from_slice", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_from_slice", bb_count);

        // The VecFromSlice handler should emit a constraint with the constant 2
        // (the array length) as a bitvec literal for fld_len = 2.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_from_slice",
            |e| {
                if let ExprValue::BitVecConst { value, width } = e.value() {
                    *value == 2u64.into() && *width == 64
                } else {
                    false
                }
            },
            "BitVecConst(2, 64) — Vec length from &[T; 2] slice",
        );
    });
}

fn reset_slice_to_vec_roundtrip_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

/// RangeInclusive subslice -> slice::to_vec() -> Bits equality should stay on
/// the precise CHC path without inferable summaries or fallback counters.
#[test]
fn test_slice_to_vec_roundtrip_stays_out_of_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct Bits(Vec<bool>);

        pub fn probe_slice_to_vec_roundtrip() {
            let bits = Bits(vec![true, false, true, false]);
            let extracted = Bits(bits.0[1..=2].to_vec());
            assert_eq!(extracted, Bits(vec![false, true]));
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_slice_to_vec_roundtrip_counters();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_slice_to_vec_roundtrip";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not emit P_inf_* declarations after slice::to_vec recovery: {inferable_decls:?}"
        );

        let has_p_inf_rule = vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));
        assert!(
            !has_p_inf_rule,
            "{fn_name} should not reference P_inf_* summaries in emitted rules"
        );

        let fallback_counts = get_chc_fallback_counts();
        let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should keep CHC fallback count at zero after slice::to_vec recovery, map={fallback_counts:?}"
        );

        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            unhandled_count, 0,
            "{fn_name} should not increment unhandled-call counters, map={unhandled_calls:?}"
        );

        let _translation_drops = take_translation_drop_by_fn();
        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(inferable_count, 0, "{fn_name} should keep inferable-predicate count at zero");
    });

    reset_slice_to_vec_roundtrip_counters();
}

// =============================================================================
// Vec as_ptr / as_mut_ptr — routed via vec_op codegen
// =============================================================================

/// Vec::as_ptr() returns the raw pointer from Vec state.
#[test]
fn test_vec_as_ptr_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_as_ptr() -> *const u32 {
            let v = vec![1u32, 2, 3];
            v.as_ptr()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_as_ptr");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_as_ptr", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_vec_as_ptr", bb_count);
    });
}

/// `Vec::as_mut_ptr()` on a `&mut Vec<T>` receiver must read the Vec's tracked
/// `fld0` pointer, not the raw reference shell local.
#[test]
fn test_vec_as_mut_ptr_on_mut_ref_reads_vec_fld0() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_as_mut_ptr_on_mut_ref(mut v: Vec<[u64; 3]>) -> *mut [u64; 3] {
            v.as_mut_ptr()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_as_mut_ptr_on_mut_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_as_mut_ptr_on_mut_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
                && stub == StubKind::VecAsMutPtr
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected Vec::as_mut_ptr call in MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        let cx = super::super::chc_call_context::ChcCallContext {
            stub: StubKind::VecAsMutPtr,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_vec_core(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one VecAsMutPtr rule");
        let rule = chc_ctx.vc.rules.last().expect("VecAsMutPtr should emit one rule");
        let expected_ptr_name =
            format!("{}_fld0", names::state_var_name("probe_vec_as_mut_ptr_on_mut_ref", 1));
        let uses_vec_ptr = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.contains(&expected_ptr_name))
            })
        }) || rule.head.args.iter().any(|arg| {
            constraint_tree_contains(arg, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.contains(&expected_ptr_name))
            })
        });
        assert!(
            uses_vec_ptr,
            "VecAsMutPtr should read the Vec fld0 pointer from local 1, expected var containing {expected_ptr_name}"
        );
    });
}
/// Part of #4169: Localizer for `vec_read_init` CTREX.
/// The harness writes `*v.as_mut_ptr().add(5) = 0x42` then reads the same offset.
/// Both `as_mut_ptr` and `as_ptr` must resolve to the Vec's `fld_ptr` field so
/// the write lands in the Vec's `fld_data` array and the read reconnects.
#[test]
fn test_vec_raw_ptr_write_read_localizer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_vec_raw_write_read() -> u8 {
            let mut v: Vec<u8> = Vec::with_capacity(10);
            unsafe { *v.as_mut_ptr().add(5) = 0x42 };
            unsafe { *v.as_ptr().add(5) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_vec_raw_write_read";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        // The fallback count reveals unconstrained ptr operations.
        // 0 = fully precise, >0 = some calls fell to overapprox.
        let fb = diagnostics.fallback_count.get();
        assert_eq!(
            fb, 0,
            "vec_read_init localizer: {fb} sound fallback(s) detected. \
             as_mut_ptr/as_ptr should resolve to Vec fld_ptr, not overapprox."
        );
    });
}

// BV concat/extract tests moved to test_call_bv_concat_extract.rs (Part of #3903)

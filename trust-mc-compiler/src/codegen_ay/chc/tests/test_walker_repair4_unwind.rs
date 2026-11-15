// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 4 of fix/chc-walker-fail-closed, the class of walker
//! fail-closed review 6 round 3 finding 6 (docs/chc-hole-fix-designs-
//! 2026-09-24.md, "Walker fail-closed: repair round 4"): a call the CHC
//! statement path MODELS (a stub, a pre-inline dispatcher, a value havoc)
//! whose callee may run a loop states Kani's unwinding assertion under a
//! declared unwind bound (`codegen_call.rs`, `model_call_unwinding_check`).
//! The BMC half is in `codegen_function/integration_bmc_model_unwind_tests.rs`;
//! the per-harness bound of the loop-removing MIR passes is in
//! `kani_middle/transform/{simple_str_iter_tests.rs, array_iter/tests.rs}`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use super::common::*;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]

    pub fn probe_vec_dedup(mut v: Vec<u8>) -> usize {
        v.dedup();
        v.len()
    }
    pub fn probe_vec_dedup_six() -> usize {
        let mut v = vec![1u8, 1, 2, 3, 3, 4];
        v.dedup();
        v.len()
    }
    pub fn probe_vec_len_only() -> usize {
        let v = vec![1u8, 2, 3];
        v.len()
    }
    pub fn probe_extend_inclusive(a: u32, b: u32) -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.extend(a..=b);
        v.len()
    }
    pub fn probe_slice_eq_full(a: [(); 6], b: [(); 6]) -> bool {
        a[..] == b[..]
    }
"#;

fn with_probe(test: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(PROBE, |ctx| {
        test(ctx.tcx);
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

fn reasons_of(ctx_name: &str) -> BTreeMap<String, usize> {
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(ctx_name)
        .unwrap_or_default()
}

/// Encode `probe` with `config` and return the VC and the fallback reasons
/// it recorded.
fn encode(
    tcx: TyCtxt<'_>,
    probe: &str,
    config: ChcConfig,
) -> (trust_mc_core::chc::ChcVc, BTreeMap<String, usize>) {
    let name = format!("walker_repair4_unwind__{probe}");
    let instance = find_instance_by_suffix(tcx, probe);
    let body = instance.body().expect("body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), config);
    (vc, reasons_of(&name))
}

fn declared_unwind(depth: u32) -> ChcConfig {
    ChcConfig { recursive_unwind_depth: depth, unwinding_assertions: true, ..ChcConfig::default() }
}

// ---------------------------------------------------------------------------
// (6) A modelled call whose callee may loop, under a declared unwind bound
// ---------------------------------------------------------------------------

/// `Vec::dedup` is a stub, and the model replaced the std loop Kani unwinds:
/// `v.dedup()` on six elements under `#[kani::unwind(2)]` verified clean where
/// Kani fails `unwinding assertion loop 1` (as did `contains`, `sort`,
/// `retain` and `Iterator::eq`). The call gets an uncertified reach check
/// under a declared bound with unwinding assertions on; without a bound, or
/// for a callee that runs no loop (`Vec::len`), it does not.
#[test]
fn test_modelled_looping_call_states_the_unwinding_assertion() {
    with_probe(|tcx| {
        let (_, reasons) = encode(tcx, "probe_vec_dedup", declared_unwind(2));
        assert!(reasons.contains_key("model_call_loop_unwind_uncertified"), "{reasons:?}");
        let (_, reasons) = encode(tcx, "probe_vec_dedup", ChcConfig::default());
        assert!(!reasons.contains_key("model_call_loop_unwind_uncertified"), "no bound: {reasons:?}");
        let (_, reasons) = encode(tcx, "probe_vec_len_only", declared_unwind(2));
        assert!(
            !reasons.contains_key("model_call_loop_unwind_uncertified"),
            "Vec::len runs no loop: {reasons:?}"
        );
    });
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness("model_call_loop_unwind_uncertified"),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::SoundHavoc
    ));
}

/// Is `expr` `bound <u U ∨ t` for some bound and the constant `unwind`?
fn is_bounded_reach_check(expr: &Expr, unwind: u64) -> bool {
    let ExprValue::Or(args) = expr.value() else {
        return false;
    };
    let names_reach =
        |e: &Expr| matches!(e.value(), ExprValue::Var { name } if name.contains("__walker_uncertified_reach"));
    let is_bound = |e: &Expr| match e.value() {
        ExprValue::BvULt(_, rhs) => {
            matches!(rhs.value(), ExprValue::BitVecConst { value, .. } if *value == unwind.into())
        }
        _ => false,
    };
    args.iter().any(names_reach) && args.iter().any(is_bound)
}

/// The check fires only where the callee's loops can run `U` passes: `dedup`
/// runs at most `len` per loop, so its check is `len < U ∨ t`, and under
/// `#[kani::unwind(8)]` a six-element `dedup` proves where Kani does
/// (`model_call_unwind_dual.rs` `u4_vec_dedup_u8_safe`).
#[test]
fn test_modelled_call_check_is_bounded_by_the_trip_count() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_vec_dedup_six", declared_unwind(8));
        assert!(reasons.contains_key("model_call_loop_unwind_uncertified"), "{reasons:?}");
        let bounded = vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .any(|c| constraint_tree_contains(c, &|e: &Expr| is_bounded_reach_check(e, 8)));
        assert!(bounded, "the check is `len < 8 ∨ t`");
    });
}

/// The bound of the check `B < U ∨ t`, for the constant `unwind`.
fn reach_check_bounds(vc: &trust_mc_core::chc::ChcVc, unwind: u64) -> Vec<Expr> {
    let mut found = Vec::new();
    for c in vc.rules.iter().flat_map(|rule| rule.body.constraints.iter()) {
        let mut stack = vec![c];
        while let Some(e) = stack.pop() {
            if is_bounded_reach_check(e, unwind)
                && let ExprValue::Or(args) = e.value()
            {
                for a in args {
                    if let ExprValue::BvULt(lhs, _) = a.value() {
                        found.push(lhs.clone());
                    }
                }
            }
            stack.extend(expr_children(e));
        }
    }
    found
}

/// `v.extend(a..=b)` runs `b - a` back edges, not `b - a + 1`: Kani fails
/// exactly when `end - start >= U` for `Range` and `RangeInclusive` alike
/// (`probes/g3_extend_grid.rs`; the inclusive fold yields its last element
/// after the loop). The bound was `end - start + 1`, so
/// `v.extend(0..4)` under `unwind(5)` failed where Kani proves
/// (`model_call_unwind_bound_dual.rs` `b3_extend_range_u5_safe`).
#[test]
fn test_extend_range_trip_bound_is_end_minus_start() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_inclusive", declared_unwind(8));
        let bounds = reach_check_bounds(&vc, 8);
        assert!(!bounds.is_empty(), "a bounded check: {reasons:?}");
        let is_end_minus_start = |b: &Expr| match b.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                matches!(cond.value(), ExprValue::BvULe(..))
                    && matches!(then_expr.value(), ExprValue::BvSub(..))
                    && matches!(else_expr.value(), ExprValue::BitVecConst { value, .. } if *value == 0u8.into())
            }
            _ => false,
        };
        assert!(bounds.iter().any(is_end_minus_start), "ite(start <= end, end - start, 0): {bounds:?}");
    });
}

/// An array `==` the harness inliner unfolds compares `a[..]` with `b[..]`:
/// the slice comparison's receiver is a full-range index of the array, whose
/// length is the array's. Its length was unresolved, so `[(); 6] == [(); 6]`
/// under `unwind(8)` failed where Kani proves
/// (`model_call_unwind_bound_dual.rs` `b5_array_eq_n6_u8_safe`). Under
/// `unwind(8)` the check `6 < 8 ∨ t` holds (written out, or folded away);
/// under `unwind(4)` it is the reach check.
#[test]
fn test_slice_eq_of_a_full_range_index_is_bounded_by_the_array_length() {
    with_probe(|tcx| {
        let reach_in_error_rules =
            |vc: &trust_mc_core::chc::ChcVc| vc_error_rules_contain_var(vc, "__walker_uncertified_reach");
        let (vc, reasons) = encode(tcx, "probe_slice_eq_full", declared_unwind(8));
        assert!(reasons.contains_key("model_call_loop_unwind_uncertified"), "{reasons:?}");
        let six = |b: &Expr| matches!(b.value(), ExprValue::BitVecConst { value, .. } if *value == 6u8.into());
        let bounds = reach_check_bounds(&vc, 8);
        assert!(
            bounds.iter().any(six) || (bounds.is_empty() && !reach_in_error_rules(&vc)),
            "under unwind(8) the bound is the array's length 6: {bounds:?} {reasons:?}"
        );
        let (vc, reasons) = encode(tcx, "probe_slice_eq_full", declared_unwind(4));
        assert!(
            reach_in_error_rules(&vc) || reach_check_bounds(&vc, 4).iter().any(six),
            "under unwind(4) the check stands: {reasons:?}"
        );
    });
}

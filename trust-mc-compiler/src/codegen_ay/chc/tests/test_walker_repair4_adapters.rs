// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 4 of fix/chc-walker-fail-closed, the class of walker
//! fail-closed review 6 round 3 finding 8 (docs/chc-hole-fix-designs-
//! 2026-09-24.md, "Walker fail-closed: repair round 4"): `Vec::extend` and
//! `collect` over an adapter the models do not replay fail closed, and an
//! unresolved extend source length is a fresh value, not the old one. The BMC
//! half is in `codegen_function/integration_bmc_extend_adapter_tests.rs`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use super::common::*;

use ay_bindings::ExprValue;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]

    pub fn probe_extend_map(a: [u8; 3]) -> usize {
        let mut v: Vec<u8> = Vec::new();
        v.extend(a.iter().map(|x| x + 1));
        v.len()
    }
    pub fn probe_extend_slice(a: [u8; 3]) -> usize {
        let mut v: Vec<u8> = Vec::new();
        v.extend(a.iter());
        v.len()
    }
    pub fn probe_extend_copied(a: [u8; 3]) -> usize {
        let mut v: Vec<u8> = vec![9];
        v.extend(a.iter().copied());
        v.len()
    }
    pub fn probe_collect_rev_map(a: [u8; 3]) -> Vec<u8> {
        a.iter().rev().map(|x| *x).collect()
    }
    pub fn probe_collect_copied(a: [u8; 3]) -> Vec<u8> {
        a.iter().copied().collect()
    }
    pub fn probe_collect_assert_map(a: [u8; 3]) -> Vec<u8> {
        a.iter().map(|x| { assert!(*x < 200); *x }).collect()
    }
    pub fn probe_extend_range_sym(a: u32, b: u32) -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.extend(a..b);
        v.len()
    }
    pub fn probe_extend_range_const() -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.extend(0..3u32);
        v.len()
    }
    pub fn probe_extend_range_incl_arg(r: core::ops::RangeInclusive<u32>) -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.extend(r);
        v.len()
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
    let name = format!("walker_repair4_adapters__{probe}");
    let instance = find_instance_by_suffix(tcx, probe);
    let body = instance.body().expect("body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), config);
    (vc, reasons_of(&name))
}


// ---------------------------------------------------------------------------
// (8) extend and collect over adapters
// ---------------------------------------------------------------------------

/// `Vec::extend` maps by name to the slice-extend model, which reads only the
/// sequence under the adapters: `v.extend(a.iter().map(|x| { assert!(..);
/// *x }))` dropped the closure (`c05_extend_map_bug`), and a `filter` or
/// `take` source extended by the unfiltered length. An adapter source fails
/// closed; a slice iterator does not.
#[test]
fn test_extend_from_an_adapter_fails_closed() {
    with_probe(|tcx| {
        let (_, reasons) = encode(tcx, "probe_extend_map", ChcConfig::default());
        assert!(reasons.contains_key("vec_extend_adapter_unmodelled"), "{reasons:?}");
        let (_, reasons) = encode(tcx, "probe_extend_slice", ChcConfig::default());
        assert!(!reasons.contains_key("vec_extend_adapter_unmodelled"), "a slice iterator: {reasons:?}");
    });
}

/// `collect` over `rev`, `enumerate`, `take`, `chain` or `scan` collected the
/// sequence underneath, and a `map` closure's checks were never run
/// (`c19`-`c27`, one harness per file). Such a receiver fails closed; `copied`
/// does not.
#[test]
fn test_collect_over_an_unmodelled_chain_fails_closed() {
    with_probe(|tcx| {
        for (probe, expected) in [
            ("probe_collect_rev_map", true),
            ("probe_collect_assert_map", true),
            ("probe_collect_copied", false),
        ] {
            let (_, reasons) = encode(tcx, probe, ChcConfig::default());
            assert_eq!(reasons.contains_key("iter_collect_adapter_unmodelled"), expected, "{probe}: {reasons:?}");
        }
    });
}

/// An extend whose source length the model cannot resolve left the length var
/// unwritten, so it kept the OLD length: `vec![9]` extended by three copied
/// elements still had length 1, `v.len() == 4` was certified a Genuine failure
/// and `v.len() == 1` would have verified (`e5_extend_copied_slice_safe`). The
/// reason the fresh length is recorded under is a sound havoc.
#[test]
fn test_unresolved_extend_length_is_a_sound_havoc() {
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness("vec_extend_source_len_unresolved"),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::SoundHavoc
    ));
    with_probe(|tcx| {
        let (_, reasons) = encode(tcx, "probe_extend_copied", ChcConfig::default());
        assert!(reasons.contains_key("vec_extend_source_len_unresolved"), "{reasons:?}");
        assert!(!reasons.contains_key("vec_extend_adapter_unmodelled"), "copied is modelled: {reasons:?}");
    });
}

/// Is `expr` `ite(start <u end, end - start, 0)`, the length of `start..end`?
fn is_exclusive_range_len(expr: &Expr) -> bool {
    let ExprValue::Ite { cond, then_expr, else_expr } = expr.value() else {
        return false;
    };
    matches!(cond.value(), ExprValue::BvULt(..))
        && matches!(then_expr.value(), ExprValue::BvSub(..))
        && matches!(else_expr.value(), ExprValue::BitVecConst { value, .. } if *value == 0u8.into())
}

/// Is `expr` `ite(¬exhausted ∧ start <= end, end - start + 1, 0)`, the length
/// of `start..=end` (`range_span.rs`, walker fail-closed repair round 5)?
fn is_inclusive_range_len(expr: &Expr) -> bool {
    let ExprValue::Ite { cond, then_expr, else_expr } = expr.value() else {
        return false;
    };
    matches!(cond.value(), ExprValue::And(..))
        && matches!(then_expr.value(), ExprValue::BvAdd(..))
        && matches!(else_expr.value(), ExprValue::BitVecConst { value, .. } if *value == 0u8.into())
}

fn vc_contains(vc: &trust_mc_core::chc::ChcVc, pred: impl Fn(&Expr) -> bool) -> bool {
    vc.rules.iter().any(|rule| rule_contains_expr(rule, &pred))
}

/// The range-extend model counted `start..end` as `end - start + 1` items,
/// unguarded: `v.extend(0..3)` grew `v` by four and `5..5` by one
/// (`extend_adapter_dual.rs` `x1`/`x3`: the bug rows verified clean on main's
/// CHC lane, the safe twins were certified Genuine). A symbolic exclusive
/// range now adds `ite(start < end, end - start, 0)`, a constant one its exact
/// count, and an inclusive range read through an argument either reads its
/// `exhausted` flag or fails closed. The count is `Step::steps_between` in the
/// element's own order since repair round 5 (`range_span.rs`).
#[test]
fn test_extend_range_length_follows_the_range() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_range_sym", ChcConfig::default());
        assert!(vc_contains(&vc, is_exclusive_range_len), "start..end adds ite(start < end, end - start, 0): {reasons:?}");
        let (vc, reasons) = encode(tcx, "probe_extend_range_const", ChcConfig::default());
        let adds = |n: u8| {
            move |e: &Expr| match e.value() {
                ExprValue::BvAdd(_, rhs) => {
                    matches!(rhs.value(), ExprValue::BitVecConst { value, width: 64 } if *value == n.into())
                }
                _ => false,
            }
        };
        assert!(vc_contains(&vc, adds(3)), "0..3 adds three: {reasons:?}");
        assert!(!vc_contains(&vc, is_exclusive_range_len), "a constant range folds: {reasons:?}");
        let (vc, reasons) = encode(tcx, "probe_extend_range_incl_arg", ChcConfig::default());
        assert!(
            vc_contains(&vc, is_inclusive_range_len)
                || reasons.contains_key("vec_extend_range_exhaustion_unresolved"),
            "start..=end reads `exhausted` or fails closed: {reasons:?}"
        );
    });
}

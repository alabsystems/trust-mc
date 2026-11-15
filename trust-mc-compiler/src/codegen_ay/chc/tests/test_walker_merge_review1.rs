// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round 1 of the repair after the merge of fix/chc-walker-fail-closed with
//! main's Rule D (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed:
//! the merge's review, round 1"), the CHC half: `Vec::extend` from a range
//! writes the Vec's own fields, `kani::any::<[bool; N]>()` states the unwinding
//! assertion of the loop the library runs for it, and `==` on an `Option` of an
//! array is bounded by the bytes it compares. The BMC half is in
//! `codegen_function/integration_bmc_merge_review1_tests.rs`; the naming of deep
//! `ite` chains is tested in trust-mc-core (`chc_optimize_ite_chains_tests.rs`).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use ay_bindings::ExprValue;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }
    }

    pub fn probe_extend_range_index() -> u32 {
        let mut v: Vec<u32> = Vec::new();
        v.extend(0..3u32);
        v[2]
    }
    pub fn probe_extend_range_sym_index(n: u32) -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.extend(0..n);
        v.len()
    }
    pub fn probe_extend_from_slice_array(a: [u8; 3]) -> u8 {
        let mut v: Vec<u8> = Vec::new();
        v.extend_from_slice(&a);
        v[2]
    }
    pub fn probe_any_bool_array() -> usize {
        let a: [bool; 4] = kani::any();
        a.len()
    }
    pub fn probe_any_u8_array() -> usize {
        let a: [u8; 8] = kani::any();
        a.len()
    }
    pub fn probe_option_array_eq() -> bool {
        let a = Some([1u8, 2, 3, 4]);
        let b = Some([1u8, 2, 3, 4]);
        a == b
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

fn encode(
    tcx: TyCtxt<'_>,
    probe: &str,
    config: ChcConfig,
) -> (trust_mc_core::chc::ChcVc, BTreeMap<String, usize>) {
    let name = format!("walker_merge_review1__{probe}");
    let instance = find_instance_by_suffix(tcx, probe);
    let body = instance.body().expect("body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), config);
    (vc, reasons_of(&name))
}

fn declared_unwind(depth: u32) -> ChcConfig {
    ChcConfig { recursive_unwind_depth: depth, unwinding_assertions: true, ..ChcConfig::default() }
}

fn vc_contains(vc: &trust_mc_core::chc::ChcVc, pred: impl Fn(&Expr) -> bool) -> bool {
    vc.rules.iter().any(|rule| rule_contains_expr(rule, &pred))
}

fn has_property(vc: &trust_mc_core::chc::ChcVc, needle: &str) -> bool {
    vc.properties.iter().any(|p| p.message.as_deref().is_some_and(|m| m.contains(needle)))
}

/// The constant values a store chain writes, outermost first.
fn stored_u32_values(expr: &Expr) -> Vec<u64> {
    let mut values = Vec::new();
    let mut cursor = expr;
    while let ExprValue::Store { array, value, .. } = cursor.value() {
        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(value);
        match folded.as_ref().map(Expr::value) {
            Some(ExprValue::BitVecConst { value, width: 32 }) => {
                values.push(u64::try_from(value).unwrap())
            }
            _ => break,
        }
        cursor = array;
    }
    values
}

/// `v.extend(0..3u32)` set the side-state length but wrote the Vec's own
/// `len` and `data` fields only for a one-element range, so `v[2]` read the
/// old length and failed `index out of bounds` certified Genuine where Kani
/// proves it (`range_extend_index_dual.rs`). The three elements are stored
/// now; a symbolic range leaves `data` a fresh array under a sound-havoc
/// record, and writes the fields all the same.
#[test]
fn test_range_extend_writes_the_vec_fields() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_range_index", ChcConfig::default());
        assert!(
            vc_contains(&vc, |e| stored_u32_values(e) == [2, 1, 0]),
            "0..3 stores 0, 1 and 2: {reasons:?}"
        );
        assert!(!reasons.contains_key("vec_extend_range_fields_unwritten"), "{reasons:?}");
        assert!(!reasons.contains_key("vec_extend_range_elements_unmodelled"), "{reasons:?}");
        let (_, reasons) = encode(tcx, "probe_extend_range_sym_index", ChcConfig::default());
        assert!(reasons.contains_key("vec_extend_range_elements_unmodelled"), "{reasons:?}");
        assert!(!reasons.contains_key("vec_extend_range_fields_unwritten"), "{reasons:?}");
    });
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness(
            "vec_extend_range_elements_unmodelled"
        ),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::SoundHavoc
    ));
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness(
            "vec_extend_range_fields_unwritten"
        ),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::FailClose
    ));
}

/// `v.extend_from_slice(&a)` for an array `a: [u8; 3]` took a fresh length
/// (the slice's length was not read through the unsizing) and left the Vec's
/// fields as they were, so `v[2]` failed `index out of bounds`, certified
/// Genuine on main where Kani proves it (`range_extend_index_dual.rs` `s2`).
/// The length is the array's, and the fields move by it over a fresh data array.
#[test]
fn test_extend_from_an_array_slice_writes_the_vec_fields() {
    with_probe(|tcx| {
        let (_, reasons) = encode(tcx, "probe_extend_from_slice_array", ChcConfig::default());
        assert!(
            !reasons.contains_key("vec_extend_source_len_unresolved"),
            "the array's length: {reasons:?}"
        );
        assert!(reasons.contains_key("vec_extend_slice_elements_unmodelled"), "{reasons:?}");
        assert!(!reasons.contains_key("vec_extend_slice_fields_unwritten"), "{reasons:?}");
    });
    assert!(matches!(
        crate::codegen_ay::chc::codegen_ctx::fallback_soundness(
            "vec_extend_slice_elements_unmodelled"
        ),
        crate::codegen_ay::chc::codegen_ctx::FallbackSoundness::SoundHavoc
    ));
}

/// `kani::any::<[bool; 4]>()` runs the library's `[(); 4].map(|_| bool::any())`,
/// four passes, so `#[kani::unwind(4)]` fails Kani's unwinding assertion; the
/// lane's fresh array skipped the loop and the harness verified clean
/// (`kani_any_array_unwind_dual.rs`). The assertion is stated under a bound the
/// loop does not fit, and not under one it does, nor for `[u8; 8]`, whose
/// `any_array` runs no loop.
#[test]
fn test_kani_any_bool_array_states_the_unwinding_assertion() {
    const MESSAGE: &str = "Arbitrary::any_array runs 4 passes";
    with_probe(|tcx| {
        let (vc, _) = encode(tcx, "probe_any_bool_array", declared_unwind(4));
        assert!(has_property(&vc, MESSAGE), "{:?}", vc.properties);
        let (vc, _) = encode(tcx, "probe_any_bool_array", declared_unwind(5));
        assert!(
            !has_property(&vc, "Arbitrary::any_array"),
            "the bound covers it: {:?}",
            vc.properties
        );
        let (vc, _) = encode(tcx, "probe_any_bool_array", ChcConfig::default());
        assert!(
            !has_property(&vc, "Arbitrary::any_array"),
            "no declared bound: {:?}",
            vc.properties
        );
        let (vc, _) = encode(tcx, "probe_any_u8_array", declared_unwind(2));
        assert!(
            !has_property(&vc, "Arbitrary::any_array"),
            "[u8; 8] has no loop: {:?}",
            vc.properties
        );
    });
}

/// `Some([1u8, 2, 3, 4]) == Some([1u8, 2, 3, 4])` compares four bytes with
/// Kani's `memcmp`; with no trip-count row for an `Option` the modelled call's
/// unwinding check failed closed under `#[kani::unwind(5)]`, which Kani proves
/// (`model_call_unwind_wrapped_eq_dual.rs`). The row bounds it by the four
/// bytes: no check under `unwind(5)`, the check under `unwind(3)`.
#[test]
fn test_option_array_eq_is_bounded_by_its_bytes() {
    const MESSAGE: &str = "a loop in a call the CHC encoder models";
    with_probe(|tcx| {
        let (vc, _) = encode(tcx, "probe_option_array_eq", declared_unwind(5));
        assert!(!has_property(&vc, MESSAGE), "four bytes fit unwind(5): {:?}", vc.properties);
        let (vc, _) = encode(tcx, "probe_option_array_eq", declared_unwind(3));
        assert!(has_property(&vc, MESSAGE), "four bytes do not fit unwind(3): {:?}", vc.properties);
    });
}

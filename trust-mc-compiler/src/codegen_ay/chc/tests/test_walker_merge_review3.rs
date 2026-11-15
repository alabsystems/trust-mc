// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Round 3 of the repair after the merge of fix/chc-walker-fail-closed with
//! main's Rule D (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed:
//! the merge's review, round 3"), the CHC half: a Vec's capacity reads its
//! element's own layout size, `clone` and `split_off` give the capacity std
//! allocates and `split_off` states its bounds panic, and a comparison whose
//! `==` or order is not its encodings' (a float, a hand-written `PartialEq`)
//! is decided by Rust's semantics or left unconstrained. The duals are
//! `vec_capacity_elem_layout_dual.rs` and `value_eq_semantics_dual.rs`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
// Exercise the actual driver policy as well as the current main controls.
#[path = "../../../../../trust-mc-driver/src/chc_claim_policy.rs"]
mod chc_claim_policy;
use crate::codegen_ay::codegen_results::AYCodegenResults;
use crate::codegen_ay::context::AYCtx;
use chc_claim_policy::{
    EvidenceAccounting, ctrex_evidence_is_complete, proof_qualifying_fallback_count,
};
use trust_mc_core::artifact::VcArtifact;
use trust_mc_metadata::{KaniMetadata, UnsoundnessCategory};

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    use std::cell::{Cell, RefCell};

    #[derive(Clone, Copy)]
    pub struct Parity(u8);
    impl PartialEq for Parity {
        fn eq(&self, other: &Parity) -> bool {
            self.0 % 2 == other.0 % 2
        }
    }

    pub fn probe_refcell_unit_cap() {
        let v: Vec<RefCell<()>> = Vec::new();
        assert!(v.capacity() == 0);
    }
    pub fn probe_cell_unit_cap() {
        let v: Vec<Cell<()>> = Vec::new();
        assert!(v.capacity() == usize::MAX);
    }
    pub fn probe_refcell_u8_push_cap() {
        let mut v: Vec<RefCell<u8>> = Vec::new();
        v.push(RefCell::new(1));
        assert!(v.capacity() == 4);
    }
    pub fn probe_clone_cap() {
        let mut v: Vec<u8> = Vec::with_capacity(10);
        v.push(1);
        v.push(2);
        let w = v.clone();
        assert!(w.capacity() == 2);
    }
    pub fn probe_clone_cap_bug() {
        let mut v: Vec<u8> = Vec::with_capacity(10);
        v.push(1);
        v.push(2);
        let w = v.clone();
        assert!(w.capacity() == 10);
    }
    pub fn probe_split_off_cap() {
        let mut v: Vec<u8> = Vec::new();
        v.push(1);
        v.push(2);
        v.push(3);
        let w = v.split_off(1);
        assert!(w.capacity() == 2);
        assert!(w.len() == 2);
        assert!(v.len() == 1);
    }
    pub fn probe_split_off_past_len() {
        let mut v: Vec<u8> = Vec::new();
        v.push(1);
        v.push(2);
        let w = v.split_off(3);
        assert!(w.len() == 0);
    }
    pub fn probe_f32_array_signed_zero() {
        let s = [0.0f32, 1.0];
        let t = [-0.0f32, 1.0];
        assert!(s == t);
    }
    pub fn probe_f32_array_nan() {
        let s = [f32::NAN, 1.0];
        let t = [f32::NAN, 1.0];
        assert!(s == t);
    }
    pub fn probe_option_f32_signed_zero() {
        let a = Some(0.0f32);
        let b = Some(-0.0f32);
        assert!(a == b);
    }
    pub fn probe_custom_eq_array() {
        let a = [Parity(1), Parity(2)];
        let b = [Parity(3), Parity(4)];
        assert!(a == b);
    }
    pub fn probe_custom_eq_array_false_twin() {
        let a = [Parity(1), Parity(2)];
        let b = [Parity(3), Parity(4)];
        assert!(a != b);
    }
    pub fn probe_eq_real_counterexample() {
        assert!(1u8 == 2u8);
    }
    #[derive(Clone, Copy)]
    pub struct Divides(u8);
    impl PartialEq for Divides {
        fn eq(&self, other: &Self) -> bool { self.0 % other.0 == 0 }
    }
    pub fn probe_custom_eq_short_circuit() {
        let a = [Divides(1), Divides(4)];
        let b = [Divides(2), Divides(0)];
        assert!(a != b);
    }
    pub fn probe_custom_eq_first_panic() {
        let a = [Divides(1), Divides(4)];
        let b = [Divides(0), Divides(2)];
        let _ = a == b;
    }
    pub fn probe_custom_eq_later_panic() {
        let a = [Divides(4), Divides(4)];
        let b = [Divides(2), Divides(0)];
        let _ = a != b;
    }
    pub fn probe_custom_eq_false_assertion() {
        let a = [Parity(1), Parity(2)];
        let b = [Parity(3), Parity(4)];
        assert!(a != b);
    }
    pub fn probe_literal_eq_array() {
        assert!([Parity(1), Parity(2)] == [Parity(3), Parity(4)]);
    }
    pub fn probe_literal_ne_false_assertion() {
        assert!([Parity(1), Parity(2)] != [Parity(3), Parity(4)]);
    }
    pub fn probe_literal_eq_false_assertion() {
        assert!([Parity(1), Parity(2)] == [Parity(2), Parity(4)]);
    }
    pub fn probe_literal_short_circuit() {
        assert!([Divides(1), Divides(4)] != [Divides(2), Divides(0)]);
    }
    pub fn probe_literal_first_panic() {
        let _ = [Divides(1), Divides(4)] == [Divides(0), Divides(2)];
    }
    pub fn probe_literal_later_panic() {
        let _ = [Divides(4), Divides(4)] != [Divides(2), Divides(0)];
    }
    #[repr(C)]
    #[derive(Clone, Copy)]
    pub struct Padded { tag: u8, value: u32 }
    impl PartialEq for Padded {
        fn eq(&self, other: &Self) -> bool {
            self.tag == other.tag && self.value % 2 == other.value % 2
        }
    }
    pub fn probe_literal_padded_fields() {
        assert!([Padded { tag: 7, value: 1 }] == [Padded { tag: 7, value: 3 }]);
    }
    pub fn probe_literal_padded_tag_must_fail() {
        assert!([Padded { tag: 7, value: 1 }] == [Padded { tag: 8, value: 3 }]);
    }
    const PADDED_WINDOWS: [Padded; 2] = [
        Padded { tag: 9, value: 0x11111111 }, Padded { tag: 7, value: 0x44444444 }
    ];
    const PADDED_TAIL: &[Padded; 1] = unsafe {
        &*(PADDED_WINDOWS.as_ptr().add(1) as *const [Padded; 1])
    };
    #[inline(never)]
    fn copy_padded_window(value: &[Padded; 1]) -> [Padded; 1] { *value }
    pub fn probe_padded_value_byte() {
        let owned = copy_padded_window(PADDED_TAIL);
        let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
        assert!(byte == 0x44, "value byte");
    }
    pub fn probe_padded_wrong_value_byte() {
        let owned = copy_padded_window(PADDED_TAIL);
        let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
        assert!(byte == 7, "wrong value byte");
    }
    pub fn probe_padded_value_u16() {
        let owned = copy_padded_window(PADDED_TAIL);
        let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u16>().read() };
        assert!(word == 0x4444, "value u16");
    }
    pub fn probe_padded_wrong_value_u16() {
        let owned = copy_padded_window(PADDED_TAIL);
        let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u16>().read() };
        assert!(word == 7, "wrong value u16");
    }
    pub fn probe_padded_tag_byte() {
        let owned = copy_padded_window(PADDED_TAIL);
        let byte = unsafe { owned.as_ptr().cast::<u8>().read() };
        assert!(byte == 7, "tag byte");
    }
    pub fn probe_padded_wrong_tag_byte() {
        let owned = copy_padded_window(PADDED_TAIL);
        let byte = unsafe { owned.as_ptr().cast::<u8>().read() };
        assert!(byte == 0x44, "wrong tag byte");
    }
    pub fn probe_typed_u8_write_then_read() {
        let mut values = [1u8, 2];
        unsafe { values.as_mut_ptr().add(1).write(3); }
        assert!(unsafe { values.as_ptr().add(1).read() } == 3);
    }
    pub fn probe_typed_u8_write_then_read_wrong_old() {
        let mut values = [1u8, 2];
        unsafe { values.as_mut_ptr().add(1).write(3); }
        assert!(unsafe { values.as_ptr().add(1).read() } == 2);
    }
    pub fn probe_typed_u16_write_then_read() {
        let mut values = [0x1111u16, 0x2222];
        unsafe { values.as_mut_ptr().add(1).write(0x3333); }
        assert!(unsafe { values.as_ptr().add(1).read() } == 0x3333);
    }
    pub fn probe_typed_u16_write_then_read_wrong_old() {
        let mut values = [0x1111u16, 0x2222];
        unsafe { values.as_mut_ptr().add(1).write(0x3333); }
        assert!(unsafe { values.as_ptr().add(1).read() } == 0x2222);
    }
    pub fn probe_typed_u16_byte_step_read() {
        let values = [0x1122u16, 0x3344];
        assert!(unsafe { values.as_ptr().byte_add(2).read() } == 0x3344);
    }
    pub fn probe_typed_u16_byte_step_read_wrong_first() {
        let values = [0x1122u16, 0x3344];
        assert!(unsafe { values.as_ptr().byte_add(2).read() } == 0x1122);
    }
    pub fn probe_typed_large_read() {
        let mut values = [0x3344u16; 300];
        values[299] = 0x5566;
        assert!(unsafe { values.as_ptr().add(299).read() } == 0x5566);
    }
    pub fn probe_typed_large_read_wrong_first() {
        let mut values = [0x3344u16; 300];
        values[299] = 0x5566;
        assert!(unsafe { values.as_ptr().add(299).read() } == 0x3344);
    }
    pub fn probe_typed_large_symbolic_read(x: u16) {
        let values = [x; 300];
        assert!(unsafe { values.as_ptr().add(299).read() } == x);
    }
    pub fn probe_typed_large_symbolic_read_wrong(x: u16) {
        let values = [x; 300];
        assert!(unsafe { values.as_ptr().add(299).read() } != x);
    }
    const OFFSET_VALUES: [Parity; 3] = [Parity(9), Parity(1), Parity(2)];
    const OFFSET_TAIL: &[Parity; 2] = unsafe {
        &*(OFFSET_VALUES.as_ptr().add(1) as *const [Parity; 2])
    };
    #[inline(never)]
    fn read_offset_window(value: &[Parity; 2]) -> [Parity; 2] { *value }
    pub fn probe_literal_nonzero_offset() {
        assert!(read_offset_window(OFFSET_TAIL) == [Parity(3), Parity(4)], "offset tail");
    }
    pub fn probe_literal_offset_is_not_base() {
        assert!(read_offset_window(OFFSET_TAIL) == [Parity(9), Parity(1)], "offset is not base");
    }
    fn literal_generic_compare<T: PartialEq, const N: usize>(a: &[T; N], b: &[T; N]) -> bool {
        a == b
    }
    pub fn probe_literal_generic_wrapper() {
        assert!(literal_generic_compare(&[Parity(1), Parity(2)], &[Parity(3), Parity(4)]), "generic eq");
    }
    pub fn probe_literal_closure() {
        let compare = || [Parity(1), Parity(2)] == [Parity(3), Parity(4)];
        assert!(compare(), "closure eq");
    }
    pub fn probe_literal_empty_no_panic() {
        let a: [Divides; 0] = [];
        let b: [Divides; 0] = [];
        assert!(a == b, "empty eq");
    }
    pub fn probe_literal_empty_ne_must_fail() {
        let a: [Divides; 0] = [];
        let b: [Divides; 0] = [];
        assert!(a != b, "empty ne");
    }
    #[derive(Clone, Copy)]
    pub struct NonComplementary(u8);
    impl PartialEq for NonComplementary {
        fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
        fn ne(&self, _: &Self) -> bool { false }
    }
    pub fn probe_custom_ne_stays_unmodeled() {
        let a = [NonComplementary(1)];
        let b = [NonComplementary(2)];
        assert!(a == b);
    }
    #[derive(Clone, Copy)]
    pub struct AddressSensitive(u8);
    impl PartialEq for AddressSensitive {
        fn eq(&self, other: &Self) -> bool {
            self as *const Self as usize == other as *const Self as usize
        }
    }
    pub fn probe_custom_address_stays_unmodeled() {
        let a = [AddressSensitive(1)];
        let b = [AddressSensitive(1)];
        assert!(a == b);
    }
    pub fn probe_f32_array_order() {
        assert!([-1.0f32, 0.0] < [1.0f32, 0.0]);
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

/// The CHC verdict of `name` ("sat": an error is reachable) and the
/// translation-drop reasons its encoding recorded.
fn chc_verdict(tcx: TyCtxt<'_>, name: &str) -> (String, BTreeMap<String, usize>) {
    let observation = chc_observation(tcx, name);
    (observation.verdict, observation.reasons)
}

struct ChcObservation {
    /// Raw solver output: diagnostic/refusal checks never rewrite it.
    verdict: String,
    reasons: BTreeMap<String, usize>,
    translation_drops: Option<trust_mc_metadata::ChcTranslationDropInfo>,
    approximation_identity_complete: bool,
    accounted_approximations: usize,
    property_count: usize,
    error_obligation_count: usize,
}

fn chc_observation(tcx: TyCtxt<'_>, name: &str) -> ChcObservation {
    let instance = find_instance_by_suffix(tcx, name);
    let body = instance.body().expect("function body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name, ChcConfig::default());
    // Capture the production metadata collector's typed category, not a
    // diagnostic spelling used as a substitute for an admission input.
    let translation_drops =
        crate::codegen_ay::unsoundness_fields_collectors::collect_fallback_fields().1;
    let reasons = translation_drops
        .as_ref()
        .and_then(|drops| drops.per_harness_translation_sites.get(name))
        .cloned()
        .unwrap_or_default();
    let aggregate_gaps =
        crate::codegen_ay::take_aggregate_gap_reasons_by_fn().remove(name).unwrap_or_default();
    if !aggregate_gaps.is_empty() {
        eprintln!("{name}: aggregate/callee diagnostics = {aggregate_gaps:?}");
    }
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    let verdict = run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
        .unwrap_or_else(|err| format!("error:{err}"));
    eprintln!(
        "{name}: raw={verdict}, ChcTranslationDrop={}, ChcSoundHavocDrop={}, identity_complete={}, accounted={}, properties={}",
        translation_drops
            .as_ref()
            .and_then(|drops| drops.per_harness.get(name))
            .copied()
            .unwrap_or(0),
        translation_drops
            .as_ref()
            .and_then(|drops| drops.sound_havoc_per_harness.get(name))
            .copied()
            .unwrap_or(0),
        vc.approximation_identity_complete,
        vc.accounted_approximations,
        vc.properties.len()
    );
    ChcObservation {
        verdict,
        reasons,
        translation_drops,
        approximation_identity_complete: vc.approximation_identity_complete,
        accounted_approximations: vc.accounted_approximations,
        property_count: vc.properties.len(),
        error_obligation_count: vc
            .rules
            .iter()
            .filter(|rule| trust_mc_core::chc::rule_is_error_obligation(rule))
            .count(),
    }
}

/// `RefCell<()>` is 8 bytes and `RefCell<u8>` 16, but the capacity model
/// read the heap model's size, which strips `RefCell` first: `RefCell<()>`
/// read as zero-sized (`capacity()` was `usize::MAX`) and `RefCell<u8>` as 1
/// byte (one push gave 8 where std gives 4). `Cell<()>` is zero-sized.
#[test]
fn test_vec_capacity_reads_the_elements_own_layout() {
    with_probe(|tcx| {
        let (v, r) = chc_verdict(tcx, "probe_refcell_unit_cap");
        assert_eq!(v, "unsat", "Vec<RefCell<()>>::new() has capacity 0, reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_cell_unit_cap");
        assert_eq!(v, "unsat", "Vec<Cell<()>> has capacity usize::MAX, reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_refcell_u8_push_cap");
        assert_eq!(v, "unsat", "one push of a 16-byte element gives 4, reasons = {r:?}");
    });
}

/// `clone` allocates exactly the length; the model copied the source's
/// capacity, so a clone of a `with_capacity(10)` Vec of two had capacity 10.
#[test]
fn test_vec_clone_capacity_is_its_length() {
    with_probe(|tcx| {
        let (v, r) = chc_verdict(tcx, "probe_clone_cap");
        assert_eq!(v, "unsat", "the clone's capacity is 2, reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_clone_cap_bug");
        assert_eq!(v, "sat", "the clone's capacity is not 10, reasons = {r:?}");
    });
}

/// `split_off(at)` panics when `at > len` (the model assumed it away) and
/// returns `with_capacity(len - at)` (the model left its capacity stale).
#[test]
fn test_vec_split_off_states_its_panic_and_capacity() {
    with_probe(|tcx| {
        let (v, r) = chc_verdict(tcx, "probe_split_off_cap");
        assert_eq!(v, "unsat", "len - at elements in a buffer of len - at, reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_split_off_past_len");
        assert_eq!(v, "sat", "split_off(3) of two elements panics, reasons = {r:?}");
    });
}

/// `==` on floats is IEEE equality: `+0.0 == -0.0`, `NaN != NaN`. The array
/// and `Option` comparisons compared bit patterns.
#[test]
fn test_float_container_equality_is_ieee() {
    with_probe(|tcx| {
        let (v, r) = chc_verdict(tcx, "probe_f32_array_signed_zero");
        assert_eq!(v, "unsat", "[0.0] == [-0.0], reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_f32_array_nan");
        assert_eq!(v, "sat", "[NaN] != [NaN], reasons = {r:?}");
        let (v, r) = chc_verdict(tcx, "probe_option_f32_signed_zero");
        assert_eq!(v, "unsat", "Some(0.0) == Some(-0.0), reasons = {r:?}");
    });
}

/// A hand-written `PartialEq` element is compared by its own `eq`, never by
/// its bits; an order of float arrays, which the lane reads as an integer
/// order, is left unconstrained.
#[test]
fn test_unfaithful_comparisons_leave_the_encoding() {
    with_probe(|tcx| {
        use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
        let observation = chc_observation(tcx, "probe_custom_eq_array");
        let (v, r) = (&observation.verdict, &observation.reasons);
        eprintln!("custom-equality per-site metadata rows: {}", observation.property_count);
        assert!(
            observation.error_obligation_count > 0,
            "the encoded input retains actual error-obligation rules"
        );
        if v == "sat" {
            // This test's contract permits an unmodeled comparison to remain
            // unconstrained, but never a certified false counterexample.
            // The product records this lost effect as ChcTranslationDrop and
            // classifies its SAT as OverApproximation. Recertification also
            // requires complete approximation identities: the actual VC must
            // retain the unaccounted lost effect, not merely a diagnostic.
            let lost = "walker_nested_call_lost_effect";
            let typed = observation.translation_drops.as_ref().expect("actual typed drop metadata");
            assert!(typed.place_count > 0, "the fail-closed category is recorded");
            assert!(
                typed.per_harness.get("probe_custom_eq_array").is_some_and(|count| *count > 0),
                "this actual harness has ChcTranslationDrop"
            );
            assert!(
                r.get(lost).is_some_and(|count| *count > 0),
                "raw SAT needs its real refusal: {r:?}"
            );
            assert_eq!(fallback_soundness(lost), FallbackSoundness::FailClose);
            assert!(
                observation.accounted_approximations > 0,
                "the actual nested return havoc is recorded"
            );
            assert!(
                !observation.approximation_identity_complete,
                "an unaccounted lost effect cannot certify Genuine"
            );
        }
        // A real, fully modeled false comparison stays SAT with no refusal.
        // In particular, bitwise equality incorrectly substituted for Parity
        // above would have this shape and would fail the preceding checks.
        let genuine = chc_observation(tcx, "probe_eq_real_counterexample");
        assert_eq!(genuine.verdict, "sat", "the false assertion remains reachable");
        assert!(
            genuine.reasons.is_empty(),
            "a real comparison failure is not hidden: {:?}",
            genuine.reasons
        );
        assert!(genuine.approximation_identity_complete);
        assert_eq!(
            genuine
                .translation_drops
                .as_ref()
                .and_then(|drops| drops.per_harness.get("probe_eq_real_counterexample"))
                .copied()
                .unwrap_or(0),
            0,
            "no typed ChcTranslationDrop may hide the concrete counterexample"
        );
        assert!(genuine.error_obligation_count > 0);
        // The order is walked through its body, which loses effects here: a
        // reachable error carries the fallback that makes it uncertified.
        let (v, r) = chc_verdict(tcx, "probe_f32_array_order");
        assert!(
            v != "sat" || !r.is_empty(),
            "a float array order is exact or not certified: {v}, reasons = {r:?}"
        );
    });
}

#[test]
fn test_value_only_array_semantics_and_short_circuit_checks() {
    with_probe(|tcx| {
        for (name, expected) in [
            ("probe_custom_eq_short_circuit", "unsat"),
            ("probe_custom_eq_first_panic", "sat"),
            ("probe_custom_eq_later_panic", "sat"),
            ("probe_custom_eq_false_assertion", "sat"),
            ("probe_literal_eq_array", "unsat"),
            ("probe_literal_ne_false_assertion", "sat"),
            ("probe_literal_eq_false_assertion", "sat"),
            ("probe_literal_short_circuit", "unsat"),
            ("probe_literal_first_panic", "sat"),
            ("probe_literal_later_panic", "sat"),
            ("probe_literal_padded_fields", "unsat"),
            ("probe_literal_padded_tag_must_fail", "sat"),
            ("probe_literal_nonzero_offset", "unsat"),
            ("probe_literal_offset_is_not_base", "sat"),
            ("probe_literal_empty_no_panic", "unsat"),
            ("probe_literal_empty_ne_must_fail", "sat"),
        ] {
            let (verdict, reasons) = chc_verdict(tcx, name);
            assert_eq!(verdict, expected, "{name}: {reasons:?}");
            assert!(reasons.is_empty(), "{name} must retain exact semantics: {reasons:?}");
        }
    });
}

#[test]
fn test_value_only_array_refuses_custom_ne_and_receiver_addresses() {
    with_probe(|tcx| {
        for name in ["probe_custom_ne_stays_unmodeled", "probe_custom_address_stays_unmodeled"] {
            let (_, reasons) = chc_verdict(tcx, name);
            assert!(
                reasons.contains_key("nested_spec_array_referent_unresolved"),
                "{name} must not enter value-only comparison: {reasons:?}"
            );
        }
    });
}

#[test]
fn test_value_only_array_survives_production_preinlining() {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
    use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
    use rustc_public::CrateDef;
    use rustc_public::mir::TerminatorKind;
    use rustc_public::mir::mono::Instance;
    use rustc_public::ty::{RigidTy, TyKind};

    with_probe(|tcx| {
        for (name, expected) in [
            ("probe_custom_eq_array", "unsat"),
            ("probe_custom_eq_short_circuit", "unsat"),
            ("probe_custom_eq_first_panic", "sat"),
            ("probe_custom_eq_later_panic", "sat"),
            ("probe_custom_eq_false_assertion", "sat"),
            ("probe_literal_eq_array", "unsat"),
            ("probe_literal_ne_false_assertion", "sat"),
            ("probe_literal_eq_false_assertion", "sat"),
            ("probe_literal_short_circuit", "unsat"),
            ("probe_literal_first_panic", "sat"),
            ("probe_literal_later_panic", "sat"),
            ("probe_literal_padded_fields", "unsat"),
            ("probe_literal_padded_tag_must_fail", "sat"),
            ("probe_padded_value_byte", "unsat"),
            ("probe_padded_wrong_value_byte", "sat"),
            ("probe_padded_value_u16", "unsat"),
            ("probe_padded_wrong_value_u16", "sat"),
            ("probe_padded_tag_byte", "unsat"),
            ("probe_padded_wrong_tag_byte", "sat"),
            ("probe_typed_u8_write_then_read", "unsat"),
            ("probe_typed_u8_write_then_read_wrong_old", "sat"),
            ("probe_typed_u16_write_then_read", "unsat"),
            ("probe_typed_u16_write_then_read_wrong_old", "sat"),
            ("probe_typed_u16_byte_step_read", "unsat"),
            ("probe_typed_u16_byte_step_read_wrong_first", "sat"),
            ("probe_typed_large_read", "unsat"),
            ("probe_typed_large_read_wrong_first", "sat"),
            ("probe_typed_large_symbolic_read", "unsat"),
            ("probe_typed_large_symbolic_read_wrong", "sat"),
            ("probe_literal_nonzero_offset", "unsat"),
            ("probe_literal_offset_is_not_base", "sat"),
            ("probe_literal_generic_wrapper", "unsat"),
            ("probe_literal_closure", "unsat"),
            ("probe_literal_empty_no_panic", "unsat"),
            ("probe_literal_empty_ne_must_fail", "sat"),
        ] {
            let instance = find_instance_by_suffix(tcx, name);
            let original = instance.body().unwrap();
            for preserve in [true, false] {
                let mut pass = FunctionInlinePass::new(InlineConfig {
                    preserve_array_comparisons: preserve,
                    ..InlineConfig::default()
                });
                let (_, body) =
                    pass.transform_with_body_provider(tcx, original.clone(), instance, |callee| {
                        crate::kani_middle::transform::walker_transformed_body(tcx, callee)
                    });
                if matches!(
                    name,
                    "probe_literal_nonzero_offset" | "probe_literal_offset_is_not_base"
                ) {
                    let constants = const_pointer::body_constants_read(
                        &body,
                        &vec![true; body.blocks.len()],
                        &|_| false,
                    );
                    assert!(
                        constants.iter().any(|(bytes, ty)| {
                            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                                if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Array(_, count))
                                    if count.eval_target_usize().ok() == Some(2)))
                                && bytes.stored_pointer(0).is_some_and(|ptr| ptr.offset() == 1)
                        }),
                        "{name}: the tested MIR must retain the nonzero pointer window"
                    );
                }
                let retained_default = body.blocks.iter().any(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        return false;
                    };
                    let Ok(ty) = func.ty(body.locals()) else { return false };
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
                        return false;
                    };
                    Instance::resolve(def, &args).ok().is_some_and(|resolved| {
                        crate::kani_middle::std_abstraction::is_default_spec_array_comparison(
                            tcx, &resolved,
                        )
                    })
                });
                let raw_control =
                    name.starts_with("probe_padded_") || name.starts_with("probe_typed_");
                if raw_control {
                    assert!(!retained_default, "raw byte controls contain no array equality");
                } else if !name.contains("empty") {
                    assert_eq!(retained_default, preserve, "{name}: CHC-only boundary");
                }
                if !preserve {
                    continue;
                }
                let mut config = ChcConfig::default();
                if raw_control {
                    config.track_level = crate::args::ChcTrackLevel::Mem;
                }
                let vc = mir_to_chc_with_instance(tcx, &body, instance, name, config);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                let smt = crate::codegen_ay::emit_chc(&vc).to_string();
                let verdict =
                    run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30)).unwrap();
                assert_eq!(verdict, expected, "{name}: {reasons:?}");
                assert!(
                    reasons.is_empty(),
                    "{name} must survive preprocessing exactly: {reasons:?}"
                );
            }
        }
    });
}

fn check_comparison_claim(
    ctx: &mut AYCtx<'_, '_>,
    name: &str,
    assertion_source: &str,
    assertion_is_true: bool,
) {
    let instance = find_instance_by_suffix(ctx.tcx, name);
    let body = instance.body().expect("function body");
    // Locate this probe's actual user assert, before collecting diagnostics.
    // Inlined library checks belong to their own caller block, not this
    // root body's exact-source panic call. Use the real stub classifier.
    let assertion_bb = {
        let scanner =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, name, ChcConfig::default());
        let sites: Vec<_> = body
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(bb, block)| {
                let rustc_public::mir::TerminatorKind::Call { func, target: None, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                if scanner.detect_stub(func) != Some(StubKind::PanicError) {
                    return None;
                }
                let span = rustc_internal::internal(
                    ctx.tcx,
                    crate::rustc_compat::mir_span!(block.terminator),
                )
                .source_callsite();
                let snippet = ctx.tcx.sess.source_map().span_to_snippet(span).ok()?;
                (snippet.trim().trim_end_matches(';') == assertion_source).then_some(bb)
            })
            .collect();
        let [bb] = sites.as_slice() else {
            panic!("{name}: expected one original {assertion_source} panic site, got {sites:?}");
        };
        *bb
    };
    let collect = || {
        AYCodegenResults::new(ctx.tcx, crate::args::ReachabilityType::Harnesses).generate_metadata()
    };
    // Drain only this test's compilation registry, then retain an empty
    // production metadata baseline so an unexpected diagnostic cannot vanish.
    drop(collect());
    let empty_metadata = serde_json::to_value(collect()).expect("empty metadata serializes");
    let vc = mir_to_chc_with_instance(ctx.tcx, &body, instance, name, ChcConfig::default());
    let assertion_properties: Vec<_> = vc
        .properties
        .iter()
        .filter(|property| {
            property.bb == assertion_bb
                && property.kind == trust_mc_core::violation::PropertyKind::Panic
        })
        .collect();
    let [assertion_property] = assertion_properties.as_slice() else {
        panic!("{name}: original user assertion at bb{assertion_bb} lost its unique property");
    };
    let assertion_identity =
        (assertion_property.id, assertion_property.kind, assertion_property.relation.clone());
    assert_eq!(assertion_identity.2, format!("error_p{}", assertion_identity.0));
    assert!(
        vc.rules.iter().any(|rule| rule.head.name.as_str() == assertion_identity.2.as_str())
            || assertion_property.discharged_at_encode.is_some(),
        "{name}: original user assertion has neither an error rule nor an explicit discharge",
    );
    // Capture before metadata drains: the collector must not create an
    // artificial incomplete verdict. These are fields of the finished VC.
    let expected_accounting = EvidenceAccounting {
        complete: vc.approximation_identity_complete,
        accounted: vc.accounted_approximations,
    };
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    let metadata_json = serde_json::to_value(collect()).expect("production metadata serializes");
    let metadata: KaniMetadata =
        serde_json::from_value(metadata_json.clone()).expect("production metadata round trips");
    let mut other_metadata = metadata_json;
    other_metadata.as_object_mut().expect("metadata object").retain(|key, _| {
        !matches!(
            key.as_str(),
            "chc_translation_drops"
                | "unhandled_calls"
                | "aggregate_encoding_gap"
                | "fp_bitvector_encoding"
        )
    });
    assert_eq!(other_metadata, empty_metadata, "{name}: unexpected diagnostic category");

    // These are the actual per-harness maps consumed by the driver, not a
    // mapping invented from reason strings. Require every event to be local.
    let mut categories = BTreeMap::new();
    let mut add = |category: UnsoundnessCategory, total, per_harness: &BTreeMap<String, usize>| {
        assert!(per_harness.keys().all(|key| key == name), "{name}: unattributed {category:?}");
        let count = per_harness.get(name).copied().unwrap_or_default();
        assert_eq!(count, total, "{name}: missing per-harness {category:?} evidence");
        if count > 0 {
            assert!(categories.insert(category.json_key().to_owned(), count).is_none());
        }
    };
    if let Some(drops) = &metadata.chc_translation_drops {
        add(
            UnsoundnessCategory::ChcTranslationDrop,
            drops.place_count + drops.constant_count + drops.field_projection_count,
            &drops.per_harness,
        );
        add(
            UnsoundnessCategory::ChcSoundHavocDrop,
            drops.sound_havoc_count,
            &drops.sound_havoc_per_harness,
        );
    }
    if let Some(fp) = &metadata.fp_bitvector_encoding {
        add(UnsoundnessCategory::FpBitvectorEncoding, fp.count, &fp.per_harness);
    }
    if let Some(gaps) = &metadata.aggregate_encoding_gap {
        // Reason labels may describe overlapping events; their sum is not
        // the producer's event count. Bind their provenance, then use the
        // actual count/per-harness fields consumed by the driver.
        assert!(
            gaps.per_harness_reasons.keys().all(|key| key == name),
            "{name}: unattributed aggregate encoding-gap reasons"
        );
        add(UnsoundnessCategory::AggregateEncodingGap, gaps.count, &gaps.per_harness);
    }
    if let Some(unhandled) = &metadata.unhandled_calls {
        add(UnsoundnessCategory::UnhandledCalls, unhandled.count, &unhandled.per_harness);
    }

    // Use the production artifact writer as well as its serialized schema.
    ctx.config.use_chc = true;
    ctx.chc_vc = Some(vc);
    let emitted_artifact = ctx.build_vc_artifact(name, None);
    let artifact_json =
        serde_json::to_string(&emitted_artifact).expect("production VC artifact serializes");
    let artifact: VcArtifact =
        serde_json::from_str(&artifact_json).expect("production VC artifact round trips");
    assert_eq!(artifact, emitted_artifact, "{name}: VC evidence changed in transport");
    assert_eq!(artifact.harness.pretty_name, name);
    assert_eq!(artifact.harness.mangled_name, name);
    let recorded_assertions = artifact
        .properties
        .iter()
        .filter(|property| {
            property.id.id == assertion_identity.0
                && property.kind == assertion_identity.1
                && property.smt_var.as_deref() == Some(assertion_identity.2.as_str())
        })
        .count();
    assert_eq!(recorded_assertions, 1, "{name}: original user assertion identity was lost");
    let evidence = EvidenceAccounting {
        complete: artifact.approximation_identity_complete,
        accounted: artifact.accounted_approximations,
    };
    assert_eq!(evidence, expected_accounting, "{name}: draining changed VC accounting");
    let rendered: Vec<_> = categories.iter().map(|(key, count)| format!("{key}={count}")).collect();
    let proof_fallbacks = proof_qualifying_fallback_count(&categories);
    let verdict = run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
        .unwrap_or_else(|err| panic!("{name}: solver failed: {err}"));
    match verdict.as_str() {
        "unsat" => assert!(
            assertion_is_true || proof_fallbacks > 0,
            "{name}: false assertion became an unqualified proof: {rendered:?}, {evidence:?}",
        ),
        "sat" if categories.is_empty() => {
            assert!(!assertion_is_true, "{name}: true assertion became a clean counterexample",)
        }
        "sat" => assert!(
            !ctrex_evidence_is_complete(&rendered, evidence),
            "{name}: fallback no longer fails the actual certification completeness gate; \
             audit property dependence before accepting this change: {rendered:?}, {evidence:?}",
        ),
        other => panic!("{name}: solver returned neither SAT nor UNSAT: {other}"),
    }
}

/// `RefCell<()>` is 8 bytes and `RefCell<u8>` 16, but the capacity model
/// read the heap model's size, which strips `RefCell` first: `RefCell<()>`
/// read as zero-sized (`capacity()` was `usize::MAX`) and `RefCell<u8>` as 1
/// byte (one push gave 8 where std gives 4). `Cell<()>` is zero-sized.

#[test]
fn merged_comparison_claims_keep_actual_driver_accounting() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(PROBE, |mut ctx| {
        check_comparison_claim(&mut ctx, "probe_custom_eq_array", "assert!(a == b)", true);
        // The same values compare equal by parity but differ bitwise. A
        // bit-comparison shortcut would incorrectly prove this false twin.
        check_comparison_claim(
            &mut ctx,
            "probe_custom_eq_array_false_twin",
            "assert!(a != b)",
            false,
        );
        check_comparison_claim(
            &mut ctx,
            "probe_f32_array_order",
            "assert!([-1.0f32, 0.0] < [1.0f32, 0.0])",
            true,
        );
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

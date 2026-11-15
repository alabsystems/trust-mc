// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Package item (c) of fix/chc-walker-fail-closed: the statement path's
//! callers of the inline walker, and the models that take over a call whose
//! walk failed, must not turn a lost obligation into a clean proof
//! (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: package
//! round"; tools/soundness-duals/walker_caller_fallback_dual.rs and
//! iter_reduce_obligation_dual.rs). Each test translates a probe harness body
//! and checks the obligation or the fail-closed record the old encoding
//! dropped.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use trust_mc_core::chc::ChcVc;
use trust_mc_core::violation::PropertyKind;

const PROBE: &str = r#"
    #![allow(dead_code)]
    use std::collections::BTreeMap;

    #[inline(never)] fn g1(x: u8) -> u8 { x ^ 1 }
    #[inline(never)] fn g2(x: u8) -> u8 { x ^ 2 }
    #[inline(never)] fn g3(x: u8) -> u8 { x ^ 3 }
    #[inline(never)] fn g4(x: u8) -> u8 { x ^ 4 }
    #[inline(never)] fn g5(x: u8) -> u8 { x ^ 5 }
    #[inline(never)] fn g6(x: u8) -> u8 { x ^ 6 }
    #[inline(never)] fn g7(x: u8) -> u8 { x ^ 7 }
    #[inline(never)] fn g8(x: u8) -> u8 { x ^ 8 }
    #[inline(never)] fn g9(x: u8) -> u8 { x ^ 9 }
    #[inline(never)] fn g10(x: u8) -> u8 { x ^ 10 }
    #[inline(never)] fn sink<T>(_v: T) {}

    // A body the fn-inline walker declines (over its block budget).
    macro_rules! bulk {
        ($x:ident) => {{
            let $x = g1($x); let $x = g2($x); let $x = g3($x); let $x = g4($x); let $x = g5($x);
            let $x = g6($x); let $x = g7($x); let $x = g8($x); let $x = g9($x); let $x = g10($x);
            let $x = g1($x); let $x = g2($x); let $x = g3($x); let $x = g4($x); let $x = g5($x);
            let $x = g6($x); let $x = g7($x); let $x = g8($x); let $x = g9($x); let $x = g10($x);
            let $x = g1($x); let $x = g2($x); let $x = g3($x); let $x = g4($x); let $x = g5($x);
            let $x = g6($x); let $x = g7($x); let $x = g8($x); let $x = g9($x); let $x = g10($x);
            let $x = g1($x); let $x = g2($x); let $x = g3($x); let $x = g4($x); let $x = g5($x);
            let $x = g6($x); let $x = g7($x); let $x = g8($x); let $x = g9($x); let $x = g10($x);
            $x
        }};
    }

    #[derive(Clone)]
    pub struct Reg {
        m: BTreeMap<u8, u8>,
        x: u8,
    }
    impl Reg {
        #[inline(never)]
        fn with_bump(&self) -> Reg {
            assert!(self.x != 100);
            let x = self.x;
            let x = bulk!(x);
            let mut r = self.clone();
            r.x = x;
            r
        }
    }
    pub fn probe_passthrough(r: &Reg) -> u8 {
        r.with_bump().x
    }

    pub struct Bag {
        v: Vec<u8>,
        x: u8,
    }
    impl Bag {
        #[inline(never)]
        fn get(&self, i: usize) -> u8 {
            assert!(i != 1);
            let x = self.x;
            let x = bulk!(x);
            sink(x);
            self.v[i]
        }
        #[inline(never)]
        fn width(&self) -> usize {
            let x = self.x;
            let x = bulk!(x);
            sink(x);
            self.v.len()
        }
        #[inline(never)]
        fn doubled(&self) -> Vec<u8> {
            assert!(self.x != 100);
            let x = self.x;
            let x = bulk!(x);
            sink(x);
            self.v.iter().map(|a| a.wrapping_mul(2)).collect()
        }
    }
    // The models read the receiver's state, so it is a local here, as in a
    // harness.
    pub fn probe_vec_accessor(x: u8, i: usize) -> u8 {
        let b = Bag { v: vec![1, 2, 3], x };
        b.get(i)
    }
    pub fn probe_vec_len_accessor(x: u8) -> usize {
        let b = Bag { v: vec![1, 2, 3], x };
        b.width()
    }
    pub fn probe_collect_method(x: u8) -> usize {
        let b = Bag { v: vec![1, 2], x };
        b.doubled().len()
    }

    pub fn probe_sum(a: u8) -> u8 {
        let v = [a, 200u8];
        v.iter().sum()
    }
    pub fn probe_fold_assert(a: u8) -> u8 {
        let v = [a, 1u8];
        v.iter().fold(0u8, |acc, &x| {
            assert!(x != 100);
            acc ^ x
        })
    }
    pub fn probe_fold_clean(a: u8) -> u8 {
        let v = [a, 1u8];
        v.iter().fold(0u8, |acc, &x| acc ^ x)
    }
    pub fn probe_try_fold_assert(a: u8) -> Option<u8> {
        let v = [a, 1u8];
        v.iter().try_fold(0u8, |acc, &x| {
            assert!(x != 100);
            Some(acc ^ x)
        })
    }
"#;

/// Translate `fn_name` and return its VC and the translation-drop site
/// reasons it recorded, under the metadata counter lock.
fn translate(fn_name: &str) -> (ChcVc, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    let mut out = None;
    with_test_ay_ctx_for_source(PROBE, |ctx| {
        let ctx_name = format!("walker_caller_fallbacks__{fn_name}");
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let vc = mir_to_chc(ctx.tcx, &body, ctx_name.as_str(), ChcConfig::default());
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(&ctx_name)
            .unwrap_or_default();
        out = Some((vc, reasons));
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
    out.expect("translated")
}

fn properties_of(vc: &ChcVc, kind: PropertyKind) -> Vec<Option<String>> {
    vc.properties.iter().filter(|p| p.kind == kind).map(|p| p.message.clone()).collect()
}

/// The struct-method passthrough constrains the result to equal the receiver
/// and drops the method's checks: it fails closed now. Before, it recorded
/// nothing, and `assert!(self.x != 100)` in the method verified clean.
#[test]
fn test_struct_method_passthrough_fails_closed() {
    let (_, reasons) = translate("probe_passthrough");
    assert!(
        reasons.contains_key("struct_method_passthrough_unmodelled"),
        "the passthrough claimed the call and records it, reasons = {reasons:?}"
    );
}

/// The Vec accessor model states the matched access only: a method that can
/// fail (its `assert!`, the index's bounds check) fails closed; a `len`
/// accessor that cannot fail records nothing.
#[test]
fn test_struct_vec_accessor_fails_closed_only_when_the_method_can_fail() {
    let (_, reasons) = translate("probe_vec_accessor");
    assert!(
        reasons.contains_key("struct_vec_accessor_unstated_check"),
        "the getter can fail, reasons = {reasons:?}"
    );
    let (_, reasons) = translate("probe_vec_len_accessor");
    assert!(
        !reasons.contains_key("struct_vec_accessor_unstated_check"),
        "the len accessor cannot fail, reasons = {reasons:?}"
    );
}

/// The iter-collect-method model states the map/collect pattern only.
#[test]
fn test_iter_collect_method_fails_closed_when_the_method_can_fail() {
    let (_, reasons) = translate("probe_collect_method");
    assert!(
        reasons.contains_key("iter_collect_method_unstated_check"),
        "the method's assert is not in the model, reasons = {reasons:?}"
    );
}

/// `Iterator::sum` checks every step's `+` for overflow (Kani's "attempt to
/// add with overflow"); the replay used to `bvadd` and check nothing.
#[test]
fn test_iter_sum_checks_each_step_for_overflow() {
    let (vc, _) = translate("probe_sum");
    let overflow = properties_of(&vc, PropertyKind::ArithmeticOverflow);
    assert!(
        overflow.iter().any(|m| m.as_deref() == Some("attempt to add with overflow")),
        "a sum step overflow property, got {overflow:?}"
    );
}

/// A walked `fold` closure's checks are the step's obligations, emitted
/// exactly (they were dropped and the harness failed closed); a closure with
/// none records nothing.
#[test]
fn test_iter_fold_emits_the_closure_checks_per_step() {
    let (vc, reasons) = translate("probe_fold_assert");
    let assertions = properties_of(&vc, PropertyKind::Assertion);
    assert!(
        assertions.iter().any(|m| !m.as_deref().is_some_and(|m| m.contains("does not replay"))),
        "the closure's assertion is an exact property, got {assertions:?}"
    );
    assert!(
        !reasons.contains_key("inline_closure_deferred_checks_dropped"),
        "no check is dropped, reasons = {reasons:?}"
    );
    let (_, reasons) = translate("probe_fold_clean");
    assert!(
        !reasons.contains_key("iter_reduce_step_uncertified"),
        "an obligation-free closure needs no reach check, reasons = {reasons:?}"
    );
}

/// A `try_fold` closure is never walked: when it can fail, the model records
/// an uncertified reach check under "the iterator has an element" (before, a
/// blessed `iter_try_fold_acc` and nothing else, so its `assert!` was gone).
#[test]
fn test_iter_try_fold_closure_that_can_fail_is_an_uncertified_reach_check() {
    let (vc, reasons) = translate("probe_try_fold_assert");
    assert!(
        reasons.contains_key("iter_reduce_step_uncertified"),
        "the unreplayed step is accounted, reasons = {reasons:?}"
    );
    let assertions = properties_of(&vc, PropertyKind::Assertion);
    assert!(
        assertions.iter().any(|m| m.as_deref().is_some_and(|m| m.contains("does not replay"))),
        "the reach check is a property, got {assertions:?}"
    );
}

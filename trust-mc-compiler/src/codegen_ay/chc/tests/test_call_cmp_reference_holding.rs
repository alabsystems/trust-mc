// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comparisons of reference-holding values: the two shapes that stay exact,
//! and the one that must stay closed.
//!
//! `PartialEq` on a value holding a reference compares REFERENTS, and the
//! primitive comparison lanes hold addresses for such values, so the encoder
//! leaves a reference-holding comparison unconstrained
//! (`cmp_value_holds_reference`). Two shapes compare no referent and keep their
//! exact answer: a comparison against a constant fieldless variant
//! (`first(&a) == None`, `comparison_against_fieldless_variant_constant`) and a
//! comparison through references to the unit type (`Some(&()) == Some(&())`,
//! `comparison_referent_is_unit_like`). The third test pins the closed shape:
//! `Some(&x) != Some(&y)` with `x == y` is false in Rust and must not be proved.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const REFERENCE_HOLDING_CMP_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn first<T>(slice: &[T]) -> Option<&T> {
        slice.first()
    }

    // `Option<&u8>` against the constant `None`: discriminants only.
    pub fn probe_first_of_empty_is_none(empty: [u8; 0]) {
        assert!(first(&empty) == None);
    }

    // `Option<&u8>` holding `Some` against the constant `None`: `!=` is exact.
    pub fn probe_some_ref_is_not_none(x: u8) {
        let holder = Some(&x);
        assert!(holder != None);
    }

    pub fn probe_first_of_singleton_is_not_none(values: [u8; 1]) {
        assert!(first(&values) != None);
    }

    pub fn probe_rebound_slice_cannot_keep_old_empty_length(x: u8) {
        let empty: [u8; 0] = [];
        let full = [x];
        let mut slice: &[u8] = &empty;
        let slot = &mut slice;
        *slot = &full;
        assert!(first(slice) == None);
    }

    pub fn probe_joined_slice_cannot_always_be_empty(pick_empty: bool, x: u8) {
        let empty: [u8; 0] = [];
        let full = [x];
        let slice: &[u8] = if pick_empty { &empty } else { &full };
        assert!(first(slice) == None);
    }

    // Through references to unit: `*l == *r` is `() == ()`.
    pub fn probe_unit_refs_compare_equal(units: [(); 3]) {
        assert!(units.first() == Some(&()));
        assert!(!(units.first() != Some(&())));
    }

    // Two `Some(&u8)` with equal referents: the negated truth must not be proved.
    pub fn probe_some_refs_with_equal_referents_not_proved_unequal(x: u8) {
        let y = 5u8;
        if x == 5 {
            assert!(Some(&x) != Some(&y));
        }
    }
"#;

fn translate_probe(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    fn_name: &str,
) -> (trust_mc_core::chc::ChcVc, std::collections::BTreeMap<String, usize>) {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    let chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
    let (vc, _, _) = chc_ctx.translate_with_diagnostics();
    assert_vc_structure(&vc, fn_name, body.blocks.len());
    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .get(fn_name)
        .cloned()
        .unwrap_or_default();
    (vc, sites)
}

fn reference_cmp_fallbacks(sites: &std::collections::BTreeMap<String, usize>) -> usize {
    sites.get("cmp_value_holds_reference").copied().unwrap_or(0)
        + sites.get("cmp_reference_level_unresolved").copied().unwrap_or(0)
}

#[test]
fn test_option_ref_against_constant_none_stays_exact() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(REFERENCE_HOLDING_CMP_SOURCE, |ctx| {
        for fn_name in [
            "probe_first_of_empty_is_none",
            "probe_some_ref_is_not_none",
            "probe_first_of_singleton_is_not_none",
        ] {
            let (vc, sites) = translate_probe(ctx.tcx, fn_name);
            assert_eq!(
                reference_cmp_fallbacks(&sites),
                0,
                "{fn_name}: a comparison against the constant None compares no referent and \
                 must not fail closed; sites={sites:?}"
            );
            assert_z3_result(&emit_chc(&vc).to_string(), "unsat");
        }
    });
}

#[test]
fn test_inlined_slice_metadata_does_not_keep_rebound_or_joined_zero_length() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(REFERENCE_HOLDING_CMP_SOURCE, |ctx| {
        for fn_name in [
            "probe_rebound_slice_cannot_keep_old_empty_length",
            "probe_joined_slice_cannot_always_be_empty",
        ] {
            let (vc, _) = translate_probe(ctx.tcx, fn_name);
            assert_z3_result(&emit_chc(&vc).to_string(), "sat");
        }
    });
}

#[test]
fn test_option_unit_ref_comparison_stays_exact() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(REFERENCE_HOLDING_CMP_SOURCE, |ctx| {
        let fn_name = "probe_unit_refs_compare_equal";
        let (vc, sites) = translate_probe(ctx.tcx, fn_name);
        assert_eq!(
            reference_cmp_fallbacks(&sites),
            0,
            "{fn_name}: `Some(&()) == Some(&())` compares units, not addresses; sites={sites:?}"
        );
        assert_z3_result(&emit_chc(&vc).to_string(), "unsat");
    });
}

#[test]
fn test_some_refs_with_equal_referents_are_not_proved_unequal() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    with_test_ay_ctx_for_source(REFERENCE_HOLDING_CMP_SOURCE, |ctx| {
        let fn_name = "probe_some_refs_with_equal_referents_not_proved_unequal";
        let (vc, _) = translate_probe(ctx.tcx, fn_name);
        // `Some(&x) != Some(&y)` with `x == y == 5` is false: the assertion
        // fails in Rust, so the error must stay reachable. A proof here would
        // be the address comparison of
        // tools/soundness-duals/negative/option_ref_partial_eq_referents.rs.
        assert_z3_result(&emit_chc(&vc).to_string(), "sat");
    });
}

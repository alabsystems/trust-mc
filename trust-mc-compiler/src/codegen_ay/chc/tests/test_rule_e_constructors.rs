// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule E (design trust-mc-reds-final §4.4; `codegen_ctx/fresh_vars.rs`): a
//! fresh CHC value is minted through a constructor that states why it is fresh,
//! and only a booked havoc reaches a verdict as an approximation.
//!
//! These tests hold the audited reason table to `fallback_soundness`, and the
//! constructors to their bookings: `Havoc::mint` books one audited sound havoc
//! with the value's identity, `Havoc::booked` adds nothing to the booking its
//! token stands for, and the `ExactVar` constructors book nothing.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::{
    ExactVar, FallbackSoundness, Havoc, fallback_soundness, sound_havoc,
};

/// Every reason a `Havoc::mint` site can book has its audit line in
/// `fallback_soundness`: removing one (or adding a const without one) fails
/// here, so no site mints under an unaudited reason.
#[test]
fn every_sound_havoc_reason_is_audited() {
    let mut seen = std::collections::HashSet::new();
    for reason in sound_havoc::ALL {
        assert_eq!(
            fallback_soundness(reason.as_str()),
            FallbackSoundness::SoundHavoc,
            "`{}` has no audit line in fallback_soundness",
            reason.as_str()
        );
        assert!(seen.insert(reason.as_str()), "`{}` is listed twice", reason.as_str());
    }
}

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_rule_e(a: u32) -> u32 { a }
"#;

/// The booking each constructor leaves on a fresh context: (sound-havoc
/// counter, fail-closed counter, accounted identities, recorded identities).
fn bookings_after(
    mint: impl FnOnce(&mut ChcCtx<'_, '_>) + Send,
) -> (usize, usize, usize, Vec<String>) {
    let mut out = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rule_e");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rule_e", ChcConfig::default());
        mint(&mut chc_ctx);
        chc_ctx.flush_deferred_approximation_identities();
        out = Some((
            chc_ctx.diagnostics.sound_havoc_drop.get(),
            chc_ctx.diagnostics.place_translation_drop.get(),
            chc_ctx.vc.accounted_approximations,
            chc_ctx.vc.approximated_vars.clone(),
        ));
    });
    out.expect("the probe compiled")
}

#[test]
fn havoc_mint_books_one_audited_havoc_with_its_identity() {
    let (havoc, fail_closed, accounted, vars) = bookings_after(|ctx| {
        let _ = Havoc::mint(
            ctx,
            sound_havoc::UNTRACKED_CALL_RESULT,
            "rule_e_minted".to_owned(),
            ay_bindings::Sort::bitvec(8),
        );
    });
    assert_eq!((havoc, fail_closed, accounted), (1, 0, 1));
    assert!(vars.iter().any(|v| v == "rule_e_minted"), "the identity is recorded: {vars:?}");
}

#[test]
fn havoc_mint_deferred_accounts_its_identity_at_finalization() {
    let (havoc, fail_closed, accounted, vars) = bookings_after(|ctx| {
        let _ = Havoc::mint_deferred(
            &*ctx,
            sound_havoc::UNTRACKED_COLLECTION_STATE,
            "rule_e_deferred".to_owned(),
            ay_bindings::Sort::bitvec(8),
        );
    });
    assert_eq!((havoc, fail_closed, accounted), (1, 0, 1));
    assert!(vars.iter().any(|v| v == "rule_e_deferred"), "the identity is recorded: {vars:?}");
}

#[test]
fn havoc_mint_unattributed_books_without_an_identity() {
    let (havoc, fail_closed, accounted, _) = bookings_after(|ctx| {
        let _ = Havoc::mint_unattributed(
            &*ctx,
            sound_havoc::UNTRACKED_WALKER_VALUE,
            "rule_e_unattributed".to_owned(),
            ay_bindings::Sort::bitvec(8),
        );
    });
    assert_eq!((havoc, fail_closed, accounted), (1, 0, 0));
}

/// The token stands for the booking already made: minting under it adds
/// nothing, and a fail-closed reason stays fail-closed.
#[test]
fn havoc_booked_stands_on_its_token() {
    let (havoc, fail_closed, accounted, _) = bookings_after(|ctx| {
        let booked = ctx.record_sound_fallback_reason("rule_e_test_not_audited");
        let _ = Havoc::booked(booked, "rule_e_booked_a".to_owned(), ay_bindings::Sort::bool());
        let _ = Havoc::booked(booked, "rule_e_booked_b".to_owned(), ay_bindings::Sort::bool());
    });
    assert_eq!((havoc, fail_closed, accounted), (0, 1, 0));
}

#[test]
fn exact_vars_book_nothing() {
    let booking = bookings_after(|_ctx| {
        let sort = ay_bindings::Sort::bitvec(16);
        let _ = ExactVar::defined("rule_e_defined".to_owned(), sort.clone());
        let _ = ExactVar::nondet("rule_e_nondet".to_owned(), sort.clone());
        let _ = ExactVar::unobserved("rule_e_unobserved".to_owned(), sort);
    });
    assert_eq!(booking, (0, 0, 0, Vec::new()));
}

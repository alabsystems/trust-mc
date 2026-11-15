// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pure claim policies shared by the driver and engine parity tests.
//! Counting and completeness are separate from per-property dependence.

use std::collections::BTreeMap;

/// The completeness fields the compiler supplies for approximation evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct EvidenceAccounting {
    pub(crate) complete: bool,
    pub(crate) accounted: usize,
}

/// Count the same proof-qualifying fallbacks as the driver fail-close gate.
pub(crate) fn proof_qualifying_fallback_count(approx: &BTreeMap<String, usize>) -> usize {
    approx
        .iter()
        .filter(|(cat, _)| !qualifies_proof_unchanged(cat.as_str()))
        .map(|(_, count)| count)
        .sum()
}

/// Sound-approximation categories that leave a PROOF exactly as it stands.
///
/// Both members still taint a COUNTEREXAMPLE through `classify_ctrex` (they are
/// SOUND_APPROXIMATION members); this predicate only keeps them out of Step B's
/// proof-qualifying count and therefore out of Step C's conversion.
///
/// * `chc_sound_havoc_drop` — a CERTIFIED fresh unconstrained havoc, so a proof
///   over it is universally quantified. The original Step B exclusion.
/// * `unstubbed_abstraction` (D1, 2026-09-14) — a stdlib function the
///   reachability boundary abstracts, with no stub and no handler. Excluded on a NARROWER ground: this
///   is the behaviour the driver already had (the event reached no counter at
///   all, so it contributed 0 to `sound_fallback_count`), and D1 is a
///   counterexample-side defect. Routing it into Step B instead would convert
///   every SUCCESS harness that merely TOUCHES such a call into an
///   OverApproximation failure — a corpus-wide change to the PROOF side that
///   this fix does not measure and does not claim. The proof-side question
///   (does dropping an abstracted call's side effects admit a false proof?) is
///   open, unchanged by this commit, and recorded in
///   docs/chc-unknown-burndown-2026-09-14.md.
pub(crate) fn qualifies_proof_unchanged(category: &str) -> bool {
    use trust_mc_metadata::UnsoundnessCategory::{ChcSoundHavocDrop, UnstubbedAbstraction};
    category == ChcSoundHavocDrop.json_key() || category == UnstubbedAbstraction.json_key()
}

// These events do not carry the compiler's freed-value identity.
const COMPILER_UNACCOUNTED_CATEGORIES: &[&str] =
    &[trust_mc_metadata::UnsoundnessCategory::UnstubbedAbstraction.json_key()];

/// Require the driver's complete, exactly accounted approximation evidence.
/// Per-property failure and independence checks remain with the caller.
pub(crate) fn ctrex_evidence_is_complete(categories: &[String], ev: EvidenceAccounting) -> bool {
    // Parse the harness taint total and its `unhandled_calls` share. Each
    // `unhandled_calls` double-labels a `chc_translation_drop` event from the
    // SAME SoundFallback site, so subtracting it recovers the count of DISTINCT
    // freed-value events the compiler was expected to account.
    let mut taint_total = 0usize;
    let mut unhandled = 0usize;
    for entry in categories {
        let Some((name, count)) = entry.rsplit_once('=') else { continue };
        let Ok(count) = count.parse::<usize>() else { continue };
        // An event the compiler never accounts frees a value no identity
        // names, so no dependence verdict can clear it: the harness stays
        // tainted whatever the counts say. A count comparison alone let one
        // unstubbed abstraction stand in for one accounted havoc of a
        // DIFFERENT event (unstubbed_abstraction_safe.rs::
        // safe_mutex_held_while_offset_stays_in_bounds, decision REDS-REST).
        if count > 0 && COMPILER_UNACCOUNTED_CATEGORIES.contains(&name) {
            return false;
        }
        taint_total += count;
        if name == "unhandled_calls" {
            unhandled += count;
        }
    }
    let effective_total = taint_total.saturating_sub(unhandled);

    // COMPLETENESS: there was real taint (effective_total > 0), the compiler's
    // local flag holds, AND the accounted count equals the driver's own
    // (double-count adjusted) taint total — i.e. EVERY approximation on the
    // harness recorded its freed-var identity. Any failure means an
    // approximation freed a value the dependence analysis never saw, so the
    // whole harness stays tainted (an unplumbed site is fail-closed).
    if effective_total == 0 || !ev.complete || ev.accounted != effective_total {
        return false;
    }

    true
}

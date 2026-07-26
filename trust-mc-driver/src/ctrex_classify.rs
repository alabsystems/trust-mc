// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! CTREX (counterexample) classification logic (#3128, #3303, #3458).
//!
//! Classifies counterexample verdicts by correlating with unsoundness counts.
//! Split from [`crate::demotion`] for module size compliance.
//! Tests in [`crate::ctrex_classify_tests`].

use std::collections::BTreeMap;

use trust_mc_metadata::HarnessMetadata;

use crate::demotion::{
    harness_names_match, lookup_per_harness, resolve_demoting_categories, resolve_per_harness_count,
};
use crate::unsoundness_counts::CrateUnsoundnessCounts;
use crate::verification_result::CtrexCategory;

fn push_fail_closed_trigger(
    triggers: &mut Vec<String>,
    category: &'static str,
    crate_total: usize,
    per_harness: &BTreeMap<String, usize>,
    harness: &HarnessMetadata,
) {
    let count = resolve_per_harness_count(crate_total, per_harness, &harness.pretty_name);
    if count > 0 {
        triggers.push(format!("{category}={count}"));
    }
}

/// Classify a CTREX verdict by correlating with unsoundness counts (#3128, #3303).
///
/// Called ONLY when the solver returned SAT (counterexample) and the result was
/// NOT demoted from a PROOF.
///
/// Classification priority:
/// 1. EncodingGap — DEMOTED_CATEGORIES nonzero (wrong model, gap in encoding)
/// 2. OverApproximation — SOUND_APPROXIMATION nonzero (unconstrained symbolics
///    allowed impossible counterexample) (#3303)
/// 3. Genuine — no unsoundness detected
pub(crate) fn classify_ctrex(
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) -> CtrexCategory {
    let categories = resolve_demoting_categories(harness, counts);

    let demoted_triggers: Vec<String> = categories
        .into_iter()
        .filter(|(_, count)| *count > 0)
        .map(|(cat, count)| format!("{cat}={count}"))
        .collect();

    let offset_only_demotion = !demoted_triggers.is_empty()
        && demoted_triggers.iter().all(|t| t.starts_with("offset_provenance_unresolved="));

    if !demoted_triggers.is_empty() && !offset_only_demotion {
        return CtrexCategory::EncodingGap { categories: demoted_triggers };
    }

    // Check FAIL_CLOSED categories (Part of #3447). These deliberately inject
    // failure (false constraints, error rules) for untranslatable constructs.
    // Any CTREX in their presence is forced, not genuine. Classified as
    // EncodingGap since the encoding has a known gap that forced the failure.
    // Most fail-closed counters are crate-level because they fire during
    // codegen. Iterator/BigInt fail-closed counters also carry per-harness
    // maps, so prefer harness-local precision when it exists.
    let mut fail_closed_triggers: Vec<String> = Vec::new();
    if counts.assert_untranslatable > 0 {
        fail_closed_triggers
            .push(format!("assert_untranslatable={}", counts.assert_untranslatable));
    }
    if counts.heap_check_untranslatable > 0 {
        fail_closed_triggers
            .push(format!("heap_check_untranslatable={}", counts.heap_check_untranslatable));
    }
    if counts.heap_check_unknown_layout > 0 {
        fail_closed_triggers
            .push(format!("heap_check_unknown_layout={}", counts.heap_check_unknown_layout));
    }
    push_fail_closed_trigger(
        &mut fail_closed_triggers,
        "iterator_unsoundness",
        counts.iterator_unsoundness,
        &counts.iterator_unsoundness_per_harness,
        harness,
    );
    push_fail_closed_trigger(
        &mut fail_closed_triggers,
        "bigint_unsoundness",
        counts.bigint_unsoundness,
        &counts.bigint_unsoundness_per_harness,
        harness,
    );
    if !fail_closed_triggers.is_empty() {
        if offset_only_demotion {
            let mut all_triggers = demoted_triggers.clone();
            all_triggers.extend(fail_closed_triggers);
            return CtrexCategory::EncodingGap { categories: all_triggers };
        }
        return CtrexCategory::EncodingGap { categories: fail_closed_triggers };
    }

    // Task #78 (offset cluster): a SAT counterexample whose ONLY demoted trigger
    // is `offset_provenance_unresolved` is a candidate for genuine certification.
    // The skipped alloc-bound check leaves the base pointer's `obj_id` lane
    // symbolic, but a count / mul-overflow overflow check reads only the offset
    // operand and is provably independent of it. Route to OverApproximation
    // carrying the FULL freeing set (offset + any co-occurring sound-approx) so
    // `recertify_overapprox_ctrex` runs the real per-property dependence check:
    // the obj_id-DEPENDENT checks (provenance / wrap / same-object) stay demoted,
    // so a spurious counterexample over a symbolic obj_id can never certify
    // Genuine.
    //
    // SOUNDNESS: this is SAT-only (see the fn doc). `OffsetProvenanceUnresolved`
    // stays a DEMOTED_CATEGORIES member, so the UNSAT proof-demotion path
    // (`demote_for_all_unsoundness`) is untouched — no skipped alloc-bound can
    // mask a real OOB into a false Safe. Any co-occurring NON-offset demoted OR
    // fail-closed trigger returns EncodingGap above. If the completeness
    // checksum or dependence gate fails, recert leaves the verdict
    // OverApproximation (still non-Genuine) — never a false positive.
    if offset_only_demotion {
        let mut freeing_set = demoted_triggers;
        if let Some(approx_cats) =
            lookup_per_harness(&counts.sound_approx_per_harness, &harness.pretty_name)
        {
            for (cat, count) in approx_cats {
                freeing_set.push(format!("{cat}={count}"));
            }
        }
        return CtrexCategory::OverApproximation { categories: freeing_set };
    }

    // Task #77 (generic driver-only Genuine shortcut — investigated, NOT shipped):
    //
    // Proposal: when a SAT counterexample names a specific violated `error_p{N}`
    // relation (BSEM-18), certify it Genuine despite harness-level taint if that
    // relation's reachability is data-INDEPENDENT of every approximated value —
    // recovering oracle=fail tests whose real bug is unrelated to the drop.
    //
    // Finding: this cannot be done SOUNDLY driver-side. Every constraint-drop
    // and unhandled-call approximation (`chc_translation_drop`,
    // `chc_sound_havoc_drop`, `unhandled_calls`, `static_init_incomplete`, …)
    // frees a NORMALLY-NAMED CHC variable — it deletes a defining constraint,
    // it does not mint a marked fresh var. In the emitted CHC that freed var is
    // indistinguishable from a fully-constrained one. Concretely (see
    // expected/foreign-function/ffi_ptr.rs and dual_77_{dependent,independent}):
    // a harness whose failing check READS the havocked extern return and a
    // harness whose failing check ignores it produce byte-identical
    // `error_p{N}` rule shapes and identical taint signatures. Any cheap
    // syntactic proxy (fragment scan / backward reachability / free-variable
    // analysis) certifies BOTH — including the ffi_ptr / unsupported_object_size
    // traps — which is the exact "overapprox-fail -> parity" gaming that is
    // forbidden. Sound recovery requires the COMPILER to plumb each dropped
    // value's SMT-var identity into the VC artifact so the driver can run a real
    // dependency check. Task #78 now does that for explicitly accounted sites
    // (including the offset-only route above); all unaccounted/default
    // sound-approximation cases still stay OverApproximation below.
    //
    // Check SOUND_APPROXIMATION categories (#3303). If the harness has nonzero
    // sound-approximation counts, the CTREX may be spurious: the solver found a
    // counterexample using unconstrained symbolic values that the real program
    // can never produce.
    if let Some(approx_cats) =
        lookup_per_harness(&counts.sound_approx_per_harness, &harness.pretty_name)
    {
        if !approx_cats.is_empty() {
            let cat_entries: Vec<String> =
                approx_cats.iter().map(|(cat, count)| format!("{cat}={count}")).collect();
            return CtrexCategory::OverApproximation { categories: cat_entries };
        }
    }

    // Part of #3447: when per-harness attribution is missing or ambiguous,
    // fall back to crate-level sound-approximation totals.
    //
    // Attribution refinement (contract REPLACE lane gate): the crate totals
    // are summed FROM the per-harness map, so every count in them is
    // attributed to a specific encoded function. Counts attributed to a
    // DIFFERENT proof harness of the same crate cannot taint THIS harness's
    // counterexample — they are evaluated when that harness is classified
    // (a modifies check-harness's honest drops must not demote the sibling
    // replace-harness's genuine counterexample). Only the residual —
    // counts attributed to non-harness function keys — keeps demoting every
    // harness in the crate (fail-closed on genuinely unattributable drops).
    if !counts.sound_approx_crate_totals.is_empty() {
        let names_match = harness_names_match;
        let residual: Vec<String> = {
            let current = harness.pretty_name.as_str();
            let mut totals: BTreeMap<&str, usize> = BTreeMap::new();
            for (fn_key, cats) in &counts.sound_approx_per_harness {
                // Fail-closed: a key that could name the CURRENT harness
                // (however ambiguously) keeps demoting it.
                let could_be_current = names_match(fn_key, current);
                let attributed_to_other_harness = !could_be_current
                    && counts
                        .harness_names
                        .iter()
                        .any(|name| name != current && names_match(fn_key, name));
                if attributed_to_other_harness {
                    continue;
                }
                for (cat, count) in cats {
                    *totals.entry(cat.as_str()).or_default() += count;
                }
            }
            totals.into_iter().map(|(cat, count)| format!("{cat}={count}")).collect()
        };
        if !residual.is_empty() {
            return CtrexCategory::OverApproximation { categories: residual };
        }
    }

    CtrexCategory::Genuine
}

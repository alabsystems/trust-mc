// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! PROOF demotion logic.
//!
//! Demotes PROOF verdicts to FAILURE when unsoundness categories are nonzero.
//! CTREX classification is in [`crate::ctrex_classify`].

use std::collections::{BTreeMap, BTreeSet};

use trust_mc_metadata::HarnessMetadata;

use crate::unsoundness_counts::CrateUnsoundnessCounts;
use crate::util::warning;
use crate::verification_result::{
    CtrexCategory, FailedProperties, VerificationResult, VerificationStatus,
};

/// Resolve the effective unsoundness count for a harness, preferring per-harness
/// data over the crate-level total (#2959).
///
/// When per-harness data is available (non-empty map), returns the count for the
/// specific harness (0 if the harness has no fallbacks). When per-harness data is
/// unavailable, falls back to the crate-level total for conservative safety.
///
/// The lookup tolerates a qualified/unqualified harness-name mismatch only when
/// the most-specific suffix match is unique within the crate. This keeps older
/// metadata and current harness names aligned without guessing across ambiguous
/// siblings.
pub(crate) fn lookup_per_harness<'a, T>(
    per_harness: &'a BTreeMap<String, T>,
    harness_name: &str,
) -> Option<&'a T> {
    if let Some(value) = per_harness.get(harness_name) {
        return Some(value);
    }

    let mut best_match: Option<(&T, usize)> = None;
    let mut best_is_ambiguous = false;

    for (candidate, value) in per_harness.iter().filter(|(candidate, _)| {
        unique_harness_suffix_match(candidate, harness_name)
            || unique_harness_suffix_match(harness_name, candidate)
    }) {
        let suffix_len = candidate.len().min(harness_name.len());
        match best_match {
            None => {
                best_match = Some((value, suffix_len));
                best_is_ambiguous = false;
            }
            Some((_, best_len)) if suffix_len > best_len => {
                best_match = Some((value, suffix_len));
                best_is_ambiguous = false;
            }
            Some((_, best_len)) if suffix_len == best_len => {
                best_is_ambiguous = true;
            }
            Some(_) => {}
        }
    }

    if best_is_ambiguous { None } else { best_match.map(|(value, _)| value) }
}

pub(crate) fn unique_harness_suffix_match(qualified: &str, suffix: &str) -> bool {
    qualified.len() > suffix.len()
        && qualified.strip_suffix(suffix).is_some_and(|prefix| prefix.ends_with("::"))
}

/// Whether two harness/function path names refer to the same item, tolerating
/// a qualified/unqualified mismatch at a `::` boundary (shared with
/// `classify_ctrex`'s residual attribution).
pub(crate) fn harness_names_match(a: &str, b: &str) -> bool {
    a == b || unique_harness_suffix_match(a, b) || unique_harness_suffix_match(b, a)
}

/// Whether a per-harness map key contributes to `harness_name`'s count under
/// the MIXED-key-space contract (task #65).
///
/// Compiler-emitted `per_harness` maps are harness-keyed when the per-harness
/// accumulator ran, but per-FUNCTION-keyed seeds survive on writer paths
/// without snapshot windows (see trust-mc-compiler unsoundness_fields.rs
/// `merge_ph`). Attribution is fail-closed:
/// - a key that could name the CURRENT harness → counts;
/// - a key naming a DIFFERENT known proof harness → does not count (it is
///   evaluated when that harness is checked);
/// - any other key (fn-keyed survivor / unattributable residual) → counts
///   against EVERY harness of the crate. Before #65 such keys silently
///   resolved to 0 — a fail-open that skipped demotion.
pub(crate) fn attributable_to_harness(
    key: &str,
    harness_name: &str,
    harness_names: &BTreeSet<String>,
) -> bool {
    harness_names_match(key, harness_name)
        || !harness_names.iter().any(|name| name != harness_name && harness_names_match(key, name))
}

pub(crate) fn resolve_per_harness_count(
    crate_total: usize,
    per_harness: &BTreeMap<String, usize>,
    harness_name: &str,
) -> usize {
    if per_harness.is_empty() {
        crate_total
    } else {
        lookup_per_harness(per_harness, harness_name).copied().unwrap_or(0)
    }
}

/// Fail-closed variant of [`resolve_per_harness_count`] (task #65).
///
/// Sums every per-harness entry attributable to `harness_name` under
/// [`attributable_to_harness`], so a per-FUNCTION-keyed survivor map no longer
/// zeroes the count for every harness (the pre-#65 fail-open). An empty map
/// still falls back to the crate total (conservative).
pub(crate) fn resolve_per_harness_count_fail_closed(
    crate_total: usize,
    per_harness: &BTreeMap<String, usize>,
    harness_name: &str,
    harness_names: &BTreeSet<String>,
) -> usize {
    if per_harness.is_empty() {
        return crate_total;
    }
    per_harness
        .iter()
        .filter(|(key, _)| attributable_to_harness(key, harness_name, harness_names))
        .map(|(_, count)| *count)
        .sum()
}

/// Resolve all demoting per-harness counts for a harness (#3080, #3099, #3128, #3192, #3715).
///
/// Returns the resolved `(category_name, count)` pairs for the DEMOTED_CATEGORIES.
/// Category names are derived from `UnsoundnessCategory::json_key()` — no raw strings.
/// Shared by `demote_for_all_unsoundness` (PROOF demotion) and `classify_ctrex`
/// (CTREX classification).
///
/// Task #65: resolution is fail-closed under the mixed key-space contract —
/// per-harness entries whose keys name no known proof harness (fn-keyed
/// survivors) count against every harness instead of silently resolving to 0.
pub(crate) fn resolve_demoting_categories(
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) -> [(&'static str, usize); 17] {
    use trust_mc_metadata::UnsoundnessCategory as UC;
    let resolve = |crate_total: usize, per_harness: &BTreeMap<String, usize>| {
        resolve_per_harness_count_fail_closed(
            crate_total,
            per_harness,
            &harness.pretty_name,
            &counts.harness_names,
        )
    };
    [
        (
            UC::ConstantZeroFallback.json_key(),
            resolve(counts.constant_zero_fallback, &counts.constant_zero_per_harness),
        ),
        (
            UC::InternalWorkaround.json_key(),
            resolve(counts.internal_workaround, &counts.internal_workaround_per_harness),
        ),
        (
            UC::ChcFallback.json_key(),
            resolve(counts.chc_fallback, &counts.chc_fallback_per_harness),
        ),
        (
            UC::TypeSortFallback.json_key(),
            resolve(counts.type_sort_fallback, &counts.type_sort_fallback_per_harness),
        ),
        (
            UC::SignednessFallback.json_key(),
            resolve(counts.signedness_fallback, &counts.signedness_fallback_per_harness),
        ),
        (
            UC::UnsupportedConstructFallback.json_key(),
            resolve(
                counts.unsupported_construct_fallback,
                &counts.unsupported_construct_per_harness,
            ),
        ),
        (
            UC::UnconstrainedAssignment.json_key(),
            resolve(counts.unconstrained_assignment, &counts.unconstrained_assignment_per_harness),
        ),
        (
            UC::BmcStoreCoercionFallback.json_key(),
            resolve(counts.bmc_store_coercion_fallback, &counts.bmc_store_coercion_per_harness),
        ),
        (
            UC::StoreDroppedTransition.json_key(),
            resolve(counts.store_dropped_transition, &counts.store_dropped_transition_per_harness),
        ),
        (
            UC::DivergingCallDrop.json_key(),
            resolve(counts.diverging_call_drop, &counts.diverging_call_drop_per_harness),
        ),
        (
            UC::OffsetProvenanceUnresolved.json_key(),
            resolve(
                counts.offset_provenance_unresolved,
                &counts.offset_provenance_unresolved_per_harness,
            ),
        ),
        (
            UC::KaniMemOverapprox.json_key(),
            resolve(counts.kani_mem_overapprox, &counts.kani_mem_overapprox_per_harness),
        ),
        (
            UC::InferablePredicate.json_key(),
            resolve(counts.inferable_predicate, &counts.inferable_predicate_per_harness),
        ),
        (
            UC::FpBitvectorEncoding.json_key(),
            resolve(counts.fp_bitvector_encoding, &counts.fp_bitvector_encoding_per_harness),
        ),
        (
            UC::RoundingAssertionBypass.json_key(),
            resolve(
                counts.rounding_assertion_bypass,
                &counts.rounding_assertion_bypass_per_harness,
            ),
        ),
        (
            UC::VecFieldFallback.json_key(),
            resolve(counts.vec_field_fallback, &counts.vec_field_fallback_per_harness),
        ),
        (
            UC::PointeeSynthesisFallback.json_key(),
            resolve(
                counts.pointee_synthesis_fallback,
                &counts.pointee_synthesis_fallback_per_harness,
            ),
        ),
    ]
}

/// Aggregate the sound-approximation categories attributable to a harness,
/// fail-closed under the mixed key-space contract (task #65).
///
/// Mirrors `classify_ctrex`'s residual attribution on the Success path: an
/// entry keyed by the current harness counts, an entry keyed by a DIFFERENT
/// known proof harness does not (it is evaluated when that harness runs), and
/// an unattributable (fn-keyed survivor) entry counts against every harness.
pub(crate) fn sound_approx_categories_fail_closed(
    counts: &CrateUnsoundnessCounts,
    harness_name: &str,
) -> BTreeMap<String, usize> {
    let mut totals: BTreeMap<String, usize> = BTreeMap::new();
    for (key, categories) in &counts.sound_approx_per_harness {
        if !attributable_to_harness(key, harness_name, &counts.harness_names) {
            continue;
        }
        for (category, count) in categories {
            *totals.entry(category.clone()).or_default() += count;
        }
    }
    totals
}

/// Step B (recognize-clean) + Step C (fail-close) — the SoundHavoc split
/// (task #65: extracted from `check_harness` so the decision is unit-testable
/// and fail-closed against fn-keyed survivor maps).
///
/// Step B: the sound-fallback count that QUALIFIES a proof excludes
/// recognized-clean SoundHavoc drops (`chc_sound_havoc_drop`), which are
/// certified fresh unconstrained havocs (universally quantified). A proof
/// whose only fallbacks are SoundHavoc therefore reports a clean success.
///
/// Step C: any REMAINING (fail-close / suspect) sound-approximation on a
/// Success harness cannot stand as a proof — the over-approximation is
/// caller-dependent, carries stale input, or drops a havoc/obligation.
/// Convert it to an OverApproximation counterexample so the harness can
/// never be a clean PROOF (and thus never a latent missed bug). Routing
/// through `ctrex_category` (NOT `demotion_reasons`) is deliberate: a
/// demoted result skips `classify_ctrex`, and on an oracle==Success test
/// the runner would then read it as FalsePositive. An OverApproximation
/// CTREX is read as inconclusive → Unknown for either oracle polarity.
pub(crate) fn apply_sound_fallback_fail_close(
    result: &mut VerificationResult,
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) {
    let havoc_key = trust_mc_metadata::UnsoundnessCategory::ChcSoundHavocDrop.json_key();
    let approx = sound_approx_categories_fail_closed(counts, &harness.pretty_name);
    result.sound_fallback_count =
        approx.iter().filter(|(cat, _)| cat.as_str() != havoc_key).map(|(_, count)| count).sum();
    if result.status == VerificationStatus::Success && result.sound_fallback_count > 0 {
        let categories: Vec<String> = approx
            .iter()
            .filter(|(cat, _)| cat.as_str() != havoc_key)
            .map(|(cat, count)| format!("{cat}={count}"))
            .collect();
        result.status = VerificationStatus::Failure;
        result.failed_properties = FailedProperties::Other;
        result.ctrex_category = Some(CtrexCategory::OverApproximation { categories });
    }
}

/// Apply all unsoundness demotion checks to a verification result (#2659, #3099).
///
/// Resolves all per-harness counts for the demoting categories upfront and
/// reports every triggered category in a single warning.
///
/// Excluded from demotion (#3099):
/// - SOUND_APPROXIMATION: constraint drops / fresh symbolics that make
///   the encoding strictly stronger (universally quantified).
/// - FAIL_CLOSED (5): inject `false` constraints or error rules that force
///   the solver to report failure (cannot produce false proofs).
pub(crate) fn demote_for_all_unsoundness(
    result: &mut VerificationResult,
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) {
    if result.status != VerificationStatus::Success {
        return;
    }

    let categories = resolve_demoting_categories(harness, counts);

    let triggers: Vec<(&str, usize)> =
        categories.into_iter().filter(|(_, count)| *count > 0).collect();

    if triggers.is_empty() {
        return;
    }

    let trigger_entries: Vec<String> =
        triggers.iter().map(|(cat, count)| format!("{cat}={count}")).collect();

    warning(&format_args!(
        "UNSOUND: demoting PROOF to FAILURE for harness `{}` (crate `{}`): [{}]",
        harness.pretty_name,
        harness.crate_name,
        trigger_entries.join(", "),
    ));

    result.status = VerificationStatus::Failure;
    result.failed_properties = FailedProperties::Other;
    result.demotion_reasons = trigger_entries;
}

/// Check if a harness result represents an effective manual success.
///
/// A should_panic harness with PanicsOnly failures is effectively a success:
/// the test expected a panic/assertion failure, and one was found.
pub(crate) fn is_effective_manual_success(
    status: VerificationStatus,
    should_panic: bool,
    failed_properties: FailedProperties,
) -> bool {
    // For a `#[kani::should_panic]` harness the verdict depends SOLELY on the
    // failures found: `PanicsOnly` => success (the expected panic occurred),
    // `None`/`Other` => failure. A should_panic body that never panics is a
    // FAILURE, matching Kani's `verification_outcome_from_properties`
    // (kani-driver/src/call_cbmc.rs). Previously this OR-ed in the raw solver
    // `status == Success`, so a should_panic harness that produced no panic
    // (Success/None) was reported SUCCESSFUL — an unsound false-positive verdict.
    if should_panic {
        matches!(failed_properties, FailedProperties::PanicsOnly)
    } else {
        status == VerificationStatus::Success
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::project::Project;
    use crate::test_support::{test_harness, test_metadata_all, test_result};
    use crate::unsoundness_counts::UnsoundnessCounts;
    use crate::util::{warning_test_capture_start, warning_test_messages_take};

    fn take_warning_messages() -> Vec<String> {
        warning_test_messages_take()
    }

    // ─── is_effective_manual_success tests ───

    #[test]
    fn test_is_effective_manual_success_true_for_successful_status() {
        assert!(is_effective_manual_success(
            VerificationStatus::Success,
            false,
            FailedProperties::Other
        ));
        // should_panic + no panic found (None) is NOT a success — it is a
        // failure ("expected a panic, none occurred"). This previously
        // (incorrectly) returned true via the raw `status == Success` disjunct.
        assert!(!is_effective_manual_success(
            VerificationStatus::Success,
            true,
            FailedProperties::None
        ));
    }

    #[test]
    fn test_is_effective_manual_success_true_for_should_panic_panics_only() {
        assert!(is_effective_manual_success(
            VerificationStatus::Failure,
            true,
            FailedProperties::PanicsOnly
        ));
    }

    #[test]
    fn test_is_effective_manual_success_false_for_should_panic_non_panics_failure() {
        assert!(!is_effective_manual_success(
            VerificationStatus::Failure,
            true,
            FailedProperties::Other
        ));
        assert!(!is_effective_manual_success(
            VerificationStatus::Failure,
            true,
            FailedProperties::None
        ));
    }

    #[test]
    fn test_is_effective_manual_success_false_for_non_should_panic_panics_only() {
        assert!(!is_effective_manual_success(
            VerificationStatus::Failure,
            false,
            FailedProperties::PanicsOnly
        ));
    }

    #[test]
    fn test_resolve_per_harness_count_unique_suffix_match() {
        let per_harness = BTreeMap::from([("crate::module::harness".to_string(), 5)]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "harness"), 5);
    }

    #[test]
    fn test_resolve_per_harness_count_unique_reverse_suffix_match() {
        let per_harness = BTreeMap::from([("harness".to_string(), 7)]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "crate::module::harness"), 7);
    }

    #[test]
    fn test_resolve_per_harness_count_exact_match_beats_suffix_fallback() {
        let per_harness =
            BTreeMap::from([("harness".to_string(), 7), ("crate::module::harness".to_string(), 5)]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "harness"), 7);
    }

    #[test]
    fn test_resolve_per_harness_count_prefers_most_specific_suffix_match() {
        let per_harness =
            BTreeMap::from([("harness".to_string(), 7), ("module::harness".to_string(), 5)]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "crate::module::harness"), 5);
    }

    #[test]
    fn test_resolve_per_harness_count_prefers_most_specific_reverse_suffix_match() {
        let per_harness =
            BTreeMap::from([("harness".to_string(), 7), ("crate::module::harness".to_string(), 5)]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "module::harness"), 5);
    }

    #[test]
    fn test_resolve_per_harness_count_ambiguous_suffix_match_returns_zero() {
        let per_harness = BTreeMap::from([
            ("crate::a::harness".to_string(), 3),
            ("crate::b::harness".to_string(), 4),
        ]);
        assert_eq!(resolve_per_harness_count(99, &per_harness, "harness"), 0);
    }

    // ─── Demotion tests ───

    #[test]
    fn test_demote_single_category_demotes_and_records_reason() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let counts = CrateUnsoundnessCounts { constant_zero_fallback: 1, ..Default::default() };
        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(result.status, VerificationStatus::Failure);
        assert!(matches!(result.failed_properties, FailedProperties::Other));
        assert_eq!(result.demotion_reasons, vec!["constant_zero_fallback=1"]);
    }

    #[test]
    fn test_demote_emits_warning_with_all_categories() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        let _warning_capture = warning_test_capture_start();

        let counts = CrateUnsoundnessCounts { constant_zero_fallback: 3, ..Default::default() };
        demote_for_all_unsoundness(&mut result, &harness, &counts);

        let warnings = take_warning_messages();
        assert_eq!(warnings.len(), 1);
        let warning = &warnings[0];
        assert!(warning.contains("UNSOUND: demoting PROOF to FAILURE"));
        assert!(warning.contains("crate::harness"));
        assert!(warning.contains("constant_zero_fallback=3"));
    }

    #[test]
    fn test_demote_no_demotion_when_all_counts_zero() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let counts = CrateUnsoundnessCounts::default();
        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(result.status, VerificationStatus::Success);
        assert!(matches!(result.failed_properties, FailedProperties::None));
        assert!(result.demotion_reasons.is_empty());
    }

    #[test]
    fn test_demote_no_change_for_existing_failure() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);

        let counts = CrateUnsoundnessCounts { constant_zero_fallback: 3, ..Default::default() };
        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(result.status, VerificationStatus::Failure);
        assert!(matches!(result.failed_properties, FailedProperties::PanicsOnly));
        assert!(result.demotion_reasons.is_empty());
    }

    #[test]
    fn test_unhandled_calls_does_not_demote() {
        // Part of #3099: unhandled_calls is now a sound over-approximation.
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let mut project = Project::default();
        project.metadata =
            vec![test_metadata_all("crate", None, None, None, None, None, None, Some(3), None)];
        let crate_counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate");
        demote_for_all_unsoundness(&mut result, &harness, &crate_counts);

        assert_eq!(
            result.status,
            VerificationStatus::Success,
            "unhandled_calls is sound over-approximation — must NOT demote (#3099)"
        );
        assert!(matches!(result.failed_properties, FailedProperties::None));
    }

    #[test]
    fn test_demote_multi_category_reports_all_triggers() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let counts = CrateUnsoundnessCounts {
            constant_zero_fallback: 2,
            internal_workaround: 3,
            chc_fallback: 5,
            type_sort_fallback: 9,
            signedness_fallback: 4,
            unsupported_construct_fallback: 7,
            ..Default::default()
        };

        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(result.status, VerificationStatus::Failure);
        assert!(matches!(result.failed_properties, FailedProperties::Other));
        assert_eq!(result.demotion_reasons.len(), 6);
        assert!(result.demotion_reasons.contains(&"constant_zero_fallback=2".to_string()));
        assert!(result.demotion_reasons.contains(&"internal_workaround=3".to_string()));
        assert!(result.demotion_reasons.contains(&"chc_fallback=5".to_string()));
        assert!(result.demotion_reasons.contains(&"type_sort_fallback=9".to_string()));
        assert!(result.demotion_reasons.contains(&"signedness_fallback=4".to_string()));
        assert!(result.demotion_reasons.contains(&"unsupported_construct_fallback=7".to_string()));
    }

    #[test]
    fn test_demote_multi_category_emits_all_in_single_warning() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        let _warning_capture = warning_test_capture_start();

        let counts = CrateUnsoundnessCounts {
            constant_zero_fallback: 2,
            chc_fallback: 5,
            ..Default::default()
        };

        demote_for_all_unsoundness(&mut result, &harness, &counts);

        let warnings = take_warning_messages();
        assert_eq!(warnings.len(), 1);
        let warning = &warnings[0];
        assert!(warning.contains("UNSOUND: demoting PROOF to FAILURE"));
        assert!(warning.contains("crate::harness"));
        assert!(warning.contains("constant_zero_fallback=2"));
        assert!(warning.contains("chc_fallback=5"));
    }

    /// Per-harness demotion: when per_harness data is available and the harness
    /// has 0 fallbacks, it should NOT be demoted even if the crate total is nonzero (#2959).
    ///
    /// Task #65: the dirty entry only attributes AWAY from clean_harness because
    /// dirty_harness is a KNOWN proof harness — see
    /// `test_fn_keyed_survivor_map_fail_closes` for the unknown-key polarity.
    #[test]
    fn test_per_harness_demotion_skips_clean_harness() {
        let harness = test_harness("crate::clean_harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let mut per_harness = BTreeMap::new();
        per_harness.insert("crate::dirty_harness".to_string(), 3);

        let counts = CrateUnsoundnessCounts {
            chc_fallback: 3,
            chc_fallback_per_harness: per_harness,
            harness_names: ["crate::clean_harness".to_string(), "crate::dirty_harness".to_string()]
                .into(),
            ..Default::default()
        };

        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(
            result.status,
            VerificationStatus::Success,
            "Harness with 0 per-harness fallbacks should NOT be demoted (#2959)"
        );
    }

    /// Per-harness demotion: when per_harness data is available and the harness
    /// HAS fallbacks, it should still be demoted (#2959).
    #[test]
    fn test_per_harness_demotion_demotes_dirty_harness() {
        let harness = test_harness("crate::dirty_harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let mut per_harness = BTreeMap::new();
        per_harness.insert("crate::dirty_harness".to_string(), 3);

        let counts = CrateUnsoundnessCounts {
            chc_fallback: 3,
            chc_fallback_per_harness: per_harness,
            ..Default::default()
        };

        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(
            result.status,
            VerificationStatus::Failure,
            "Harness with nonzero per-harness fallbacks should still be demoted"
        );
    }

    /// Per-harness demotion: when per_harness data is empty (no per-harness
    /// tracking), falls back to crate-level total (conservative safety) (#2959).
    #[test]
    fn test_per_harness_demotion_falls_back_to_crate_total() {
        let harness = test_harness("crate::harness", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);

        let counts = CrateUnsoundnessCounts {
            chc_fallback: 3,
            chc_fallback_per_harness: BTreeMap::new(),
            ..Default::default()
        };

        demote_for_all_unsoundness(&mut result, &harness, &counts);

        assert_eq!(
            result.status,
            VerificationStatus::Failure,
            "Without per-harness data, should fall back to crate total (conservative)"
        );
    }

    /// Task #65 key-space-trap regression (fail-open closed): a per-harness
    /// map whose only entries are FUNCTION-keyed (no known harness name) must
    /// no longer zero the resolved count — the survivor entries fail close
    /// against every harness of the crate.
    #[test]
    fn test_fn_keyed_survivor_map_fail_closes() {
        use std::collections::BTreeSet;

        let per_harness = BTreeMap::from([("crate::helper_fn".to_string(), 2)]);
        let names: BTreeSet<String> =
            ["crate::harness_a".to_string(), "crate::harness_b".to_string()].into();

        // Pre-#65 lookup semantics zeroed the count (documented fail-open)...
        assert_eq!(resolve_per_harness_count(9, &per_harness, "crate::harness_a"), 0);
        // ...the fail-closed resolution counts the unattributable survivor.
        assert_eq!(
            resolve_per_harness_count_fail_closed(9, &per_harness, "crate::harness_a", &names),
            2
        );
        // An entry naming a DIFFERENT known harness still attributes away.
        let other = BTreeMap::from([("crate::harness_b".to_string(), 4)]);
        assert_eq!(resolve_per_harness_count_fail_closed(9, &other, "crate::harness_a", &names), 0);

        // End-to-end: a fn-keyed survivor in a DEMOTED category demotes PROOF.
        let counts = CrateUnsoundnessCounts {
            rounding_assertion_bypass: 2,
            rounding_assertion_bypass_per_harness: per_harness,
            harness_names: names,
            ..Default::default()
        };
        let harness = test_harness("crate::harness_a", "crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        demote_for_all_unsoundness(&mut result, &harness, &counts);
        assert_eq!(result.status, VerificationStatus::Failure);
        assert_eq!(result.demotion_reasons, vec!["rounding_assertion_bypass=2"]);
    }

    /// Task #65 Step-C: sound-approximation entries (harness-keyed AND fn-keyed
    /// survivors) convert a Success into an OverApproximation counterexample;
    /// recognized-clean SoundHavoc drops are excluded (Step B).
    #[test]
    fn test_apply_sound_fallback_fail_close_step_c() {
        let harness = test_harness("crate::harness_a", "crate");
        let harness_names: std::collections::BTreeSet<String> =
            ["crate::harness_a".to_string(), "crate::harness_b".to_string()].into();

        // (1) Harness-keyed entry → Step-C fires.
        let counts = CrateUnsoundnessCounts {
            sound_approx_per_harness: BTreeMap::from([(
                "crate::harness_a".to_string(),
                vec![("stub_approximation".to_string(), 2)],
            )]),
            harness_names: harness_names.clone(),
            ..Default::default()
        };
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        apply_sound_fallback_fail_close(&mut result, &harness, &counts);
        assert_eq!(result.status, VerificationStatus::Failure);
        assert_eq!(result.sound_fallback_count, 2);
        assert_eq!(
            result.ctrex_category,
            Some(CtrexCategory::OverApproximation {
                categories: vec!["stub_approximation=2".to_string()]
            })
        );

        // (2) Key-space trap: a fn-keyed survivor entry must also fire Step-C
        // (previously the harness-name lookup returned None → silent skip).
        let counts = CrateUnsoundnessCounts {
            sound_approx_per_harness: BTreeMap::from([(
                "crate::helper_fn".to_string(),
                vec![("ptr_metadata_unconstrained".to_string(), 1)],
            )]),
            harness_names: harness_names.clone(),
            ..Default::default()
        };
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        apply_sound_fallback_fail_close(&mut result, &harness, &counts);
        assert_eq!(result.status, VerificationStatus::Failure);
        assert_eq!(
            result.ctrex_category,
            Some(CtrexCategory::OverApproximation {
                categories: vec!["ptr_metadata_unconstrained=1".to_string()]
            })
        );

        // (3) An entry attributed to ANOTHER known harness does not taint this one.
        let counts = CrateUnsoundnessCounts {
            sound_approx_per_harness: BTreeMap::from([(
                "crate::harness_b".to_string(),
                vec![("stub_approximation".to_string(), 5)],
            )]),
            harness_names: harness_names.clone(),
            ..Default::default()
        };
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        apply_sound_fallback_fail_close(&mut result, &harness, &counts);
        assert_eq!(result.status, VerificationStatus::Success);
        assert_eq!(result.sound_fallback_count, 0);

        // (4) Step B: recognized-clean SoundHavoc drops alone stay a clean pass.
        let havoc_key =
            trust_mc_metadata::UnsoundnessCategory::ChcSoundHavocDrop.json_key().to_string();
        let counts = CrateUnsoundnessCounts {
            sound_approx_per_harness: BTreeMap::from([(
                "crate::harness_a".to_string(),
                vec![(havoc_key, 3)],
            )]),
            harness_names,
            ..Default::default()
        };
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        apply_sound_fallback_fail_close(&mut result, &harness, &counts);
        assert_eq!(result.status, VerificationStatus::Success);
        assert_eq!(result.sound_fallback_count, 0);
    }

    #[test]
    fn test_replacement_quality_hard_gate_uses_per_harness_counts() {
        let counts = CrateUnsoundnessCounts {
            kani_mem_overapprox: 5,
            kani_mem_overapprox_per_harness: BTreeMap::from([(
                "crate::dirty_harness".to_string(),
                3,
            )]),
            // Task #65: dirty_harness must be a KNOWN harness so its entry
            // attributes to it alone instead of fail-closing against everyone.
            harness_names: ["crate::clean_harness".to_string(), "crate::dirty_harness".to_string()]
                .into(),
            ..Default::default()
        };

        let dirty_harness = test_harness("crate::dirty_harness", "crate");
        let mut dirty_result = test_result(VerificationStatus::Success, FailedProperties::None);
        demote_for_all_unsoundness(&mut dirty_result, &dirty_harness, &counts);

        assert_eq!(dirty_result.status, VerificationStatus::Failure);
        assert_eq!(dirty_result.demotion_reasons, vec!["kani_mem_overapprox=3"]);

        let clean_harness = test_harness("crate::clean_harness", "crate");
        let mut clean_result = test_result(VerificationStatus::Success, FailedProperties::None);
        demote_for_all_unsoundness(&mut clean_result, &clean_harness, &counts);

        assert_eq!(clean_result.status, VerificationStatus::Success);
        assert!(clean_result.demotion_reasons.is_empty());
    }
}

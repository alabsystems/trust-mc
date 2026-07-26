// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! UNKNOWN-quality classification for inconclusive solver results.
//!
//! Distinguishes clean solver UNKNOWN from UNKNOWN results that already carry
//! known encoding gaps or sound over-approximation signals.

use std::collections::BTreeMap;

use trust_mc_metadata::HarnessMetadata;

use crate::demotion::{lookup_per_harness, resolve_demoting_categories, resolve_per_harness_count};
use crate::unsoundness_counts::CrateUnsoundnessCounts;
use crate::verification_result::UnknownQuality;

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

fn collect_encoding_gap_reasons(
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) -> Vec<String> {
    let mut reasons: Vec<String> = resolve_demoting_categories(harness, counts)
        .into_iter()
        .filter(|(_, count)| *count > 0)
        .map(|(category, count)| format!("{category}={count}"))
        .collect();

    if counts.assert_untranslatable > 0 {
        reasons.push(format!("assert_untranslatable={}", counts.assert_untranslatable));
    }
    if counts.heap_check_untranslatable > 0 {
        reasons.push(format!("heap_check_untranslatable={}", counts.heap_check_untranslatable));
    }
    if counts.heap_check_unknown_layout > 0 {
        reasons.push(format!("heap_check_unknown_layout={}", counts.heap_check_unknown_layout));
    }
    push_fail_closed_trigger(
        &mut reasons,
        "iterator_unsoundness",
        counts.iterator_unsoundness,
        &counts.iterator_unsoundness_per_harness,
        harness,
    );
    push_fail_closed_trigger(
        &mut reasons,
        "bigint_unsoundness",
        counts.bigint_unsoundness,
        &counts.bigint_unsoundness_per_harness,
        harness,
    );

    reasons
}

fn collect_overapprox_reasons(
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) -> Vec<String> {
    lookup_per_harness(&counts.sound_approx_per_harness, &harness.pretty_name)
        .map(|categories| {
            categories.iter().map(|(category, count)| format!("{category}={count}")).collect()
        })
        .unwrap_or_default()
}

/// Classify an UNKNOWN verdict as clean or already-known dirty.
pub(crate) fn classify_unknown_quality(
    harness: &HarnessMetadata,
    counts: &CrateUnsoundnessCounts,
) -> UnknownQuality {
    let encoding_gap_reasons = collect_encoding_gap_reasons(harness, counts);
    let overapprox_reasons = collect_overapprox_reasons(harness, counts);

    match (encoding_gap_reasons.is_empty(), overapprox_reasons.is_empty()) {
        (true, true) => UnknownQuality::Clean,
        (false, true) => UnknownQuality::EncodingGap { reasons: encoding_gap_reasons },
        (true, false) => UnknownQuality::OverApproximation { reasons: overapprox_reasons },
        (false, false) => {
            let mut reasons = encoding_gap_reasons;
            reasons.extend(overapprox_reasons);
            UnknownQuality::Mixed { reasons }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::test_harness;

    #[test]
    fn test_classify_unknown_quality_clean_when_no_unsoundness_detected() {
        let harness = test_harness("crate::harness", "crate");
        let counts = CrateUnsoundnessCounts::default();

        assert_eq!(classify_unknown_quality(&harness, &counts), UnknownQuality::Clean);
    }

    #[test]
    fn test_classify_unknown_quality_encoding_gap_from_demoted_category() {
        let harness = test_harness("crate::harness", "crate");
        let counts = CrateUnsoundnessCounts { chc_fallback: 2, ..Default::default() };

        assert_eq!(
            classify_unknown_quality(&harness, &counts),
            UnknownQuality::EncodingGap { reasons: vec!["chc_fallback=2".to_string()] }
        );
    }

    #[test]
    fn test_classify_unknown_quality_over_approximation_from_sound_approximation() {
        let harness = test_harness("crate::harness", "crate");
        let counts = CrateUnsoundnessCounts {
            sound_approx_per_harness: BTreeMap::from([(
                "crate::harness".to_string(),
                vec![("chc_translation_drop".to_string(), 4)],
            )]),
            ..Default::default()
        };

        assert_eq!(
            classify_unknown_quality(&harness, &counts),
            UnknownQuality::OverApproximation {
                reasons: vec!["chc_translation_drop=4".to_string()]
            }
        );
    }

    #[test]
    fn test_classify_unknown_quality_mixed_when_both_reason_families_exist() {
        let harness = test_harness("crate::harness", "crate");
        let counts = CrateUnsoundnessCounts {
            heap_check_unknown_layout: 1,
            sound_approx_per_harness: BTreeMap::from([(
                "crate::harness".to_string(),
                vec![("chc_translation_drop".to_string(), 3)],
            )]),
            ..Default::default()
        };

        assert_eq!(
            classify_unknown_quality(&harness, &counts),
            UnknownQuality::Mixed {
                reasons: vec![
                    "heap_check_unknown_layout=1".to_string(),
                    "chc_translation_drop=3".to_string(),
                ]
            }
        );
    }

    #[test]
    fn test_classify_unknown_quality_store_dropped_transition_is_encoding_gap() {
        let harness = test_harness("crate::harness", "crate");
        let counts = CrateUnsoundnessCounts {
            store_dropped_transition: 5,
            store_dropped_transition_per_harness: BTreeMap::from([(
                "crate::harness".to_string(),
                3,
            )]),
            ..Default::default()
        };

        assert_eq!(
            classify_unknown_quality(&harness, &counts),
            UnknownQuality::EncodingGap { reasons: vec!["store_dropped_transition=3".to_string()] }
        );
    }
}

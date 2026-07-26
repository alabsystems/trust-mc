// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Tests for [`crate::ctrex_classify`]. Split for module size compliance.

use std::collections::BTreeMap;

use crate::ctrex_classify::classify_ctrex;
use crate::demotion::demote_for_all_unsoundness;
use crate::test_support::{test_harness, test_result};
use crate::unsoundness_counts::CrateUnsoundnessCounts;
use crate::verification_result::{CtrexCategory, FailedProperties, VerificationStatus};

#[test]
fn test_classify_ctrex_genuine_when_all_counts_zero() {
    let harness = test_harness("crate::harness", "crate");
    let counts = CrateUnsoundnessCounts::default();
    let category = classify_ctrex(&harness, &counts);
    assert_eq!(category, CtrexCategory::Genuine);
}

#[test]
fn test_classify_ctrex_encoding_gap_single_category() {
    let harness = test_harness("crate::harness", "crate");
    let counts = CrateUnsoundnessCounts { chc_fallback: 3, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories, vec!["chc_fallback=3"]);
        }
        other => panic!("expected EncodingGap, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_encoding_gap_multiple_categories() {
    let harness = test_harness("crate::harness", "crate");
    let counts =
        CrateUnsoundnessCounts { chc_fallback: 2, signedness_fallback: 1, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories.len(), 2);
            assert!(categories.contains(&"chc_fallback=2".to_string()));
            assert!(categories.contains(&"signedness_fallback=1".to_string()));
        }
        other => panic!("expected EncodingGap, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_uses_per_harness_counts() {
    let harness = test_harness("my_harness", "crate");
    let mut per_harness = BTreeMap::new();
    per_harness.insert("my_harness".to_string(), 5);
    per_harness.insert("other_harness".to_string(), 10);
    let counts = CrateUnsoundnessCounts {
        chc_fallback: 15, // crate-level
        chc_fallback_per_harness: per_harness,
        // Task #65: keys attribute to specific harnesses only when they name a
        // known proof harness — unknown keys fail closed against every harness.
        harness_names: ["my_harness".to_string(), "other_harness".to_string()].into(),
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            // Should use per-harness count (5), not crate-level (15)
            assert_eq!(categories, vec!["chc_fallback=5"]);
        }
        other => panic!("expected EncodingGap, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_genuine_when_per_harness_zero() {
    let harness = test_harness("clean_harness", "crate");
    let mut per_harness = BTreeMap::new();
    per_harness.insert("other_harness".to_string(), 10);
    let counts = CrateUnsoundnessCounts {
        chc_fallback: 10, // crate-level
        chc_fallback_per_harness: per_harness,
        // Task #65: "other_harness" must be a KNOWN harness for its entry to be
        // excluded from clean_harness; an unknown key would fail closed.
        harness_names: ["clean_harness".to_string(), "other_harness".to_string()].into(),
        ..Default::default()
    };
    // Per-harness data available but clean_harness has 0 count → Genuine
    let category = classify_ctrex(&harness, &counts);
    assert_eq!(category, CtrexCategory::Genuine);
}

#[test]
fn test_classify_ctrex_over_approximation_with_sound_approx() {
    let harness = test_harness("my_harness", "crate");
    let mut sound_approx = BTreeMap::new();
    sound_approx.insert(
        "my_harness".to_string(),
        vec![
            ("chc_translation_drop".to_string(), 3),
            ("ptr_metadata_unconstrained".to_string(), 2),
        ],
    );
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories.len(), 2);
            assert!(categories.contains(&"chc_translation_drop=3".to_string()));
            assert!(categories.contains(&"ptr_metadata_unconstrained=2".to_string()));
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_over_approximation_with_unique_suffix_match() {
    let harness = test_harness("my_harness", "crate");
    let mut sound_approx = BTreeMap::new();
    sound_approx.insert(
        "crate::module::my_harness".to_string(),
        vec![("aggregate_encoding_gap".to_string(), 2)],
    );
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories, vec!["aggregate_encoding_gap=2"]);
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_falls_back_to_crate_level_when_sound_approx_suffix_match_is_ambiguous() {
    let harness = test_harness("my_harness", "crate");
    let sound_approx = BTreeMap::from([
        ("crate::a::my_harness".to_string(), vec![("aggregate_encoding_gap".to_string(), 1)]),
        ("crate::b::my_harness".to_string(), vec![("stub_approximation".to_string(), 1)]),
    ]);
    let counts = CrateUnsoundnessCounts {
        sound_approx_per_harness: sound_approx,
        sound_approx_crate_totals: vec![
            ("aggregate_encoding_gap".to_string(), 1),
            ("stub_approximation".to_string(), 1),
        ],
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories.len(), 2);
            assert!(categories.contains(&"aggregate_encoding_gap=1".to_string()));
            assert!(categories.contains(&"stub_approximation=1".to_string()));
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_encoding_gap_takes_priority_over_sound_approx() {
    let harness = test_harness("my_harness", "crate");
    let mut sound_approx = BTreeMap::new();
    sound_approx.insert("my_harness".to_string(), vec![("chc_translation_drop".to_string(), 5)]);
    let counts = CrateUnsoundnessCounts {
        chc_fallback: 2,
        sound_approx_per_harness: sound_approx,
        ..Default::default()
    };
    // EncodingGap should take priority over OverApproximation
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { .. } => {}
        other => panic!("expected EncodingGap, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_offset_only_routes_to_recertification_with_full_freeing_set() {
    let harness = test_harness("my_harness", "crate");
    let counts = CrateUnsoundnessCounts {
        offset_provenance_unresolved: 1,
        offset_provenance_unresolved_per_harness: BTreeMap::from([("my_harness".to_string(), 1)]),
        sound_approx_per_harness: BTreeMap::from([(
            "my_harness".to_string(),
            vec![("chc_translation_drop".to_string(), 2)],
        )]),
        harness_names: ["my_harness".to_string()].into(),
        ..Default::default()
    };

    match classify_ctrex(&harness, &counts) {
        CtrexCategory::OverApproximation { categories } => {
            assert!(categories.contains(&"offset_provenance_unresolved=1".to_string()));
            assert!(categories.contains(&"chc_translation_drop=2".to_string()));
            assert_eq!(categories.len(), 2, "the recertifier must receive the complete taint set");
        }
        other => {
            panic!("offset-only demotion should enter fail-closed recertification, got {other:?}")
        }
    }
}

#[test]
fn test_classify_ctrex_offset_plus_other_demoted_trigger_stays_encoding_gap() {
    let harness = test_harness("my_harness", "crate");
    let counts = CrateUnsoundnessCounts {
        offset_provenance_unresolved: 1,
        offset_provenance_unresolved_per_harness: BTreeMap::from([("my_harness".to_string(), 1)]),
        chc_fallback: 1,
        chc_fallback_per_harness: BTreeMap::from([("my_harness".to_string(), 1)]),
        harness_names: ["my_harness".to_string()].into(),
        ..Default::default()
    };

    match classify_ctrex(&harness, &counts) {
        CtrexCategory::EncodingGap { categories } => {
            assert!(categories.contains(&"offset_provenance_unresolved=1".to_string()));
            assert!(categories.contains(&"chc_fallback=1".to_string()));
        }
        other => {
            panic!("a second demoted trigger must block offset recertification, got {other:?}")
        }
    }
}

#[test]
fn test_classify_ctrex_offset_plus_fail_closed_trigger_stays_encoding_gap() {
    let harness = test_harness("my_harness", "crate");
    let counts = CrateUnsoundnessCounts {
        offset_provenance_unresolved: 1,
        offset_provenance_unresolved_per_harness: BTreeMap::from([("my_harness".to_string(), 1)]),
        heap_check_unknown_layout: 1,
        harness_names: ["my_harness".to_string()].into(),
        ..Default::default()
    };

    match classify_ctrex(&harness, &counts) {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(
                categories,
                vec!["offset_provenance_unresolved=1", "heap_check_unknown_layout=1"]
            );
        }
        other => panic!("a fail-closed trigger must block offset recertification, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_per_harness_sound_approx_takes_priority_over_crate_level_fallback() {
    let harness = test_harness("my_harness", "crate");
    let sound_approx = BTreeMap::from([(
        "my_harness".to_string(),
        vec![("ptr_metadata_unconstrained".to_string(), 2)],
    )]);
    let counts = CrateUnsoundnessCounts {
        sound_approx_per_harness: sound_approx,
        sound_approx_crate_totals: vec![
            ("aggregate_encoding_gap".to_string(), 3),
            ("ptr_metadata_unconstrained".to_string(), 2),
        ],
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories, vec!["ptr_metadata_unconstrained=2"]);
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_falls_back_to_crate_level_when_sound_approx_on_different_harness() {
    let harness = test_harness("clean_harness", "crate");
    let mut sound_approx = BTreeMap::new();
    sound_approx.insert("other_harness".to_string(), vec![("chc_translation_drop".to_string(), 5)]);
    let counts = CrateUnsoundnessCounts {
        sound_approx_per_harness: sound_approx,
        sound_approx_crate_totals: vec![("chc_translation_drop".to_string(), 5)],
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories, vec!["chc_translation_drop=5"]);
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_wired_into_check_result_failure() {
    // Simulate: solver returned Failure (CTREX), no demotion.
    let harness = test_harness("crate::harness", "crate");
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::Other);
    let counts = CrateUnsoundnessCounts { chc_fallback: 2, ..Default::default() };

    // Manually apply the same logic as check_harness:
    demote_for_all_unsoundness(&mut result, &harness, &counts);
    if result.status == VerificationStatus::Failure && result.demotion_reasons.is_empty() {
        result.ctrex_category = Some(classify_ctrex(&harness, &counts));
    }

    // Result was already Failure → demotion did not fire → CTREX classified
    assert!(result.demotion_reasons.is_empty());
    assert!(result.ctrex_category.is_some());
    match result.ctrex_category.unwrap() {
        CtrexCategory::EncodingGap { categories } => {
            assert!(categories.contains(&"chc_fallback=2".to_string()));
        }
        other => panic!("expected EncodingGap, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_unknown_when_undecided_with_no_violation() {
    // #3374: When `ay` returns `unknown` (solver incompleteness), the driver
    // encodes the undecided result conservatively as VerificationStatus::Failure
    // with FailedProperties::Other and no decided violation properties. This must
    // classify as Unknown, NOT Genuine — an undecided result has no real
    // counterexample.
    let harness = test_harness("crate::harness", "crate");
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::Other);
    // No properties at all (empty model on `unknown`) → no non-CHC violation.
    let counts = CrateUnsoundnessCounts::default();

    // Mirror the classification logic in harness_runner::check_harness.
    demote_for_all_unsoundness(&mut result, &harness, &counts);
    if result.status == VerificationStatus::Failure && result.demotion_reasons.is_empty() {
        let has_non_chc_violation = result.results.iter().any(|p| {
            p.status == crate::property_model::CheckStatus::Failure && p.property_id.class != "chc"
        });
        if matches!(result.failed_properties, FailedProperties::Other) && !has_non_chc_violation {
            result.ctrex_category = Some(CtrexCategory::Unknown);
        } else {
            result.ctrex_category = Some(classify_ctrex(&harness, &counts));
        }
    }

    // No demotion (clean crate), undecided Other with no violation → Unknown.
    assert!(result.demotion_reasons.is_empty());
    assert_eq!(
        result.ctrex_category,
        Some(CtrexCategory::Unknown),
        "undecided (unknown) result must classify as Unknown, never Genuine"
    );
}

/// Verify that the CheckedBinaryOp overflow bypass (inline translator
/// Field(1) → false) classifies as OverApproximation via chc_translation_drop.
///
/// When the inline translator (inline_shared.rs) encounters a CheckedBinaryOp
/// result and returns false for the overflow flag, it increments
/// place_translation_drop which feeds into chc_translation_drop. This test
/// verifies the isolated scenario: only chc_translation_drop present, no
/// encoding gap categories. Part of #3341.
#[test]
fn test_classify_ctrex_checked_binary_op_overflow_bypass_is_over_approximation() {
    let harness = test_harness("checked_add_harness", "crate");
    let mut sound_approx = BTreeMap::new();
    sound_approx
        .insert("checked_add_harness".to_string(), vec![("chc_translation_drop".to_string(), 1)]);
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories.len(), 1);
            assert_eq!(categories[0], "chc_translation_drop=1");
        }
        other => panic!(
            "CheckedBinaryOp overflow bypass should classify as OverApproximation, got {other:?}"
        ),
    }
}

#[test]
fn test_classify_ctrex_fail_closed_heap_unknown_layout() {
    // Part of #3447: heap_check_unknown_layout fires for types without known
    // layout (#2501). This fail-closed counter forces CTREX — classify as
    // EncodingGap, not Genuine.
    let harness = test_harness("crate::harness", "crate");
    let counts = CrateUnsoundnessCounts { heap_check_unknown_layout: 2, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories.len(), 1);
            assert_eq!(categories[0], "heap_check_unknown_layout=2");
        }
        other => panic!("Expected EncodingGap for heap_check_unknown_layout, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_fail_closed_assert_untranslatable() {
    let harness = test_harness("crate::harness", "crate");
    let counts = CrateUnsoundnessCounts { assert_untranslatable: 1, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories[0], "assert_untranslatable=1");
        }
        other => panic!("Expected EncodingGap for assert_untranslatable, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_fail_closed_iterator_prefers_per_harness_count() {
    let harness = test_harness("crate::iter_harness", "crate");
    let counts = CrateUnsoundnessCounts {
        iterator_unsoundness: 7,
        iterator_unsoundness_per_harness: BTreeMap::from([
            ("crate::iter_harness".to_string(), 2),
            ("crate::other".to_string(), 5),
        ]),
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories, vec!["iterator_unsoundness=2"]);
        }
        other => panic!("Expected EncodingGap for iterator_unsoundness, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_fail_closed_bigint() {
    let harness = test_harness("crate::bigint_harness", "crate");
    let counts = CrateUnsoundnessCounts { bigint_unsoundness: 3, ..Default::default() };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories, vec!["bigint_unsoundness=3"]);
        }
        other => panic!("Expected EncodingGap for bigint_unsoundness, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_demoted_takes_priority_over_fail_closed() {
    // DEMOTED categories should be reported before fail-closed.
    let harness = test_harness("crate::harness", "crate");
    let counts = CrateUnsoundnessCounts {
        chc_fallback: 1,
        heap_check_unknown_layout: 3,
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert!(categories.iter().any(|c| c.starts_with("chc_fallback=")));
        }
        other => panic!("Expected EncodingGap from DEMOTED priority, got {other:?}"),
    }
}

#[test]
fn test_classify_ctrex_not_applied_to_demoted_results() {
    // Simulate: solver returned Success (PROOF), then demoted to Failure.
    let harness = test_harness("crate::harness", "crate");
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    let counts = CrateUnsoundnessCounts { chc_fallback: 2, ..Default::default() };

    demote_for_all_unsoundness(&mut result, &harness, &counts);
    if result.status == VerificationStatus::Failure && result.demotion_reasons.is_empty() {
        result.ctrex_category = Some(classify_ctrex(&harness, &counts));
    }

    // Result was demoted → demotion_reasons non-empty → no CTREX classification
    assert!(!result.demotion_reasons.is_empty());
    assert!(result.ctrex_category.is_none());
}

/// Part of #3779: rounding_assertion_bypass hard-gates replacement-quality
/// PROOFs and classifies CTREX as an encoding gap.
#[test]
fn test_classify_ctrex_rounding_assertion_bypass_is_encoding_gap() {
    let harness = test_harness("ceilf32::test_diff_one", "crate");
    let counts = CrateUnsoundnessCounts {
        rounding_assertion_bypass: 3,
        rounding_assertion_bypass_per_harness: BTreeMap::from([(
            "ceilf32::test_diff_one".to_string(),
            2,
        )]),
        ..Default::default()
    };
    let category = classify_ctrex(&harness, &counts);
    match category {
        CtrexCategory::EncodingGap { categories } => {
            assert_eq!(categories.len(), 1);
            assert_eq!(categories[0], "rounding_assertion_bypass=2");
        }
        other => panic!("rounding_assertion_bypass should classify as EncodingGap, got {other:?}"),
    }
}

/// Contract REPLACE lane attribution (A3 gate): sound-approximation counts
/// fully attributed to a DIFFERENT proof harness of the same crate must not
/// demote this harness's counterexample to OverApproximation — the sibling
/// modifies check-harness's honest drops would otherwise mask the replace
/// harness's genuine counterexample.
#[test]
fn test_classify_ctrex_genuine_when_sound_approx_attributed_to_sibling_harness() {
    let harness = test_harness("main", "crate");
    let sound_approx = BTreeMap::from([(
        "check_modify".to_string(),
        vec![("chc_translation_drop".to_string(), 2)],
    )]);
    let counts = CrateUnsoundnessCounts {
        sound_approx_per_harness: sound_approx.clone(),
        sound_approx_crate_totals: vec![("chc_translation_drop".to_string(), 2)],
        harness_names: ["main".to_string(), "check_modify".to_string()].into_iter().collect(),
        ..Default::default()
    };
    // The sibling harness itself stays demoted.
    let sibling = test_harness("check_modify", "crate");
    match classify_ctrex(&sibling, &counts) {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories, vec!["chc_translation_drop=2"]);
        }
        other => panic!("expected OverApproximation for sibling, got {other:?}"),
    }
    // This harness has no attributed counts — genuine.
    assert_eq!(classify_ctrex(&harness, &counts), CtrexCategory::Genuine);
}

/// Fail-closed twin: counts attributed to a NON-harness function key (or any
/// key that could ambiguously name the current harness) keep demoting every
/// harness in the crate.
#[test]
fn test_classify_ctrex_residual_non_harness_attribution_still_demotes() {
    let harness = test_harness("main", "crate");
    let sound_approx =
        BTreeMap::from([("helper_fn".to_string(), vec![("chc_translation_drop".to_string(), 1)])]);
    let counts = CrateUnsoundnessCounts {
        sound_approx_per_harness: sound_approx,
        sound_approx_crate_totals: vec![("chc_translation_drop".to_string(), 1)],
        harness_names: ["main".to_string(), "check_modify".to_string()].into_iter().collect(),
        ..Default::default()
    };
    match classify_ctrex(&harness, &counts) {
        CtrexCategory::OverApproximation { categories } => {
            assert_eq!(categories, vec!["chc_translation_drop=1"]);
        }
        other => panic!("expected OverApproximation residual, got {other:?}"),
    }
}

// --- Task #77 regression locks: per-property Genuine certification boundary ---
//
// These pin the SOUND behavior established in the Task #77 investigation: a
// counterexample under ANY sound-approximation taint stays OverApproximation,
// even when a per-property syntactic proxy would call the violated relation
// "independent". They guard against a future re-attempt of the unsound
// fragment/free-variable certifier that would flip the ffi_ptr /
// unsupported_object_size traps (and dual_77_dependent) to a certified Genuine.
// See the Task #77 note in `crate::ctrex_classify`.

/// Trap shape — expected/foreign-function/ffi_ptr.rs and dual_77_dependent.rs:
/// the failing assertion READS the unconstrained extern return. Its taint
/// signature (`chc_translation_drop=1,unhandled_calls=1`) is byte-identical to
/// the "independent" dual, so it MUST stay OverApproximation.
#[test]
fn test_classify_ctrex_task77_unhandled_call_trap_stays_over_approximation() {
    let harness = test_harness("check_fn_ptr_called", "crate");
    let sound_approx = BTreeMap::from([(
        "check_fn_ptr_called".to_string(),
        vec![("chc_translation_drop".to_string(), 1), ("unhandled_calls".to_string(), 1)],
    )]);
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    match classify_ctrex(&harness, &counts) {
        CtrexCategory::OverApproximation { categories } => {
            assert!(categories.contains(&"unhandled_calls=1".to_string()));
            assert!(categories.contains(&"chc_translation_drop=1".to_string()));
        }
        other => panic!("ffi_ptr-shape trap must stay OverApproximation, got {other:?}"),
    }
}

/// Trap shape — expected/shadow/unsupported_object_size/test.rs: the object-size
/// intrinsic is unmodeled (`static_init_incomplete` + `chc_translation_drop`).
/// The havoc IS the semantics; the counterexample is fabricated. Stays tainted.
#[test]
fn test_classify_ctrex_task77_object_size_trap_stays_over_approximation() {
    let harness = test_harness("check_max_object_size_fail", "crate");
    let sound_approx = BTreeMap::from([(
        "check_max_object_size_fail".to_string(),
        vec![("chc_translation_drop".to_string(), 2), ("static_init_incomplete".to_string(), 1)],
    )]);
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    match classify_ctrex(&harness, &counts) {
        CtrexCategory::OverApproximation { categories } => {
            assert!(categories.contains(&"static_init_incomplete=1".to_string()));
            assert!(categories.contains(&"chc_translation_drop=2".to_string()));
        }
        other => panic!("object-size trap must stay OverApproximation, got {other:?}"),
    }
}

/// Target shape — any_vec/out_bounds.rs and dual_77_independent.rs: the bug is
/// (arguably) independent of the drop, but the freed value is a normally-named,
/// driver-indistinguishable CHC var, so the sound verdict is to leave the taint.
/// Locks that a lone `chc_translation_drop` is NOT reclassified to Genuine.
#[test]
fn test_classify_ctrex_task77_independent_target_still_stays_over_approximation() {
    let harness = test_harness("dual_independent", "crate");
    let sound_approx = BTreeMap::from([(
        "dual_independent".to_string(),
        vec![("chc_translation_drop".to_string(), 1), ("unhandled_calls".to_string(), 1)],
    )]);
    let counts =
        CrateUnsoundnessCounts { sound_approx_per_harness: sound_approx, ..Default::default() };
    assert!(
        matches!(classify_ctrex(&harness, &counts), CtrexCategory::OverApproximation { .. }),
        "an independent-looking bug under sound-approximation taint must NOT be \
         certified Genuine driver-side (Task #77)"
    );
}

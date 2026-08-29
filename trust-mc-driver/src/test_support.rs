// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Shared test construction helpers for trust-mc-driver tests (#3458).
//!
//! This module is `#[cfg(test)]` only and provides factory functions for
//! building test metadata, harnesses, and verification results used across
//! multiple test modules (unsoundness_counts, demotion, ctrex_classify, etc.).

use std::collections::BTreeMap;
use std::path::PathBuf;

use trust_mc_metadata::{HarnessAttributes, HarnessKind, HarnessMetadata, KaniMetadata};

use crate::project::Project;
use crate::verification_result::{
    FailedProperties, ProofCrosscheck, ValidationStatus, VerificationResult, VerificationStatus,
};

/// Build a minimal HarnessMetadata for testing.
pub(crate) fn test_harness(pretty_name: &str, crate_name: &str) -> HarnessMetadata {
    HarnessMetadata {
        pretty_name: pretty_name.to_string(),
        mangled_name: pretty_name.to_string(),
        crate_name: crate_name.to_string(),
        original_file: "test.rs".to_string(),
        original_start_line: 1,
        original_end_line: 1,
        model_file: PathBuf::from("test.symtab.out"),
        attributes: HarnessAttributes::new(HarnessKind::Proof),
        contract: None,
        has_loop_contracts: false,
        is_automatically_generated: false,
    }
}

/// Build a minimal VerificationResult for testing.
pub(crate) fn test_result(
    status: VerificationStatus,
    failed_properties: FailedProperties,
) -> VerificationResult {
    use std::time::Duration;
    VerificationResult {
        status,
        failed_properties,
        results: vec![],
        runtime: Duration::default(),
        generated_concrete_test: false,
        coverage_results: None,
        logic_tier: Default::default(),
        validation_status: ValidationStatus::Validated,
        demotion_reasons: Vec::new(),
        ctrex_category: None,
        unknown_quality: None,
        solver_unknown_reason: None,
        kani_mem_overapprox_count: 0,
        sound_fallback_count: 0,
        proof_crosscheck: ProofCrosscheck::NotRun,
        proof_qualifiers: Vec::new(),
        proof_transcript_metadata: None,
        native_full_verification_verdict: None,
        harness_feasibility: Default::default(),
    }
}

/// Build KaniMetadata with basic unsoundness fields.
pub(crate) fn test_metadata(
    crate_name: &str,
    constant_fallback_count: Option<usize>,
    assume_dropped_count: Option<usize>,
) -> KaniMetadata {
    test_metadata_full(
        crate_name,
        constant_fallback_count,
        assume_dropped_count,
        None,
        None,
        None,
        None,
    )
}

/// Build KaniMetadata with more unsoundness fields.
#[allow(clippy::too_many_arguments)]
pub(crate) fn test_metadata_full(
    crate_name: &str,
    constant_fallback_count: Option<usize>,
    assume_dropped_count: Option<usize>,
    iterator_unsoundness_count: Option<(usize, usize)>,
    bigint_unsoundness_count: Option<usize>,
    chc_fallback_count: Option<usize>,
    unhandled_calls_count: Option<usize>,
) -> KaniMetadata {
    test_metadata_all(
        crate_name,
        constant_fallback_count,
        assume_dropped_count,
        None,
        iterator_unsoundness_count,
        bigint_unsoundness_count,
        chc_fallback_count,
        unhandled_calls_count,
        None,
    )
}

/// Build KaniMetadata with all unsoundness fields.
#[allow(clippy::too_many_arguments)]
pub(crate) fn test_metadata_all(
    crate_name: &str,
    constant_fallback_count: Option<usize>,
    assume_dropped_count: Option<usize>,
    store_dropped_count: Option<usize>,
    iterator_unsoundness_count: Option<(usize, usize)>,
    bigint_unsoundness_count: Option<usize>,
    chc_fallback_count: Option<usize>,
    unhandled_calls_count: Option<usize>,
    type_sort_fallback_count: Option<usize>,
) -> KaniMetadata {
    use trust_mc_metadata::*;
    KaniMetadata {
        crate_name: crate_name.to_string(),
        proof_harnesses: vec![],
        unsupported_features: vec![],
        test_harnesses: vec![],
        contracted_functions: vec![],
        autoharness_md: None,
        iterator_unsoundness: iterator_unsoundness_count.map(|(chc, bmc)| {
            IteratorUnsoundnessInfo {
                chc_skip_count: chc,
                bmc_skip_count: bmc,
                ..Default::default()
            }
        }),
        bigint_unsoundness: bigint_unsoundness_count
            .map(|count| BigIntUnsoundnessInfo { chc_skip_count: count, ..Default::default() }),
        chc_fallbacks: chc_fallback_count
            .map(|count| ChcFallbackInfo { total_count: count, per_harness: Default::default() }),
        chc_translation_drops: None,
        chc_coerce_eq_drops: None,
        assume_dropped_transitions: assume_dropped_count
            .map(|count| AssumeDroppedTransitionInfo { count, ..Default::default() }),
        store_dropped_transitions: store_dropped_count
            .map(|count| StoreDroppedTransitionInfo { count, per_harness: Default::default() }),
        constant_zero_fallbacks: constant_fallback_count
            .map(|count| ConstantZeroFallbackInfo { count, ..Default::default() }),
        unhandled_calls: unhandled_calls_count
            .map(|count| UnhandledCallInfo { count, per_harness: Default::default() }),
        error_blocked_fmt: None,
        known_stdlib_unconstrained: None,
        inferable_predicates: None,
        diverging_call_drops: None,
        assert_untranslatable: None,
        heap_check_untranslatable: None,
        heap_check_unknown_layout: None,
        type_sort_fallbacks: type_sort_fallback_count
            .map(|count| TypeSortFallbackInfo { count, ..Default::default() }),
        signedness_fallbacks: None,
        into_option_drops: None,
        internal_workarounds: None,
        abstracted_fallbacks: None,
        vec_field_fallbacks: None,
        pointee_synthesis_fallbacks: None,
        unsupported_construct_fallbacks: None,
        unconstrained_assignments: None,
        bmc_store_coercion_fallbacks: None,
        kani_mem_overapprox: None,
        offset_provenance_unresolved: None,
        sort_harmonize_fresh_var_fallbacks: None,
        ptr_metadata_unconstrained: None,
        static_init_incomplete: None,
        fp_bitvector_encoding: None,
        aggregate_encoding_gap: None,
        stub_approximation: None,
        rounding_assertion_bypass: None,
    }
}

/// Build KaniMetadata with a custom mutation applied to defaults.
pub(crate) fn md_with(f: impl FnOnce(&mut KaniMetadata)) -> KaniMetadata {
    let mut md = test_metadata_all("c", None, None, None, None, None, None, None, None);
    f(&mut md);
    md
}

/// Build one KaniMetadata per unsoundness category, each with exactly one nonzero counter.
/// Covers only DEMOTED_CATEGORIES (categories that trigger PROOF→FAILURE demotion).
/// Sound over-approximation and fail-closed categories are tested separately.
/// Category names are derived from `UnsoundnessCategory::json_key()` (#3715).
pub(crate) fn all_single_category_metadata() -> Vec<(&'static str, KaniMetadata)> {
    let mut metadata = legacy_single_category_metadata();
    metadata.extend(replacement_quality_single_category_metadata());
    metadata
}

fn legacy_single_category_metadata() -> Vec<(&'static str, KaniMetadata)> {
    use trust_mc_metadata::UnsoundnessCategory as UC;
    use trust_mc_metadata::{
        InternalWorkaroundInfo, SignednessFallbackInfo, UnconstrainedAssignmentInfo,
        UnsupportedConstructFallbackInfo,
    };

    vec![
        (
            UC::ConstantZeroFallback.json_key(),
            test_metadata_all("c", Some(1), None, None, None, None, None, None, None),
        ),
        (
            UC::InternalWorkaround.json_key(),
            md_with(|m| {
                m.internal_workarounds =
                    Some(InternalWorkaroundInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::ChcFallback.json_key(),
            test_metadata_all("c", None, None, None, None, None, Some(1), None, None),
        ),
        (
            UC::TypeSortFallback.json_key(),
            test_metadata_all("c", None, None, None, None, None, None, None, Some(1)),
        ),
        (
            UC::SignednessFallback.json_key(),
            md_with(|m| {
                m.signedness_fallbacks =
                    Some(SignednessFallbackInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::UnsupportedConstructFallback.json_key(),
            md_with(|m| {
                m.unsupported_construct_fallbacks =
                    Some(UnsupportedConstructFallbackInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::UnconstrainedAssignment.json_key(),
            md_with(|m| {
                m.unconstrained_assignments =
                    Some(UnconstrainedAssignmentInfo { count: 1, ..Default::default() })
            }),
        ),
    ]
}

fn replacement_quality_single_category_metadata() -> Vec<(&'static str, KaniMetadata)> {
    use trust_mc_metadata::UnsoundnessCategory as UC;
    use trust_mc_metadata::{
        BmcStoreCoercionFallbackInfo, DivergingCallDropInfo, FpBitvectorEncodingInfo,
        InferablePredicateInfo, KaniMemOverapproxInfo, OffsetProvenanceUnresolvedInfo,
        PointeeSynthesisFallbackInfo, RoundingAssertionBypassInfo, VecFieldFallbackInfo,
    };

    vec![
        (
            UC::BmcStoreCoercionFallback.json_key(),
            md_with(|m| {
                m.bmc_store_coercion_fallbacks =
                    Some(BmcStoreCoercionFallbackInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::StoreDroppedTransition.json_key(),
            test_metadata_all("c", None, None, Some(1), None, None, None, None, None),
        ),
        (
            UC::DivergingCallDrop.json_key(),
            md_with(|m| {
                m.diverging_call_drops =
                    Some(DivergingCallDropInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::OffsetProvenanceUnresolved.json_key(),
            md_with(|m| {
                m.offset_provenance_unresolved =
                    Some(OffsetProvenanceUnresolvedInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::KaniMemOverapprox.json_key(),
            md_with(|m| {
                m.kani_mem_overapprox =
                    Some(KaniMemOverapproxInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::InferablePredicate.json_key(),
            md_with(|m| {
                m.inferable_predicates =
                    Some(InferablePredicateInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::FpBitvectorEncoding.json_key(),
            md_with(|m| {
                m.fp_bitvector_encoding =
                    Some(FpBitvectorEncodingInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::RoundingAssertionBypass.json_key(),
            md_with(|m| {
                m.rounding_assertion_bypass =
                    Some(RoundingAssertionBypassInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::VecFieldFallback.json_key(),
            md_with(|m| {
                m.vec_field_fallbacks =
                    Some(VecFieldFallbackInfo { count: 1, ..Default::default() })
            }),
        ),
        (
            UC::PointeeSynthesisFallback.json_key(),
            md_with(|m| {
                m.pointee_synthesis_fallbacks =
                    Some(PointeeSynthesisFallbackInfo { count: 1, ..Default::default() })
            }),
        ),
    ]
}

// ─── Test-only extraction helpers ───
// These compute per-crate counts from Project metadata for test assertions.
// They are NOT used in production code — production extraction is in unsoundness_extract.rs.

pub(crate) fn chc_translation_drop_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.chc_translation_drops.as_ref().map_or(0, |info| {
                info.place_count + info.constant_count + info.field_projection_count
            });
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn chc_coerce_eq_drop_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.chc_coerce_eq_drops.as_ref().map_or(0, |info| info.total_count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn unhandled_call_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.unhandled_calls.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

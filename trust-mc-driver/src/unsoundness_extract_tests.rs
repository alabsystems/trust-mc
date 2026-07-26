// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::BTreeMap;

use trust_mc_metadata::{
    AggregateEncodingGapInfo, FpBitvectorEncodingInfo, PtrMetadataUnconstrainedInfo,
    RoundingAssertionBypassInfo, StaticInitIncompleteInfo, StubApproximationInfo,
};

use crate::project::Project;
use crate::test_support::md_with;
use crate::unsoundness_extract::sound_approximation_per_harness_by_crate;

/// Part of #3447: statement-level sound-approximation counters must flow into
/// per-harness extraction so CTREX classification does not fall back to Genuine
/// when only these counters fired. fp_bitvector_encoding is now a hard gate and
/// must stay out of this map.
#[test]
fn test_sound_approx_per_harness_includes_issue_3447_stmt_level_counters() {
    let mut project = Project::default();
    let md = md_with(|m| {
        m.crate_name = "crate_stmt".to_string();
        m.ptr_metadata_unconstrained = Some(PtrMetadataUnconstrainedInfo {
            count: 2,
            per_harness: BTreeMap::from([("harness_stmt".to_string(), 2)]),
        });
        m.static_init_incomplete = Some(StaticInitIncompleteInfo {
            count: 3,
            per_harness: BTreeMap::from([("harness_stmt".to_string(), 3)]),
        });
        m.fp_bitvector_encoding = Some(FpBitvectorEncodingInfo {
            count: 4,
            per_harness: BTreeMap::from([("harness_stmt".to_string(), 4)]),
        });
        m.aggregate_encoding_gap = Some(AggregateEncodingGapInfo {
            count: 5,
            per_harness: BTreeMap::from([("harness_stmt".to_string(), 5)]),
        });
        m.stub_approximation = Some(StubApproximationInfo {
            count: 6,
            per_harness: BTreeMap::from([("harness_stmt".to_string(), 6)]),
        });
    });
    project.metadata = vec![md];

    let result = sound_approximation_per_harness_by_crate(&project);
    let crate_map = result.get("crate_stmt").expect("crate_stmt must be present");
    let cats = crate_map.get("harness_stmt").expect("harness_stmt must be present");

    assert_eq!(cats.len(), 4, "only sound-approx #3447 counters must be present: {cats:?}");
    assert!(
        cats.iter().any(|(name, count)| name == "ptr_metadata_unconstrained" && *count == 2),
        "ptr_metadata_unconstrained must appear with count 2, got: {cats:?}"
    );
    assert!(
        cats.iter().any(|(name, count)| name == "static_init_incomplete" && *count == 3),
        "static_init_incomplete must appear with count 3, got: {cats:?}"
    );
    assert!(
        cats.iter().all(|(name, _)| name != "fp_bitvector_encoding"),
        "fp_bitvector_encoding must hard-gate instead of appearing as sound approximation: {cats:?}"
    );
    assert!(
        cats.iter().any(|(name, count)| name == "aggregate_encoding_gap" && *count == 5),
        "aggregate_encoding_gap must appear with count 5, got: {cats:?}"
    );
    assert!(
        cats.iter().any(|(name, count)| name == "stub_approximation" && *count == 6),
        "stub_approximation must appear with count 6, got: {cats:?}"
    );
}

/// Part of #3779: rounding_assertion_bypass now hard-gates replacement-quality
/// PROOFs instead of flowing through sound-approximation extraction.
#[test]
fn test_sound_approx_per_harness_excludes_rounding_assertion_bypass() {
    let mut project = Project::default();
    let md = md_with(|m| {
        m.crate_name = "crate_round".to_string();
        m.rounding_assertion_bypass = Some(RoundingAssertionBypassInfo {
            count: 2,
            per_harness: BTreeMap::from([("harness_ceil".to_string(), 2)]),
        });
    });
    project.metadata = vec![md];

    let result = sound_approximation_per_harness_by_crate(&project);
    assert!(
        result.get("crate_round").is_none(),
        "rounding_assertion_bypass must not be classified as sound approximation: {result:?}"
    );
}

/// Task #65 (a): metadata with nonzero ptr_metadata_unconstrained /
/// static_init_incomplete / stub_approximation — as now emitted by the
/// generate_metadata (codegen_units.rs) proof path — must produce a Step-C
/// OverApproximation on a Success instead of a clean PROOF. The metadata is
/// JSON round-tripped to prove the serialized form carries the fields.
#[test]
fn test_task65_sound_approx_fields_step_c_overapprox_on_success() {
    use crate::demotion::apply_sound_fallback_fail_close;
    use crate::test_support::{test_harness, test_result};
    use crate::unsoundness_counts::UnsoundnessCounts;
    use crate::verification_result::{CtrexCategory, FailedProperties, VerificationStatus};

    let md = md_with(|m| {
        m.crate_name = "crate65".to_string();
        m.proof_harnesses = vec![test_harness("crate65::h", "crate65")];
        m.ptr_metadata_unconstrained = Some(PtrMetadataUnconstrainedInfo {
            count: 1,
            per_harness: BTreeMap::from([("crate65::h".to_string(), 1)]),
        });
        m.static_init_incomplete = Some(StaticInitIncompleteInfo {
            count: 2,
            per_harness: BTreeMap::from([("crate65::h".to_string(), 2)]),
        });
        m.stub_approximation = Some(StubApproximationInfo {
            count: 3,
            per_harness: BTreeMap::from([("crate65::h".to_string(), 3)]),
        });
    });
    // JSON round-trip: the driver reads these fields from serialized metadata.
    let json = serde_json::to_string(&md).expect("metadata serializes");
    let md: trust_mc_metadata::KaniMetadata =
        serde_json::from_str(&json).expect("metadata deserializes");

    let mut project = Project::default();
    project.metadata = vec![md];
    let counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate65");

    let harness = test_harness("crate65::h", "crate65");
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    apply_sound_fallback_fail_close(&mut result, &harness, &counts);

    assert_eq!(result.status, VerificationStatus::Failure);
    assert_eq!(result.sound_fallback_count, 6);
    match &result.ctrex_category {
        Some(CtrexCategory::OverApproximation { categories }) => {
            assert!(categories.contains(&"ptr_metadata_unconstrained=1".to_string()));
            assert!(categories.contains(&"static_init_incomplete=2".to_string()));
            assert!(categories.contains(&"stub_approximation=3".to_string()));
        }
        other => panic!("expected OverApproximation, got {other:?}"),
    }
}

/// Task #65 (b): metadata with nonzero rounding_assertion_bypass — as now
/// emitted by the generate_metadata (codegen_units.rs) proof path — must
/// demote a Success (DEMOTED category), JSON round-tripped as above.
#[test]
fn test_task65_rounding_assertion_bypass_demotes_success() {
    use crate::demotion::demote_for_all_unsoundness;
    use crate::test_support::{test_harness, test_result};
    use crate::unsoundness_counts::UnsoundnessCounts;
    use crate::verification_result::{FailedProperties, VerificationStatus};

    let md = md_with(|m| {
        m.crate_name = "crate65r".to_string();
        m.proof_harnesses = vec![test_harness("crate65r::h", "crate65r")];
        m.rounding_assertion_bypass = Some(RoundingAssertionBypassInfo {
            count: 1,
            per_harness: BTreeMap::from([("crate65r::h".to_string(), 1)]),
        });
    });
    let json = serde_json::to_string(&md).expect("metadata serializes");
    let md: trust_mc_metadata::KaniMetadata =
        serde_json::from_str(&json).expect("metadata deserializes");

    let mut project = Project::default();
    project.metadata = vec![md];
    let counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate65r");

    let harness = test_harness("crate65r::h", "crate65r");
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    demote_for_all_unsoundness(&mut result, &harness, &counts);

    assert_eq!(result.status, VerificationStatus::Failure);
    assert_eq!(result.demotion_reasons, vec!["rounding_assertion_bypass=1"]);
}

/// Task #65 (c), metadata level: a per-FUNCTION-keyed survivor map (the
/// key-space trap) must fail close through the whole extraction path — both
/// the Step-C sound-approximation leg and the DEMOTED leg — instead of
/// zeroing the per-harness lookup.
#[test]
fn test_task65_fn_keyed_survivor_metadata_fail_closes() {
    use crate::demotion::{apply_sound_fallback_fail_close, demote_for_all_unsoundness};
    use crate::test_support::{test_harness, test_result};
    use crate::unsoundness_counts::UnsoundnessCounts;
    use crate::verification_result::{CtrexCategory, FailedProperties, VerificationStatus};

    let md = md_with(|m| {
        m.crate_name = "crate65f".to_string();
        m.proof_harnesses = vec![test_harness("crate65f::h", "crate65f")];
        // fn-keyed survivors: keys name a helper fn, NOT the proof harness.
        m.stub_approximation = Some(StubApproximationInfo {
            count: 2,
            per_harness: BTreeMap::from([("crate65f::helper_fn".to_string(), 2)]),
        });
        m.rounding_assertion_bypass = Some(RoundingAssertionBypassInfo {
            count: 1,
            per_harness: BTreeMap::from([("crate65f::helper_fn".to_string(), 1)]),
        });
    });
    let mut project = Project::default();
    project.metadata = vec![md];
    let counts = UnsoundnessCounts::from_project(&project).get_for_crate("crate65f");
    let harness = test_harness("crate65f::h", "crate65f");

    // Step-C leg: the survivor stub_approximation entry converts the Success.
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    apply_sound_fallback_fail_close(&mut result, &harness, &counts);
    assert_eq!(result.status, VerificationStatus::Failure);
    assert_eq!(
        result.ctrex_category,
        Some(CtrexCategory::OverApproximation {
            categories: vec!["stub_approximation=2".to_string()]
        })
    );

    // DEMOTED leg: the survivor rounding entry demotes a fresh Success.
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    demote_for_all_unsoundness(&mut result, &harness, &counts);
    assert_eq!(result.status, VerificationStatus::Failure);
    assert_eq!(result.demotion_reasons, vec!["rounding_assertion_bypass=1"]);
}

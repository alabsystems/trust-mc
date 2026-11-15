// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::test_support::test_result;
use std::borrow::Cow;
use std::fs;
use tempfile::TempDir;

#[test]
fn test_find_smt_file_absolute_path() {
    let temp_dir = TempDir::new().unwrap();
    // set_extension replaces only the last extension: test.symtab.out -> test.symtab.smt2
    let smt_file = temp_dir.path().join("test.symtab.smt2");
    fs::write(&smt_file, "(check-sat)").unwrap();

    let model_file = temp_dir.path().join("test.symtab.out");
    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_ok(), "Expected success for absolute path: {:?}", result);
    assert_eq!(result.unwrap(), smt_file);
}

#[test]
fn test_find_smt_file_relative_path_resolved_against_outdir() {
    let temp_dir = TempDir::new().unwrap();
    // set_extension replaces only the last extension: test.symtab.out -> test.symtab.smt2
    let smt_file = temp_dir.path().join("test.symtab.smt2");
    fs::write(&smt_file, "(check-sat)").unwrap();

    // Test with relative path - should be resolved against outdir
    let model_file = PathBuf::from("test.symtab.out");
    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_ok(), "Expected success for relative path: {:?}", result);
    assert_eq!(result.unwrap(), smt_file);
}

#[test]
fn test_find_smt_file_not_found() {
    let temp_dir = TempDir::new().unwrap();
    let model_file = temp_dir.path().join("nonexistent.symtab.out");

    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(err_msg.contains("not found"), "Error should mention 'not found': {}", err_msg);
    assert!(err_msg.contains(".smt2"), "Error should mention .smt2 extension: {}", err_msg);
}

#[test]
fn test_find_smt_file_path_exists_but_is_directory() {
    let temp_dir = TempDir::new().unwrap();
    // Create a directory where the SMT file should be
    let smt_dir = temp_dir.path().join("test.symtab.smt2");
    fs::create_dir(&smt_dir).unwrap();

    let model_file = temp_dir.path().join("test.symtab.out");
    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(err_msg.contains("not a file"), "Error should mention 'not a file': {}", err_msg);
}

#[test]
fn test_find_smt_file_absolute_path_ignores_outdir() {
    // When model_file is absolute, outdir is never consulted (is_relative check fails)
    let temp_dir = TempDir::new().unwrap();
    let abs_dir = temp_dir.path().join("abs");
    let out_dir = temp_dir.path().join("out");
    fs::create_dir_all(&abs_dir).unwrap();
    fs::create_dir_all(&out_dir).unwrap();

    let abs_smt = abs_dir.join("test.symtab.smt2");
    fs::write(&abs_smt, "(check-sat) ; absolute").unwrap();

    let model_file = abs_dir.join("test.symtab.out");
    let result = find_smt_file(&model_file, &out_dir);
    assert!(result.is_ok(), "Absolute path should work: {:?}", result);
    assert_eq!(result.unwrap(), abs_smt);
}

#[test]
fn test_find_smt_file_error_includes_tried_paths() {
    // Verify error message includes the paths that were tried
    let temp_dir = TempDir::new().unwrap();
    let model_file = PathBuf::from("nonexistent.symtab.out");

    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();

    // Should include the relative path in the error
    assert!(
        err_msg.contains("nonexistent.symtab.smt2"),
        "Error should include original path: {}",
        err_msg
    );
    assert!(err_msg.contains("tried:"), "Error should mention paths were tried: {}", err_msg);
}

#[test]
#[cfg(unix)]
fn test_find_smt_file_follows_symlinks() {
    use std::os::unix::fs::symlink;

    let temp_dir = TempDir::new().unwrap();
    let real_file = temp_dir.path().join("real.smt2");
    let symlink_file = temp_dir.path().join("test.symtab.smt2");

    fs::write(&real_file, "(check-sat)").unwrap();
    symlink(&real_file, &symlink_file).unwrap();

    let model_file = temp_dir.path().join("test.symtab.out");
    let result = find_smt_file(&model_file, temp_dir.path());
    assert!(result.is_ok(), "Should follow symlinks: {:?}", result);
    assert_eq!(result.unwrap(), symlink_file);
}

#[test]
fn test_fail_fast_harness_info_roundtrip() {
    // FailFastHarnessInfo wraps a failed result as an anyhow::Error,
    // then is recovered via downcast. This test verifies the roundtrip:
    // creation -> Error -> downcast -> extracted index + result.
    let result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    let info = FailFastHarnessInfo { index_to_failing_harness: 3, result };

    // Verify Display impl (used in error messages)
    assert_eq!(format!("{info}"), "harness failed");

    // Wrap in anyhow::Error and downcast back
    let err = anyhow::Error::new(info);
    assert!(err.is::<FailFastHarnessInfo>());
    let recovered = err.downcast::<FailFastHarnessInfo>().unwrap();
    assert_eq!(recovered.index_to_failing_harness, 3);
    assert_eq!(recovered.result.status, VerificationStatus::Failure);
    assert!(matches!(recovered.result.failed_properties, FailedProperties::PanicsOnly));
}

#[test]
fn test_demotion_reasons_marker_emits_joined_categories() {
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    result.demotion_reasons =
        vec!["constant_zero_fallback=1".to_string(), "chc_fallback=2".to_string()];

    let marker = demotion_reasons_marker(&result);

    assert_eq!(
        marker.as_deref(),
        Some("[AY:DEMOTION_REASONS:constant_zero_fallback=1,chc_fallback=2]")
    );
}

#[test]
fn test_demotion_reasons_marker_skips_empty_results() {
    let result = test_result(VerificationStatus::Success, FailedProperties::None);

    assert_eq!(demotion_reasons_marker(&result), None);
}

#[test]
fn test_proof_crosscheck_marker_not_run() {
    let marker = proof_crosscheck_marker(&ProofCrosscheck::NotRun);
    assert_eq!(marker, None);
}

#[test]
fn test_proof_qualifiers_marker_skips_failure_results() {
    let result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    assert_eq!(proof_qualifiers_marker(&result), None);
}

#[test]
fn test_proof_qualifiers_marker_emits_trivial_safe_qualifier() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.proof_qualifiers.push("trivial_safe=no_error_rule".to_string());

    assert_eq!(
        proof_qualifiers_marker(&result).as_deref(),
        Some("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]")
    );
}

#[test]
fn test_proof_qualifiers_marker_omits_kani_mem_overapprox_success_qualifier() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.proof_qualifiers.push("trivial_safe=no_error_rule".to_string());
    result.sound_fallback_count = 2;
    result.kani_mem_overapprox_count = 1;

    assert_eq!(
        proof_qualifiers_marker(&result).as_deref(),
        Some("[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,sound_fallback=2]")
    );
}

fn anonymous_chc_check(status: CheckStatus) -> Property {
    Property {
        description: Cow::Borrowed("CHC verification: error unreachable (ay-chc)"),
        property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
        source_location: RawSourceLocation { column: None, file: None, function: None, line: None },
        status,
        trace: None,
    }
}

fn attributed_check(class: &'static str, status: CheckStatus) -> Property {
    Property {
        description: Cow::Borrowed("assertion failed: a + b < 200"),
        property_id: PropertyId {
            fn_name: Some("check".to_string()),
            class: Cow::Borrowed(class),
            id: 1,
        },
        source_location: RawSourceLocation {
            column: Some("5".to_string()),
            file: Some("pass.rs".to_string()),
            function: Some("check".to_string()),
            line: Some("9".to_string()),
        },
        status,
        trace: None,
    }
}

/// T1 first green: a CHC proof whose only check is the anonymous `chc.0` fallback names no
/// property, which is how a bypassed `assert!` override went unnoticed. It must not read
/// as a clean proof.
#[test]
fn test_proof_qualifiers_marker_names_a_success_with_only_the_anonymous_chc_check() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.results = vec![anonymous_chc_check(CheckStatus::Success)];

    assert_eq!(
        proof_qualifiers_marker(&result).as_deref(),
        Some("[AY:PROOF_QUALIFIERS:unattributed_check=chc.0]")
    );
    assert_eq!(reported_proof_qualifiers(&result), vec![UNATTRIBUTED_CHC_CHECK_QUALIFIER]);
}

#[test]
fn test_proof_qualifiers_marker_ignores_covers_next_to_the_anonymous_chc_check() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.results = vec![
        anonymous_chc_check(CheckStatus::Success),
        attributed_check("cover", CheckStatus::Satisfied),
    ];
    result.proof_qualifiers.push("trivial_safe=no_error_rule".to_string());
    result.sound_fallback_count = 1;

    assert_eq!(
        proof_qualifiers_marker(&result).as_deref(),
        Some(
            "[AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule,unattributed_check=chc.0,sound_fallback=1]"
        )
    );
}

/// V7: a `should_panic` harness cannot stand on the anonymous `chc.0` check. It names no
/// property, so it cannot show the failure was a panic (the parity-1 review's
/// `sp_abort_refuted` / `sp_unreachable_unchecked_refuted` printed "encountered one or more
/// panics as expected" resting on it alone).
#[test]
fn test_should_panic_rests_on_unattributed_chc_check_only_when_every_failure_is_anonymous() {
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    result.results = vec![anonymous_chc_check(CheckStatus::Failure)];
    assert!(should_panic_rests_on_unattributed_chc_check(&result));

    // A cover beside it does not attribute the failure.
    result.results.push(attributed_check("cover", CheckStatus::Satisfied));
    assert!(should_panic_rests_on_unattributed_chc_check(&result));

    // A registered panic property does.
    result.results = vec![attributed_check("assertion", CheckStatus::Failure)];
    assert!(!should_panic_rests_on_unattributed_chc_check(&result));

    // Mixed: one attributed and one anonymous failure is not "resting only on chc.0".
    result.results = vec![
        attributed_check("assertion", CheckStatus::Failure),
        anonymous_chc_check(CheckStatus::Failure),
    ];
    assert!(!should_panic_rests_on_unattributed_chc_check(&result));

    // No failing check at all.
    result.results = vec![anonymous_chc_check(CheckStatus::Success)];
    assert!(!should_panic_rests_on_unattributed_chc_check(&result));
}

#[test]
fn test_proof_qualifiers_marker_stays_clean_for_attributed_checks() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.results = vec![attributed_check("assertion", CheckStatus::Success)];
    assert_eq!(proof_qualifiers_marker(&result).as_deref(), Some("[AY:PROOF_QUALIFIERS:clean]"));

    // No checks at all is the no-checks gate's business, not this qualifier's.
    result.results.clear();
    assert_eq!(unattributed_chc_check_qualifier(&result), None);
}

#[test]
fn test_unattributed_chc_check_leaves_failed_results_unqualified() {
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    result.results = vec![anonymous_chc_check(CheckStatus::Failure)];

    assert_eq!(unattributed_chc_check_qualifier(&result), None);
    assert_eq!(proof_qualifiers_marker(&result), None);
    assert!(reported_proof_qualifiers(&result).is_empty());
    assert_eq!(result.status, VerificationStatus::Failure);
}

#[test]
fn test_proof_transcript_metadata_marker_skips_absent_metadata() {
    let result = test_result(VerificationStatus::Success, FailedProperties::None);
    assert_eq!(proof_transcript_metadata_marker(&result), None);
}

#[test]
fn test_proof_transcript_metadata_marker_hex_encodes_compact_json() {
    let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    let metadata = serde_json::json!({
        "schema": "ay.chc-proof-transcript/v1",
        "result": "unsafe",
        "transcript": {
            "metadata_only": true,
            "status": "metadata-only"
        }
    });
    result.proof_transcript_metadata = Some(metadata.clone());

    let marker = proof_transcript_metadata_marker(&result).expect("metadata marker");
    let encoded = marker
        .strip_prefix("[AY:PROOF_TRANSCRIPT_METADATA:v1:json_hex=")
        .and_then(|s| s.strip_suffix(']'))
        .expect("marker envelope");

    assert!(
        encoded.chars().all(|ch| ch.is_ascii_hexdigit() && !ch.is_ascii_uppercase()),
        "metadata marker should use lowercase hex: {marker}"
    );

    let decoded = decode_hex(encoded);
    let decoded_json: serde_json::Value =
        serde_json::from_slice(&decoded).expect("hex payload should be JSON");
    assert_eq!(decoded_json, metadata);
    assert_eq!(trust_trust_mc_chc_pdr_evidence_marker(&result), None);
}

#[test]
fn test_native_proof_grade_marker_rejects_metadata_only_transcript() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.proof_transcript_metadata = Some(serde_json::json!({
        "schema": "ay.chc-proof-transcript/v1",
        "result": "safe",
        "proof_status": "verified-invariant",
        "accepted_as_proof": true,
        "replay": {
            "status": "replayable",
            "input_sha256": digest('a')
        },
        "transcript": {
            "metadata_only": true,
            "status": "metadata-only"
        }
    }));

    assert_eq!(trust_trust_mc_chc_pdr_evidence_marker(&result), None);
    assert_eq!(
        native_proof_grade_marker(&result).as_deref(),
        Some("[AY:NATIVE_PROOF_GRADE:rejected:transcript_not_replayable]")
    );
}

#[test]
fn test_legacy_chc_pdr_metadata_stays_diagnostic_even_with_full_artifacts() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.proof_transcript_metadata = Some(serde_json::json!({
        "schema": "ay.chc-proof-transcript/v1",
        "result": "safe",
        "proof_status": "verified-invariant",
        "accepted_as_proof": true,
        "normalized_input_sha256": digest('a'),
        "replay": {
            "status": "replayable",
            "sha256": digest('b')
        },
        "transcript": {
            "status": "replayable",
            "metadata_only": false,
            "uri": "reports/trust_mc/chc-transcript.jsonl",
            "sha256": digest('c')
        },
        "checked_report": {
            "status": "checked",
            "sha256": digest('d')
        }
    }));

    assert_eq!(trust_trust_mc_chc_pdr_evidence_marker(&result), None);
    assert_eq!(
        native_proof_grade_marker(&result).as_deref(),
        Some(
            "[AY:NATIVE_PROOF_GRADE:rejected:pdr_invariant_candidates_require_fresh_private_consumer_replay_before_proof_grade_admission]"
        )
    );
}

#[test]
fn test_top_v1_transcript_accepts_bundle_v2_checked_report_without_alethe() {
    let mut metadata = serde_json::json!({
        "schema": "ay.chc-proof-transcript/v1",
        "result": "safe",
        "proof_status": "verified-invariant",
        "accepted_as_proof": true,
        "replay": {
            "status": "replayable",
            "sha256": digest('b')
        },
        "transcript": {
            "status": "replayable",
            "metadata_only": false,
            "uri": "reports/trust_mc/chc-transcript.jsonl",
            "sha256": digest('c')
        },
        "checked_report": {
            "status": "checked",
            "sha256": digest('d'),
            "strict_cert": {
                "schema": "ay.chc-obligation-strict-proof-bundle-cert/v2",
                "schema_version": 2,
                "proof_checker": "ay-proof::re_check_bundle_strict",
                "proof_bundle_schema": "ay.proofbundle/v3",
                "bundle_sha256": digest('e'),
                "verdict": "verified"
            }
        }
    });

    let payload = trust_trust_mc_chc_pdr_evidence_payload(&metadata)
        .expect("nested bundle-v2 evidence is opaque to the stable top-v1 contract");
    assert_eq!(payload["schema"], "trust.trust_mc-chc-pdr-evidence.v1");
    assert_eq!(payload["reasoning"], "Pdr");
    assert_eq!(payload["transcript_sha256"], digest('c'));

    metadata["schema"] = serde_json::Value::String("ay.chc-proof-transcript/v2".to_string());
    assert_eq!(
        trust_trust_mc_chc_pdr_evidence_payload(&metadata),
        Err("unexpected_schema"),
        "an unknown top-level transcript schema must still fail closed"
    );
}

#[test]
fn test_pdr_candidate_verdict_is_rejected_pending_fresh_private_replay() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    let obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
        "harness::proof",
        trust_mc_core::MirObligationKind::Assertion,
        "(set-logic HORN)\n(rule true)\n(query error)\n",
    );
    let proof = trust_mc_core::ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
        obligation,
        trust_mc_core::ChcPdrStats { relation_count: 1, clause_count: 2 },
        1,
        ("ay://chc-pdr/proof-metadata.json", b"proof metadata"),
        ("trust_mc://chc-pdr/replay-log.json", b"replay log"),
        ("trust_mc://chc-pdr/checked-proof-report.json", b"checked proof report"),
        ("ay://chc-pdr/invariant-model.json", b"invariant model"),
    )
    .expect("test proof artifacts are nonempty and bounded");
    result.native_full_verification_verdict =
        Some(trust_mc_core::FullVerificationVerdict::Proved {
            evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
        });

    assert_eq!(
        native_proof_grade_marker(&result).as_deref(),
        Some(
            "[AY:NATIVE_PROOF_GRADE:rejected:pdr_invariant_candidates_require_fresh_private_consumer_replay_before_proof_grade_admission]"
        )
    );
    assert_eq!(trust_trust_mc_chc_pdr_evidence_marker(&result), None);
}

#[test]
fn test_native_full_verification_unknown_rejects_proof_grade_marker() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    result.native_full_verification_verdict =
        Some(trust_mc_core::FullVerificationVerdict::Unknown {
            reason: "ay ChcPdrProofRun was not accepted_as_proof".to_string(),
        });

    assert_eq!(trust_trust_mc_chc_pdr_evidence_marker(&result), None);
    assert_eq!(
        native_proof_grade_marker(&result).as_deref(),
        Some(
            "[AY:NATIVE_PROOF_GRADE:rejected:solver_did_not_prove_the_obligation_ay_chcpdrproofrun_was_not_accepted_as_proof]"
        )
    );
}

fn decode_hex(encoded: &str) -> Vec<u8> {
    assert_eq!(encoded.len() % 2, 0, "hex payload length must be even");
    encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_value(pair[0]) << 4) | hex_value(pair[1]))
        .collect()
}

fn hex_value(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => panic!("invalid hex byte: {byte}"),
    }
}

fn digest(ch: char) -> String {
    std::iter::repeat_n(ch, 64).collect()
}

// --- Task #78: driver-side Genuine-certification decision (twin-dual proof) ---
//
// These pin `ctrex_certifiable_genuine`, the pure gate behind
// `recertify_overapprox_ctrex`. Together they encode the Task #77 twin duals:
// an independent violation certifies; a dependent one (the ffi_ptr trap) does
// not; and any incompleteness fails closed.

#[cfg(test)]
mod task78 {
    use crate::ay_parse::vc_artifact::ApproximationEvidence;
    use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
    use std::borrow::Cow;
    use std::collections::HashMap;

    /// Matching typed slice of the retained native Parity-array observation:
    /// two fail-closed drops, two accounted return havocs, incomplete identity
    /// and no per-site properties. Raw SAT is not a concrete source CEX.
    #[test]
    fn typed_custom_comparison_drop_stays_uncertified() {
        use crate::ctrex_classify::classify_ctrex;
        use crate::project::Project;
        use crate::test_support::{test_harness, test_metadata};
        use crate::unsoundness_counts::UnsoundnessCounts;
        use crate::verification_result::CtrexCategory;
        use trust_mc_metadata::ChcTranslationDropInfo;

        let name = "probe_custom_eq_array";
        let harness = test_harness("captured::probe_custom_eq_array", "captured");
        let mut metadata = test_metadata("captured", None, None);
        metadata.proof_harnesses.push(harness.clone());
        metadata.chc_translation_drops = Some(ChcTranslationDropInfo {
            place_count: 2,
            per_harness: [(name.to_string(), 2)].into(),
            sound_havoc_count: 2,
            sound_havoc_per_harness: [(name.to_string(), 2)].into(),
            ..Default::default()
        });
        let mut project = Project::default();
        project.metadata.push(metadata);
        let counts = UnsoundnessCounts::from_project(&project).get_for_crate("captured");
        let CtrexCategory::OverApproximation { categories } = classify_ctrex(&harness, &counts)
        else {
            panic!("actual typed translation drops must not certify a source counterexample")
        };
        assert_eq!(categories.len(), 2);
        assert!(categories.contains(&"chc_translation_drop=2".to_string()));
        assert!(categories.contains(&"chc_sound_havoc_drop=2".to_string()));
        assert!(!super::ctrex_certifiable_genuine(&categories, &evidence(false, 2, &[]), &[]));

        // Even fabricated independence and a matching event count cannot
        // erase the compiler's actual incomplete-identity refusal.
        assert!(!super::ctrex_certifiable_genuine(
            &categories,
            &evidence(false, 4, &[(3, Some(false))]),
            &[failing_error_p(3)],
        ));
    }

    /// The paired native false primitive assertion has complete identity and
    /// no drops. The real classifier must retain its concrete counterexample,
    /// so a blanket refusal cannot satisfy the preceding negative control.
    #[test]
    fn typed_complete_false_assertion_is_a_genuine_counterexample() {
        use crate::ctrex_classify::classify_ctrex;
        use crate::project::Project;
        use crate::test_support::{test_harness, test_metadata};
        use crate::unsoundness_counts::UnsoundnessCounts;
        use crate::verification_result::CtrexCategory;

        let harness = test_harness("captured::probe_eq_real_counterexample", "captured");
        let mut metadata = test_metadata("captured", None, None);
        metadata.proof_harnesses.push(harness.clone());
        let mut project = Project::default();
        project.metadata.push(metadata);
        let counts = UnsoundnessCounts::from_project(&project).get_for_crate("captured");
        assert_eq!(classify_ctrex(&harness, &counts), CtrexCategory::Genuine);
    }

    fn failing_error_p(id: u32) -> Property {
        Property {
            description: Cow::Borrowed("assertion failed"),
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id },
            source_location: RawSourceLocation {
                file: None,
                line: None,
                column: None,
                function: None,
            },
            status: CheckStatus::Failure,
            trace: None,
        }
    }

    fn evidence(
        complete: bool,
        accounted: usize,
        deps: &[(u32, Option<bool>)],
    ) -> ApproximationEvidence {
        ApproximationEvidence {
            complete,
            accounted,
            approximated_vars: vec!["_freed".to_string()],
            dependent_by_id: deps.iter().copied().collect::<HashMap<u32, Option<bool>>>(),
            relation_by_id: deps.iter().map(|(id, _)| (*id, format!("error_p{id}"))).collect(),
        }
    }

    /// kani/Intrinsics/FastMath/add_overflow_f32.rs as emitted at 9e086301c
    /// (relations renamed): `error_p6`/`error_p7` are the operand-finiteness
    /// checks, and a result check over the table value is added as `error_p8`.
    const FAST_ADD_CHC: &str = r#"
(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-var z (_ BitVec 32))
(declare-var z__out (_ BitVec 32))
(declare-var float_binop_tbl_f32 (Array (_ BitVec 72) (_ BitVec 32)))
(declare-rel bb0 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (Array (_ BitVec 72) (_ BitVec 32))))
(declare-rel bb2 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (Array (_ BitVec 72) (_ BitVec 32))))
(declare-rel bb3 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (Array (_ BitVec 72) (_ BitVec 32))))
(declare-rel error ())
(declare-rel error_p6 ())
(declare-rel error_p7 ())
(declare-rel error_p8 ())
(rule (=> true (bb0 x y z float_binop_tbl_f32)))
(rule (=> (bb0 x y z float_binop_tbl_f32) (bb2 x y z float_binop_tbl_f32)))
(rule (=> error_p6 error))
(rule (=> (and (bb2 x y z float_binop_tbl_f32) (not (not (= ((_ extract 30 23) x) #xff)))) error_p6))
(rule (=> error_p7 error))
(rule (=> (and (bb2 x y z float_binop_tbl_f32) (not (not (= ((_ extract 30 23) y) #xff)))) error_p7))
(rule (=> (and (bb2 x y z float_binop_tbl_f32) (= z__out (select float_binop_tbl_f32 (concat (concat #x00 x) y)))) (bb3 x y z__out float_binop_tbl_f32)))
(rule (=> error_p8 error))
(rule (=> (and (bb3 x y z float_binop_tbl_f32) (= ((_ extract 30 23) z) #xff)) error_p8))
(query error)
"#;

    fn table_evidence(deps: &[(u32, Option<bool>)]) -> ApproximationEvidence {
        ApproximationEvidence {
            approximated_vars: vec![trust_mc_core::chc::FLOAT_BINOP_TABLE_F32.to_string()],
            ..evidence(true, 1, deps)
        }
    }

    /// T1 (row 72, FastMath): an operand-finiteness failure the dependence
    /// analysis finds independent of the float table replays without it.
    #[test]
    fn table_independent_operand_failure_replays() {
        let replay = super::float_table_ctrex_replay(
            FAST_ADD_CHC,
            &table_evidence(&[(6, Some(false)), (7, Some(false)), (8, Some(true))]),
            &[failing_error_p(6)],
        );
        let summary = replay.expect("a table is freed").expect("error_p6 replays");
        assert!(summary.contains("error_p6"), "{summary}");
    }

    /// The gate never trusts the dependence verdict alone: a check marked
    /// independent that in fact reads the table value does not replay, so the
    /// counterexample stays uncertified.
    #[test]
    fn table_dependent_failure_does_not_replay_even_if_marked_independent() {
        let replay = super::float_table_ctrex_replay(
            FAST_ADD_CHC,
            &table_evidence(&[(6, Some(false)), (7, Some(false)), (8, Some(false))]),
            &[failing_error_p(8)],
        );
        assert!(replay.expect("a table is freed").is_err());
    }

    /// No violated independent check, or no table freed at all.
    #[test]
    fn table_replay_gate_scope() {
        let replay = super::float_table_ctrex_replay(
            FAST_ADD_CHC,
            &table_evidence(&[(6, Some(true))]),
            &[failing_error_p(6)],
        );
        assert!(replay.expect("a table is freed").is_err(), "a dependent check is never replayed");
        assert!(
            super::float_table_ctrex_replay(
                FAST_ADD_CHC,
                &evidence(true, 1, &[(6, Some(false))]),
                &[failing_error_p(6)],
            )
            .is_none(),
            "the gate applies only when a float-binop table is freed"
        );
    }

    /// The taint shape shared by every unhandled-indirect-call harness: one
    /// SoundFallback event bumps both `chc_translation_drop` AND `unhandled_calls`.
    fn unhandled_call_taint() -> Vec<String> {
        vec!["chc_translation_drop=1".to_string(), "unhandled_calls=1".to_string()]
    }

    fn failing_check(description: &'static str) -> Property {
        Property { description: Cow::Borrowed(description), ..failing_error_p(0) }
    }

    /// BMC lane (no error_p properties in the artifact): a counterexample whose
    /// only taint is `offset_provenance_unresolved` certifies Genuine when no
    /// failing check is a same-allocation obligation, and stays tainted when one
    /// is, when another taint rides along, or when the artifact is a CHC one.
    #[test]
    fn bmc_offset_only_taint_certifies_off_the_same_allocation_family() {
        let offset = vec!["offset_provenance_unresolved=2".to_string()];
        let bmc = evidence(true, 0, &[]);
        assert!(super::bmc_offset_only_ctrex_is_genuine(
            &offset,
            &bmc,
            &[failing_check("assertion failed: *before == 2")],
        ));
        assert!(!super::bmc_offset_only_ctrex_is_genuine(
            &offset,
            &bmc,
            &[
                failing_check("assertion failed: offset != 0"),
                failing_check(
                    "Offset result and original pointer should point to the same allocation"
                ),
            ],
        ));
        let mixed = vec![
            "offset_provenance_unresolved=1".to_string(),
            "chc_sound_havoc_drop=1".to_string(),
        ];
        assert!(!super::bmc_offset_only_ctrex_is_genuine(
            &mixed,
            &bmc,
            &[failing_check("assertion failed: x == 1")],
        ));
        let chc = evidence(true, 0, &[(3, Some(false))]);
        assert!(!super::bmc_offset_only_ctrex_is_genuine(
            &offset,
            &chc,
            &[failing_check("assertion failed: x == 1")],
        ));
        assert!(!super::bmc_offset_only_ctrex_is_genuine(&offset, &bmc, &[]));
    }

    /// dual_77_independent: complete plumbing, violated `error_p3` is data
    /// INDEPENDENT of the freed extern return → certify Genuine. Also exercises
    /// the double-count subtraction: effective_total = (1+1) − 1 = 1 == accounted.
    #[test]
    fn independent_violation_certifies_genuine() {
        assert!(super::ctrex_certifiable_genuine(
            &unhandled_call_taint(),
            &evidence(true, 1, &[(3, Some(false))]),
            &[failing_error_p(3)],
        ));
    }

    /// ffi_ptr / dual_77_dependent trap: complete plumbing, but the violated
    /// `error_p3` READS the freed extern return → STAY OverApproximation.
    #[test]
    fn dependent_violation_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &unhandled_call_taint(),
            &evidence(true, 1, &[(3, Some(true))]),
            &[failing_error_p(3)],
        ));
    }

    /// An unplumbed approximation (accounted < effective taint total) blocks
    /// certification for the whole harness, even when the violation looks
    /// independent — this is what makes PARTIAL plumbing sound.
    #[test]
    fn incomplete_identity_stays_tainted() {
        // Two chc_translation_drops but only one accounted: effective = (2+1)−1 = 2 != 1.
        let taint = vec!["chc_translation_drop=2".to_string(), "unhandled_calls=1".to_string()];
        assert!(!super::ctrex_certifiable_genuine(
            &taint,
            &evidence(true, 1, &[(3, Some(false))]),
            &[failing_error_p(3)],
        ));
    }

    /// An unstubbed abstraction frees a value the compiler never accounts, so
    /// it blocks certification even when the counts coincide: one unstubbed
    /// abstraction against one accounted havoc of a different event
    /// (unstubbed_abstraction_safe.rs, decision REDS-REST).
    #[test]
    fn unstubbed_abstraction_blocks_certification_whatever_the_counts() {
        let taint = vec!["unstubbed_abstraction=1".to_string()];
        assert!(!super::ctrex_certifiable_genuine(
            &taint,
            &evidence(true, 1, &[(3, Some(false))]),
            &[failing_error_p(3)],
        ));
    }

    /// The compiler-side completeness flag being false also blocks certification.
    #[test]
    fn compiler_incomplete_flag_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &unhandled_call_taint(),
            &evidence(false, 1, &[(3, Some(false))]),
            &[failing_error_p(3)],
        ));
    }

    /// An unattributed counterexample (no violated `error_p` matches the
    /// evidence, e.g. all per-checks SUCCESS) never certifies — fail-closed.
    #[test]
    fn unattributed_counterexample_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &unhandled_call_taint(),
            &evidence(true, 1, &[(3, Some(false))]),
            &[], // no violated check
        ));
    }

    /// A violated check whose dependence verdict is unknown (`None`) is treated
    /// as dependent — fail-closed.
    #[test]
    fn unknown_verdict_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &unhandled_call_taint(),
            &evidence(true, 1, &[(3, None)]),
            &[failing_error_p(3)],
        ));
    }

    // --- OFFSET_PROV_GENUINE_CERT: the offset-provenance EncodingGap lane ---
    //
    // The `offset_provenance_unresolved` demotion skips an allocation-bound /
    // in-bounds check but frees NO readable var (compiler accounts it with a
    // `None` identity, so `approximated_vars` stays empty and every property is
    // independent). The violated isize-overflow check reads only count+size, so
    // its per-property verdict is `Some(false)` → certify Genuine. `accounted`
    // (1) matches the driver's offset taint total (1).

    /// The offset overflow shape: complete plumbing, one accounted offset event,
    /// an independent violated `error_p1` → certify Genuine.
    #[test]
    fn offset_provenance_independent_overflow_certifies() {
        assert!(super::ctrex_certifiable_genuine(
            &["offset_provenance_unresolved=1".to_string()],
            &evidence(true, 1, &[(1, Some(false))]),
            &[failing_error_p(1)],
        ));
    }

    /// Missed-bug guard: if the violated check READS the (hypothetical) freed
    /// offset var (dependent), it must STAY tainted even under offset provenance.
    #[test]
    fn offset_provenance_dependent_violation_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &["offset_provenance_unresolved=1".to_string()],
            &evidence(true, 1, &[(1, Some(true))]),
            &[failing_error_p(1)],
        ));
    }

    /// An unaccounted offset event (accounted 0 != taint total 1) fails closed:
    /// this is exactly the pre-plumbing state the compiler fix repairs.
    #[test]
    fn offset_provenance_unaccounted_stays_tainted() {
        assert!(!super::ctrex_certifiable_genuine(
            &["offset_provenance_unresolved=1".to_string()],
            &evidence(true, 0, &[(1, Some(false))]),
            &[failing_error_p(1)],
        ));
    }
}

fn no_checks_test_property() -> crate::property_model::Property {
    crate::property_model::Property {
        description: std::borrow::Cow::Borrowed("test assertion"),
        property_id: crate::property_model::PropertyId {
            fn_name: Some("h".to_string()),
            class: std::borrow::Cow::Borrowed("assertion"),
            id: 1,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: crate::property_model::CheckStatus::Success,
        trace: None,
    }
}

/// A success over an EMPTY obligation set is refused — the verdict
/// `a_harness_with_no_checks_is_inconclusive_not_proved` pins end to end.
#[test]
fn no_checks_gate_refuses_a_success_with_no_obligations() {
    let result = test_result(VerificationStatus::Success, FailedProperties::None);
    assert!(result.results.is_empty());
    assert!(no_checks_gate_fires(&result, false));
}

#[test]
fn no_checks_gate_leaves_real_checks_failures_and_should_panic_alone() {
    let mut proved = test_result(VerificationStatus::Success, FailedProperties::None);
    proved.results.push(no_checks_test_property());
    assert!(!no_checks_gate_fires(&proved, false), "a real proof must not be refused");

    let failed = test_result(VerificationStatus::Failure, FailedProperties::Other);
    assert!(!no_checks_gate_fires(&failed, false), "already failed closed");

    let should_panic = test_result(VerificationStatus::Success, FailedProperties::None);
    assert!(!no_checks_gate_fires(&should_panic, true), "should_panic verdicts are panic-shaped");
}

/// Both wordings carry the tag that kani-domination, the CLI tests and the
/// expected files key on; only the certified one names the qualifier the
/// verdict carries, and only the uncertified one says an obligation may have
/// been dropped.
#[test]
fn no_checks_marker_keeps_the_tag_for_both_causes() {
    for certified in [true, false] {
        let marker = no_checks_marker("h", certified);
        assert!(
            marker.starts_with(
                "[AY:VACUOUS:no-checks] h: the harness produced no verification conditions"
            ),
            "{marker}"
        );
    }
    let certified = no_checks_marker("h", true);
    assert!(certified.contains(OBLIGATION_FREE_CERTIFIED_QUALIFIER), "{certified}");
    assert!(certified.contains("never as a clean proof"), "{certified}");
    let uncertified = no_checks_marker("h", false);
    assert!(uncertified.contains("may have been dropped"), "{uncertified}");
    assert!(!uncertified.contains("SUCCESSFUL"), "{uncertified}");
}

/// D16's second step: a certified empty obligation set is a success that is
/// never clean, an uncertified one fails closed.
#[test]
fn settle_no_checks_result_keeps_a_certified_success_and_fails_an_uncertified_one() {
    let mut certified = test_result(VerificationStatus::Success, FailedProperties::None);
    settle_no_checks_result(&mut certified, true);
    assert_eq!(certified.status, VerificationStatus::Success);
    assert!(matches!(certified.failed_properties, FailedProperties::None));
    assert!(certified.is_certified_obligation_free());
    assert_eq!(
        proof_qualifiers_marker(&certified).as_deref(),
        Some("[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]"),
        "the qualifier must displace `clean`"
    );
    // Settling twice does not stack the qualifier.
    settle_no_checks_result(&mut certified, true);
    assert_eq!(certified.proof_qualifiers.len(), 1);

    let mut uncertified = test_result(VerificationStatus::Success, FailedProperties::None);
    settle_no_checks_result(&mut uncertified, false);
    assert_eq!(uncertified.status, VerificationStatus::Failure);
    assert!(matches!(uncertified.failed_properties, FailedProperties::Other));
    assert!(!uncertified.is_certified_obligation_free());
    assert_eq!(proof_qualifiers_marker(&uncertified), None);
}

/// The gate runs twice per harness (once before and once after the two-lane
/// retry). A result it already settled as certified must not trip it again,
/// or the marker prints twice.
#[test]
fn no_checks_gate_does_not_fire_twice_on_a_settled_certified_result() {
    let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
    assert!(no_checks_gate_fires(&result, false));
    settle_no_checks_result(&mut result, true);
    assert!(!no_checks_gate_fires(&result, false), "settled: still empty, still a success");
}

// ── An exhausted unwinding bound is never a counterexample ──────────────────
//
// Two classes carry the same meaning and must be treated identically: `"unwind"`
// (the BMC loop bound) and `"recursion"` (the recursive-inline bound, planted by
// `verdict_policy::recursion_unwind_property`). Measured defect: only `"unwind"`
// was recognised, so a recursion unwinding assertion on the trustc route
// (`kani/DynTrait/unsized_cast.rs`, `unsized_rc_cast.rs` — `Box`/`Rc` drop-glue
// dyn dispatch) was classified `[AY:CTREX_CAT:Genuine]` and reported a CERTIFIED
// failure on a program the frozen-nightly route proves.

#[test]
fn test_unwind_bound_exhausted_sees_a_failed_loop_unwinding_assertion() {
    assert!(unwind_bound_exhausted(&[attributed_check("unwind", CheckStatus::Failure)]));
}

#[test]
fn test_unwind_bound_exhausted_sees_a_failed_recursion_unwinding_assertion() {
    assert!(
        unwind_bound_exhausted(&[attributed_check("recursion", CheckStatus::Failure)]),
        "a recursion unwinding assertion is the recursive sibling of the loop unwind bound: \
         the search was truncated, so the harness must not certify a counterexample"
    );
}

#[test]
fn test_unwind_bound_exhausted_ignores_a_passing_unwinding_assertion() {
    assert!(!unwind_bound_exhausted(&[
        attributed_check("unwind", CheckStatus::Success),
        attributed_check("recursion", CheckStatus::Success),
    ]));
}

#[test]
fn test_unwind_bound_exhausted_ignores_an_ordinary_failed_assertion() {
    assert!(!unwind_bound_exhausted(&[
        attributed_check("assertion", CheckStatus::Failure),
        anonymous_chc_check(CheckStatus::Failure),
    ]));
}

#[test]
fn test_unwind_bound_exhausted_fires_on_a_recursion_failure_beside_other_checks() {
    // The whole-harness rule: one truncated search taints every sibling verdict,
    // because the model that satisfied `(or viol_0 … viol_n)` may have used the
    // cut edge. Same position upstream Kani takes.
    assert!(unwind_bound_exhausted(&[
        attributed_check("memory_safety", CheckStatus::Success),
        attributed_check("recursion", CheckStatus::Failure),
        attributed_check("assertion", CheckStatus::Success),
    ]));
}

// ── CHC exact-derivation counterexamples are not undecided verdicts ─────────
//
// Root cause measured 2026-09-14 (docs/chc-unknown-root-causes-2026-09-14.md,
// group G8): `interpret_chc_trivial_unsafe` DERIVES `error` and prints
// "(exact CHC derivation)", but when per-property attribution finds no
// `error_p{N}` it reports the legacy aggregate `chc.0` property, whose class is
// "chc" and whose failure class is the reachable check's kind. A memory-safety
// / pointer-overflow / valid-value counterexample therefore arrived spelled
// exactly like a solver that could not decide, and was categorised `Unknown`.

#[test]
fn an_undecided_chc_failure_is_still_undecided() {
    // The shape `call_ay`'s undecided-model arm preserves: Other, no non-chc
    // failing property, and no exact derivation. Unchanged by the fix.
    assert!(chc_failure_is_undecided(FailedProperties::Other, false, false));
}

#[test]
fn an_exactly_derived_chc_failure_is_decided() {
    // Same shape, plus the driver's own derivation witness.
    assert!(!chc_failure_is_undecided(FailedProperties::Other, false, true));
}

#[test]
fn a_non_chc_violation_is_decided_with_or_without_the_flag() {
    // A decided non-assertion violation (BMC overflow / bounds check) reports a
    // failing property outside class "chc"; it never depended on the flag.
    assert!(!chc_failure_is_undecided(FailedProperties::Other, true, false));
    assert!(!chc_failure_is_undecided(FailedProperties::Other, true, true));
}

#[test]
fn panics_only_is_decided_whatever_the_flag_says() {
    // `PanicsOnly` names the failing class, so it was never the undecided
    // spelling. The flag must not change that either way.
    assert!(!chc_failure_is_undecided(FailedProperties::PanicsOnly, false, false));
    assert!(!chc_failure_is_undecided(FailedProperties::PanicsOnly, false, true));
}

#[test]
fn the_flag_defaults_to_false_on_a_plain_result() {
    // Fail-closed default: every producer that computed no derivation leaves it
    // unset, so `test_result` (and every non-CHC lane) keeps the old reading.
    let r = test_result(VerificationStatus::Failure, FailedProperties::Other);
    assert!(!r.chc_exact_counterexample);
    assert!(chc_failure_is_undecided(r.failed_properties, false, r.chc_exact_counterexample));
}

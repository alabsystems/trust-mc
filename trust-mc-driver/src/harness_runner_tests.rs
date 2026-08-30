// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::test_support::test_result;
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
        }
    }

    /// The taint shape shared by every unhandled-indirect-call harness: one
    /// SoundFallback event bumps both `chc_translation_drop` AND `unhandled_calls`.
    fn unhandled_call_taint() -> Vec<String> {
        vec!["chc_translation_drop=1".to_string(), "unhandled_calls=1".to_string()]
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

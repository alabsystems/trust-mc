// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn stats() -> ChcPdrStats {
    ChcPdrStats { relation_count: 2, clause_count: 3 }
}

fn obligation() -> MirDerivedChcPdrObligation {
    MirDerivedChcPdrObligation::new(
        "mir-obligation-1",
        MirObligationKind::Termination,
        "(set-logic HORN)\r\n(rule true)  \r\n(query error)\r\n\r\n",
    )
}

fn linked_candidate(kind: ChcPdrProofKind) -> ChcPdrProofEvidence {
    match kind {
        ChcPdrProofKind::ChcValidity => {
            ChcPdrProofEvidence::try_chc_validity_candidate_from_linked_bytes(
                obligation(),
                stats(),
                ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
                ("artifact://trust_mc/replay.jsonl", b"replay log"),
                ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
            )
        }
        ChcPdrProofKind::PdrInvariant => {
            ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
                obligation(),
                stats(),
                1,
                ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
                ("artifact://trust_mc/replay.jsonl", b"replay log"),
                ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
                ("artifact://trust_mc/invariant.json", b"invariant model"),
            )
        }
    }
    .expect("test proof artifacts are nonempty and bounded")
}

#[test]
fn pdr_invariant_model_is_bound_but_remains_reject_only_without_fresh_replay() {
    let proof = linked_candidate(ChcPdrProofKind::PdrInvariant);
    let invariant = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::PdrInvariantModel)
        .expect("PDR invariant artifact");
    let replay = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::ReplayLog)
        .expect("replay artifact");
    let checked = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::CheckedProofReport)
        .expect("checked artifact");
    let invariant_digest = invariant.digest.clone().expect("invariant digest");

    assert_eq!(invariant.materialized_bytes(), Some(b"invariant model".as_slice()));
    assert_eq!(invariant.proof_binding_id(), replay.proof_binding_id());
    assert_eq!(invariant.proof_binding_id(), checked.proof_binding_id());
    assert!(replay.referenced_artifacts().contains(&FullVerificationArtifactReference::new(
        FullVerificationArtifactKind::PdrInvariantModel,
        invariant_digest.clone(),
    )));
    assert!(checked.referenced_artifacts().contains(&FullVerificationArtifactReference::new(
        FullVerificationArtifactKind::PdrInvariantModel,
        invariant_digest,
    )));

    let verdict =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof.clone()) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("arbitrary producer-authored invariant bytes must not become proof-grade");
    };
    assert!(reasons.contains(&PDR_INVARIANT_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()));
    assert_eq!(
        proof.metadata.replay_check_status,
        Some(ProofReplayCheckStatus {
            replay: ProofReplayStatus::Unknown,
            check: ProofCheckStatus::Unknown,
        })
    );
    assert!(accepted_chc_pdr_proof(&verdict).is_err());

    let mut mutated_count = proof.clone();
    mutated_count.invariant_count += 1;
    let mutated_count =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(mutated_count) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } =
        classify_proof_grade_verdict(&mutated_count)
    else {
        panic!("mutating a bound invariant count must fail closed");
    };
    assert!(reasons.iter().any(|reason| reason.contains("proof-set binding")));

    let mut missing_model = proof.clone();
    missing_model
        .artifacts
        .retain(|artifact| artifact.kind != FullVerificationArtifactKind::PdrInvariantModel);
    let rejected =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(missing_model) };
    assert!(matches!(
        classify_proof_grade_verdict(&rejected),
        ProofGradeVerdict::NotProofGrade { .. }
    ));

    let mut swapped_model = proof;
    let invariant = swapped_model
        .artifacts
        .iter_mut()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::PdrInvariantModel)
        .expect("PDR invariant artifact");
    *invariant = FullVerificationArtifact::from_bytes(
        FullVerificationArtifactKind::PdrInvariantModel,
        "artifact://trust_mc/swapped-invariant.json",
        b"swapped invariant",
    );
    let rejected =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(swapped_model) };
    assert!(matches!(
        classify_proof_grade_verdict(&rejected),
        ProofGradeVerdict::NotProofGrade { .. }
    ));
}

#[test]
fn pdr_requires_candidate_constructor_and_chc_validity_rejects_stray_model() {
    let error = ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::PdrInvariant,
        obligation(),
        stats(),
        ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
        ("artifact://trust_mc/replay.jsonl", b"replay log"),
        ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
    )
    .expect_err("generic proof-grade constructor must reject PDR candidates");
    assert_eq!(error, FullVerificationArtifactMaterializationError::PdrInvariantCandidateRequired);

    let error = ChcPdrProofEvidence::try_pdr_invariant_candidate_from_linked_bytes(
        obligation(),
        stats(),
        0,
        ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
        ("artifact://trust_mc/replay.jsonl", b"replay log"),
        ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
        ("artifact://trust_mc/invariant.json", b"invariant model"),
    )
    .expect_err("a zero-interpretation PDR candidate must fail closed");
    assert_eq!(error, FullVerificationArtifactMaterializationError::InvalidPdrInvariantCount);

    let validity = linked_candidate(ChcPdrProofKind::ChcValidity).with_artifact(
        FullVerificationArtifact::from_bytes(
            FullVerificationArtifactKind::PdrInvariantModel,
            "artifact://trust_mc/stray-invariant.json",
            b"stray invariant",
        ),
    );
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(validity) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("CHC validity must reject a stray PDR model");
    };
    assert!(
        reasons.contains(&"CHC validity proof must not carry a PDR invariant model".to_string())
    );
}

fn digest_artifact(
    kind: FullVerificationArtifactKind,
    label: &str,
    bytes: &[u8],
) -> FullVerificationArtifact {
    FullVerificationArtifact::from_bytes(kind, label, bytes)
}

fn native_digest(seed: u8) -> NativeArtifactDigest {
    NativeArtifactDigest::new("sha256", format!("{seed:02x}").repeat(32))
}

fn native_metadata(
    native_request_id: u32,
    proof_obligation_ids: Vec<u32>,
    verification_mode: &str,
) -> NativeTypedChcObligationMetadata {
    let compiler_fact_sources = proof_obligation_ids
        .iter()
        .map(|id| NativeObligationCompilerFacts {
            proof_obligation_id: *id,
            function_id: Some(9),
            span: Some(NativeSourceSpanMetadata { file: 0, line: 10 + *id, col: 3 }),
            cause: NativeObligationCauseMetadata::Translation,
            monomorphization_id: Some(0),
            fact_refs: vec![NativeCompilerFactReference::new(
                NativeCompilerFactKind::Monomorphization,
                0,
            )],
        })
        .collect::<Vec<_>>();
    let compiler_fact_counts = NativeCompilerFactCounts {
        monomorphizations: 1,
        obligation_sources: compiler_fact_sources.len(),
        ..NativeCompilerFactCounts::default()
    };
    let first_proof_obligation_id = proof_obligation_ids.first().copied();

    NativeTypedChcObligationMetadata::new(
        "tRust",
        "rust-mir",
        Some(native_digest(0x11)),
        native_digest(0x22),
        NativeArtifactDigest::new("trust_ir-stable-v1", "33".repeat(32)),
        native_request_id,
        verification_mode,
        9,
        proof_obligation_ids,
        vec![0],
    )
    .with_compiler_facts(
        NativeArtifactDigest::new("trust_ir-stable-v1", "44".repeat(32)),
        compiler_fact_counts,
        compiler_fact_sources,
    )
    .with_replay_metadata(
        NativeReplayIdentityMetadata {
            engine: "trust_mc".to_string(),
            invocation: format!("trust_mc native request {native_request_id}"),
            transcript_digest: NativeArtifactDigest::new("sha256", "55".repeat(32)),
        },
        NativeReplayContextMetadata {
            atoms: vec![NativeReplayAtomMetadata {
                atom_id: 0,
                kind: NativeReplayAtomKindMetadata::Assertion,
                formula_schema: "smtlib2".to_string(),
                payload_digest: NativeArtifactDigest::new("trust_ir-stable-v1", "66".repeat(32)),
                proof_obligation_id: first_proof_obligation_id,
                assertion_id: Some(7),
                span: Some(NativeSourceSpanMetadata { file: 0, line: 10, col: 3 }),
            }],
            unsupported_modes: Vec::new(),
        },
    )
}

fn native_typed_proof(metadata: NativeTypedChcObligationMetadata) -> ChcPdrProofEvidence {
    let obligation_id = metadata.expected_obligation_id();
    let obligation = MirDerivedChcPdrObligation::new(
        obligation_id,
        MirObligationKind::Assertion,
        "(set-logic HORN)\n(declare-rel error ())\n(rule false)\n(query error)\n",
    )
    .with_native_metadata(metadata);

    ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::ChcValidity,
        obligation,
        stats(),
        ("artifact://trust_mc/native-transcript.json", b"native solver transcript"),
        ("artifact://trust_mc/native-replay.json", b"native replay log"),
        ("artifact://trust_mc/native-checked.json", b"native checked proof report"),
    )
    .expect("native test proof artifacts are nonempty and bounded")
}

#[test]
fn normalized_input_hash_is_stable_for_line_endings_and_trailing_space() {
    let a = MirDerivedChcPdrObligation::new(
        "term",
        MirObligationKind::Termination,
        "(set-logic HORN)\r\n(rule true)  \r\n(query error)\r\n",
    );
    let b = MirDerivedChcPdrObligation::new(
        "term",
        MirObligationKind::Termination,
        "(set-logic HORN)\n(rule true)\n(query error)\n\n",
    );

    assert_eq!(a.normalized_input, "(set-logic HORN)\n(rule true)\n(query error)\n");
    assert_eq!(a.normalized_input, b.normalized_input);
    assert_eq!(a.normalized_input_hash, b.normalized_input_hash);
    assert_eq!(a.normalized_input_hash.algorithm, "sha256");
    assert_eq!(a.normalized_input_hash.value.len(), 64);
    assert!(a.normalized_input_hash.value.bytes().all(|byte| !byte.is_ascii_uppercase()));
}

#[test]
fn linked_proof_artifacts_retain_exact_bytes_and_typed_relationships() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let input = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::NormalizedInput)
        .expect("normalized input artifact");
    let transcript = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::SolverTranscript)
        .expect("solver transcript artifact");
    let replay = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::ReplayLog)
        .expect("replay artifact");
    let checked = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::CheckedProofReport)
        .expect("checked-report artifact");

    assert_eq!(input.materialized_bytes(), Some(proof.obligation.normalized_input.as_bytes()));
    assert_eq!(transcript.materialized_bytes(), Some(b"solver transcript".as_slice()));
    assert_eq!(replay.materialized_bytes(), Some(b"replay log".as_slice()));
    assert_eq!(checked.materialized_bytes(), Some(b"checked proof report".as_slice()));
    assert_eq!(transcript.materialized_byte_len(), transcript.byte_len);
    let binding = input.proof_binding_id().expect("content-addressed proof binding");
    assert!(binding.as_str().starts_with("trust_mc-proof-set-sha256:"));
    assert_eq!(transcript.proof_binding_id(), Some(binding));
    assert_eq!(replay.proof_binding_id(), Some(binding));
    assert_eq!(checked.proof_binding_id(), Some(binding));
    assert_eq!(
        transcript.referenced_artifacts(),
        &[FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::NormalizedInput,
            proof.obligation.normalized_input_hash.clone(),
        )]
    );
    assert_eq!(
        replay.referenced_artifacts(),
        &[FullVerificationArtifactReference::new(
            FullVerificationArtifactKind::SolverTranscript,
            transcript.digest.clone().expect("transcript digest"),
        )]
    );
    assert_eq!(
        checked.referenced_artifacts(),
        &[
            FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::SolverTranscript,
                transcript.digest.clone().expect("transcript digest"),
            ),
            FullVerificationArtifactReference::new(
                FullVerificationArtifactKind::ReplayLog,
                replay.digest.clone().expect("replay digest"),
            ),
        ]
    );
}

#[test]
fn linked_proof_constructor_rejects_empty_or_oversized_payloads() {
    let empty = ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::ChcValidity,
        obligation(),
        stats(),
        ("transcript", b""),
        ("replay", b"replay"),
        ("checked", b"checked"),
    )
    .expect_err("empty proof-bearing payload must fail closed");
    assert_eq!(
        empty,
        FullVerificationArtifactMaterializationError::EmptyProofPayload {
            kind: FullVerificationArtifactKind::SolverTranscript,
        }
    );

    let empty_input =
        MirDerivedChcPdrObligation::new("empty-input", MirObligationKind::Assertion, " \n\t");
    let error = ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::ChcValidity,
        empty_input,
        stats(),
        ("transcript", b"transcript"),
        ("replay", b"replay"),
        ("checked", b"checked"),
    )
    .expect_err("empty normalized proof input must fail closed");
    assert_eq!(error, FullVerificationArtifactMaterializationError::EmptyNormalizedInput);

    let mut mismatched_input = obligation();
    mismatched_input.normalized_input_hash = EvidenceHash::sha256_bytes(b"different input");
    let error = ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::ChcValidity,
        mismatched_input,
        stats(),
        ("transcript", b"transcript"),
        ("replay", b"replay"),
        ("checked", b"checked"),
    )
    .expect_err("stale normalized-input digest must fail at construction");
    assert_eq!(error, FullVerificationArtifactMaterializationError::NormalizedInputDigestMismatch);

    let oversized = vec![0x5a; MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES + 1];
    let error = ChcPdrProofEvidence::try_proof_grade_from_linked_bytes(
        ChcPdrProofKind::ChcValidity,
        obligation(),
        stats(),
        ("transcript", &oversized),
        ("replay", b"replay"),
        ("checked", b"checked"),
    )
    .expect_err("oversized proof-bearing payload must fail closed");
    assert!(matches!(
        error,
        FullVerificationArtifactMaterializationError::PayloadTooLarge {
            max: MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES,
            actual,
        } if actual == oversized.len()
    ));

    let descriptor = FullVerificationArtifact::from_bytes(
        FullVerificationArtifactKind::DiagnosticTrace,
        "diagnostic",
        &oversized,
    );
    assert!(descriptor.digest.is_some());
    assert_eq!(descriptor.byte_len, Some(oversized.len() as u64));
    assert!(descriptor.materialized_bytes().is_none());
}

#[test]
fn bounded_byte_deserializer_rejects_oversize_from_sequence_hint_before_allocation() {
    use serde::de::value::{Error, SeqDeserializer};

    let sequence =
        std::iter::repeat_n(0_u8, MAX_FULL_VERIFICATION_ARTIFACT_MATERIALIZATION_BYTES + 1);
    let deserializer = SeqDeserializer::<_, Error>::new(sequence);
    let error = deserialize_bounded_artifact_bytes(deserializer)
        .expect_err("oversized declared sequence must be rejected");

    assert!(error.to_string().contains("exceeds the 16777216-byte materialization limit"));
}

#[test]
fn digest_string_deserializers_reject_huge_single_values_and_noncanonical_forms() {
    let canonical_hex = "00".repeat(32);
    let huge = "x".repeat(1024 * 1024);

    let huge_algorithm = serde_json::json!({
        "kind": "SolverTranscript",
        "digest": { "algorithm": huge, "value": canonical_hex },
    });
    let error = serde_json::from_value::<FullVerificationArtifactReference>(huge_algorithm)
        .expect_err("one huge algorithm string inside one reference must fail closed");
    assert!(error.to_string().contains("algorithm must be exactly `sha256`"));
    assert!(error.to_string().len() < 256, "error must not echo hostile input");

    let huge_value = serde_json::json!({
        "algorithm": "sha256",
        "value": "x".repeat(1024 * 1024),
    });
    let error = serde_json::from_value::<EvidenceHash>(huge_value)
        .expect_err("one huge digest value must fail closed");
    assert!(error.to_string().contains("exactly 64 lowercase hexadecimal"));
    assert!(error.to_string().len() < 256, "error must not echo hostile input");

    let uppercase = serde_json::json!({
        "algorithm": "sha256",
        "value": "AA".repeat(32),
    });
    assert!(
        serde_json::from_value::<EvidenceHash>(uppercase).is_err(),
        "uppercase digest metadata must not deserialize as canonical"
    );

    let huge_binding = serde_json::Value::String("x".repeat(1024 * 1024));
    let error = serde_json::from_value::<ProofArtifactBindingId>(huge_binding)
        .expect_err("one huge proof binding string must fail closed");
    assert!(error.to_string().contains("proof artifact binding id is not canonical"));
    assert!(error.to_string().len() < 256, "error must not echo hostile input");

    let uppercase_binding =
        serde_json::Value::String(format!("{}{}", ProofArtifactBindingId::PREFIX, "AA".repeat(32)));
    assert!(
        serde_json::from_value::<ProofArtifactBindingId>(uppercase_binding).is_err(),
        "uppercase proof binding must not deserialize as canonical"
    );
}

#[test]
fn artifact_materialization_serde_roundtrip_preserves_bytes_and_rejects_tampering() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let transcript = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::SolverTranscript)
        .expect("solver transcript artifact");
    let encoded = serde_json::to_value(transcript).expect("serialize artifact");
    let decoded: FullVerificationArtifact =
        serde_json::from_value(encoded.clone()).expect("deserialize valid artifact");
    assert_eq!(decoded, *transcript);
    assert_eq!(decoded.materialized_bytes(), transcript.materialized_bytes());

    let mut wrong_digest = encoded.clone();
    wrong_digest["digest"]["value"] = serde_json::Value::String("00".repeat(32));
    assert!(serde_json::from_value::<FullVerificationArtifact>(wrong_digest).is_err());

    let mut wrong_length = encoded.clone();
    wrong_length["materialization"]["byte_len"] = serde_json::json!(999_u64);
    assert!(serde_json::from_value::<FullVerificationArtifact>(wrong_length).is_err());

    let mut invalid_binding = encoded;
    invalid_binding["materialization"]["proof_binding_id"] =
        serde_json::Value::String("request-7-proof-0".to_string());
    assert!(serde_json::from_value::<FullVerificationArtifact>(invalid_binding).is_err());

    let checked = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::CheckedProofReport)
        .expect("checked report");
    let mut reordered = serde_json::to_value(checked).expect("serialize checked report");
    reordered["materialization"]["referenced_artifacts"]
        .as_array_mut()
        .expect("reference array")
        .swap(0, 1);
    let error = serde_json::from_value::<FullVerificationArtifact>(reordered)
        .expect_err("noncanonical reference order must fail at deserialization");
    assert!(error.to_string().contains("strict canonical kind/digest order"));
}

#[test]
fn proof_vector_deserializers_enforce_small_preallocation_caps() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let transcript = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::SolverTranscript)
        .expect("solver transcript");
    let materialization = transcript.materialization().expect("transcript materialization");
    let mut materialization_json =
        serde_json::to_value(materialization).expect("serialize materialization");
    let reference = serde_json::to_value(FullVerificationArtifactReference::new(
        FullVerificationArtifactKind::NormalizedInput,
        proof.obligation.normalized_input_hash.clone(),
    ))
    .expect("serialize reference");
    materialization_json["referenced_artifacts"] =
        serde_json::Value::Array(vec![reference; MAX_LINKED_ARTIFACT_REFERENCES + 1]);
    let error =
        serde_json::from_value::<FullVerificationArtifactMaterialization>(materialization_json)
            .expect_err("oversized reference list must fail before materialization validation");
    assert!(error.to_string().contains("artifact references exceeds the 8-entry limit"));

    let mut too_many_hashes = serde_json::to_value(&proof).expect("serialize proof");
    too_many_hashes["metadata"]["transcript_hashes"] = serde_json::Value::Array(vec![
        serde_json::to_value(EvidenceHash::sha256_bytes(b"hash"))
            .expect("serialize hash");
        MAX_PROOF_EVIDENCE_HASHES + 1
    ]);
    let error = serde_json::from_value::<ChcPdrProofEvidence>(too_many_hashes)
        .expect_err("oversized proof hash inventory must fail at deserialization");
    assert!(error.to_string().contains("proof evidence hashes exceeds the 8-entry limit"));

    let mut too_many_artifacts = serde_json::to_value(&proof).expect("serialize proof");
    too_many_artifacts["artifacts"] =
        serde_json::Value::Array(vec![
            serde_json::to_value(transcript).expect("serialize artifact");
            MAX_PROOF_EVIDENCE_ARTIFACTS + 1
        ]);
    let error = serde_json::from_value::<ChcPdrProofEvidence>(too_many_artifacts)
        .expect_err("oversized proof artifact inventory must fail at deserialization");
    assert!(error.to_string().contains("proof evidence artifacts exceeds the 16-entry limit"));
}

#[test]
fn legacy_descriptor_deserializes_but_cannot_claim_linked_proof_grade() {
    let bytes = b"legacy transcript";
    let digest = EvidenceHash::sha256_bytes(bytes);
    let descriptor: FullVerificationArtifact = serde_json::from_value(serde_json::json!({
        "kind": "SolverTranscript",
        "label": "artifact://legacy/transcript",
        "digest": digest,
        "byte_len": bytes.len(),
    }))
    .expect("legacy descriptor remains backward-compatible");
    assert!(descriptor.materialized_bytes().is_none());

    let proof = ChcPdrProofEvidence::proof_grade_from_bytes(
        ChcPdrProofKind::ChcValidity,
        obligation(),
        stats(),
        ("transcript", b"solver transcript"),
        ("replay", b"replay log"),
        ("checked", b"checked report"),
    );
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("unlinked compatibility evidence must not become proof-grade");
    };
    assert!(reasons.iter().any(|reason| reason.contains("typed proof relationship")));
}

#[test]
fn role_confused_artifact_reference_fails_proof_classification() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let mut encoded = serde_json::to_value(&proof).expect("serialize proof");
    let artifacts = encoded["artifacts"].as_array_mut().expect("artifact array");
    let replay = artifacts
        .iter_mut()
        .find(|artifact| artifact["kind"] == "ReplayLog")
        .expect("replay artifact");
    replay["materialization"]["referenced_artifacts"][0]["kind"] =
        serde_json::Value::String("CheckedProofReport".to_string());
    let confused: ChcPdrProofEvidence =
        serde_json::from_value(encoded).expect("typed but role-confused proof decodes");
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(confused) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("role-confused reference must fail closed");
    };
    assert!(reasons.iter().any(|reason| reason.contains("typed proof relationship")));
}

#[test]
fn duplicate_required_artifact_role_fails_proof_classification() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let duplicate = proof
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == FullVerificationArtifactKind::SolverTranscript)
        .expect("solver transcript")
        .clone();
    proof.artifacts.push(duplicate);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };
    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("duplicate proof role must fail closed");
    };
    assert!(
        reasons
            .iter()
            .any(|reason| { reason.contains("solver transcript must occur exactly once, got 2") })
    );
}

#[test]
fn linked_chc_validity_candidate_is_complete_but_not_public_proof_grade() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let verdict =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof.clone()) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("caller-supplied CHC-validity bytes must remain reject-only");
    };
    assert_eq!(reasons, vec![CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()]);
    let candidate = validated_chc_pdr_candidate(&verdict)
        .expect("content-addressed candidate structure should validate separately");
    assert_eq!(candidate.proof_kind, ChcPdrProofKind::ChcValidity);
    assert!(accepted_chc_pdr_proof(&verdict).is_err());
    assert!(proof.metadata.normalized_input_hash.is_some());
    assert_eq!(proof.metadata.transcript_hashes.len(), 1);
    assert_eq!(proof.metadata.replay_log_hashes.len(), 1);
    assert_eq!(proof.metadata.checked_report_hashes.len(), 1);
    assert_eq!(
        proof.metadata.replay_check_status,
        Some(ProofReplayCheckStatus {
            replay: ProofReplayStatus::Unknown,
            check: ProofCheckStatus::Unknown,
        })
    );
    assert_eq!(
        proof
            .artifacts
            .iter()
            .find(|a| a.kind == FullVerificationArtifactKind::NormalizedInput)
            .and_then(|a| a.byte_len),
        Some(proof.obligation.normalized_input.len() as u64)
    );
    assert!(proof.artifacts.iter().any(|a| {
        a.kind == FullVerificationArtifactKind::SolverTranscript
            && a.byte_len == Some(b"solver transcript".len() as u64)
    }));
    assert!(proof.artifacts.iter().any(|a| {
        a.kind == FullVerificationArtifactKind::ReplayLog
            && a.byte_len == Some(b"replay log".len() as u64)
    }));
    assert!(proof.artifacts.iter().any(|a| {
        a.kind == FullVerificationArtifactKind::CheckedProofReport
            && a.byte_len == Some(b"checked proof report".len() as u64)
    }));
}

#[test]
fn arbitrary_linked_chc_validity_payloads_cannot_self_certify() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let verdict =
        FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof.clone()) };

    let rejection = accepted_chc_pdr_proof(&verdict)
        .expect_err("arbitrary nonempty transcript/replay/report bytes must not grant authority");
    assert_eq!(rejection.reasons, vec![CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()]);
    let candidate = validated_chc_pdr_candidate(&verdict)
        .expect("counterfeit-shaped bytes may be structurally valid without being authoritative");
    assert_eq!(candidate.normalized_input_hash, &proof.obligation.normalized_input_hash);
}

#[test]
fn accepted_native_typed_chc_pdr_proof_requires_native_metadata() {
    let proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("native candidate validation must require native metadata");

    assert_eq!(rejection.problem_kind, Some(FullVerificationProblemKind::ChcPdr));
    assert!(
        rejection
            .reasons
            .iter()
            .any(|reason| reason.contains("missing native typed CHC obligation metadata"))
    );
}

#[test]
fn validated_native_typed_chc_pdr_candidate_exposes_matching_bundle_metadata() {
    let proof = native_typed_proof(native_metadata(7, vec![0], "chc"));
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let accepted = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect("matching native candidate metadata should validate");

    let metadata = accepted.native_metadata.expect("accepted native proof carries metadata");
    assert_eq!(
        accepted.proof.obligation.obligation_id,
        "trust_ir-native-trust_mc-request-7-proof-0"
    );
    assert_eq!(metadata.native_request_id, 7);
    assert_eq!(metadata.proof_obligation_ids, vec![0]);
    assert_eq!(metadata.lineage_root_ids, vec![0]);
    assert_eq!(metadata.verification_mode, "chc");
    assert_eq!(
        metadata.compiler_facts_digest.as_ref().map(|digest| digest.algorithm.as_str()),
        Some("trust_ir-stable-v1")
    );
    assert_eq!(metadata.compiler_fact_counts.monomorphizations, 1);
    assert_eq!(metadata.compiler_fact_counts.obligation_sources, 1);
    let source = metadata
        .compiler_fact_sources
        .first()
        .expect("accepted native proof carries compiler fact source");
    assert_eq!(source.proof_obligation_id, 0);
    assert_eq!(source.cause, NativeObligationCauseMetadata::Translation);
    assert_eq!(
        source.fact_refs,
        vec![NativeCompilerFactReference::new(NativeCompilerFactKind::Monomorphization, 0)]
    );
    let rejection = accepted_native_typed_chc_pdr_proof(&verdict)
        .expect_err("valid native candidate metadata still cannot grant public authority");
    assert_eq!(rejection.reasons, vec![CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()]);
}

#[test]
fn accepted_native_typed_chc_pdr_proof_rejects_stale_metadata_identity() {
    let mut proof = native_typed_proof(native_metadata(7, vec![0], "chc"));
    proof.obligation.obligation_id = "trust_ir-native-trust_mc-request-8-proof-0".to_string();
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("stale native request metadata must fail closed");

    assert!(rejection.reasons.iter().any(|reason| {
        reason.contains("content-addressed proof-set binding")
            || reason.contains("does not match metadata identity")
    }));
}

#[test]
fn native_proof_artifact_set_cannot_be_transplanted_across_requests() {
    let mut proof = native_typed_proof(native_metadata(7, vec![0], "chc"));
    let original_binding = proof
        .artifacts
        .iter()
        .find_map(FullVerificationArtifact::proof_binding_id)
        .expect("native proof binding")
        .clone();
    let replacement = native_metadata(8, vec![0], "chc");
    proof.obligation.obligation_id = replacement.expected_obligation_id();
    proof.obligation.native_metadata = Some(replacement);

    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };
    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("request-7 artifacts must not transplant into request 8");
    assert!(
        rejection
            .reasons
            .iter()
            .any(|reason| { reason.contains("content-addressed proof-set binding") })
    );

    let fresh = native_typed_proof(native_metadata(8, vec![0], "chc"));
    let fresh_binding = fresh
        .artifacts
        .iter()
        .find_map(FullVerificationArtifact::proof_binding_id)
        .expect("fresh request-8 binding");
    assert_ne!(&original_binding, fresh_binding);
}

#[test]
fn accepted_native_typed_chc_pdr_proof_rejects_mismatched_compiler_fact_source() {
    let mut metadata = native_metadata(7, vec![0], "chc");
    metadata.compiler_fact_sources[0].proof_obligation_id = 99;
    let proof = native_typed_proof(metadata);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("stale compiler_facts source metadata must fail closed");

    assert!(
        rejection.reasons.iter().any(|reason| {
            reason.contains("compiler_facts source references proof obligation 99")
        })
    );
    assert!(
        rejection.reasons.iter().any(|reason| {
            reason.contains("missing compiler_facts source for proof obligation 0")
        })
    );
}

#[test]
fn accepted_native_typed_chc_pdr_proof_rejects_stale_compiler_fact_counts() {
    let mut metadata = native_metadata(7, vec![0], "chc");
    metadata.compiler_fact_counts.monomorphizations = 0;
    let proof = native_typed_proof(metadata);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("stale compiler_facts count metadata must fail closed");

    assert!(
        rejection
            .reasons
            .iter()
            .any(|reason| { reason.contains("references Monomorphization compiler fact 0") })
    );
}

#[test]
fn accepted_native_typed_chc_pdr_proof_rejects_out_of_range_compiler_fact_id() {
    let mut metadata = native_metadata(7, vec![0], "chc");
    metadata.compiler_fact_sources[0].fact_refs[0] =
        NativeCompilerFactReference::new(NativeCompilerFactKind::Monomorphization, 1);
    let proof = native_typed_proof(metadata);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("out-of-range compiler_facts id metadata must fail closed");

    assert!(rejection.reasons.iter().any(|reason| {
        reason.contains("references Monomorphization compiler fact 1")
            && reason.contains("reports only ids 0..0")
    }));
}

#[test]
fn accepted_native_typed_chc_pdr_proof_rejects_non_chc_pdr_admission_metadata() {
    let proof = native_typed_proof(native_metadata(7, vec![0], "bmc"));
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let rejection = validated_native_typed_chc_pdr_candidate(&verdict)
        .expect_err("non-CHC/PDR native metadata must not be accepted as CHC/PDR proof");

    assert!(
        rejection
            .reasons
            .iter()
            .any(|reason| reason.contains("verification mode must be `chc` or `pdr`"))
    );
}

#[test]
fn missing_checked_report_hash_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.checked_report_hashes.clear();
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("missing checked report metadata must not classify as proof-grade");
    };

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("missing checked proof report digest metadata"))
    );
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("missing checked proof report artifact matching"))
    );
}

#[test]
fn mismatched_checked_report_hash_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.checked_report_hashes = vec![EvidenceHash::sha256_bytes(b"different report")];
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("mismatched checked report metadata must not classify as proof-grade");
    };

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("missing checked proof report artifact matching"))
    );
}

#[test]
fn missing_normalized_input_artifact_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof
        .artifacts
        .retain(|artifact| artifact.kind != FullVerificationArtifactKind::NormalizedInput);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("missing normalized input artifact must not classify as proof-grade");
    };

    assert!(
        reasons.iter().any(|reason| reason.contains("missing normalized input artifact matching"))
    );
}

#[test]
fn missing_producer_identity_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.producer = None;
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("missing producer identity must not classify as proof-grade");
    };

    assert!(
        reasons.iter().any(|reason| reason.contains("missing proof evidence producer identity"))
    );
}

#[test]
fn missing_replay_log_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.replay_log_hashes.clear();
    proof.artifacts.retain(|artifact| artifact.kind != FullVerificationArtifactKind::ReplayLog);
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("missing replay evidence must not classify as proof-grade");
    };

    assert!(reasons.iter().any(|reason| reason.contains("missing replay log digest metadata")));
    assert!(reasons.iter().any(|reason| reason.contains("missing replay log artifact")));
}

#[test]
fn missing_replay_check_status_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.replay_check_status = None;
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("missing replay/check status must not classify as proof-grade");
    };

    assert!(reasons.iter().any(|reason| reason.contains("missing replay/check status metadata")));
}

#[test]
fn rejected_replay_check_status_fails_closed() {
    let mut proof = linked_candidate(ChcPdrProofKind::ChcValidity);
    proof.metadata.replay_check_status = Some(ProofReplayCheckStatus {
        replay: ProofReplayStatus::Replayed,
        check: ProofCheckStatus::Rejected,
    });
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("rejected replay/check status must not classify as proof-grade");
    };

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("candidate replay/check status must be Unknown/Unknown"))
    );
}

#[test]
fn diagnostic_bmc_success_is_not_proof_grade() {
    let verdict = FullVerificationVerdict::DiagnosticOnly {
        evidence: DiagnosticOnlyEvidence {
            problem_kind: FullVerificationProblemKind::DiagnosticBmc,
            summary: "bounded diagnostic BMC returned SAFE at depth 8".to_string(),
            artifacts: vec![FullVerificationArtifact::from_bytes(
                FullVerificationArtifactKind::DiagnosticTrace,
                "artifact://trust_mc/bmc.log",
                b"bmc diagnostic log",
            )],
        },
    };

    let ProofGradeVerdict::NotProofGrade { problem_kind, reasons } =
        classify_proof_grade_verdict(&verdict)
    else {
        panic!("diagnostic BMC must not classify as proof-grade");
    };

    assert_eq!(problem_kind, Some(FullVerificationProblemKind::DiagnosticBmc));
    assert!(reasons.iter().any(|reason| reason.contains("diagnostic-only evidence")));
    assert!(reasons.iter().any(|reason| reason.contains("diagnostic BMC is bounded evidence")));
}

#[test]
fn router_placeholder_chc_pdr_evidence_is_not_proof_grade() {
    let placeholder = MirDerivedChcPdrObligation::router_placeholder(
        "router-placeholder",
        MirObligationKind::UnreachableCode,
        "(set-logic HORN)\n(rule true)\n(query error)\n",
    );
    let proof = ChcPdrProofEvidence::proof_grade_from_bytes(
        ChcPdrProofKind::ChcValidity,
        placeholder,
        stats(),
        ("artifact://trust_mc/solver-transcript.smt2", b"solver transcript"),
        ("artifact://trust_mc/replay.jsonl", b"replay log"),
        ("artifact://trust_mc/checked-proof.json", b"checked proof report"),
    );
    let verdict = FullVerificationVerdict::Proved { evidence: FullProofEvidence::ChcPdr(proof) };

    let ProofGradeVerdict::NotProofGrade { reasons, .. } = classify_proof_grade_verdict(&verdict)
    else {
        panic!("router placeholders must fail closed");
    };

    assert!(reasons.iter().any(|reason| reason.contains("router placeholder")));
}

#[test]
fn content_addressed_manifest_cache_key_covers_native_artifact_digests() {
    let manifest =
        ContentAddressedEvidenceManifest::from_parts(ContentAddressedEvidenceManifestParts {
            input: digest_artifact(
                FullVerificationArtifactKind::CompilerInput,
                "trust_mc://native/input/trust_ir-module",
                b"typed trust_ir module",
            ),
            obligation_set: digest_artifact(
                FullVerificationArtifactKind::ObligationSet,
                "trust_mc://native/obligations",
                b"obligation-a\nobligation-b\n",
            ),
            typed_problem: Some(digest_artifact(
                FullVerificationArtifactKind::TypedChcProblem,
                "trust_mc://native/chc-problem",
                b"typed chc problem",
            )),
            smt_rendering: Some(digest_artifact(
                FullVerificationArtifactKind::SmtRendering,
                "artifact://trust_mc/debug.smt2",
                b"(set-logic HORN)\n",
            )),
            solver_binary: Some(digest_artifact(
                FullVerificationArtifactKind::SolverBinary,
                "ay://solver/bin",
                b"ay binary",
            )),
            solver_transcript: Some(digest_artifact(
                FullVerificationArtifactKind::SolverTranscript,
                "artifact://trust_mc/transcript.json",
                b"transcript",
            )),
            replay_log: Some(digest_artifact(
                FullVerificationArtifactKind::ReplayLog,
                "artifact://trust_mc/replay.json",
                b"replay",
            )),
            checked_report: Some(digest_artifact(
                FullVerificationArtifactKind::CheckedProofReport,
                "artifact://trust_mc/checked.json",
                b"checked",
            )),
            invariants: vec![digest_artifact(
                FullVerificationArtifactKind::PdrInvariantModel,
                "artifact://trust_mc/invariant.json",
                b"invariant",
            )],
            counterexamples: Vec::new(),
            options: digest_artifact(
                FullVerificationArtifactKind::VerificationOptions,
                "trust_mc://native/options",
                b"proof-mode=chc",
            ),
            resource_limits: digest_artifact(
                FullVerificationArtifactKind::ResourceLimits,
                "trust_mc://native/resource-limits",
                b"timeout-ms=1000",
            ),
        });

    assert_eq!(manifest.schema_version, ContentAddressedEvidenceManifest::SCHEMA_VERSION);
    assert_eq!(manifest.cache_key, manifest.recompute_cache_key());
    assert!(manifest.validate().is_ok());

    let mut mutated = manifest.clone();
    mutated.options = digest_artifact(
        FullVerificationArtifactKind::VerificationOptions,
        "trust_mc://native/options",
        b"proof-mode=pdr",
    );

    assert_ne!(manifest.recompute_cache_key(), mutated.recompute_cache_key());
    let errors = mutated.validate().expect_err("mutating options must stale the manifest key");
    assert!(errors.iter().any(|error| error.contains("cache key")));
}

fn cache_key_parts(proof_mode: &str) -> FullVerificationCacheKeyParts {
    FullVerificationCacheKeyParts {
        trust_mc_version: "0.1.0".to_string(),
        trust_mc_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
        trust_mc_dirty: false,
        ay_solver: digest_artifact(
            FullVerificationArtifactKind::SolverBinary,
            "ay://solver/ay-chc",
            b"ay-chc rev 954c174",
        ),
        trust_ir_snapshot: Some(digest_artifact(
            FullVerificationArtifactKind::CompilerInput,
            "trust_ir://snapshot/module",
            b"typed trust_ir module snapshot",
        )),
        proof_mode: proof_mode.to_string(),
        options: digest_artifact(
            FullVerificationArtifactKind::VerificationOptions,
            "trust_mc://native/options",
            format!("proof-mode={proof_mode}").as_bytes(),
        ),
        resource_limits: digest_artifact(
            FullVerificationArtifactKind::ResourceLimits,
            "trust_mc://native/resource-limits",
            b"timeout-ms=1000",
        ),
        normalized_input_hash: EvidenceHash::sha256_bytes(b"normalized typed CHC problem"),
        obligation_set_hash: EvidenceHash::sha256_bytes(b"obligation ids and spans"),
    }
}

#[test]
fn full_verification_cache_key_covers_identity_mode_and_obligation_parts() {
    let key = FullVerificationCacheKey::from_parts(cache_key_parts("chc"));

    assert_eq!(key.schema_version, FullVerificationCacheKey::SCHEMA_VERSION);
    assert_eq!(key.key, key.recompute_key());
    key.validate().expect("cache-key parts should validate");

    let mut changed_trust_mc = key.clone();
    changed_trust_mc.parts.trust_mc_commit = "fedcba9876543210fedcba9876543210fedcba98".to_string();
    assert_ne!(key.key, changed_trust_mc.recompute_key());

    let changed_mode = FullVerificationCacheKey::from_parts(cache_key_parts("pdr"));
    assert_ne!(key.key, changed_mode.key);

    let mut changed_obligations = key.clone();
    changed_obligations.parts.obligation_set_hash =
        EvidenceHash::sha256_bytes(b"different obligation ids and spans");
    assert_ne!(key.key, changed_obligations.recompute_key());
}

#[test]
fn full_verification_cache_key_rejects_stale_or_missing_components() {
    let mut key = FullVerificationCacheKey::from_parts(cache_key_parts("chc"));
    key.parts.resource_limits =
        FullVerificationArtifact::new(FullVerificationArtifactKind::ResourceLimits, "missing");

    let errors = key.validate().expect_err("missing resource digest and stale key must fail");
    assert!(errors.iter().any(|error| error.contains("resource_limits artifact is missing")));
    assert!(errors.iter().any(|error| error.contains("cache key digest does not match")));
}

#[test]
fn content_addressed_manifest_rejects_missing_required_digests() {
    let manifest =
        ContentAddressedEvidenceManifest::from_parts(ContentAddressedEvidenceManifestParts {
            input: FullVerificationArtifact::new(
                FullVerificationArtifactKind::CompilerInput,
                "trust_mc://native/input",
            ),
            obligation_set: digest_artifact(
                FullVerificationArtifactKind::ObligationSet,
                "trust_mc://native/obligations",
                b"obligation",
            ),
            typed_problem: None,
            smt_rendering: None,
            solver_binary: None,
            solver_transcript: None,
            replay_log: None,
            checked_report: None,
            invariants: Vec::new(),
            counterexamples: Vec::new(),
            options: digest_artifact(
                FullVerificationArtifactKind::VerificationOptions,
                "trust_mc://native/options",
                b"proof-mode=bmc",
            ),
            resource_limits: digest_artifact(
                FullVerificationArtifactKind::ResourceLimits,
                "trust_mc://native/resource-limits",
                b"timeout-ms=1000",
            ),
        });

    let errors = manifest.validate().expect_err("input digest is required");
    assert!(errors.iter().any(|error| error.contains("input artifact is missing digest")));
}

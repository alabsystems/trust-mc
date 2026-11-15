// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::{NativeVerificationRequest, TrustMcNativeRequest};

fn request(bundle: &trust_ir::NativeVerificationBundle) -> TrustMcNativeRequest {
    bundle
        .requests
        .iter()
        .find_map(|row| match row {
            NativeVerificationRequest::TrustMc(request) => Some(request.clone()),
            _ => None,
        })
        .unwrap()
}

fn caller() -> NativeTrustIrChcPdrRunner {
    NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(8)),
    )
}

#[test]
fn native_request_frame_caps_reach_the_actual_ay_configuration() {
    let bundle = compiler_style_safe_trust_ir_bundle();
    for limit in [None, Some(1), Some(37), Some(u32::MAX)] {
        let mut raw = request(&bundle);
        raw.options.chc.pdr.max_frames = limit;
        let config =
            trust_mc_trust_bmc::EffectiveNativeMcRequestConfig::from_request(&raw).unwrap();
        let options = config.solve_options(caller().solve_options());
        let actual =
            native_ay_pdr_config(&options, Duration::from_secs(2), Vec::new()).to_pdr_config();
        assert_eq!(
            actual.max_frames,
            limit
                .map(|value| value as usize)
                .unwrap_or_else(|| ay_chc::PdrConfig::production(false).max_frames)
        );
        assert_eq!(actual.solve_timeout, Some(Duration::from_secs(2)));
    }
}

#[test]
fn native_execution_configuration_separates_solves_but_preserves_equivalent_sharing() {
    for different in [false, true] {
        let mut bundle = compiler_style_safe_trust_ir_bundle();
        for row in &mut bundle.requests {
            if let NativeVerificationRequest::TrustMc(request) = row {
                request.options.chc.pdr.max_frames = Some(10);
            }
        }
        let mut sibling = request(&bundle);
        sibling.id = trust_ir::NativeRequestId::new(101);
        sibling.options.chc.pdr.max_frames = Some(if different { 11 } else { 10 });
        bundle.requests.push(NativeVerificationRequest::TrustMc(sibling));
        bundle.validate().unwrap();
        let (result, work) = caller().solve_bundle_native_proof_grade_with_work(&bundle).unwrap();
        assert_eq!(result.obligations.len(), 2, "{result:#?}");
        assert!(result.refused_requests.is_empty());
        assert_eq!(work.share_groups, if different { 2 } else { 1 }, "{work:?}");
        assert_eq!(work.solves_run, if different { 2 } else { 1 }, "{work:?}");
        for row in &result.obligations {
            row.verification.authorized_native_proof().unwrap();
        }
    }
}

#[test]
fn unsupported_native_options_do_not_discard_a_proved_sibling() {
    let mut bundle = compiler_style_safe_trust_ir_bundle();
    let mut unsupported = request(&bundle);
    unsupported.id = trust_ir::NativeRequestId::new(102);
    unsupported.options.chc.pdr.generalization = trust_ir::TrustMcPdrGeneralization::Interpolants;
    bundle.requests.push(NativeVerificationRequest::TrustMc(unsupported));
    bundle.validate().unwrap();
    let result = caller().solve_bundle_native_proof_grade(&bundle).unwrap();
    assert_eq!(result.obligations.len(), 1, "{result:#?}");
    result.obligations[0].verification.authorized_native_proof().unwrap();
    assert_eq!(result.refused_requests.len(), 1);
    assert_eq!(result.refused_requests[0].request_id, trust_ir::NativeRequestId::new(102));
    assert_eq!(result.refused_requests[0].field, "chc.pdr.generalization");
}

#[test]
fn changed_request_options_cannot_borrow_private_authorization() {
    let bundle = compiler_style_safe_trust_ir_bundle();
    let runner = caller();
    let rows = runner.translate_configured_obligations(&bundle).unwrap().obligations;
    let row = &rows[0];
    let options = row.request_config.solve_options(runner.solve_options());
    let solved = NativeTypedChcPdrRunner::with_options(options.clone())
        .solve_full_verification(row.obligation.clone())
        .unwrap();
    let mut changed = row.clone();
    let mut raw = request(&bundle);
    raw.options.chc.pdr.max_frames = Some(7);
    changed.request_config =
        trust_mc_trust_bmc::EffectiveNativeMcRequestConfig::from_request(&raw).unwrap();
    let changed_options = changed.request_config.solve_options(runner.solve_options());
    assert!(validate_native_request_execution(&row.obligation, &changed_options).is_err());
    assert!(validate_native_request_execution(&row.obligation, runner.solve_options()).is_err());
    let rejected = solved.with_private_native_bundle_authority(&changed, &changed_options, None);
    assert!(rejected.authorized_native_proof().is_err());
    let live = runner.solve_bundle_native_proof_grade(&bundle).unwrap();
    live.obligations[0].verification.authorized_native_proof().unwrap();
}

#[test]
fn native_refutation_replay_binds_request_options_without_binding_wall_time() {
    // The native bundle transport admits the grounding-checked bounded-unroll
    // class. This existing u8 overflow loop supplies that real false question;
    // an acyclic direct-SMT witness correctly stays outside its refuted channel.
    let mut bundle = loop_overflow_trust_ir_bundle();
    let runner = caller();
    let result = runner.solve_bundle_native_proof_grade(&bundle).unwrap();
    assert!(result.obligations.is_empty());
    assert_eq!(result.refuted.len(), 1, "{result:#?}");
    let row = &result.refuted[0];
    let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
        &row.verification.outcome.status
    else {
        panic!("exact false body retains a witness");
    };
    assert!(
        matches!(
            witness.verification,
            trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
        ),
        "the original false loop must use the admitted witness class"
    );
    let mut options = row.translated.request_config.solve_options(runner.solve_options());
    independently_replay_typed_chc_pdr_refutation_witness_with_options(
        &row.translated.obligation,
        &options,
        witness,
    )
    .unwrap();
    assert!(
        independently_replay_typed_chc_pdr_refutation_witness(
            &row.translated.obligation,
            options.engine,
            witness
        )
        .is_err()
    );
    let mut substituted = options.clone();
    substituted.native_request.as_mut().unwrap().request_digest.value = "00".repeat(32);
    assert!(
        independently_replay_typed_chc_pdr_refutation_witness_with_options(
            &row.translated.obligation,
            &substituted,
            witness
        )
        .is_err()
    );
    let semantic_identity =
        typed_chc_pdr_semantic_config_sha256_for_options(&options, row.verification.route);
    options.timeout = Some(Duration::from_secs(2));
    assert_eq!(
        typed_chc_pdr_semantic_config_sha256_for_options(&options, row.verification.route),
        semantic_identity
    );
    independently_replay_typed_chc_pdr_refutation_witness_with_options(
        &row.translated.obligation,
        &options,
        witness,
    )
    .unwrap();
    let expired = options.clone().with_timeout(Duration::ZERO);
    let rejected = independently_replay_typed_chc_pdr_refutation_witness_with_options(
        &row.translated.obligation,
        &expired,
        witness,
    )
    .unwrap_err();
    assert!(rejected.to_string().contains("ceiling expired"), "{rejected}");
    for request in &mut bundle.requests {
        if let NativeVerificationRequest::TrustMc(request) = request {
            request.options.chc.pdr.max_frames = Some(7);
        }
    }
    let changed = runner.translate_configured_obligations(&bundle).unwrap();
    let changed = &changed.obligations[0];
    let options = changed.request_config.solve_options(runner.solve_options());
    assert!(
        independently_replay_typed_chc_pdr_refutation_witness_with_options(
            &changed.obligation,
            &options,
            witness
        )
        .is_err()
    );
}

#[test]
fn an_unsupported_separate_function_cannot_poison_a_supported_sibling() {
    let mut bundle = mixed_outcome_trust_ir_bundle(true);
    let bad = bundle
        .module
        .functions
        .iter_mut()
        .find(|function| function.name == "trust_ir_native_unchecked_assert")
        .unwrap();
    let bad_id = bad.id;
    let block = &mut bad.blocks[0];
    let position = block
        .body
        .iter()
        .position(|node| matches!(node.inst, trust_ir::Inst::Assert { .. }))
        .unwrap();
    let trust_ir::Inst::Assert { cond, .. } = block.body[position].inst else { unreachable!() };
    block.body.insert(position, trust_ir::InstrNode::new(trust_ir::Inst::Assume { cond }));
    for row in &mut bundle.requests {
        if let NativeVerificationRequest::TrustMc(request) = row {
            if request.function == bad_id {
                request.options.chc.pdr.generalization =
                    trust_ir::TrustMcPdrGeneralization::Interpolants;
            }
        }
    }
    refresh_native_test_bundle_module_identity(&mut bundle);
    let result = caller().solve_bundle_native_proof_grade(&bundle).unwrap();
    assert_eq!(result.obligations.len(), 1, "{result:#?}");
    result.obligations[0].verification.authorized_native_proof().unwrap();
    assert_eq!(result.refused_requests.len(), 1);
    assert_eq!(result.refused_requests[0].function, bad_id);
    // Once that body is a supported root, its untrusted assumption still
    // refuses proof-grade admission. No guard is weakened for a real question.
    for row in &mut bundle.requests {
        if let NativeVerificationRequest::TrustMc(request) = row {
            request.options.chc.pdr.generalization = trust_ir::TrustMcPdrGeneralization::Cubes;
        }
    }
    assert!(caller().solve_bundle_native_proof_grade(&bundle).is_err());
}

#[test]
fn generic_semantic_configuration_retains_legacy_bytes() {
    for engine in [trust_mc_core::ChcPdrEngine::Pdr, trust_mc_core::ChcPdrEngine::AdaptivePortfolio]
    {
        for route in [TypedChcPdrRoute::PdrProof, TypedChcPdrRoute::TriviallySafe] {
            let options = trust_mc_core::ChcPdrSolveOptions::default()
                .with_engine(engine)
                .with_timeout(Duration::from_millis(1))
                .with_proof_certificate(true);
            let expected = format!(
                "{{\"schema\":\"trust_mc.typed-chc-pdr-semantic-config/v1\",\"engine\":\"{engine:?}\",\"route\":\"{route:?}\",\"typed_lowering\":\"typed-chc-ay/exact-or-reject/v1\"}}"
            );
            assert_eq!(typed_chc_pdr_semantic_config_for_options(&options, route), expected);
            assert_eq!(
                typed_chc_pdr_semantic_config_sha256_for_options(&options, route),
                typed_chc_pdr_semantic_config_sha256(engine, route)
            );
        }
    }
}

#[test]
fn native_request_metadata_epoch_preserves_generic_bytes_and_refuses_erased_bindings() {
    let row = caller()
        .translate_configured_obligations(&compiler_style_safe_trust_ir_bundle())
        .unwrap()
        .obligations
        .remove(0);
    let metadata = row.obligation.native_metadata.as_ref().unwrap();
    assert_eq!(
        metadata.schema_version,
        trust_mc_core::NativeTypedChcObligationMetadata::REQUEST_CONFIG_SCHEMA_VERSION
    );
    let mut erased = metadata.clone();
    erased.request_config = None;
    assert!(erased.validate_for_obligation_id(&row.obligation.obligation_id).is_err());
    erased.schema_version = trust_mc_core::NativeTypedChcObligationMetadata::SCHEMA_VERSION;
    assert_eq!(erased.schema_version, 3);
    erased.validate_for_obligation_id(&row.obligation.obligation_id).unwrap();
    let wire = serde_json::to_value(&erased).unwrap();
    assert!(wire.get("request_config").is_none());
    assert_eq!(wire["schema_version"], 3);
    assert_eq!(erased.with_request_config(row.request_config.binding().clone()), *metadata);
}

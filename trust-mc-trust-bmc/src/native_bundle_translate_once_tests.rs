// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A native bundle's CHC/PDR rows: one per request, one translation per
//! function.
//!
//! The translator takes no obligation input, so every request on a function
//! used to carry a byte-identical copy of the same whole-function CHC (measured
//! on the ever-init family: 8 of 8 rows at N=1, 14 of 14 at N=2), translated
//! afresh per request — `obligations × function size` work and memory. These
//! tests pin that the function is now translated once and shared, that each
//! row still carries exactly the CHC a per-request translation produces, and
//! that each row's identity — obligation id, kind, native metadata, unmodeled
//! and not-refuted lists — is the per-request identity it always was.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use trust_ir::{
    FuncId, Module, NativeAdapterInput, NativeAssertionId, NativeBundleProducer,
    NativeObligationCause, NativeObligationSource, NativeRequestId, NativeVerificationBundle,
    NativeVerificationRequest, ObligationKind, ProofFormula, ProofId, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage, TrustMcNativeRequest, TrustMcVerificationMode,
};
use trust_mc_core::NativeTypedChcObligationMetadata;

use super::{
    bundle_producer_name, native_compiler_fact_counts, native_obligation_compiler_facts_row,
    native_obligation_id, native_obligations_not_refuted_by_a_counterexample,
    native_replay_context_metadata, native_replay_identity, native_unmodeled_obligations,
    proof_digest_metadata, trust_mc_chc_pdr_obligations_from_native_bundle_with_work,
    trust_mc_verification_mode_name,
};
use crate::tests::{
    native_digest, native_obligation_identity, native_trust_mc_bundle,
    native_trust_mc_bundle_with_fail_closed_lowering, trust_mc_request_options,
    trust_mc_request_provenance,
};
use crate::translate::TranslateOptions;
use crate::translate_chc::liveness_tests::ever_init_family;
use crate::translate_chc::trust_ir_function_to_chc_translation_output;

#[test]
fn malformed_module_is_refused_before_native_request_translation() {
    let mut mb = trust_ir_build::ModuleBuilder::new("invalid_native_chc_input");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let no = fb.bool_const(false);
    fb.assume(no);
    let yes = fb.bool_const(true);
    fb.assert(yes);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().unwrap();
    let function = module.functions[0].id;
    let trust_ir::Inst::Assert { cond, .. } = &mut module.functions[0].blocks[0].body[3].inst
    else {
        panic!("assert fixture")
    };
    *cond = trust_ir::ValueId::new(999);
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    // Actual transport/request identities remain coherent; the missing boundary
    // is canonical IR validity, not a fabricated source or function owner.
    let bundle = one_request_per_obligation(module, function, 8);
    bundle.validate().expect("malformed IR still has coherent bundle transport");
    let error = trust_mc_chc_pdr_obligations_from_native_bundle_with_work(
        &bundle,
        &TranslateOptions::default(),
    )
    .expect_err("no native CHC rows may escape for malformed IR");
    assert!(matches!(error, super::NativeTrustMcBundleError::InvalidModule(_)));
}

/// `bundle` plus one more CHC request for each obligation list in `extra`,
/// on the function its existing trust_mc request names, with fresh ids.
fn with_requests(
    mut bundle: NativeVerificationBundle,
    extra: &[Vec<u32>],
) -> NativeVerificationBundle {
    let template = chc_requests(&bundle)[0].clone();
    let first_free =
        bundle.requests.iter().map(|request| request.id().index()).max().unwrap_or(0) + 1;
    for (id, obligations) in (first_free..).zip(extra) {
        let mut request = template.clone();
        request.id = NativeRequestId::new(id);
        request.obligations = obligations.iter().copied().map(ProofId::new).collect();
        keep_only_requested_replay_atoms(&mut request);
        bundle.requests.push(NativeVerificationRequest::TrustMc(request));
    }
    bundle
}

/// A request's replay context may only name obligations the request asks.
fn keep_only_requested_replay_atoms(request: &mut TrustMcNativeRequest) {
    let requested = request.obligations.clone();
    request
        .provenance
        .replay_context
        .atoms
        .retain(|atom| atom.obligation.is_none_or(|obligation| requested.contains(&obligation)));
}

/// A valid native bundle around `function` of `module`, declaring `obligations`
/// function-scoped panic-freedom obligations and asking one CHC request per
/// obligation — the shape the compiler emits (one request per bound public
/// obligation, all on the same function).
pub(crate) fn one_request_per_obligation(
    mut module: Module,
    function: FuncId,
    obligations: u32,
) -> NativeVerificationBundle {
    let source_digest = native_digest(0x71);
    let file = module.intern_file("generated.rs").expect("Module::intern_file: test fixture");
    for index in 0..obligations {
        let mut obligation = ProofObligation::new(
            ProofId::new(index),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            format!("generated obligation {index}"),
        )
        .with_formula(ProofFormula::smtlib2(format!("generated_ok_{index}"), "Bool"))
        .with_source(native_obligation_identity(
            file,
            10 + index,
            5,
            index,
            &format!("vc:generated:{index}"),
            format!("generated:{index}").as_bytes(),
        ));
        obligation.function = Some(function);
        module.proof_obligations.push(obligation);
    }
    let digest = module.stable_digest();
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust-ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        digest,
    );
    node.obligations.extend((0..obligations).map(ProofId::new));
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![node],
        roots: vec![ProofLineageId::new(0)],
    };
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        digest,
        module,
        lineage,
    );
    for index in 0..obligations {
        bundle.compiler_facts.obligation_sources.push(NativeObligationSource {
            obligation: ProofId::new(index),
            public_obligation_id: format!("vc:generated:{index}"),
            function: Some(function),
            span: Some(trust_ir::SourceSpan { file, line: 10 + index, col: 5 }),
            assertion_id: Some(NativeAssertionId::new(index)),
            cause: NativeObligationCause::Panic,
            monomorphization: None,
            facts: Vec::new(),
        });
        let mut request = TrustMcNativeRequest {
            id: NativeRequestId::new(index + 1),
            mode: TrustMcVerificationMode::Chc,
            function,
            obligations: vec![ProofId::new(index)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: trust_mc_request_options(TrustMcVerificationMode::Chc),
            diagnostics: Default::default(),
            provenance: trust_mc_request_provenance(TrustMcVerificationMode::Chc),
        };
        // The shared fixture's replay atoms describe the fixture's own obligation.
        request.provenance.replay_context.atoms.clear();
        bundle.requests.push(NativeVerificationRequest::TrustMc(request));
    }
    bundle
}

/// The bundles every test below runs on: the crate's native fixture asked
/// several questions of its one function (clean and fail-closed lowering), and
/// the ever-init family with one request per obligation.
fn corpus() -> Vec<(String, NativeVerificationBundle)> {
    let mut corpus = vec![
        (
            "fixture".to_owned(),
            with_requests(
                native_trust_mc_bundle(TrustMcVerificationMode::Chc),
                &[vec![0], vec![1], vec![0, 1]],
            ),
        ),
        (
            "fixture(fail-closed)".to_owned(),
            with_requests(
                native_trust_mc_bundle_with_fail_closed_lowering(TrustMcVerificationMode::Chc),
                &[vec![0], vec![1]],
            ),
        ),
    ];
    for n in [1, 2, 4] {
        let (module, function) = ever_init_family(n);
        corpus.push((
            format!("ever_init({n})"),
            one_request_per_obligation(module, function, 6 * n as u32 + 2),
        ));
    }
    corpus
}

fn chc_requests(bundle: &NativeVerificationBundle) -> Vec<&trust_ir::TrustMcNativeRequest> {
    bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustMc(request)
                if matches!(
                    request.mode,
                    TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr
                ) =>
            {
                Some(request)
            }
            _ => None,
        })
        .collect()
}

fn instruction_count(bundle: &NativeVerificationBundle, function: FuncId) -> u64 {
    let func = bundle.module.function_by_id(function).expect("requested function");
    func.blocks.iter().map(|block| block.body.len() as u64).sum()
}

/// The metadata the per-request code built before the translation was shared,
/// restated VERBATIM from that code (digests recomputed per request, compiler
/// facts filtered from every source row, reasons from the full diagnostic list).
fn per_request_reference_metadata(
    bundle: &NativeVerificationBundle,
    request: &trust_ir::TrustMcNativeRequest,
) -> NativeTypedChcObligationMetadata {
    let (adapter_input, source_digest) = match bundle.input {
        trust_ir::NativeAdapterInput::RustMir { body_digest } => {
            ("rust-mir", Some(proof_digest_metadata(body_digest)))
        }
        trust_ir::NativeAdapterInput::RustThir { source_digest } => {
            ("rust-thir", Some(proof_digest_metadata(source_digest)))
        }
        trust_ir::NativeAdapterInput::TrustIrModule => ("trust_ir-module", None),
    };
    let metadata = NativeTypedChcObligationMetadata::new(
        bundle_producer_name(bundle.producer),
        adapter_input,
        source_digest,
        proof_digest_metadata(bundle.trust_ir_module_digest),
        proof_digest_metadata(bundle.lineage.stable_digest()),
        request.id.index(),
        trust_mc_verification_mode_name(request.mode),
        request.function.index(),
        request.obligations.iter().map(|id| id.index()).collect(),
        request.lineage_roots.iter().map(|id| id.index()).collect(),
    )
    .with_compiler_facts(
        proof_digest_metadata(bundle.compiler_facts.stable_digest()),
        native_compiler_fact_counts(&bundle.compiler_facts),
        bundle
            .compiler_facts
            .obligation_sources
            .iter()
            .filter(|source| request.obligations.contains(&source.obligation))
            .map(native_obligation_compiler_facts_row)
            .collect(),
    )
    .with_structural_reachability_complete(true)
    .with_request_config(
        crate::EffectiveNativeMcRequestConfig::from_request(request).unwrap().binding().clone(),
    );
    let metadata = if let Some(replay_identity) =
        native_replay_identity(request.provenance.replay_identity())
    {
        metadata.with_replay_metadata(
            replay_identity,
            native_replay_context_metadata(request.provenance.replay_context()),
        )
    } else {
        metadata
    };
    let output = trust_ir_function_to_chc_translation_output(
        &bundle.module,
        request.function,
        &TranslateOptions::default(),
    )
    .expect("requested function translates");
    metadata
        .with_fail_closed_lowering_site_count(
            u32::try_from(output.diagnostics.len()).unwrap_or(u32::MAX),
        )
        .with_fail_closed_lowering_reasons(output.diagnostics.iter().map(|d| d.reason.label()))
        .with_inductive_hypothesis_site_count(
            u32::try_from(output.inductive_hypothesis_sites.len()).unwrap_or(u32::MAX),
        )
}

#[test]
fn each_function_is_translated_once_and_its_rows_share_it() {
    for (name, bundle) in corpus() {
        let requests = chc_requests(&bundle);
        let (rows, work) = trust_mc_chc_pdr_obligations_from_native_bundle_with_work(
            &bundle,
            &TranslateOptions::default(),
        )
        .expect("fixture bundle translates");
        let functions: BTreeSet<FuncId> = requests.iter().map(|request| request.function).collect();
        assert!(
            requests.len() > functions.len(),
            "{name}: the fixture must ask several questions of one function"
        );
        assert_eq!(rows.len(), requests.len(), "{name}: one row per request");
        assert_eq!(work.requests, requests.len() as u64, "{name}");
        assert_eq!(
            work.functions_translated,
            functions.len() as u64,
            "{name}: one translation per function"
        );
        assert_eq!(
            work.translation.instructions_translated,
            functions.iter().map(|function| instruction_count(&bundle, *function)).sum::<u64>(),
            "{name}: each instruction of each requested function is translated once"
        );
        assert_eq!(work.translation.carried_value_misses, 0, "{name}");

        let mut first_by_function: BTreeMap<FuncId, usize> = BTreeMap::new();
        for (index, row) in rows.iter().enumerate() {
            let first = &rows[*first_by_function.entry(row.function).or_insert(index)];
            assert!(
                Arc::ptr_eq(&row.obligation.vc, &first.obligation.vc),
                "{name}: row {index} shares its function's CHC"
            );
            assert!(
                Arc::ptr_eq(&row.diagnostics, &first.diagnostics),
                "{name}: row {index} shares its diagnostics"
            );

            // The shared CHC is exactly what a fresh per-request translation emits.
            let fresh = trust_ir_function_to_chc_translation_output(
                &bundle.module,
                row.function,
                &TranslateOptions::default(),
            )
            .expect("requested function translates");
            assert_eq!(
                row.obligation.vc.to_horn_smt2(),
                fresh.vc.to_horn_smt2(),
                "{name}: row {index}"
            );
            assert_eq!(
                row.diagnostics.as_ref(),
                fresh.diagnostics.as_slice(),
                "{name}: row {index}"
            );
        }
    }
}

#[test]
fn every_row_keeps_its_own_per_request_identity() {
    for (name, bundle) in corpus() {
        let requests = chc_requests(&bundle);
        let (rows, _) = trust_mc_chc_pdr_obligations_from_native_bundle_with_work(
            &bundle,
            &TranslateOptions::default(),
        )
        .expect("fixture bundle translates");
        let mut ids = BTreeSet::new();
        for (row, request) in rows.iter().zip(&requests) {
            assert_eq!(row.request_id, request.id, "{name}");
            assert_eq!(row.function, request.function, "{name}");
            assert_eq!(row.obligations, request.obligations, "{name}");
            assert_eq!(row.lineage_roots, request.lineage_roots, "{name}");
            assert_eq!(
                row.obligation.obligation_id,
                native_obligation_id(request.id, &request.obligations),
                "{name}"
            );
            assert!(
                ids.insert(row.obligation.obligation_id.clone()),
                "{name}: obligation ids stay distinct"
            );
            assert_eq!(
                row.obligation.native_metadata.as_ref(),
                Some(&per_request_reference_metadata(&bundle, request)),
                "{name}: request {}",
                request.id.index()
            );
            assert_eq!(
                row.unmodeled_obligations,
                native_unmodeled_obligations(
                    &bundle.module,
                    request.function,
                    &request.obligations
                ),
                "{name}"
            );
            assert_eq!(
                row.not_refuted_by_a_counterexample,
                native_obligations_not_refuted_by_a_counterexample(
                    &bundle.module,
                    request.function,
                    &request.obligations,
                ),
                "{name}"
            );
            row.obligation.validate().expect("row validates");
        }
    }
}

#[test]
fn translation_work_does_not_grow_with_the_number_of_requests() {
    let (module, function) = ever_init_family(4);
    let size = {
        let func = module.function_by_id(function).expect("generated function");
        func.blocks.iter().map(|block| block.body.len() as u64).sum::<u64>()
    };
    let mut baseline = None;
    for requests in [1u32, 8, 64, 256] {
        let bundle = one_request_per_obligation(module.clone(), function, requests);
        let (rows, work) = trust_mc_chc_pdr_obligations_from_native_bundle_with_work(
            &bundle,
            &TranslateOptions::default(),
        )
        .expect("generated bundle translates");
        assert_eq!(rows.len(), requests as usize);
        assert_eq!(work.requests, u64::from(requests));
        assert_eq!(work.functions_translated, 1, "requests={requests}");
        assert_eq!(work.translation.instructions_translated, size, "requests={requests}");
        let first = &rows[0].obligation.vc;
        assert!(rows.iter().all(|row| Arc::ptr_eq(&row.obligation.vc, first)));
        // Identical translation work at every request count.
        let baseline = *baseline.get_or_insert(work.translation);
        assert_eq!(work.translation, baseline, "requests={requests}");
    }
}

#[test]
fn obligation_ids_resolve_to_their_first_declaration() {
    // `ObligationIndex` must answer what the front-to-back `find` it replaced
    // answered, a repeated id included.
    let (module, function) = ever_init_family(1);
    let mut bundle = one_request_per_obligation(module, function, 4);
    let duplicate = bundle.module.proof_obligations[2].clone();
    let mut shadow = duplicate.clone();
    shadow.kind = ObligationKind::Postcondition;
    bundle.module.proof_obligations.push(shadow);
    let index = super::ObligationIndex::new(&bundle.module);
    for obligation in &bundle.module.proof_obligations {
        let first = bundle.module.proof_obligations.iter().find(|o| o.id == obligation.id);
        assert!(std::ptr::eq(
            index.get(obligation.id).expect("declared"),
            first.expect("declared")
        ));
    }
    assert_eq!(index.get(duplicate.id).map(|o| o.kind.clone()), Some(duplicate.kind));
    assert!(index.get(ProofId::new(u32::MAX)).is_none());
}

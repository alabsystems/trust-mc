// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for trust_ir → BmcVc translation.
//!
//! Uses `trust_ir-build` to construct test programs, then verifies the
//! generated VCs match expectations.

use ay_bindings::{Expr, ExprValue};
use trust_ir::dialect::{AttrValue, trust_rust};
use trust_ir::inst::{AllocOrigin, BinOp, CastOp, ICmpOp, OverflowOp, SwitchCase, UnOp};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::{FatPtrKind, FieldDef, FuncTy, StructDef, Ty};
use trust_ir::value::StructId;
use trust_ir::{
    NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactId,
    NativeCompilerFactRef, NativeCompilerFacts, NativeMonomorphizationFact,
    NativeMonomorphizationId, NativeObligationCause, NativeObligationSource, NativeReplayAtom,
    NativeReplayAtomId, NativeReplayContext, NativeRequestId, NativeRequestProvenance,
    NativeToolIdentity, NativeVerificationBundle, NativeVerificationRequest, NativeVerifierSuite,
    ObligationKind, ProofDigest, ProofFormula, ProofId, ProofLineageId, ProofLineageManifest,
    ProofLineageNode, ProofObligation, ProofObligationSourceIdentity, ProofObligationSourceRange,
    ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
    PublicObligationIdentity, TrustMcNativeRequest, TrustMcVerificationMode, TrustWpNativeRequest,
    TrustWpVerificationMode,
};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::violation::PropertyKind;

use crate::translate::{TranslateOptions, const_to_expr, trust_ir_to_bmc_vc, ty_to_sort};
use crate::{
    NativeTrustMcBundleError, SEMANTICS_COVERAGE, SemanticsFamily, SemanticsStatus,
    TrustIrChcUnsupportedReason, coverage_for_family, family_for_inst,
    trust_ir_function_to_chc_translation_output, trust_ir_to_chc_translation_outputs,
    trust_ir_to_chc_vc, trust_mc_bmc_vcs_from_native_bundle,
    trust_mc_chc_pdr_obligations_from_native_bundle,
};

#[test]
fn semantics_coverage_matrix_documents_fail_closed_families() {
    assert!(
        SEMANTICS_COVERAGE.len() >= 11,
        "coverage matrix should track all active trust_ir semantic families"
    );

    for row in SEMANTICS_COVERAGE {
        assert_eq!(coverage_for_family(row.family), row);
    }

    assert_eq!(coverage_for_family(SemanticsFamily::Casts).status, SemanticsStatus::Conservative);
    assert_eq!(
        coverage_for_family(SemanticsFamily::Aggregates).status,
        SemanticsStatus::Conservative
    );
    assert_eq!(
        coverage_for_family(SemanticsFamily::Floats).status,
        SemanticsStatus::FailClosedUnsupported
    );
    assert_eq!(
        coverage_for_family(SemanticsFamily::ProofAnnotations).status,
        SemanticsStatus::Conservative
    );
    assert_eq!(
        coverage_for_family(SemanticsFamily::ControlFlow).status,
        SemanticsStatus::Conservative
    );
}

#[test]
fn pointer_metadata_instructions_are_memory_provenance_family() {
    let ptr_ty = Ty::FatPtr(FatPtrKind::Str);

    assert_eq!(
        family_for_inst(&trust_ir::Inst::PtrData {
            ptr_ty: ptr_ty.clone(),
            ptr: trust_ir::value::ValueId::new(0),
        }),
        SemanticsFamily::MemoryProvenance
    );
    assert_eq!(
        family_for_inst(&trust_ir::Inst::PtrMetadata {
            ptr_ty: ptr_ty.clone(),
            metadata_ty: Ty::U64,
            ptr: trust_ir::value::ValueId::new(0),
        }),
        SemanticsFamily::MemoryProvenance
    );
    assert_eq!(
        family_for_inst(&trust_ir::Inst::PtrFromParts {
            ptr_ty,
            metadata_ty: Ty::U64,
            data: trust_ir::value::ValueId::new(0),
            metadata: trust_ir::value::ValueId::new(1),
        }),
        SemanticsFamily::MemoryProvenance
    );
}

#[test]
fn heap_and_global_address_instructions_are_memory_provenance_family() {
    assert_eq!(
        family_for_inst(&trust_ir::Inst::HeapAlloc {
            ty: Ty::I32,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        }),
        SemanticsFamily::MemoryProvenance
    );
    assert_eq!(
        family_for_inst(&trust_ir::Inst::GlobalAddr { global: trust_ir::value::GlobalId::new(0) }),
        SemanticsFamily::MemoryProvenance
    );
}

#[test]
fn ty_to_sort_maps_f16_to_bv16() {
    assert_eq!(ty_to_sort(&Ty::F16).bitvec_width(), Some(16));
}

#[test]
fn ty_to_sort_maps_vector_to_packed_bitvec() {
    assert_eq!(ty_to_sort(&Ty::Vector(Box::new(Ty::I32), 4)).bitvec_width(), Some(128));
    assert_eq!(ty_to_sort(&Ty::Vector(Box::new(Ty::Bool), 4)).bitvec_width(), Some(4));
}

#[test]
fn const_to_expr_packs_vector_lanes_with_lane_zero_low_bits() {
    let ty = Ty::Vector(Box::new(Ty::U8), 4);
    let value = trust_ir::constant::Constant::Vector(vec![
        trust_ir::constant::Constant::Int(0x11),
        trust_ir::constant::Constant::Int(0x22),
        trust_ir::constant::Constant::Int(0x33),
        trust_ir::constant::Constant::Int(0x44),
    ]);

    let expr = const_to_expr(&ty, &value).expect("integer vector constants pack exactly");
    assert_eq!(expr.sort().bitvec_width(), Some(32));
    assert_eq!(
        bitvec_concat_leaves(&expr),
        vec![
            ("68".to_owned(), 8),
            ("51".to_owned(), 8),
            ("34".to_owned(), 8),
            ("17".to_owned(), 8),
        ]
    );
}

#[test]
fn const_to_expr_packs_bool_vector_as_one_bit_lanes() {
    let ty = Ty::Vector(Box::new(Ty::Bool), 4);
    let value = trust_ir::constant::Constant::Vector(vec![
        trust_ir::constant::Constant::Bool(true),
        trust_ir::constant::Constant::Bool(false),
        trust_ir::constant::Constant::Bool(true),
        trust_ir::constant::Constant::Bool(true),
    ]);

    let expr = const_to_expr(&ty, &value).expect("bool vector constants pack exactly");
    assert_eq!(expr.sort().bitvec_width(), Some(4));
    assert_eq!(
        bitvec_concat_leaves(&expr),
        vec![("1".to_owned(), 1), ("1".to_owned(), 1), ("0".to_owned(), 1), ("1".to_owned(), 1),]
    );
}

fn bitvec_concat_leaves(expr: &Expr) -> Vec<(String, u32)> {
    let mut leaves = Vec::new();
    collect_bitvec_concat_leaves(expr, &mut leaves);
    leaves
}

fn collect_bitvec_concat_leaves(expr: &Expr, leaves: &mut Vec<(String, u32)>) {
    match expr.value() {
        ExprValue::BvConcat(lhs, rhs) => {
            collect_bitvec_concat_leaves(lhs, leaves);
            collect_bitvec_concat_leaves(rhs, leaves);
        }
        ExprValue::BitVecConst { value, width } => {
            leaves.push((value.to_string(), *width));
        }
        other => panic!("expected bitvector concat leaf, got {other:?}"),
    }
}

fn native_digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn native_trust_mc_bundle(mode: TrustMcVerificationMode) -> NativeVerificationBundle {
    let source_digest = native_digest(0x51);

    let mut mb = ModuleBuilder::new("native_trust_mc_bundle");
    let assert_ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    {
        let mut fb = mb.function("non_trust_mc_assert", assert_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
    }

    let add_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("trust_mc_checked_add", add_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let lhs = fb.add_block_param(entry, Ty::I32);
        let rhs = fb.add_block_param(entry, Ty::I32);
        let sum = fb.add(Ty::I32, lhs, rhs);
        fb.ret(vec![sum]);
        fb.build();
    }

    let mut module = mb.build();
    let source_file = module.intern_file("native_trust_mc_bundle.rs");
    let trust_mc_function = module
        .functions
        .iter()
        .find(|func| func.name == "trust_mc_checked_add")
        .expect("native bundle fixture includes the trust_mc target function")
        .id;

    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "native unrequested sidecar obligation",
        )
        .with_formula(ProofFormula::smtlib2("native_sidecar_ok", "Bool"))
        .with_source(native_obligation_identity(
            source_file,
            10,
            5,
            0,
            "vc:trust-mc:memory:0",
            b"memory:0",
        )),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "native trust_mc checked_add obligation",
        )
        .with_formula(ProofFormula::smtlib2("trust_mc_checked_add_ok", "Bool"))
        .with_source(native_obligation_identity(
            source_file,
            20,
            9,
            1,
            "vc:trust-mc:translation:1",
            b"translation:1",
        )),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(2),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "native trust_wp precondition obligation",
        )
        .with_formula(ProofFormula::smtlib2("trust_wp_precondition_ok", "Bool"))
        .with_source(native_obligation_identity(
            source_file,
            30,
            13,
            2,
            "vc:trust-mc:precondition:2",
            b"precondition:2",
        )),
    );

    let trust_ir_module_digest = module.stable_digest();

    let mut lineage_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust-ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        trust_ir_module_digest,
    );
    lineage_node.obligations.extend([ProofId::new(0), ProofId::new(1), ProofId::new(2)]);

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        trust_ir_module_digest,
        module,
        lineage,
    );
    bundle.compiler_facts = NativeCompilerFacts {
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "native_trust_mc_bundle::trust_mc_checked_add::<i32>".to_owned(),
            symbol: "_RNvNtC6native16trust_mc_checked_add_i32".to_owned(),
            generic_args: Vec::new(),
            function: Some(trust_mc_function),
            stable_digest: native_digest(0x53),
        }],
        obligation_sources: vec![
            NativeObligationSource {
                obligation: ProofId::new(0),
                public_obligation_id: "vc:trust-mc:memory:0".to_string(),
                function: Some(trust_mc_function),
                span: Some(trust_ir::SourceSpan { file: 0, line: 10, col: 5 }),
                assertion_id: Some(NativeAssertionId::new(0)),
                cause: NativeObligationCause::Other,
                monomorphization: None,
                facts: Vec::new(),
            },
            NativeObligationSource {
                obligation: ProofId::new(1),
                public_obligation_id: "vc:trust-mc:translation:1".to_string(),
                function: Some(trust_mc_function),
                span: Some(trust_ir::SourceSpan { file: 0, line: 20, col: 9 }),
                assertion_id: Some(NativeAssertionId::new(1)),
                cause: NativeObligationCause::Translation,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            },
            NativeObligationSource {
                obligation: ProofId::new(2),
                public_obligation_id: "vc:trust-mc:precondition:2".to_string(),
                function: Some(trust_mc_function),
                span: Some(trust_ir::SourceSpan { file: 0, line: 30, col: 13 }),
                assertion_id: Some(NativeAssertionId::new(2)),
                cause: NativeObligationCause::Precondition,
                monomorphization: Some(NativeMonomorphizationId::new(0)),
                facts: vec![NativeCompilerFactRef::Monomorphization(
                    NativeMonomorphizationId::new(0),
                )],
            },
        ],
        ..NativeCompilerFacts::default()
    };
    bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(1),
        mode,
        function: trust_mc_function,
        obligations: vec![ProofId::new(1)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: trust_mc_request_options(mode),
        diagnostics: Default::default(),
        provenance: trust_mc_request_provenance(mode),
    }));
    bundle.requests.push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(2),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function: trust_mc_function,
        obligations: vec![ProofId::new(2)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: Default::default(),
        diagnostics: Default::default(),
        provenance: NativeRequestProvenance::trust_wp(
            NativeToolIdentity::new("trust_wp").with_version("wp-v1"),
        )
        .with_solver(NativeToolIdentity::new("trust_wp-vcgen").with_version("wp-v1"))
        .with_replay(native_replay_identity("trust_wp", 0x63)),
    }));
    bundle
}

fn native_obligation_identity(
    file: u32,
    line: u32,
    col: u32,
    assertion: u32,
    public_obligation_id: &str,
    semantic_payload: &[u8],
) -> ProofObligationSourceIdentity {
    ProofObligationSourceIdentity::new(
        "rust:native_trust_mc_bundle::trust_mc_checked_add",
        format!("assertion:{assertion}"),
    )
    .with_range(ProofObligationSourceRange {
        file,
        start_line: line,
        start_col: col,
        end_line: line,
        end_col: col + 1,
    })
    .with_public(PublicObligationIdentity {
        obligation_id: public_obligation_id.to_owned(),
        semantic_digest: ProofDigest::sha256_domain(
            "trust-mc.test.native-obligation.v1",
            semantic_payload,
        ),
    })
}

fn refresh_native_trust_mc_bundle_module_identity(bundle: &mut NativeVerificationBundle) {
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = digest;
        }
    }
}

fn native_trust_mc_request(bundle: &NativeVerificationBundle) -> &TrustMcNativeRequest {
    bundle
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("native fixture includes a trust_mc request")
}

fn native_trust_mc_request_mut(bundle: &mut NativeVerificationBundle) -> &mut TrustMcNativeRequest {
    bundle
        .requests
        .iter_mut()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request),
            _ => None,
        })
        .expect("native fixture includes a trust_mc request")
}

fn trust_mc_request_provenance(mode: TrustMcVerificationMode) -> NativeRequestProvenance {
    let (verifier_version, solver_name) = match mode {
        TrustMcVerificationMode::BoundedModelCheck => ("bmc-v1", "ay-bmc"),
        TrustMcVerificationMode::Chc => ("chc-v1", "ay-chc"),
        TrustMcVerificationMode::Pdr => ("pdr-v1", "ay-pdr"),
    };

    NativeRequestProvenance::trust_mc(
        NativeToolIdentity::new("trust_mc").with_version(verifier_version),
    )
    .with_solver(NativeToolIdentity::new(solver_name).with_version("native-v1"))
    .with_replay(native_replay_identity("trust_mc", 0x62))
    .with_replay_context(trust_mc_replay_context())
}

fn native_replay_identity(engine: &str, seed: u8) -> ProofReplayIdentity {
    ProofReplayIdentity::new(engine, format!("{engine} native replay fixture"))
        .with_transcript_digest(native_digest(seed))
}

fn trust_mc_replay_context() -> NativeReplayContext {
    let span = trust_ir::SourceSpan { file: 0, line: 20, col: 9 };
    NativeReplayContext::default()
        .with_atom(
            NativeReplayAtom::assumption(
                NativeReplayAtomId::new(0),
                ProofFormula::smtlib2("trust_mc_checked_add_pre", "Bool"),
            )
            .with_obligation(ProofId::new(1))
            .with_span(span),
        )
        .with_atom(
            NativeReplayAtom::assertion(
                NativeReplayAtomId::new(1),
                ProofFormula::smtlib2("trust_mc_checked_add_ok", "Bool"),
            )
            .with_obligation(ProofId::new(1))
            .with_assertion_id(NativeAssertionId::new(1))
            .with_span(span),
        )
}

fn trust_mc_request_options(mode: TrustMcVerificationMode) -> trust_ir::TrustMcRequestOptions {
    let mut options = trust_ir::TrustMcRequestOptions::default();
    if matches!(mode, TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr) {
        options.chc.emit_horn_clauses = true;
    }
    if mode == TrustMcVerificationMode::Pdr {
        options.chc.pdr.enabled = true;
    }
    options
}

fn not_inner_matches<F>(expr: &Expr, matches_inner: F) -> bool
where
    F: Fn(&ExprValue) -> bool,
{
    match expr.value() {
        ExprValue::Not(inner) => matches_inner(inner.value()),
        _ => false,
    }
}

fn head_arg_suffix<'a>(
    output: &'a crate::ChcTranslationOutput,
    relation: &str,
    suffix_len: usize,
) -> &'a [Expr] {
    let args = &output
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == relation)
        .unwrap_or_else(|| panic!("expected {relation} transition rule"))
        .head
        .args;
    assert!(
        args.len() >= suffix_len,
        "{relation} transition has {} args, expected at least {suffix_len}",
        args.len()
    );
    &args[args.len() - suffix_len..]
}

fn emit_thread_local_addr(
    fb: &mut trust_ir_build::FunctionBuilder,
    symbol: &str,
) -> trust_ir::value::ValueId {
    let results = fb.dialect_op(trust_rust::thread_local_addr(symbol));
    assert_eq!(results.len(), 1, "canonical TLS address op has one SSA result");
    results[0]
}

fn assert_thread_local_addr_case_fails_closed(module: &trust_ir::Module, case: &str) {
    let outputs = trust_ir_to_chc_translation_outputs(module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1, "{case}: expected one CHC output");
    assert!(
        outputs[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::DialectOperation),
        "{case}: a non-canonical TLS address op must fail closed in CHC, got {:?}",
        outputs[0].diagnostics
    );
    assert!(
        outputs[0].vc.rules.iter().any(|rule| rule.head.name == "error"),
        "{case}: CHC fail-closed lowering must emit a reachable error rule"
    );

    let vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1, "{case}: expected one BMC VC");
    assert!(
        vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("dialect operation"))
        }),
        "{case}: a non-canonical TLS address op must fail closed in BMC, got {:?}",
        vcs[0].violations
    );
}

fn is_bv_zero_eq(expr: &Expr, width: u32) -> bool {
    let zero = Expr::bitvec_const(0u64, width);
    matches!(expr.value(), ExprValue::Eq(lhs, rhs) if lhs == &zero || rhs == &zero)
}

fn is_bv_const_eq(expr: &Expr, value: u64, width: u32) -> bool {
    let constant = Expr::bitvec_const(value, width);
    matches!(expr.value(), ExprValue::Eq(lhs, rhs) if lhs == &constant || rhs == &constant)
}

fn default_switch_guard_excludes(expr: &Expr, values: &[u64], width: u32) -> bool {
    match expr.value() {
        ExprValue::And(clauses) => values.iter().all(|value| {
            clauses.iter().any(|clause| {
                not_inner_matches(clause, |inner| {
                    let constant = Expr::bitvec_const(*value, width);
                    matches!(inner, ExprValue::Eq(lhs, rhs) if lhs == &constant || rhs == &constant)
                })
            })
        }),
        _ => false,
    }
}

#[test]
fn native_trust_mc_bundle_bmc_request_translates_requested_function() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::BoundedModelCheck);
    let vcs = trust_mc_bmc_vcs_from_native_bundle(&bundle, &TranslateOptions::default())
        .expect("valid native trust_mc BMC request should translate");

    assert_eq!(vcs.len(), 1, "only the typed trust_mc request should produce a VC");
    let request_vc = &vcs[0];
    assert_eq!(request_vc.request_id, NativeRequestId::new(1));
    assert_eq!(request_vc.obligations, vec![ProofId::new(1)]);
    assert_eq!(request_vc.lineage_roots, vec![ProofLineageId::new(0)]);

    assert!(
        request_vc
            .vc
            .violations
            .iter()
            .any(|violation| violation.kind == PropertyKind::ArithmeticOverflow),
        "trust_mc native BMC request should translate the requested checked_add function"
    );
    assert!(
        !request_vc.vc.violations.iter().any(|violation| violation.kind == PropertyKind::Assertion),
        "non-trust_mc request variants must not cause whole-module translation"
    );
}

#[test]
fn native_trust_mc_bundle_chc_request_translates_requested_function_to_typed_obligation() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let request = native_trust_mc_request(&bundle);
    assert_eq!(request.provenance.verifier_suite, NativeVerifierSuite::TrustMc);
    assert_eq!(request.provenance.expected_verifier().name.as_str(), "trust_mc");
    assert_eq!(request.provenance.solver_identities()[0].name.as_str(), "ay-chc");

    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc CHC request should translate");

    assert_eq!(
        obligations.len(),
        1,
        "only the typed trust_mc request should produce an obligation"
    );
    let request_obligation = &obligations[0];
    assert_eq!(request_obligation.request_id, NativeRequestId::new(1));
    assert_eq!(request_obligation.obligations, vec![ProofId::new(1)]);
    assert_eq!(request_obligation.lineage_roots, vec![ProofLineageId::new(0)]);
    assert_eq!(request_obligation.obligation.function_name, "trust_mc_checked_add");
    assert_eq!(request_obligation.obligation.kind, trust_mc_core::MirObligationKind::Protocol);
    request_obligation
        .obligation
        .validate()
        .expect("native CHC request should produce a valid typed CHC/PDR obligation");
    let metadata = request_obligation
        .obligation
        .native_metadata
        .as_ref()
        .expect("native CHC obligation should carry bundle metadata");
    assert_eq!(
        metadata.schema_version,
        trust_mc_core::NativeTypedChcObligationMetadata::SCHEMA_VERSION
    );
    assert_eq!(metadata.producer, "tRust");
    assert_eq!(metadata.adapter_input, "rust-mir");
    assert_eq!(
        metadata.source_digest.as_ref().map(|digest| digest.algorithm.as_str()),
        Some("sha256")
    );
    assert_eq!(metadata.trust_ir_module_digest.algorithm, "sha256");
    assert_eq!(metadata.lineage_manifest_digest.algorithm, "sha256");
    assert_eq!(metadata.native_request_id, 1);
    assert_eq!(metadata.verification_mode, "chc");
    assert_eq!(metadata.function_id, request_obligation.function.index());
    assert_eq!(metadata.proof_obligation_ids, vec![1]);
    assert_eq!(metadata.lineage_root_ids, vec![0]);
    assert_eq!(
        metadata.compiler_facts_digest.as_ref().map(|digest| digest.algorithm.as_str()),
        Some("sha256")
    );
    assert_eq!(metadata.compiler_fact_counts.monomorphizations, 1);
    assert_eq!(metadata.compiler_fact_counts.obligation_sources, 3);
    assert_eq!(metadata.compiler_fact_sources.len(), 1);
    let replay_identity = metadata
        .replay_identity
        .as_ref()
        .expect("native CHC metadata should retain replay identity");
    assert_eq!(replay_identity.engine, "trust_mc");
    assert_eq!(replay_identity.transcript_digest.algorithm, "sha256");
    assert_eq!(metadata.replay_context.atoms.len(), 2);
    assert!(
        metadata.replay_context.atoms.iter().any(|atom| {
            atom.kind == trust_mc_core::NativeReplayAtomKindMetadata::Assertion
                && atom.proof_obligation_id == Some(1)
                && atom.assertion_id == Some(1)
                && atom.span
                    == Some(trust_mc_core::NativeSourceSpanMetadata { file: 0, line: 20, col: 9 })
        }),
        "typed replay assertion atom should preserve obligation/assertion/span binding"
    );
    let compiler_source = &metadata.compiler_fact_sources[0];
    assert_eq!(compiler_source.proof_obligation_id, 1);
    assert_eq!(compiler_source.function_id, Some(request_obligation.function.index()));
    assert_eq!(compiler_source.cause, trust_mc_core::NativeObligationCauseMetadata::Translation);
    assert_eq!(
        compiler_source.fact_refs,
        vec![trust_mc_core::NativeCompilerFactReference::new(
            trust_mc_core::NativeCompilerFactKind::Monomorphization,
            0
        )]
    );

    let vc = &request_obligation.obligation.vc;
    assert!(vc.relations.iter().any(|rel| rel.name == "error"));
    assert!(
        vc.rules.iter().any(|rule| rule.head.name == "error"),
        "checked_add should produce a typed error rule for overflow"
    );
}

#[test]
fn native_trust_mc_bundle_bmc_rejects_missing_solver_identity_before_translation() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::BoundedModelCheck);
    let request = native_trust_mc_request_mut(&mut bundle);
    request.provenance.solvers.clear();

    let err = trust_mc_bmc_vcs_from_native_bundle(&bundle, &TranslateOptions::default())
        .expect_err("trust_mc BMC admission must reject missing solver identity");

    let NativeTrustMcBundleError::InvalidBundle(errors) = err else {
        panic!("missing solver identity should be reported by bundle validation");
    };
    assert!(errors.iter().any(|error| {
        matches!(
            error,
            trust_ir::NativeVerificationBundleError::EmptyProvenanceField(
                "request.provenance.solvers"
            )
        )
    }));
}

#[test]
fn native_trust_mc_bundle_chc_rejects_missing_solver_identity_before_translation() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let request = native_trust_mc_request_mut(&mut bundle);
    request.provenance.solvers.clear();

    let err =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect_err("trust_mc CHC/PDR admission must reject missing solver identity");

    let NativeTrustMcBundleError::InvalidBundle(errors) = err else {
        panic!("missing solver identity should be reported by bundle validation");
    };
    assert!(errors.iter().any(|error| {
        matches!(
            error,
            trust_ir::NativeVerificationBundleError::EmptyProvenanceField(
                "request.provenance.solvers"
            )
        )
    }));
}

#[test]
fn native_trust_mc_bundle_chc_rejects_invalid_translated_obligation_shape() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let requested_function = native_trust_mc_request(&bundle).function;
    let function = bundle
        .module
        .functions
        .iter_mut()
        .find(|function| function.id == requested_function)
        .expect("fixture includes the requested trust_mc function");
    function.name.clear();
    refresh_native_trust_mc_bundle_module_identity(&mut bundle);

    let err =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect_err(
                "native CHC/PDR adapter must validate translated obligations before returning",
            );

    assert!(matches!(
        err,
        NativeTrustMcBundleError::InvalidChcPdrObligation {
            request: NativeRequestId(1),
            source: trust_mc_core::MirChcPdrObligationError::EmptyFunctionName,
        }
    ));
}

#[test]
fn native_trust_mc_bundle_chc_metadata_binds_non_authoritative_candidate_evidence() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc CHC request should translate");
    let translated = obligations.into_iter().next().expect("one native trust_mc CHC obligation");
    let metadata = translated
        .obligation
        .native_metadata
        .clone()
        .expect("typed native CHC obligation should carry bundle metadata");
    let normalized_input = translated.obligation.vc.to_horn_smt2();
    let evidence_obligation = trust_mc_core::MirDerivedChcPdrObligation::new(
        translated.obligation.obligation_id.clone(),
        translated.obligation.kind,
        normalized_input,
    )
    .with_native_metadata(metadata);
    let proof = trust_mc_core::ChcPdrProofEvidence::try_chc_validity_candidate_from_linked_bytes(
        evidence_obligation,
        translated.obligation.stats(),
        ("trust_mc://typed-chc/solver-transcript.json", b"typed solver transcript"),
        ("trust_mc://typed-chc/replay-log.json", b"typed replay log"),
        ("trust_mc://typed-chc/checked-proof-report.json", b"typed checked proof report"),
    )
    .expect("test proof artifacts are nonempty and bounded");
    let verdict = trust_mc_core::FullVerificationVerdict::Proved {
        evidence: trust_mc_core::FullProofEvidence::ChcPdr(proof),
    };

    let candidate = trust_mc_core::validated_native_typed_chc_pdr_candidate(&verdict)
        .expect("translated native metadata should bind a structurally valid candidate");
    let rejection = trust_mc_core::accepted_native_typed_chc_pdr_proof(&verdict)
        .expect_err("public linked bytes must not self-certify as proof authority");
    assert_eq!(
        rejection.reasons,
        vec![trust_mc_core::CHC_VALIDITY_FRESH_CONSUMER_REPLAY_REQUIRED.to_string()]
    );

    assert_eq!(
        candidate.proof.obligation.obligation_id,
        "trust_ir-native-trust_mc-request-1-proof-1"
    );
    assert_eq!(candidate.proof_kind, trust_mc_core::ChcPdrProofKind::ChcValidity);
    assert_eq!(candidate.proof.stats, translated.obligation.stats());
    let candidate_metadata = candidate.native_metadata.expect("candidate retains metadata");
    assert_eq!(candidate_metadata.producer, "tRust");
    assert_eq!(candidate_metadata.native_request_id, 1);
    assert_eq!(candidate_metadata.proof_obligation_ids, vec![1]);
    assert_eq!(candidate_metadata.compiler_fact_sources.len(), 1);
    assert_eq!(
        candidate_metadata.compiler_fact_sources[0].fact_refs,
        vec![trust_mc_core::NativeCompilerFactReference::new(
            trust_mc_core::NativeCompilerFactKind::Monomorphization,
            0
        )]
    );
}

#[test]
fn native_trust_mc_bundle_pdr_request_translates_with_typed_compiler_fact_refs() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::Pdr);
    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc PDR request should use CHC/PDR adapter");

    assert_eq!(obligations.len(), 1);
    let request_obligation = &obligations[0];
    let metadata = request_obligation
        .obligation
        .native_metadata
        .as_ref()
        .expect("native PDR obligation should carry compiler-facts metadata");

    assert_eq!(metadata.verification_mode, "pdr");
    assert_eq!(metadata.proof_obligation_ids, vec![1]);
    assert_eq!(metadata.compiler_fact_sources.len(), 1);
    assert_eq!(
        metadata.compiler_fact_sources[0].fact_refs,
        vec![trust_mc_core::NativeCompilerFactReference::new(
            trust_mc_core::NativeCompilerFactKind::Monomorphization,
            0
        )]
    );
}

#[test]
fn native_trust_mc_bundle_rejects_unknown_compiler_fact_reference() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let trust_mc_source = bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(1))
        .expect("fixture maps trust_mc proof obligation");
    trust_mc_source.facts = vec![NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(99))];

    let err =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect_err("unknown compiler_facts references must fail closed before translation");

    let NativeTrustMcBundleError::InvalidBundle(errors) = err else {
        panic!("unknown compiler_facts reference should be reported by bundle validation");
    };
    assert!(errors.iter().any(|error| {
        matches!(
            error,
            trust_ir::NativeVerificationBundleError::UnknownCompilerFactReference {
                obligation: ProofId(1),
                fact: NativeCompilerFactRef::AdtLayout(NativeCompilerFactId(99)),
            }
        )
    }));
}

#[test]
fn native_trust_mc_bundle_bmc_api_rejects_chc_without_downgrading() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let err = trust_mc_bmc_vcs_from_native_bundle(&bundle, &TranslateOptions::default())
        .expect_err("BMC API must not silently downgrade CHC native requests");

    assert!(matches!(
        err,
        NativeTrustMcBundleError::UnsupportedTrustMcMode {
            request: NativeRequestId(1),
            mode: TrustMcVerificationMode::Chc,
        }
    ));
}

#[test]
fn native_trust_mc_bundle_without_trust_mc_request_is_rejected() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::BoundedModelCheck);
    bundle.requests.retain(|request| !matches!(request, NativeVerificationRequest::TrustMc(_)));

    let err = trust_mc_bmc_vcs_from_native_bundle(&bundle, &TranslateOptions::default())
        .expect_err("trust_mc consumer should reject bundles for other tools");
    assert!(matches!(err, NativeTrustMcBundleError::NoTrustMcRequests));
}

/// Build a module with a single function that adds two i32 parameters.
/// Expected: one signed overflow VC.
#[test]
fn add_two_i32_generates_overflow_vc() {
    let mut mb = ModuleBuilder::new("test_add");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("add_i32", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let sum = fb.add(Ty::I32, a, b);
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1, "should produce one VC per function");
    let vc = &vcs[0];

    // Should have at least one overflow violation.
    let overflow_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert!(!overflow_violations.is_empty(), "add should generate an arithmetic overflow check");

    // Should have declarations for the symbolic variables.
    assert!(!vc.decls.is_empty(), "should have declarations for symbolic vars");
}

/// Build a module with a single function that adds two i32 parameters.
/// Expected: one typed CHC error rule for signed overflow.
#[test]
fn add_two_i32_generates_typed_chc_overflow_rule() {
    let mut mb = ModuleBuilder::new("test_add_chc");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("add_i32_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let sum = fb.add(Ty::I32, a, b);
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build();
    let vcs = trust_ir_to_chc_vc(&module, &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert_eq!(vc.query.target.as_deref(), Some("error"));
    assert!(vc.relations.iter().any(|rel| rel.name == "bb0" && rel.arity() == 2));
    assert!(vc.relations.iter().any(|rel| rel.name == "error" && rel.arity() == 0));
    assert!(vc.rules.iter().any(|rule| rule.head.name == "bb0"));
    assert!(
        vc.rules.iter().any(|rule| rule.head.name == "error"),
        "add should generate a typed CHC error rule for overflow"
    );
}

#[test]
fn typed_chc_translation_rejects_return_arity_mismatch() {
    let mut mb = ModuleBuilder::new("test_return_arity_mismatch_chc");
    let ft = mb.add_func_type(vec![], vec![Ty::U32]);

    let mut fb = mb.function("return_arity_mismatch_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::SafetyProperties);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::ReturnArityMismatch);
    assert_eq!(output.diagnostics[0].function, "return_arity_mismatch_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "malformed return arity should fail closed"
    );
}

#[test]
fn call_summary_models_total_unops_instead_of_failing_closed() {
    // rung-2 precision: a callee whose body uses a TOTAL unary op (here `!x`, `UnOp::Not`)
    // must be SUMMARIZED — the unop modeled as a fresh-symbolic value — so its caller is NOT
    // conservatively poisoned to UNKNOWN. Before the total-UnOp arm, `Not` hit the call-summary
    // interpreter's `_ => return None` fail-close, so the whole summary declined and the caller
    // got an `UnsupportedDirectCallSummary` may-panic error rule despite the callee being total.
    let mut mb = ModuleBuilder::new("test_total_unop_summary");
    let g_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let f_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // callee g(x) = !x  (bitwise Not — total, never panics)
    let g_id = {
        let mut fb = mb.function("total_unop_callee", g_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let y = fb.unop(UnOp::Not, Ty::I32, x);
        fb.ret(vec![y]);
        fb.build()
    };

    // caller f(a) = g(a)
    {
        let mut fb = mb.function("total_unop_caller", f_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::I32);
        let r = fb.call(g_id, vec![a]);
        fb.ret(vec![r]);
        fb.build();
    }

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    // The callee with a total unop must be summarized: NO unsupported-call-summary diagnostic
    // anywhere, and the caller's VC must NOT carry a fail-closed error rule from the call.
    let unsupported_summary = outputs.iter().flat_map(|o| o.diagnostics.iter()).any(|d| {
        d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
            || d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall
    });
    assert!(
        !unsupported_summary,
        "a callee using a total unary op (`!x`) must be summarized, not fail-closed to UNKNOWN"
    );

    // Identify the CALLER f: its body (`g(a)`; ret) lowers cleanly, so its output carries NO
    // diagnostics — whereas the callee g's standalone VC has a `UnaryOperation` diagnostic
    // (the MAIN translate path havocs `UnOp`; only the call-summary path models it). The
    // caller's reused summary of the TOTAL g must add no obligation, so f's VC has no error rule.
    // (Before the fix, f's call fail-closed and emitted an unconditional error rule.)
    assert_eq!(outputs.len(), 2, "callee + caller");
    let caller = outputs
        .iter()
        .find(|o| o.diagnostics.is_empty())
        .expect("the caller f lowers with no diagnostics");
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "a total callee's reused summary must add no panic obligation to the caller"
    );
}

#[test]
fn call_summary_proves_obligation_free_self_recursion() {
    // rung-2 recursion FIXPOINT: a SELF-recursive callee with NO per-level obligation is panic-free
    // at EVERY depth by induction (the recursive call is assumed safe; the body adds no panic), so
    // its caller must PROVE — not fail-close to UNKNOWN. Before the fixpoint arm, the self-call hit
    // `_ => return None` and the whole summary declined.
    let mut mb = ModuleBuilder::new("test_self_rec_total");
    let g_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let f_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // g(x) = if x == 0 { x } else { g(x) } — structural self-recursion, NO arithmetic obligation.
    let g_id = {
        let mut fb = mb.function("self_rec_callee", g_ft);
        let entry = fb.create_block();
        let base = fb.create_block();
        let rec = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let zero = fb.iconst(Ty::I32, 0);
        let cond = fb.icmp(ICmpOp::Eq, Ty::I32, x, zero);
        fb.condbr(cond, base, vec![], rec, vec![]);
        fb.switch_to_block(base);
        fb.ret(vec![x]);
        fb.switch_to_block(rec);
        let r = fb.call(trust_ir::value::FuncId::new(0), vec![x]); // self-call (g is function 0)
        fb.ret(vec![r]);
        fb.build()
    };
    assert_eq!(
        g_id,
        trust_ir::value::FuncId::new(0),
        "callee g must be function 0 for the self-call to reference it"
    );

    // caller f(a) = g(a)
    {
        let mut fb = mb.function("self_rec_caller", f_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::I32);
        let r = fb.call(g_id, vec![a]);
        fb.ret(vec![r]);
        fb.build();
    }

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    // The caller f lowers cleanly (no diagnostics); the callee g's STANDALONE VC carries a
    // `RecursiveDirectCall` diagnostic (the MAIN translate fail-closes self-recursion — only the
    // call-SUMMARY path models it via the fixpoint). The caller's reused summary of the
    // obligation-free g adds no error rule.
    let caller = outputs
        .iter()
        .find(|o| o.diagnostics.is_empty())
        .expect("the caller f lowers with no diagnostics");
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "an obligation-free self-recursive callee's summary must add no obligation to the caller"
    );
}

#[test]
fn call_summary_fails_closed_on_self_recursion_with_obligation() {
    // SOUNDNESS GUARD for the recursion fixpoint: a self-recursive callee that HAS a per-level
    // obligation (here an UNGUARDED `x + x` overflow) must NOT be proven — the obligation can't be
    // shown to hold at EVERY recursion depth from one invocation, so the summary fail-closes and the
    // caller carries a conservative `UnsupportedDirectCallSummary` (NOT a false proof). Holds both
    // before and after the fixpoint arm — it locks the boundary the fixpoint must never cross.
    let mut mb = ModuleBuilder::new("test_self_rec_obligation");
    let g_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let f_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);

    // g(x) = { let y = x + x; g(y) } — an UNGUARDED add-overflow obligation, then self-recurse.
    let g_id = {
        let mut fb = mb.function("self_rec_ob_callee", g_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let y = fb.add(Ty::U32, x, x); // BinOp Add → an overflow obligation in the summary
        let r = fb.call(trust_ir::value::FuncId::new(0), vec![y]);
        fb.ret(vec![r]);
        fb.build()
    };

    // caller f(a) = g(a)
    {
        let mut fb = mb.function("self_rec_ob_caller", f_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::U32);
        let r = fb.call(g_id, vec![a]);
        fb.ret(vec![r]);
        fb.build();
    }

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    // The summary of the obligation-bearing recursive callee MUST decline: somewhere there is an
    // `UnsupportedDirectCallSummary` (the caller's fail-closed call), and the caller carries an
    // error rule — the recursion is NOT falsely proved safe.
    let declined = outputs
        .iter()
        .flat_map(|o| o.diagnostics.iter())
        .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary);
    assert!(
        declined,
        "a self-recursive callee WITH a per-level obligation must fail-close, not be summarized safe"
    );
}

#[test]
fn call_summary_fails_closed_on_unsummarizable_panicking_callee() {
    // SOUNDNESS GUARD for the interprocedural panic-freedom seam (the 2211
    // `UnsupportedDirectCallSummary` path in `translate_call`). A caller of an
    // IN-CRATE callee whose body CANNOT be value-summarized — here a `Load`
    // through a `&mut self`-style `Ptr`, which is EXACTLY why `Lcg::next_u64`
    // declines the summary — AND which can PANIC (an `assert(false)`) must fail
    // CLOSED: the caller's CHC MUST carry a reachable `error` rule. Modeling the
    // call as havoc-with-no-error would make the caller's panic-freedom CHC
    // trivially-safe, which the complete-by-construction native translator
    // accepts as a GENUINE panic-freedom proof (native `Proved`) — bypassing the
    // compiler-side `all_calls_target_proven_panic_free` seam, so a caller of a
    // genuinely-panicking in-crate callee would FALSELY prove panic-free. Locks
    // the boundary any "drop the in-crate-call error edge" relaxation must never
    // cross.
    let mut mb = ModuleBuilder::new("test_unsummarizable_panicking_callee");
    let g_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let f_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);

    // callee g(p): assert(false) — an unconditional panic — then a `Load` through
    // p, which the value-summary interpreter has no arm for, so the whole summary
    // DECLINES and the caller falls to the fail-closed 2211 path.
    let g_id = {
        let mut fb = mb.function("unsummarizable_panicking_callee", g_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let p = fb.add_block_param(entry, Ty::Ptr);
        let zero = fb.iconst(Ty::U32, 0);
        let one = fb.iconst(Ty::U32, 1);
        let never = fb.icmp(ICmpOp::Eq, Ty::U32, zero, one); // 0 == 1 => false
        fb.assert(never); // assert(false): the callee always panics
        let _v = fb.load(Ty::U32, p); // unmodeled by the summary => declines
        fb.ret(vec![]);
        fb.build()
    };

    // caller f(p): g(p)
    let f_id = {
        let mut fb = mb.function("unsummarizable_panicking_caller", f_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let p = fb.add_block_param(entry, Ty::Ptr);
        let _ = fb.call(g_id, vec![p]);
        fb.ret(vec![]);
        fb.build()
    };

    let module = mb.build();
    let caller = crate::trust_ir_function_to_chc_translation_output(
        &module,
        f_id,
        &TranslateOptions::default(),
    )
    .expect("caller function exists");

    assert!(
        caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "a caller of an unsummarizable, panicking in-crate callee MUST fail closed \
         with a reachable error rule; modeling the call as havoc-no-error is a false \
         structural panic-freedom proof (bypasses the all_calls_target_proven_panic_free seam)"
    );
}

#[test]
fn cross_block_instruction_result_is_threaded_not_havoced() {
    // Root-cause regression guard: an SSA instruction result DEFINED in one block and
    // USED (by dominance, not re-passed as a block arg) in a successor must be THREADED
    // through block relations so the successor's use resolves to the COMPUTED value —
    // not a fresh symbolic. Before the general threading, `declare_block_relations`
    // threaded only `Undef`/`InsertField` results, so a loop-body `count = count + 1`
    // (a `BinOp` defined in the update block, stored/used in the next) was re-`resolve`d
    // to a fresh havoc after the per-block `self.values` reset, leaving the loop-carried
    // value free and the loop invariant unprovable.
    let mut mb = ModuleBuilder::new("test_cross_block_thread");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("cross_block_thread", ft);
    let entry = fb.create_block();
    let next = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let t = fb.add(Ty::U32, a, b); // t := a + b, DEFINED in entry
    fb.br(next, vec![]); // NO block args — t must cross the edge by dominance/threading
    fb.switch_to_block(next);
    let _u = fb.add(Ty::U32, t, t); // uses t in the SUCCESSOR block
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];

    // The successor relation `bb1` must carry the threaded cross-block value as an arg.
    let bb1 = output.vc.relations.iter().find(|rel| rel.name == "bb1").expect("bb1 relation");
    assert!(
        bb1.arity() >= 1,
        "the successor relation must carry the threaded cross-block instruction result"
    );

    // The entry->next transition must FORWARD `t = bvadd(a, b)`, not a fresh havoc var.
    let [forwarded] = head_arg_suffix(output, "bb1", 1) else {
        panic!("bb1 transition should forward the single threaded value");
    };
    assert!(
        matches!(forwarded.value(), ExprValue::BvAdd(_, _)),
        "a cross-block instruction result must be threaded as its computed value \
         bvadd(a, b), not re-resolved to a fresh var; got {:?}",
        forwarded.value()
    );
}

#[test]
fn canonical_thread_local_addr_is_chc_only_and_bmc_fails_closed() {
    let mut mb = ModuleBuilder::new("test_thread_local_addr_exact");
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("thread_local_addr_exact", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let addr = emit_thread_local_addr(&mut fb, "crate::TLS");
    fb.ret(vec![addr]);
    fb.build();

    let module = mb.build();
    assert_eq!(
        family_for_inst(&trust_ir::Inst::DialectOp(Box::new(trust_rust::thread_local_addr(
            "crate::TLS"
        )))),
        SemanticsFamily::MemoryProvenance,
        "the sealed TLS address op belongs to the memory/provenance lane"
    );

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "the exact TLS address schema must be accepted by CHC, got {:?}",
        outputs[0].diagnostics
    );
    assert!(
        !outputs[0].vc.rules.iter().any(|rule| rule.head.name == "error"),
        "an operand-free demonic address grants no assumptions and needs no error rule"
    );

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("dialect operation"))
        }),
        "the legacy BMC lane has no TLS address model and must fail closed, got {:?}",
        vcs[0].violations
    );
}

#[test]
fn canonical_thread_local_addr_result_is_threaded_across_blocks() {
    let mut mb = ModuleBuilder::new("test_thread_local_addr_cross_block");
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("thread_local_addr_cross_block", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let addr = emit_thread_local_addr(&mut fb, "crate::TLS");
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![addr]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "cross-block use of the exact TLS address must remain supported"
    );
    let exit_relation =
        output.vc.relations.iter().find(|relation| relation.name == "bb1").expect("bb1 relation");
    assert_eq!(
        exit_relation.arity(),
        1,
        "the successor relation must carry the TLS address defined in its predecessor"
    );
    let [forwarded] = head_arg_suffix(output, "bb1", 1) else {
        panic!("bb1 transition should forward the one TLS address result");
    };
    assert!(
        matches!(forwarded.value(), ExprValue::Var { name } if name.contains("thread_local_addr")),
        "the entry-to-exit transition must forward the demonic TLS address, got {forwarded:?}"
    );
}

#[test]
fn canonical_thread_local_addr_is_supported_in_direct_call_summary() {
    let mut mb = ModuleBuilder::new("test_thread_local_addr_call_summary");
    let callee_ft = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let caller_ft = mb.add_func_type(vec![], vec![]);

    let callee = {
        let mut fb = mb.function("thread_local_addr_callee", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let addr = emit_thread_local_addr(&mut fb, "crate::TLS");
        fb.ret(vec![addr]);
        fb.build()
    };

    let mut fb = mb.function("thread_local_addr_caller", caller_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let addr = fb.call(callee, vec![]);
    fb.add_block_param(exit, Ty::Ptr);
    fb.br(exit, vec![addr]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "a direct call returning the sealed TLS address must summarize, got {:?}",
        caller.diagnostics
    );
    let [summary_result] = head_arg_suffix(caller, "bb1", 1) else {
        panic!("the caller transition should forward its one summarized return value");
    };
    assert!(
        matches!(summary_result.value(), ExprValue::Var { name } if name.contains("call_thread_local_addr")),
        "the direct-call summary must bind a demonic pointer result, got {summary_result:?}"
    );
}

#[test]
fn malformed_thread_local_addr_schema_fails_closed() {
    let mut mb = ModuleBuilder::new("test_thread_local_addr_bad_schema");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("thread_local_addr_bad_schema", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let mut op = trust_rust::thread_local_addr("crate::TLS");
    let schema = op
        .attrs
        .iter_mut()
        .find(|attr| attr.name == trust_rust::THREAD_LOCAL_ADDR_ATTR_SCHEMA)
        .expect("canonical op carries its schema attribute");
    schema.value = AttrValue::Str("trust-rust.thread-local-addr/v2".to_owned());
    fb.dialect_op(op);
    fb.ret(vec![]);
    fb.build();

    assert_thread_local_addr_case_fails_closed(&mb.build(), "schema mismatch");
}

#[test]
fn thread_local_addr_node_result_arity_mismatch_fails_closed() {
    let mut mb = ModuleBuilder::new("test_thread_local_addr_node_arity");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("thread_local_addr_node_arity", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    emit_thread_local_addr(&mut fb, "crate::TLS");
    fb.ret(vec![]);
    fb.build();
    let canonical = mb.build();

    let mut no_results = canonical.clone();
    let node = no_results.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(&node.inst, trust_ir::Inst::DialectOp(_)))
        .expect("TLS dialect node");
    node.results.clear();
    assert_thread_local_addr_case_fails_closed(&no_results, "zero node results");

    let mut two_results = canonical;
    let node = two_results.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(&node.inst, trust_ir::Inst::DialectOp(_)))
        .expect("TLS dialect node");
    node.results.push(node.results[0]);
    assert_thread_local_addr_case_fails_closed(&two_results, "two node results");
}

#[test]
fn wrapping_add_intrinsic_call_lowers_to_modular_bvadd_not_fresh() {
    // A `count = count.wrapping_add(1)` reaches the trust-ir as a direct `Call` to a
    // numeric method whose body the bounded summary interpreter does not model, so it
    // used to fall through to a fresh-symbolic HAVOC — leaving the loop-carried count
    // cell unconstrained (`count'` free) and the count-parity loop invariant
    // unprovable. `translate_call` now recognizes the wrapping intrinsic by its method
    // name + integer 2-in/1-out signature and models it as the MODULAR `bvadd`, so the
    // call result is CONSTRAINED (`= bvadd(x, 1)`), not a fresh variable.
    let mut mb = ModuleBuilder::new("test_wrapping_add_intrinsic");
    let wrap_ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let f_ft = mb.add_func_type(vec![Ty::U64], vec![]);

    // Intrinsic-shaped callee: named `…::wrapping_add`, (u64, u64) -> u64. Its body is
    // a stub (never interpreted — `translate_call` intercepts by name/signature and
    // models the modular BV op directly, exactly as the compiler MIR path does).
    let wrap_id = {
        let mut fb = mb.function("core::num::<impl u64>::wrapping_add", wrap_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::U64);
        let _b = fb.add_block_param(entry, Ty::U64);
        fb.ret(vec![a]);
        fb.build()
    };

    // caller f(x) { let r = x.wrapping_add(1); r }  — routed through an exit block so
    // the wrapping result surfaces as an inspectable relation head argument.
    {
        let mut fb = mb.function("wrapping_add_caller", f_ft);
        let entry = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U64);
        let one = fb.iconst(Ty::U64, 1);
        let r = fb.call(wrap_id, vec![x, one]);
        fb.add_block_param(exit, Ty::U64);
        fb.br(exit, vec![r]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    // The caller is the output carrying the entry->exit transition (`bb1` head).
    let caller = outputs
        .iter()
        .find(|o| o.vc.rules.iter().any(|rule| rule.head.name == "bb1"))
        .expect("the caller f has an entry->exit transition rule");
    let [result] = head_arg_suffix(caller, "bb1", 1) else {
        panic!("bb1 transition should forward the single wrapping result arg");
    };
    assert!(
        matches!(result.value(), ExprValue::BvAdd(_, _)),
        "wrapping_add must lower to a MODULAR bvadd, got {:?}",
        result.value()
    );
    assert!(
        !matches!(result.value(), ExprValue::Var { .. }),
        "the wrapping result must be CONSTRAINED, not a fresh havoc variable"
    );
    // Modular wrapping carries NO overflow obligation, so the modeled call adds no
    // fail-closed error rule of its own.
    assert!(
        caller.diagnostics.is_empty(),
        "a modeled wrapping intrinsic must not emit an unsupported-call diagnostic"
    );
}

#[test]
fn direct_call_body_not_summary_binds_precise_negation_not_fresh() {
    // A direct call whose callee body is `!x` (`UnOp::Not`) must be summarized so its
    // result is CONSTRAINED to `not(x)` — this is exactly the shape MIR gives
    // `xor_accumulate_parity`'s `a ^ true` (`Select(true, !a, a)` → `!a`). Before the
    // fix the summary interpreter havoced every total unary op (including `Not`) to a
    // fresh symbolic, so the summarized result — and any loop cell it fed — was
    // unconstrained (`acc'` free), blocking the count-parity loop invariant. The
    // summary now models `!x` precisely as boolean `not`.
    let mut mb = ModuleBuilder::new("test_not_body_summary");
    let g_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let f_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    // callee g(x) = !x  (bool negation — total, never panics)
    let g_id = {
        let mut fb = mb.function("not_body_callee", g_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::Bool);
        let y = fb.unop(UnOp::Not, Ty::Bool, x);
        fb.ret(vec![y]);
        fb.build()
    };

    // caller f(a) { let r = g(a); r }  — routed through an exit block so g's summarized
    // result surfaces as an inspectable relation head argument.
    {
        let mut fb = mb.function("not_body_caller", f_ft);
        let entry = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::Bool);
        let r = fb.call(g_id, vec![a]);
        fb.add_block_param(exit, Ty::Bool);
        fb.br(exit, vec![r]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    let caller = outputs
        .iter()
        .find(|o| o.vc.rules.iter().any(|rule| rule.head.name == "bb1"))
        .expect("the caller f has an entry->exit transition rule");
    let [result] = head_arg_suffix(caller, "bb1", 1) else {
        panic!("bb1 transition should forward the single summarized-call result arg");
    };
    assert!(
        not_inner_matches(result, |inner| matches!(inner, ExprValue::Var { .. })),
        "the summarized `!x` call result must be CONSTRAINED to not(x), got {:?}",
        result.value()
    );
}

#[test]
fn inline_unop_not_binds_precise_negation_not_havoc() {
    // An INLINE `UnOp::Not` on a bool — the shape trustc gives an inlined
    // `acc = !acc` (and `acc ^ true`, which const-folds to `UnOp::Not`) — must
    // lower to `not(x)`, NOT a fresh `unsupported_result` havoc. Before the fix
    // `translate_node`'s `Inst::UnOp` arm failed closed (fresh symbolic), so the
    // result and any loop cell it fed were left free (`acc'` unconstrained),
    // making the count-parity loop invariant unprovable. This is the direct
    // (non-call) twin of `direct_call_body_not_summary_binds_precise_negation_not_fresh`.
    let mut mb = ModuleBuilder::new("test_inline_not");
    let f_ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("inline_not_fn", f_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::Bool);
    let r = fb.unop(UnOp::Not, Ty::Bool, a);
    fb.add_block_param(exit, Ty::Bool);
    fb.br(exit, vec![r]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    let f = outputs
        .iter()
        .find(|o| o.vc.rules.iter().any(|rule| rule.head.name == "bb1"))
        .expect("the fn has an entry->exit transition rule");
    let [result] = head_arg_suffix(f, "bb1", 1) else {
        panic!("bb1 transition should forward the single UnOp::Not result arg");
    };
    assert!(
        not_inner_matches(result, |inner| matches!(inner, ExprValue::Var { .. })),
        "inline `!x` must be CONSTRAINED to not(x), got {:?}",
        result.value()
    );
}

#[test]
fn typed_chc_translation_uses_unsigned_overflow_guard_for_u32_add() {
    let mut mb = ModuleBuilder::new("test_u32_add_chc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("add_u32_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let sum = fb.add(Ty::U32, a, b);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![sum]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "u32 add should lower without unsupported diagnostics");

    let has_unsigned_guard = output.vc.rules.iter().any(|rule| {
        rule.head.name == "error"
            && rule.body.constraints.iter().any(|constraint| {
                not_inner_matches(constraint, |inner| {
                    matches!(inner, ExprValue::BvAddNoOverflowUnsigned(_, _))
                })
            })
    });
    assert!(has_unsigned_guard, "u32 add should emit a typed unsigned overflow guard");

    let has_signed_guard = output.vc.rules.iter().any(|rule| {
        rule.head.name == "error"
            && rule.body.constraints.iter().any(|constraint| {
                not_inner_matches(constraint, |inner| {
                    matches!(inner, ExprValue::BvAddNoOverflowSigned(_, _))
                })
            })
    });
    assert!(
        !has_signed_guard,
        "u32 add must not use signed overflow semantics in typed CHC lowering"
    );

    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(matches!(branch_arg.value(), ExprValue::BvAdd(_, _)));
}

/// A `CheckedBinaryOp` (`Inst::Overflow`) over u32 must lower to a real
/// overflow check in the typed CHC path, not the `OverflowIntrinsic`
/// fail-closed marker. The only branch of the lowering that omits the
/// unsupported diagnostic is the one that binds the overflow flag to a real
/// no-overflow predicate (`bvadd_no_overflow_unsigned`), so an empty diagnostic
/// set proves the flag carries genuine semantics — the following
/// `Assert{Overflow}` panic-freedom obligation can then be proved or refuted
/// instead of always failing closed (the "unsupported MIR
/// FullVerification::Arithmetic" regression).
#[test]
fn typed_chc_translation_lowers_checked_u32_add_overflow_with_real_flag() {
    let mut mb = ModuleBuilder::new("test_checked_u32_add_chc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("checked_add_u32_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let (_sum, ovf) = fb.overflow(OverflowOp::AddOverflow, Ty::U32, a, b);
    // Use the flag so its bound expression flows into a constraint.
    fb.assert(ovf);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "checked u32 add must lower without an OverflowIntrinsic unsupported diagnostic, got {:?}",
        output.diagnostics
    );
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "checked u32 add should still produce an error rule for the asserted obligation"
    );
}

/// The BMC translation path must give `Inst::Overflow` the same real semantics:
/// no `PropertyKind::Other` "overflow intrinsic result pair" unsupported
/// violation, because the overflow flag is now bound to the no-overflow
/// predicate rather than a fresh unconstrained symbolic.
#[test]
fn typed_bmc_translation_lowers_checked_u32_add_overflow_with_real_flag() {
    let mut mb = ModuleBuilder::new("test_checked_u32_add_bmc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("checked_add_u32_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let (_sum, ovf) = fb.overflow(OverflowOp::AddOverflow, Ty::U32, a, b);
    fb.assert(ovf);
    fb.ret(vec![]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    let unsupported: Vec<_> = vcs[0]
        .violations
        .iter()
        .filter(|v| {
            v.kind == PropertyKind::Other
                && v.message.as_deref().is_some_and(|m| m.contains("overflow intrinsic"))
        })
        .collect();
    assert!(
        unsupported.is_empty(),
        "checked u32 add must not produce an 'overflow intrinsic result pair' unsupported violation, got {unsupported:?}"
    );
}

#[test]
fn typed_bmc_translation_uses_unsigned_overflow_guard_for_u32_sub() {
    let mut mb = ModuleBuilder::new("test_u32_sub_bmc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);

    let mut fb = mb.function("sub_u32_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let diff = fb.sub(Ty::U32, a, b);
    fb.ret(vec![diff]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let overflow_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert_eq!(overflow_violations.len(), 1);
    assert!(
        not_inner_matches(&overflow_violations[0].condition, |inner| {
            matches!(inner, ExprValue::BvSubNoUnderflowUnsigned(_, _))
        }),
        "u32 subtraction should use an unsigned underflow guard"
    );
}

#[test]
fn typed_chc_translation_uses_signed_division_overflow_guard_for_i32_div() {
    let mut mb = ModuleBuilder::new("test_i32_sdiv_chc");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("sdiv_i32_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let result = fb.sdiv(Ty::I32, a, b);
    fb.ret(vec![result]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "i32 sdiv should lower without diagnostics");
    assert!(
        output.vc.rules.iter().any(|rule| {
            rule.head.name == "error"
                && rule.body.constraints.iter().any(|constraint| {
                    not_inner_matches(constraint, |inner| {
                        matches!(inner, ExprValue::BvSdivNoOverflow(_, _))
                    })
                })
        }),
        "i32 sdiv should emit a typed signed-division overflow guard"
    );
}

#[test]
fn typed_bmc_translation_uses_signed_division_overflow_guard_for_i32_rem() {
    let mut mb = ModuleBuilder::new("test_i32_srem_bmc");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("srem_i32_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let result = fb.binop(BinOp::SRem, Ty::I32, a, b);
    fb.ret(vec![result]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let overflow_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert_eq!(overflow_violations.len(), 1);
    assert!(
        not_inner_matches(&overflow_violations[0].condition, |inner| {
            matches!(inner, ExprValue::BvSdivNoOverflow(_, _))
        }),
        "i32 srem should use the signed division overflow predicate for MIN % -1"
    );
}

#[test]
fn typed_chc_translation_uses_div_by_zero_guard_for_u32_div_without_overflow_guard() {
    let mut mb = ModuleBuilder::new("test_u32_udiv_chc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);

    let mut fb = mb.function("udiv_u32_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let result = fb.binop(BinOp::UDiv, Ty::U32, a, b);
    fb.ret(vec![result]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "u32 udiv should lower without diagnostics");
    assert!(
        output.vc.rules.iter().any(|rule| {
            rule.head.name == "error"
                && rule.body.constraints.iter().any(|constraint| is_bv_zero_eq(constraint, 32))
        }),
        "u32 udiv should emit a typed RHS == 0 division guard"
    );
    assert!(
        !output.vc.rules.iter().any(|rule| {
            rule.head.name == "error"
                && rule.body.constraints.iter().any(|constraint| {
                    not_inner_matches(constraint, |inner| {
                        matches!(inner, ExprValue::BvSdivNoOverflow(_, _))
                    })
                })
        }),
        "unsigned division must not use signed overflow guard semantics"
    );
}

#[test]
fn typed_bmc_translation_uses_div_by_zero_guard_for_u16_rem_without_overflow_guard() {
    let mut mb = ModuleBuilder::new("test_u16_urem_bmc");
    let ft = mb.add_func_type(vec![Ty::U16, Ty::U16], vec![Ty::U16]);

    let mut fb = mb.function("urem_u16_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::U16);
    let b = fb.add_block_param(entry, Ty::U16);
    let result = fb.binop(BinOp::URem, Ty::U16, a, b);
    fb.ret(vec![result]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let div_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::DivisionByZero).collect();
    assert_eq!(div_violations.len(), 1);
    assert!(
        is_bv_zero_eq(&div_violations[0].condition, 16),
        "u16 urem should use a typed RHS == 0 division guard"
    );
    assert!(
        !vcs[0].violations.iter().any(|v| v.kind == PropertyKind::ArithmeticOverflow),
        "unsigned remainder should not emit an overflow violation"
    );
}

/// CHC translation should encode trust_ir block control flow as relation transitions.
#[test]
fn condbr_generates_typed_chc_successor_rules() {
    let mut mb = ModuleBuilder::new("test_condbr_chc");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("branching_chc", ft);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.condbr(cond, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    fb.ret(vec![]);
    fb.switch_to_block(else_block);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let vcs = trust_ir_to_chc_vc(&module, &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert!(vc.rules.iter().any(|rule| rule.head.name == "bb1"));
    assert!(vc.rules.iter().any(|rule| rule.head.name == "bb2"));
    assert!(
        !vc.rules.iter().any(|rule| rule.head.name == "error"),
        "plain branching with no failing instruction should not introduce an error rule"
    );
}

#[test]
fn typed_chc_translation_rejects_non_bool_assume_condition() {
    let mut mb = ModuleBuilder::new("test_non_bool_assume_chc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("non_bool_assume_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let raw = fb.add_block_param(entry, Ty::U32);
    fb.assume(raw);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::SafetyProperties);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::NonBooleanCondition);
    assert_eq!(output.diagnostics[0].function, "non_bool_assume_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert!(
        output
            .vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .all(|constraint| constraint.sort().is_bool()),
        "non-Bool assume operands must not be emitted as CHC constraints"
    );
}

#[test]
fn typed_chc_translation_rejects_non_bool_condbr_condition() {
    let mut mb = ModuleBuilder::new("test_non_bool_condbr_chc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("non_bool_condbr_chc", ft);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let raw = fb.add_block_param(entry, Ty::U32);
    fb.condbr(raw, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    fb.ret(vec![]);
    fb.switch_to_block(else_block);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::ControlFlow);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::NonBooleanCondition);
    assert_eq!(output.diagnostics[0].function, "non_bool_condbr_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "malformed branch predicate should fail closed"
    );
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "bb1" || rule.head.name == "bb2"),
        "malformed branch predicate must not produce successor facts"
    );
}

#[test]
fn typed_chc_translation_lowers_bool_eq_comparison() {
    let mut mb = ModuleBuilder::new("test_bool_eq_icmp_chc");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![]);

    let mut fb = mb.function("bool_eq_icmp_chc", ft);
    let entry = fb.create_block();
    let equal_block = fb.create_block();
    let different_block = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let lhs = fb.add_block_param(entry, Ty::Bool);
    let rhs = fb.add_block_param(entry, Ty::Bool);
    let equal = fb.icmp(ICmpOp::Eq, Ty::Bool, lhs, rhs);
    fb.condbr(equal, equal_block, vec![], different_block, vec![]);

    fb.switch_to_block(equal_block);
    fb.ret(vec![]);
    fb.switch_to_block(different_block);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "Bool equality should lower without diagnostics");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported Bool equality should not introduce unsupported error rules"
    );
    let equal_rule = output
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "bb1")
        .expect("then edge should be guarded by the Bool equality");
    assert!(
        equal_rule
            .body
            .constraints
            .iter()
            .any(|constraint| matches!(constraint.value(), ExprValue::Eq(_, _))),
        "then edge should carry a typed Bool equality guard"
    );
}

#[test]
fn typed_chc_translation_rejects_ordered_bool_comparison() {
    let mut mb = ModuleBuilder::new("test_ordered_bool_icmp_chc");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![]);

    let mut fb = mb.function("ordered_bool_icmp_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let lhs = fb.add_block_param(entry, Ty::Bool);
    let rhs = fb.add_block_param(entry, Ty::Bool);
    let ordered = fb.icmp(ICmpOp::Ult, Ty::Bool, lhs, rhs);
    fb.assume(ordered);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::IntegerArithmetic);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::UnsupportedComparison);
    assert_eq!(output.diagnostics[0].function, "ordered_bool_icmp_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert_eq!(output.diagnostics[0].result_values, vec![ordered]);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "unsupported ordered Bool comparison should fail closed"
    );
    assert!(
        output
            .vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .all(|constraint| !matches!(constraint.value(), ExprValue::BvULt(_, _))),
        "ordered Bool comparison must not be emitted as a bit-vector predicate"
    );
}

#[test]
fn switch_generates_typed_chc_successor_rules() {
    let mut mb = ModuleBuilder::new("test_switch_chc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("switching_chc", ft);
    let entry = fb.create_block();
    let case_seven = fb.create_block();
    let case_nine = fb.create_block();
    let default_block = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let selector = fb.add_block_param(entry, Ty::U32);
    fb.add_block_param(case_seven, Ty::U32);
    fb.add_block_param(case_nine, Ty::U32);
    fb.add_block_param(default_block, Ty::U32);
    fb.switch(
        selector,
        vec![
            SwitchCase {
                value: trust_ir::Constant::Int(7),
                target: case_seven,
                args: vec![selector],
            },
            SwitchCase {
                value: trust_ir::Constant::Int(9),
                target: case_nine,
                args: vec![selector],
            },
        ],
        default_block,
        vec![selector],
    );

    fb.switch_to_block(case_seven);
    fb.ret(vec![]);
    fb.switch_to_block(case_nine);
    fb.ret(vec![]);
    fb.switch_to_block(default_block);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "scalar switch should lower without diagnostics");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported switch lowering should not introduce unsupported error rules"
    );

    let case_seven_rule = output
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "bb1")
        .expect("case 7 should produce a successor rule");
    assert!(case_seven_rule.body.constraints.iter().any(|guard| is_bv_const_eq(guard, 7, 32)));

    let case_nine_rule = output
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "bb2")
        .expect("case 9 should produce a successor rule");
    assert!(case_nine_rule.body.constraints.iter().any(|guard| is_bv_const_eq(guard, 9, 32)));

    let default_rule = output
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "bb3")
        .expect("default should produce a successor rule");
    assert!(
        default_rule.body.constraints.iter().any(|guard| default_switch_guard_excludes(
            guard,
            &[7, 9],
            32
        )),
        "default switch edge should exclude all explicit case values"
    );
}

#[test]
fn typed_chc_translation_lowers_integer_casts_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_int_cast_chc");
    let ft = mb.add_func_type(vec![Ty::U8], vec![]);

    let mut fb = mb.function("zext_u8_u16_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::U8);
    let cast = fb.cast(CastOp::ZExt, Ty::U8, Ty::U16, input);
    fb.add_block_param(exit, Ty::U16);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "integer casts should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported integer casts should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(branch_arg.value(), ExprValue::BvZeroExtend { extra_bits: 8, .. }),
        "zext u8 to u16 should lower to a typed bit-vector zero extension"
    );
}

#[test]
fn typed_chc_translation_lowers_bool_to_integer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_bool_cast_chc");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("zext_bool_u8_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::Bool);
    let cast = fb.cast(CastOp::ZExt, Ty::Bool, Ty::U8, input);
    fb.add_block_param(exit, Ty::U8);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "bool-to-integer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported bool-to-integer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    let one = Expr::bitvec_const(1u64, 8);
    let zero = Expr::bitvec_const(0u64, 8);
    assert!(
        matches!(
            branch_arg.value(),
            ExprValue::Ite { cond, then_expr, else_expr }
                if matches!(cond.value(), ExprValue::Var { name } if name == "bb0_v0")
                    && then_expr == &one
                    && else_expr == &zero
        ),
        "zext Bool to u8 should lower to ite(cond, #x01, #x00)"
    );
}

#[test]
fn typed_chc_translation_lowers_same_width_integer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_same_width_int_cast_chc");
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);

    let mut fb = mb.function("sext_i32_u32_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::I32);
    let cast = fb.cast(CastOp::SExt, Ty::I32, Ty::U32, input);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "same-width integer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported same-width integer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(branch_arg.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "same-width integer cast should preserve the source bits without an extension wrapper"
    );
}

#[test]
fn typed_chc_translation_lowers_thin_pointer_to_pointer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_ptr_to_ptr_cast_chc");
    let src_ty = Ty::PtrConst(Box::new(Ty::U32));
    let dst_ty = Ty::PtrMut(Box::new(Ty::U8));
    let ft = mb.add_func_type(vec![src_ty.clone()], vec![]);

    let mut fb = mb.function("ptr_to_ptr_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, src_ty.clone());
    let cast = fb.cast(CastOp::PtrToPtr, src_ty, dst_ty.clone(), input);
    fb.add_block_param(exit, dst_ty);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "thin pointer-to-pointer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported pointer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(branch_arg.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "thin pointer-to-pointer cast should preserve the source address"
    );
}

#[test]
fn typed_chc_translation_lowers_thin_pointer_to_integer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_ptr_to_int_cast_chc");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);

    let mut fb = mb.function("ptr_to_u32_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::Ptr);
    let cast = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U32, input);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "thin pointer-to-integer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported pointer-to-integer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(
            branch_arg.value(),
            ExprValue::BvExtract { expr, high: 31, low: 0 }
                if matches!(expr.value(), ExprValue::Var { name } if name == "bb0_v0")
        ),
        "ptrtoint Ptr to u32 should truncate the 64-bit address to the low 32 bits"
    );
}

#[test]
fn pointer_parts_roundtrip_lowers_without_unsupported_diagnostics() {
    let mut mb = ModuleBuilder::new("test_pointer_parts_roundtrip");
    let fat_str = Ty::FatPtr(FatPtrKind::Str);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::Ptr, Ty::U64]);

    let mut fb = mb.function("ptr_parts_roundtrip", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let data = fb.add_block_param(entry, Ty::Ptr);
    let len = fb.add_block_param(entry, Ty::U64);
    let fat = fb.ptr_from_parts(fat_str.clone(), Ty::U64, data, len);
    let copied_fat = fb.copy(fat_str.clone(), fat);
    let roundtrip_data = fb.ptr_data(fat_str.clone(), copied_fat);
    let roundtrip_len = fb.ptr_metadata(fat_str, Ty::U64, copied_fat);
    fb.ret(vec![roundtrip_data, roundtrip_len]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let bmc_vcs = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(bmc_vcs.len(), 1);
    assert!(
        bmc_vcs[0].violations.iter().all(|violation| violation.kind != PropertyKind::Other),
        "PtrFromParts facts should make local PtrData/PtrMetadata lowering precise in BMC"
    );

    let outputs = trust_ir_to_chc_translation_outputs(&module, &options);
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "PtrFromParts facts should make local PtrData/PtrMetadata lowering precise in CHC"
    );
}

/// Slice-length metadata is DETERMINISTIC per SSA fat value: two `PtrMetadata`
/// reads of the SAME `ValueId` must resolve to ONE symbol. A fresh symbol per
/// read makes any producer-asserted exact length (trust-ir-bridge's faithful
/// `&str` constant: `Assume(PtrMetadata(v) == len)`) silently inert — the fact
/// constrains one symbol while the `s.len()` read mints another. Reuse is
/// sound in both directions: the real metadata IS a function of the value, so
/// linking same-value reads only removes valuations with two readings for one
/// value; distinct values keep independent symbols (asserted by the negative
/// half below).
#[test]
fn typed_chc_translation_reuses_one_length_symbol_per_fat_value() {
    let fat_str = Ty::FatPtr(FatPtrKind::Str);

    // Same value read twice -> one slice_len symbol.
    let mut mb = ModuleBuilder::new("test_deterministic_slice_len");
    let ft = mb.add_func_type(vec![fat_str.clone()], vec![Ty::U64, Ty::U64]);
    let mut fb = mb.function("len_twice", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let v = fb.add_block_param(entry, fat_str.clone());
    let len_a = fb.ptr_metadata(fat_str.clone(), Ty::U64, v);
    let len_b = fb.ptr_metadata(fat_str.clone(), Ty::U64, v);
    fb.ret(vec![len_a, len_b]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "modeled U64 metadata must not fail closed");
    let slice_len_syms = outputs[0]
        .vc
        .vars()
        .iter()
        .filter(|var| var.name.contains("_slice_len_"))
        .count();
    assert_eq!(
        slice_len_syms, 1,
        "two PtrMetadata reads of one SSA value must share one length symbol"
    );

    // Distinct values -> independent symbols (no cross-value equality).
    let mut mb = ModuleBuilder::new("test_independent_slice_len");
    let ft = mb.add_func_type(vec![fat_str.clone(), fat_str.clone()], vec![Ty::U64, Ty::U64]);
    let mut fb = mb.function("len_of_each", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let v1 = fb.add_block_param(entry, fat_str.clone());
    let v2 = fb.add_block_param(entry, fat_str.clone());
    let len_1 = fb.ptr_metadata(fat_str.clone(), Ty::U64, v1);
    let len_2 = fb.ptr_metadata(fat_str, Ty::U64, v2);
    fb.ret(vec![len_1, len_2]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty());
    let slice_len_syms = outputs[0]
        .vc
        .vars()
        .iter()
        .filter(|var| var.name.contains("_slice_len_"))
        .count();
    assert_eq!(
        slice_len_syms, 2,
        "distinct fat values must keep independent length symbols"
    );
}

/// A `NonNull`-shaped single-pointer-newtype struct for the cast-leg tests.
fn nonnull_shaped_struct(mb: &mut ModuleBuilder) -> Ty {
    let id = StructId::new(0);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id,
        name: "NonNullShaped".to_owned(),
        fields: vec![FieldDef { name: "pointer".to_owned(), ty: Ty::Ptr, offset: None }],
        size: None,
        align: None,
    });
    Ty::Struct(id)
}

#[test]
fn typed_chc_usize_newtype_pack_unpack_lowers_exactly() {
    // The `fmt::Arguments` bit-packing: usize -> NonNull -> usize. Both legs are
    // bit-identity at the pinned 64-bit target, so the round trip must translate
    // with NO unsupported diagnostic and NO havoc stand-in — the unpacked value
    // is the packed operand itself. (Value-level falsification — the round trip
    // proves `== x` and refutes `== x + 1` — lives in the trust-mc-driver solve
    // tests; this pins the translation never falls to the fail-closed Cast arm.)
    let mut mb = ModuleBuilder::new("test_usize_newtype_pack_unpack");
    let newtype = nonnull_shaped_struct(&mut mb);
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("pack_unpack", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U64);
    let packed = fb.cast(CastOp::Bitcast, Ty::U64, newtype.clone(), x);
    let bits = fb.cast(CastOp::Bitcast, newtype, Ty::U64, packed);
    fb.ret(vec![bits]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "the usize<->newtype bit-identity legs must not fail closed: {:?}",
        outputs[0].diagnostics
    );
    let havoc_stand_ins = outputs[0]
        .vc
        .vars()
        .iter()
        .filter(|var| var.name.contains("unsupported_result"))
        .count();
    assert_eq!(havoc_stand_ins, 0, "neither leg may degrade to a havoc cast result");
}

#[test]
fn typed_chc_narrow_int_newtype_pack_stays_fail_closed() {
    // Only the POINTER-WIDTH unsigned spellings are bit-identical to the
    // newtype's address leaf. A `u32` pack is a genuine value reinterpretation
    // and must keep the fail-closed Cast refusal.
    let mut mb = ModuleBuilder::new("test_narrow_int_newtype_pack");
    let newtype = nonnull_shaped_struct(&mut mb);
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("narrow_pack", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let _packed = fb.cast(CastOp::Bitcast, Ty::U32, newtype, x);
    fb.ret(vec![]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].diagnostics.len(), 1);
    assert_eq!(outputs[0].diagnostics[0].reason, TrustIrChcUnsupportedReason::Cast);
}

#[test]
fn typed_chc_same_type_fat_bitcast_forwards_deterministic_metadata() {
    // `&str -> &[u8]` lowers as a same-type fat Bitcast. The real cast does not
    // change the fat pointer, so a metadata read through the cast result must
    // share the ORIGINAL value's deterministic `slice_len` symbol — one symbol,
    // not two (two symbols would let the solver give one real length two
    // readings, making a producer-asserted exact length inert).
    let fat_str = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("test_fat_bitcast_metadata_forwarding");
    let ft = mb.add_func_type(vec![fat_str.clone()], vec![Ty::U64, Ty::U64]);
    let mut fb = mb.function("len_through_cast", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let v = fb.add_block_param(entry, fat_str.clone());
    let len_direct = fb.ptr_metadata(fat_str.clone(), Ty::U64, v);
    let cast = fb.cast(CastOp::Bitcast, fat_str.clone(), fat_str.clone(), v);
    let len_via_cast = fb.ptr_metadata(fat_str, Ty::U64, cast);
    fb.ret(vec![len_direct, len_via_cast]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    let slice_len_syms = outputs[0]
        .vc
        .vars()
        .iter()
        .filter(|var| var.name.contains("_slice_len_"))
        .count();
    assert_eq!(
        slice_len_syms, 1,
        "a metadata read through a same-type fat Bitcast must reuse the operand's symbol"
    );
}

#[test]
fn typed_chc_mismatched_fat_bitcast_stays_fail_closed() {
    // A fat->fat cast BETWEEN different fat types is not the identity shape; it
    // must keep the fail-closed Cast refusal (no metadata forwarding either).
    let mut mb = ModuleBuilder::new("test_fat_bitcast_mismatch");
    let elem = mb.add_type(Ty::U32);
    let fat_str = Ty::FatPtr(FatPtrKind::Str);
    let fat_slice = Ty::FatPtr(FatPtrKind::Slice(elem));
    let ft = mb.add_func_type(vec![fat_str.clone()], vec![]);
    let mut fb = mb.function("fat_mismatch", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let v = fb.add_block_param(entry, fat_str.clone());
    let _cast = fb.cast(CastOp::Bitcast, fat_str, fat_slice, v);
    fb.ret(vec![]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].diagnostics.len(), 1);
    assert_eq!(outputs[0].diagnostics[0].reason, TrustIrChcUnsupportedReason::Cast);
}

#[test]
fn typed_chc_fat_to_thin_bitcast_is_the_data_lane() {
    // `*const [u8] -> *const u8` (the `as_ptr` leg): a fat value's SSA
    // expression IS its data lane, so the thin result translates exactly with
    // no unsupported diagnostic and no havoc stand-in.
    let fat_str = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("test_fat_to_thin_bitcast");
    let ft = mb.add_func_type(vec![fat_str.clone()], vec![Ty::Ptr]);
    let mut fb = mb.function("data_lane", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let v = fb.add_block_param(entry, fat_str.clone());
    let thin = fb.cast(CastOp::Bitcast, fat_str, Ty::Ptr, v);
    fb.ret(vec![thin]);
    fb.build();
    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    let havoc_stand_ins = outputs[0]
        .vc
        .vars()
        .iter()
        .filter(|var| var.name.contains("unsupported_result"))
        .count();
    assert_eq!(havoc_stand_ins, 0);
}

#[test]
fn typed_chc_translation_fails_closed_for_unknown_fat_pointer_metadata() {
    // A `dyn Trait` fat pointer's metadata is a VTABLE POINTER (Ty::Ptr), which is
    // NOT a bounded scalar we can soundly model — so it must still fail closed.
    // (Slice/str LENGTH metadata, Ty::U64, IS now modeled — see the test below.)
    let mut mb = ModuleBuilder::new("test_unknown_pointer_metadata");
    let fat_dyn = Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 });
    let ft = mb.add_func_type(vec![fat_dyn.clone()], vec![Ty::Ptr]);

    let mut fb = mb.function("unknown_ptr_metadata", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, fat_dyn.clone());
    let metadata = fb.ptr_metadata(fat_dyn, Ty::Ptr, ptr);
    fb.ret(vec![metadata]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].diagnostics.len(), 1);
    assert_eq!(outputs[0].diagnostics[0].reason, TrustIrChcUnsupportedReason::PointerMetadata);
}

#[test]
fn typed_chc_translation_models_slice_length_metadata() {
    // A slice/str fat pointer's metadata is its LENGTH (Ty::U64), which the
    // language bounds to [0, isize::MAX]. The CHC translator now models it as a
    // bounded symbolic (not an opaque unsupported value), so reading `s.len()`
    // produces NO unsupported diagnostic — letting the native CHC/PDR lane prove
    // obligations over slice lengths under `-Z trust-verify-full`.
    let mut mb = ModuleBuilder::new("test_slice_length_metadata");
    let fat_str = Ty::FatPtr(FatPtrKind::Str);
    let ft = mb.add_func_type(vec![fat_str.clone()], vec![Ty::U64]);

    let mut fb = mb.function("slice_length_metadata", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, fat_str.clone());
    let metadata = fb.ptr_metadata(fat_str, Ty::U64, ptr);
    fb.ret(vec![metadata]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "slice-length (U64) metadata is now soundly modeled, not unsupported: {:?}",
        outputs[0].diagnostics
    );
}

#[test]
fn typed_chc_translation_fails_closed_for_heap_and_global_addresses() {
    let mut mb = ModuleBuilder::new("test_heap_and_global_address_chc");
    mb.add_global(trust_ir::Global {
        name: "static_i32".to_string(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(trust_ir::constant::Constant::Int(0)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
    });
    let ft = mb.add_func_type(vec![], vec![]);

    let mut heap_fb = mb.function("heap_alloc_chc", ft);
    let heap_entry = heap_fb.create_block();
    heap_fb.switch_to_block(heap_entry);
    heap_fb.set_entry(heap_entry);
    let _ptr = heap_fb.heap_alloc(Ty::I32, None, None, AllocOrigin::RustHeap);
    heap_fb.ret(vec![]);
    heap_fb.build();

    let mut global_fb = mb.function("global_addr_chc", ft);
    let global_entry = global_fb.create_block();
    global_fb.switch_to_block(global_entry);
    global_fb.set_entry(global_entry);
    let _ptr = global_fb.global_addr(trust_ir::value::GlobalId::new(0));
    global_fb.ret(vec![]);
    global_fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);

    let heap = outputs
        .iter()
        .find(|output| output.diagnostics[0].function == "heap_alloc_chc")
        .expect("heap allocation diagnostic should be present");
    assert_eq!(heap.diagnostics.len(), 1);
    assert_eq!(heap.diagnostics[0].family, SemanticsFamily::MemoryProvenance);
    assert_eq!(heap.diagnostics[0].reason, TrustIrChcUnsupportedReason::HeapAllocation);
    assert!(
        heap.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "heap allocation must fail closed until modeled precisely"
    );

    let global = outputs
        .iter()
        .find(|output| output.diagnostics[0].function == "global_addr_chc")
        .expect("global address diagnostic should be present");
    assert_eq!(global.diagnostics.len(), 1);
    assert_eq!(global.diagnostics[0].family, SemanticsFamily::MemoryProvenance);
    assert_eq!(global.diagnostics[0].reason, TrustIrChcUnsupportedReason::GlobalAddress);
    assert!(
        global.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "global address materialization must fail closed until modeled precisely"
    );
}

#[test]
fn typed_chc_translation_fails_closed_for_symbol_address_constants() {
    let mut module = trust_ir::Module::new("test_symbol_address_constant_chc");
    let ft = module.add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false });
    let entry = trust_ir::value::BlockId::new(0);
    let symbol = trust_ir::value::ValueId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "symbol_addr_const_chc",
        ft,
        entry,
    );
    let mut block = trust_ir::Block::new(entry);
    block.body.push(
        trust_ir::node::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::Ptr,
            value: trust_ir::constant::Constant::SymbolAddr {
                symbol: "static_i32".to_string(),
                addend: 0,
            },
        })
        .with_result(symbol),
    );
    block.body.push(trust_ir::node::InstrNode::new(trust_ir::Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module.functions.push(func);

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::MemoryProvenance);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::SymbolAddress);
    assert_eq!(output.diagnostics[0].result_values, vec![symbol]);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "relocatable symbol constants must fail closed until modeled precisely"
    );
}

#[test]
fn typed_chc_translation_lowers_signed_integer_to_pointer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_int_to_ptr_cast_chc");
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);

    let mut fb = mb.function("i32_to_ptr_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::I32);
    let cast = fb.cast(CastOp::IntToPtr, Ty::I32, Ty::Ptr, input);
    fb.add_block_param(exit, Ty::Ptr);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "integer-to-thin-pointer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported integer-to-pointer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(
            branch_arg.value(),
            ExprValue::BvSignExtend { expr, extra_bits: 32 }
                if matches!(expr.value(), ExprValue::Var { name } if name == "bb0_v0")
        ),
        "inttoptr i32 to Ptr should sign-extend to the 64-bit address width"
    );
}

#[test]
fn typed_chc_translation_lowers_scalar_struct_field_insert_extract() {
    let mut mb = ModuleBuilder::new("test_scalar_struct_fields_chc");
    let pair_id = StructId::new(0);
    let pair_ty = Ty::Struct(pair_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: pair_id,
        name: "Pair".to_owned(),
        fields: vec![
            FieldDef { name: "x".to_owned(), ty: Ty::U32, offset: None },
            FieldDef { name: "flag".to_owned(), ty: Ty::Bool, offset: None },
        ],
        size: None,
        align: None,
    });
    let ft = mb.add_func_type(vec![pair_ty.clone(), Ty::U32], vec![]);

    let mut fb = mb.function("scalar_struct_fields_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let pair = fb.add_block_param(entry, pair_ty.clone());
    let replacement = fb.add_block_param(entry, Ty::U32);
    let pair_copy = fb.copy(pair_ty.clone(), pair);
    let updated_pair = fb.insert_field(pair_ty.clone(), pair_copy, 0, replacement);
    let updated_x = fb.extract_field(Ty::U32, updated_pair, 0);
    let updated_matches_replacement = fb.icmp(ICmpOp::Eq, Ty::U32, updated_x, replacement);
    fb.assert(updated_matches_replacement);
    fb.add_block_param(exit, pair_ty);
    fb.br(exit, vec![updated_pair]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "scalar struct field insert/extract should lower without unsupported diagnostics"
    );
    assert!(output.vc.relations.iter().any(|rel| rel.name == "bb0" && rel.arity() == 3));
    // Liveness-aware relation threading correctly drops the DEAD entry params
    // from `bb1`, so its arity is 2 (the two live successor scalars), not 5.
    // The suffix-2 assertions below pin those two live args
    // (`bb0_v1`, `bb0_v0_field1`) — which already match the actual head args —
    // so this is strictly more precise, not a weakening.
    assert!(output.vc.relations.iter().any(|rel| rel.name == "bb1" && rel.arity() == 2));

    let transition_args = head_arg_suffix(output, "bb1", 2);
    assert!(
        matches!(transition_args[0].value(), ExprValue::Var { name } if name == "bb0_v1"),
        "updated field should carry the replacement scalar into the successor relation"
    );
    assert!(
        matches!(transition_args[1].value(), ExprValue::Var { name } if name == "bb0_v0_field1"),
        "untouched field should preserve the original struct field in the successor relation"
    );
}

#[test]
fn typed_chc_translation_lowers_scalar_stack_store_load() {
    let mut mb = ModuleBuilder::new("test_scalar_stack_memory_chc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("scalar_stack_memory_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::U32);
    let slot = fb.alloca(Ty::U32);
    fb.store(Ty::U32, slot, input);
    let loaded = fb.load(Ty::U32, slot);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![loaded]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "single-cell scalar alloca/store/load should lower without unsupported diagnostics"
    );
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported scalar stack memory should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    assert!(
        matches!(branch_arg.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "load after store from the same scalar stack cell should preserve the stored typed value"
    );
}

#[test]
fn typed_chc_translation_lowers_scalar_struct_stack_store_load() {
    let mut mb = ModuleBuilder::new("test_scalar_struct_stack_memory_chc");
    let pair_id = StructId::new(0);
    let pair_ty = Ty::Struct(pair_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: pair_id,
        name: "Pair".to_owned(),
        fields: vec![
            FieldDef { name: "x".to_owned(), ty: Ty::U32, offset: None },
            FieldDef { name: "flag".to_owned(), ty: Ty::Bool, offset: None },
        ],
        size: None,
        align: None,
    });
    let ft = mb.add_func_type(vec![pair_ty.clone()], vec![]);

    let mut fb = mb.function("scalar_struct_stack_memory_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let pair = fb.add_block_param(entry, pair_ty.clone());
    let slot = fb.alloca(pair_ty.clone());
    fb.store(pair_ty.clone(), slot, pair);
    let loaded = fb.load(pair_ty, slot);
    let loaded_x = fb.extract_field(Ty::U32, loaded, 0);
    let loaded_flag = fb.extract_field(Ty::Bool, loaded, 1);
    fb.add_block_param(exit, Ty::U32);
    fb.add_block_param(exit, Ty::Bool);
    fb.br(exit, vec![loaded_x, loaded_flag]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "single-cell scalar-field aggregate alloca/store/load should lower without unsupported diagnostics"
    );
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported aggregate stack memory should not introduce unsupported error rules"
    );

    let transition_args = head_arg_suffix(output, "bb1", 2);
    assert!(
        matches!(transition_args[0].value(), ExprValue::Var { name } if name == "bb0_v0_field0"),
        "loaded struct field 0 should preserve the stored aggregate field"
    );
    assert!(
        matches!(transition_args[1].value(), ExprValue::Var { name } if name == "bb0_v0_field1"),
        "loaded struct field 1 should preserve the stored aggregate field"
    );
}

#[test]
fn typed_chc_translation_lowers_direct_scalar_leaf_call() {
    let mut mb = ModuleBuilder::new("test_direct_scalar_leaf_call_chc");
    let callee_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("inc_u32_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U32);
    let one = fb.iconst(Ty::U32, 1);
    let incremented = fb.add(Ty::U32, input, one);
    fb.ret(vec![incremented]);
    fb.build();

    let mut fb = mb.function("caller_uses_inc_u32_chc", caller_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_input = fb.add_block_param(entry, Ty::U32);
    let call_result = fb.call(trust_ir::value::FuncId::new(0), vec![caller_input]);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![call_result]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported scalar leaf direct call should lower without unsupported diagnostics"
    );
    let arg = &head_arg_suffix(caller, "bb1", 1)[0];
    let ExprValue::BvAdd(lhs, rhs) = arg.value() else {
        panic!("direct call return should be the callee add expression, got {arg:?}");
    };
    assert!(
        matches!(lhs.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "callee parameter should be bound to the caller argument, not to a colliding callee SSA id"
    );
    assert!(
        matches!(rhs.value(), ExprValue::BitVecConst { value, width } if value.to_string() == "1" && *width == 32),
        "callee constant should be preserved in the inlined call summary"
    );
    assert!(
        caller.vc.rules.iter().any(|rule| {
            rule.head.name == "error"
                && rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0")
        }),
        "callee arithmetic safety conditions should be propagated into the caller CHC VC"
    );
}

#[test]
fn typed_chc_translation_fails_closed_for_recursive_direct_call() {
    let mut mb = ModuleBuilder::new("test_recursive_direct_call_chc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);

    let mut fb = mb.function("countdown_recursive_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U32);
    let call_result = fb.call(trust_ir::value::FuncId::new(0), vec![input]);
    fb.ret(vec![call_result]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::Calls);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::RecursiveDirectCall);
    assert_eq!(output.diagnostics[0].function, "countdown_recursive_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert_eq!(output.diagnostics[0].result_values, vec![call_result]);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "recursive direct calls must fail closed instead of silently using a symbolic summary"
    );
}

#[test]
fn typed_chc_translation_fails_closed_for_unsummarizable_direct_call() {
    let mut mb = ModuleBuilder::new("test_unsummarizable_direct_call_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let caller_ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);

    let mut fb = mb.function("loads_through_pointer_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let loaded = fb.load(Ty::I32, ptr);
    fb.ret(vec![loaded]);
    fb.build();

    let mut fb = mb.function("caller_uses_pointer_loader_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_ptr = fb.add_block_param(entry, Ty::Ptr);
    let call_result = fb.call(trust_ir::value::FuncId::new(0), vec![caller_ptr]);
    fb.ret(vec![call_result]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert_eq!(caller.diagnostics.len(), 1);
    assert_eq!(caller.diagnostics[0].family, SemanticsFamily::Calls);
    assert_eq!(
        caller.diagnostics[0].reason,
        TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
    );
    assert_eq!(caller.diagnostics[0].function, "caller_uses_pointer_loader_chc");
    assert_eq!(caller.diagnostics[0].block, entry);
    assert_eq!(caller.diagnostics[0].instruction_index, 0);
    assert_eq!(caller.diagnostics[0].result_values, vec![call_result]);
    assert!(
        caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "known direct calls that cannot be summarized must fail closed"
    );
}

#[test]
fn typed_chc_translation_fails_closed_for_heap_alloc_and_global_addr() {
    let mut mb = ModuleBuilder::new("test_heap_global_chc");
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("heap_global_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let heap = fb.heap_alloc(Ty::I32, None, None, trust_ir::inst::AllocOrigin::RustHeap);
    let _global = fb.global_addr(trust_ir::value::GlobalId::new(0));
    fb.ret(vec![heap]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let reasons =
        outputs[0].diagnostics.iter().map(|diagnostic| diagnostic.reason).collect::<Vec<_>>();
    assert!(reasons.contains(&TrustIrChcUnsupportedReason::HeapAllocation));
    assert!(reasons.contains(&TrustIrChcUnsupportedReason::GlobalAddress));
    assert!(
        outputs[0].vc.rules.iter().any(|rule| rule.head.name == "error"),
        "heap/global pointer semantics must fail closed in CHC"
    );
}

#[test]
fn typed_chc_translation_propagates_direct_call_assertion() {
    let mut mb = ModuleBuilder::new("test_direct_call_assertion_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("requires_flag_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let flag = fb.add_block_param(entry, Ty::Bool);
    fb.assert(flag);
    fb.ret(vec![]);
    fb.build();

    let mut fb = mb.function("caller_checks_flag_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_flag = fb.add_block_param(entry, Ty::Bool);
    fb.call_void(trust_ir::value::FuncId::new(0), vec![caller_flag]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported void direct call should lower without unsupported diagnostics"
    );
    let Some(error_rule) = caller.vc.rules.iter().find(|rule| rule.head.name == "error") else {
        panic!("callee assertion should produce a caller error rule");
    };
    assert!(
        error_rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0"),
        "callee assertion should be guarded by the caller block relation"
    );
    assert!(
        error_rule.body.constraints.iter().any(|constraint| {
            matches!(
                constraint.value(),
                ExprValue::Not(inner)
                    if matches!(inner.value(), ExprValue::Var { name } if name == "bb0_v0")
            )
        }),
        "callee assertion should be expressed over the caller argument"
    );
}

#[test]
fn typed_chc_translation_summarizes_direct_call_with_unreachable_panic_block() {
    // A callee whose FALSE branch is a panic block ending in `Inst::Unreachable`
    // (Trust's panic lowering shape: `Assert(false)` then `Unreachable`, here just the
    // terminator). BEFORE handling `Inst::Unreachable` in the call-summary interpreter,
    // the panic block was not `terminated`, the whole summary returned `None`, and the
    // call was conservatively modeled as an UNCONDITIONAL may-panic
    // (UnsupportedDirectCallSummary) — so a caller of even a TOTAL callee could not be
    // proved panic-free (the `type_min` -> `signed_min` gap). The interpreter now
    // summarizes the callee and records the panic as a GUARDED error condition, so:
    //   * a reachable panic (this test: `!flag`) STILL surfaces as a caller error rule
    //     (refutable — no false-PROVE), and
    //   * a guarded/total callee's panic becomes UNSAT under its dominating guards, so
    //     the caller proves panic-free (validated end-to-end by `type_min`).
    let mut mb = ModuleBuilder::new("test_direct_call_unreachable_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    // callee may_panic(flag): `if flag { ret } else { unreachable }` — panics iff !flag.
    let mut fb = mb.function("may_panic_chc", callee_ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let flag = fb.add_block_param(entry, Ty::Bool);
    fb.condbr(flag, ok, vec![], panic, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![]);
    fb.switch_to_block(panic);
    fb.unreachable();
    fb.build();

    // caller(flag): `may_panic(flag); ret` — forwards an unconstrained flag.
    let mut fb = mb.function("caller_of_may_panic_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_flag = fb.add_block_param(entry, Ty::Bool);
    fb.call_void(trust_ir::value::FuncId::new(0), vec![caller_flag]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "a callee with an `Unreachable` panic block must summarize cleanly (no \
         UnsupportedDirectCallSummary), got {:?}",
        caller.diagnostics
    );
    let error_rule =
        caller.vc.rules.iter().find(|rule| rule.head.name == "error").expect(
            "a reachable callee `Unreachable` must produce a caller error rule (refutable)",
        );
    assert!(
        error_rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0"),
        "the panic path must be guarded by the caller block relation"
    );
    // The error must be GUARDED by the caller flag (reachable exactly when the flag is
    // false: the `!flag` else-branch path), NOT an unconditional may-panic. The exact
    // AST is `And([Not(bb0_v0), true])` (branch path guard `¬flag` ∧ the Unreachable
    // marker), so we assert the flag is referenced rather than pinning the shape — an
    // unconditional (old conservative) error rule would not mention `bb0_v0`.
    assert!(
        !error_rule.body.constraints.is_empty()
            && format!("{:?}", error_rule.body.constraints).contains("bb0_v0"),
        "the panic must be GUARDED by the caller flag (reachable iff !flag), not \
         unconditional; constraints: {:?}",
        error_rule.body.constraints
    );
}

#[test]
fn typed_chc_translation_summarizes_direct_call_with_checked_overflow() {
    // The operative `type_min` -> `signed_min` shape: a callee performing a Rust
    // `CheckedBinaryOp` (`Inst::Overflow`, here `width - 1` as a `SubOverflow`) whose
    // overflow flag branches to a panic block ending in `Unreachable`. BEFORE handling
    // `Inst::Overflow` in the call-summary interpreter it bailed
    // (UnsupportedDirectCallSummary), so the caller was conservatively modeled as an
    // unconditional may-panic and could not be proved panic-free. Now the interpreter
    // summarizes the callee and propagates the overflow obligation as a GUARDED caller
    // error rule (reachable exactly when the op overflows), so a real overflow refutes
    // (no false-PROVE) while a guarded/total callee discharges (proved end-to-end by
    // `type_min`).
    let mut mb = ModuleBuilder::new("test_direct_call_checked_overflow_chc");
    let callee_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32], vec![]);

    // callee dec(n): `let (v, ovf) = n.overflowing_sub(1); if ovf { unreachable } else { v }`
    let mut fb = mb.function("dec_chk_chc", callee_ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U32);
    let one = fb.iconst(Ty::U32, 1);
    let (value, flag) = fb.overflow(OverflowOp::SubOverflow, Ty::U32, n, one);
    fb.condbr(flag, panic, vec![], ok, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![value]);
    fb.switch_to_block(panic);
    fb.unreachable();
    fb.build();

    // caller(n): `dec(n); ret` — forwards an unconstrained n.
    let mut fb = mb.function("caller_of_dec_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_n = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_n]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "a callee doing a checked-overflow op (`Inst::Overflow`) into an `Unreachable` \
         panic block must summarize cleanly (no UnsupportedDirectCallSummary), got {:?}",
        caller.diagnostics
    );
    let error_rule = caller
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "error")
        .expect("the checked-sub overflow must propagate as a caller error rule (refutable)");
    // The error must be GUARDED by the overflow flag (reachable iff `n` underflows: the
    // op result depends on `bb0_v0`), not an unconditional may-panic.
    assert!(
        error_rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0")
            && format!("{:?}", error_rule.body.constraints).contains("bb0_v0"),
        "the overflow panic must be GUARDED by the caller argument, not unconditional; \
         constraints: {:?}",
        error_rule.body.constraints
    );
}

#[test]
fn typed_chc_translation_summarizes_direct_call_with_signed_negation() {
    // A callee performing a signed negation `-x` (`Inst::UnOp { Neg }` — the shape of
    // `signed_min`'s `-(1 << (width-1))`). The main translate leaves `Inst::UnOp`
    // UNSUPPORTED (havoc + error rule); the call-summary interpreter models it precisely
    // and records the OverflowNeg obligation (`-x` overflows iff `x == INT_MIN`) as a
    // GUARDED caller error rule — so an unguarded `-(i64::MIN)` refutes (no false-PROVE)
    // while a guarded operand discharges (proved end-to-end by `signed_min`/`type_min`).
    let mut mb = ModuleBuilder::new("test_direct_call_signed_negation_chc");
    let callee_ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let caller_ft = mb.add_func_type(vec![Ty::I64], vec![]);

    let mut fb = mb.function("negate_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::I64);
    let neg = fb.unop(UnOp::Neg, Ty::I64, x);
    fb.ret(vec![neg]);
    fb.build();

    let mut fb = mb.function("caller_of_negate_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_x = fb.add_block_param(entry, Ty::I64);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_x]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "a callee doing a signed negation must summarize cleanly (no \
         UnsupportedDirectCallSummary), got {:?}",
        caller.diagnostics
    );
    let error_rule =
        caller.vc.rules.iter().find(|rule| rule.head.name == "error").expect(
            "the neg-overflow obligation must propagate as a caller error rule (refutable)",
        );
    assert!(
        format!("{:?}", error_rule.body.constraints).contains("bb0_v0"),
        "the neg-overflow panic must be GUARDED by the caller argument (x == INT_MIN), \
         not unconditional; constraints: {:?}",
        error_rule.body.constraints
    );
}

#[test]
fn typed_chc_translation_summarizes_realcall_parity_toggle_as_not_acc() {
    // G2 GUARD TEST (Finding 1): the count-parity realcall loop's body is a direct
    // call to `xor_accumulate_parity(acc) = acc ^ true` (== !acc). translate_chc
    // must SUMMARIZE that call into the caller's transition — binding the return
    // to the REAL boolean value `!acc`, NOT a fresh havoc symbolic — so the G2 IC3
    // loop lane sees an `acc' == !acc` transition rather than an unconstrained
    // call. This machinery already exists (`try_direct_call_summary` →
    // `bind_call_result`, Bool-BinOp arm); if it ever regresses to havoc, the
    // summarized effect vanishes and the whole G2 real-call milestone breaks.
    let mut mb = ModuleBuilder::new("test_realcall_parity_toggle_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    // callee `xor_accumulate_parity(acc) = acc ^ true`  (total → summarizable).
    let callee_id = {
        let mut fb = mb.function("xor_accumulate_parity_chc", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let acc = fb.add_block_param(entry, Ty::Bool);
        let t = fb.bool_const(true);
        let toggled = fb.binop(BinOp::Xor, Ty::Bool, acc, t);
        fb.ret(vec![toggled]);
        fb.build()
    };

    // caller `f(acc)`: r = xor_accumulate_parity(acc); assert!(r).
    // r == !acc, so `assert!(r)` fails exactly when acc is true — a guard over the
    // REAL caller argument `bb0_v0`. Under a havoc, the guard would be over a
    // fresh call-result symbol instead, and `bb0_v0` would not appear.
    {
        let mut fb = mb.function("caller_toggles_parity_chc", caller_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let caller_acc = fb.add_block_param(entry, Ty::Bool);
        let r = fb.call(callee_id, vec![caller_acc]);
        fb.assert(r);
        fb.ret(vec![]);
        fb.build();
    }

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2, "callee + caller");

    // The direct call to a TOTAL bool-xor callee must be summarized cleanly —
    // never fail-closed to a havoc / unsupported-summary.
    let unsupported = outputs.iter().flat_map(|o| o.diagnostics.iter()).any(|d| {
        d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
            || d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall
    });
    assert!(!unsupported, "the `acc ^ true` realcall must be summarized, not havoced/fail-closed");

    let caller = &outputs[1];
    let error_rule = caller
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "error")
        .expect("assert!(r) over the summarized call must propagate a caller error rule");

    // Load-bearing: the assertion guard is expressed over the REAL caller argument
    // `bb0_v0` (acc). A havoced call would guard over a fresh call-result symbol,
    // so `bb0_v0` would NOT appear. This is the structural witness that the call
    // was summarized to `!acc` (acc' == !acc), not havoced.
    assert!(
        format!("{:?}", error_rule.body.constraints).contains("bb0_v0"),
        "the summarized `acc ^ true` return must bind to the caller argument \
         (acc' == !acc), so the assert guard references bb0_v0; constraints: {:?}",
        error_rule.body.constraints
    );
}

#[test]
fn typed_chc_translation_declines_direct_call_with_no_terminator_leaf() {
    // CASE-2 SOUNDNESS SENTINEL — the reverted `7e5a2e345` false-proof class.
    //
    // A callee whose block falls off the end with NO terminator models a MALFORMED
    // CFG in which a successor EDGE was dropped (trust-ir's validator forbids a
    // missing terminator: `BlockMissingTerminator`). The dropped edge can lead to a
    // panic — e.g. the `?`/`Try::branch` continuation holding a post-`?`
    // `assert!(x == 0)`. The unsound predecessor of the fix treated such a leaf as a
    // clean havoc-return + `continue`, so the dropped block's panic vanished from the
    // summary → a false PROVE (`let x = r?; assert!(x == 0); Ok(x)` over an
    // unconstrained `Result` reported "1 proved").
    //
    // The fix FAILS CLOSED: `try_direct_call_summary` returns `None`, so the caller
    // gets an `UnsupportedDirectCallSummary` diagnostic + an unconditional (TOP) error
    // rule — i.e. the caller is NOT proved. If this test ever sees empty `diagnostics`
    // or no caller error rule, CASE 2 has leaked back in (the call was summarized as
    // clean, masking the dropped panic).
    let mut mb = ModuleBuilder::new("test_direct_call_no_terminator_leaf_chc");
    let callee_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32], vec![]);

    // callee `falloff(x)`: entry block with a param but NO terminator — it falls off
    // the end of its body (a dropped successor edge), exactly the CASE-2 shape.
    let mut fb = mb.function("falloff_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let _x = fb.add_block_param(entry, Ty::U32);
    // Deliberately NO `ret` / `br` / `unreachable`: a no-terminator leaf.
    fb.build();

    // caller `caller_of_falloff(x)`: `falloff(x); ret`.
    let mut fb = mb.function("caller_of_falloff_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_x = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_x]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        !caller.diagnostics.is_empty(),
        "a no-terminator-leaf callee MUST be DECLINED (UnsupportedDirectCallSummary), \
         never summarized as clean — CASE 2 leaked back if diagnostics is empty"
    );
    caller.vc.rules.iter().find(|rule| rule.head.name == "error").expect(
        "declining a malformed (no-terminator) callee must emit an unconditional \
             caller error rule (TOP / may-panic), i.e. the caller is NOT proved",
    );
}

#[test]
fn typed_chc_translation_lowers_direct_scalar_multiblock_call() {
    let mut mb = ModuleBuilder::new("test_direct_scalar_multiblock_call_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("choose_and_inc_u32_chc", callee_ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let choose_lhs = fb.add_block_param(entry, Ty::Bool);
    let lhs = fb.add_block_param(entry, Ty::U32);
    let rhs = fb.add_block_param(entry, Ty::U32);
    let selected = fb.add_block_param(join, Ty::U32);
    fb.condbr(choose_lhs, join, vec![lhs], join, vec![rhs]);
    fb.switch_to_block(join);
    let one = fb.iconst(Ty::U32, 1);
    let incremented = fb.add(Ty::U32, selected, one);
    fb.ret(vec![incremented]);
    fb.build();

    let mut fb = mb.function("caller_uses_choose_and_inc_chc", caller_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_choose_lhs = fb.add_block_param(entry, Ty::Bool);
    let caller_lhs = fb.add_block_param(entry, Ty::U32);
    let caller_rhs = fb.add_block_param(entry, Ty::U32);
    let call_result =
        fb.call(trust_ir::value::FuncId::new(0), vec![caller_choose_lhs, caller_lhs, caller_rhs]);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![call_result]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported scalar multi-block direct call should lower without unsupported diagnostics"
    );
    let branch_arg = &head_arg_suffix(caller, "bb1", 1)[0];
    let ExprValue::Ite { cond, then_expr, else_expr } = branch_arg.value() else {
        panic!("multi-block direct call should lower to a path-sensitive ite, got {branch_arg:?}");
    };
    assert!(
        matches!(cond.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "callee branch guard should be expressed over the caller condition"
    );
    assert!(
        matches!(
            then_expr.value(),
            ExprValue::BvAdd(lhs, rhs)
                if matches!(lhs.value(), ExprValue::Var { name } if name == "bb0_v1")
                    && matches!(rhs.value(), ExprValue::BitVecConst { value, width } if value.to_string() == "1" && *width == 32)
        ),
        "then branch should add one to the caller lhs"
    );
    assert!(
        matches!(
            else_expr.value(),
            ExprValue::BvAdd(lhs, rhs)
                if matches!(lhs.value(), ExprValue::Var { name } if name == "bb0_v2")
                    && matches!(rhs.value(), ExprValue::BitVecConst { value, width } if value.to_string() == "1" && *width == 32)
        ),
        "else branch should add one to the caller rhs"
    );
}

#[test]
fn typed_chc_translation_propagates_multiblock_direct_call_assertion_guard() {
    let mut mb = ModuleBuilder::new("test_multiblock_direct_call_assertion_guard_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![]);

    let mut fb = mb.function("maybe_requires_flag_chc", callee_ft);
    let entry = fb.create_block();
    let check = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let should_check = fb.add_block_param(entry, Ty::Bool);
    let flag = fb.add_block_param(entry, Ty::Bool);
    let check_flag = fb.add_block_param(check, Ty::Bool);
    fb.condbr(should_check, check, vec![flag], exit, vec![]);
    fb.switch_to_block(check);
    fb.assert(check_flag);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let mut fb = mb.function("caller_maybe_checks_flag_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_should_check = fb.add_block_param(entry, Ty::Bool);
    let caller_flag = fb.add_block_param(entry, Ty::Bool);
    fb.call_void(trust_ir::value::FuncId::new(0), vec![caller_should_check, caller_flag]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported scalar multi-block assertion should lower without unsupported diagnostics"
    );
    let Some(error_rule) = caller.vc.rules.iter().find(|rule| rule.head.name == "error") else {
        panic!("callee assertion should produce a caller error rule");
    };
    assert!(
        error_rule.body.constraints.iter().any(|constraint| {
            matches!(
                constraint.value(),
                ExprValue::And(clauses)
                    if clauses
                        .iter()
                        .any(|clause| matches!(clause.value(), ExprValue::Var { name } if name == "bb0_v0"))
                        && clauses.iter().any(|clause| {
                            matches!(
                                clause.value(),
                                ExprValue::Not(inner)
                                    if matches!(inner.value(), ExprValue::Var { name } if name == "bb0_v1")
                            )
                        })
            )
        }),
        "callee assertion should be guarded by the caller branch condition"
    );
}

#[test]
fn typed_chc_translation_summarizes_paramless_merge_value_return() {
    // Reproduces the lowering shape of `divide_safe`/`unsigned_subtract_safe`: a
    // guarded value flows to a PARAMLESS merge block that `Return`s a value
    // defined on only one incoming path. The direct-call summary must resolve the
    // undefined-on-path return to a fresh symbolic (mirroring the main
    // translation) instead of bailing to an unconditional unsupported-error rule,
    // which produced a spurious counterexample and made a caller's whole-function
    // panic-freedom unprovable.
    let mut mb = ModuleBuilder::new("test_paramless_merge_value_return_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("guarded_value_chc", callee_ft);
    let entry = fb.create_block();
    let then_b = fb.create_block();
    let else_b = fb.create_block();
    let merge = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.condbr(cond, then_b, vec![], else_b, vec![]);
    fb.switch_to_block(then_b);
    let then_val = fb.iconst(Ty::U32, 7);
    fb.br(merge, vec![]);
    fb.switch_to_block(else_b);
    let _else_val = fb.iconst(Ty::U32, 9);
    fb.br(merge, vec![]);
    fb.switch_to_block(merge);
    // `then_val` is defined only on the then-path; the merge block carries no
    // params to thread it, so the else-path reaches this `Return` with `then_val`
    // undefined.
    fb.ret(vec![then_val]);
    fb.build();

    let mut fb = mb.function("caller_discards_value_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_cond = fb.add_block_param(entry, Ty::Bool);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_cond]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "paramless-merge value return must summarize without unsupported diagnostics, got {:?}",
        caller.diagnostics
    );
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "a non-panicking callee returned through a paramless merge must not inject a spurious error rule"
    );
}

#[test]
fn typed_chc_translation_paramless_merge_preserves_branch_panic() {
    // Soundness guard for the paramless-merge return fix: minting a fresh value
    // for the undefined-on-path return must NOT suppress an error condition raised
    // on the OTHER path. The else-branch subtracts (unsigned underflow when
    // x < y) and returns the result through a paramless merge; the caller must
    // still receive the guarded error rule. This is the no-false-proof check.
    let mut mb = ModuleBuilder::new("test_paramless_merge_panic_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("maybe_subtracts_chc", callee_ft);
    let entry = fb.create_block();
    let safe_b = fb.create_block();
    let sub_b = fb.create_block();
    let merge = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let x = fb.add_block_param(entry, Ty::U32);
    let y = fb.add_block_param(entry, Ty::U32);
    fb.condbr(cond, safe_b, vec![], sub_b, vec![]);
    fb.switch_to_block(safe_b);
    fb.br(merge, vec![]);
    fb.switch_to_block(sub_b);
    let diff = fb.sub(Ty::U32, x, y); // unsigned underflow obligation when x < y
    fb.br(merge, vec![]);
    fb.switch_to_block(merge);
    // `diff` is defined only on the sub-path; safe-path reaches this Return with
    // `diff` undefined (-> fresh symbolic), but the underflow error condition on
    // the sub-path must survive.
    fb.ret(vec![diff]);
    fb.build();

    let mut fb = mb.function("caller_maybe_subtracts_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let c = fb.add_block_param(entry, Ty::Bool);
    let cx = fb.add_block_param(entry, Ty::U32);
    let cy = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![c, cx, cy]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "subtraction through a paramless merge should summarize without unsupported diagnostics, got {:?}",
        caller.diagnostics
    );
    assert!(
        caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "unsigned underflow on the sub-branch must still surface a guarded caller error rule (soundness)"
    );
}

#[test]
fn typed_chc_translation_summarizes_direct_call_with_overflow_intrinsic() {
    // `Inst::Overflow` (checked arithmetic) must be modeled by the direct-call
    // summary, not bailed on. A callee that performs a checked add and asserts on
    // the overflow flag must (a) summarize WITHOUT an unsupported diagnostic (the
    // new Overflow arm — previously this hit `_ => return None` ->
    // UnsupportedDirectCallSummary), and (b) flow the modeled overflow flag into a
    // caller error rule (soundness: the obligation is not silently dropped).
    let mut mb = ModuleBuilder::new("test_direct_call_overflow_intrinsic_chc");
    let callee_ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("checked_add_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::U32);
    let b = fb.add_block_param(entry, Ty::U32);
    let (sum, ovf) = fb.overflow(OverflowOp::AddOverflow, Ty::U32, a, b);
    // Reference the modeled overflow flag in an obligation. (a + b) can overflow
    // for unconstrained inputs, so this assert is genuinely dischargeable-or-not
    // depending on the flag the Overflow arm produces.
    fb.assert(ovf);
    fb.ret(vec![sum]);
    fb.build();

    let mut fb = mb.function("caller_checked_add_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let ca = fb.add_block_param(entry, Ty::U32);
    let cb = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![ca, cb]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "checked-arithmetic direct call should summarize without unsupported diagnostics, got {:?}",
        caller.diagnostics
    );
    assert!(
        caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "the modeled overflow flag must flow into a caller error rule (soundness)"
    );
}

#[test]
fn typed_chc_translation_summarizes_direct_call_with_boolean_binop() {
    // A direct call whose callee combines comparisons with a boolean `And`
    // (the `x == i32::MIN && y == -1` guard shape in signed division) must
    // summarize: the bool `BinOp` arm models the connective via `eval_binop`
    // instead of falling past the integer-only `if ty.is_integer()` arm to
    // `_ => return None` (which injected a spurious caller counterexample).
    let mut mb = ModuleBuilder::new("test_direct_call_bool_binop_chc");
    let callee_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![]);
    let caller_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![]);

    let mut fb = mb.function("both_zero_guard_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let zero = fb.iconst(Ty::I32, 0);
    let a_zero = fb.icmp(ICmpOp::Eq, Ty::I32, a, zero);
    let b_zero = fb.icmp(ICmpOp::Eq, Ty::I32, b, zero);
    let both = fb.binop(BinOp::And, Ty::Bool, a_zero, b_zero);
    fb.assert(both);
    fb.ret(vec![]);
    fb.build();

    let mut fb = mb.function("caller_both_zero_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let ca = fb.add_block_param(entry, Ty::I32);
    let cb = fb.add_block_param(entry, Ty::I32);
    fb.call_void(trust_ir::value::FuncId::new(0), vec![ca, cb]);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "boolean-And direct call should summarize without unsupported diagnostics, got {:?}",
        caller.diagnostics
    );
    assert!(
        caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "the asserted boolean guard must flow into a caller error rule"
    );
}

#[test]
fn typed_chc_translation_lowers_direct_aggregate_param_return_call() {
    let mut mb = ModuleBuilder::new("test_direct_aggregate_call_chc");
    let pair_id = StructId::new(0);
    let pair_ty = Ty::Struct(pair_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: pair_id,
        name: "Pair".to_owned(),
        fields: vec![
            FieldDef { name: "x".to_owned(), ty: Ty::U32, offset: None },
            FieldDef { name: "flag".to_owned(), ty: Ty::Bool, offset: None },
        ],
        size: None,
        align: None,
    });
    let callee_ft = mb.add_func_type(vec![pair_ty.clone(), Ty::U32], vec![pair_ty.clone()]);
    let caller_ft = mb.add_func_type(vec![pair_ty.clone(), Ty::U32], vec![]);

    let mut fb = mb.function("replace_pair_x_chc", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let pair = fb.add_block_param(entry, pair_ty.clone());
    let replacement = fb.add_block_param(entry, Ty::U32);
    let updated_pair = fb.insert_field(pair_ty.clone(), pair, 0, replacement);
    fb.ret(vec![updated_pair]);
    fb.build();

    let mut fb = mb.function("caller_uses_replace_pair_x_chc", caller_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_pair = fb.add_block_param(entry, pair_ty.clone());
    let caller_replacement = fb.add_block_param(entry, Ty::U32);
    let call_result =
        fb.call(trust_ir::value::FuncId::new(0), vec![caller_pair, caller_replacement]);
    let result_x = fb.extract_field(Ty::U32, call_result, 0);
    let result_flag = fb.extract_field(Ty::Bool, call_result, 1);
    fb.add_block_param(exit, Ty::U32);
    fb.add_block_param(exit, Ty::Bool);
    fb.br(exit, vec![result_x, result_flag]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported aggregate direct call should lower without unsupported diagnostics"
    );
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported aggregate direct call should not introduce unsupported error rules"
    );
    let transition_args = head_arg_suffix(caller, "bb1", 2);
    assert!(
        matches!(transition_args[0].value(), ExprValue::Var { name } if name == "bb0_v1"),
        "aggregate return field 0 should carry the replacement scalar"
    );
    assert!(
        matches!(transition_args[1].value(), ExprValue::Var { name } if name == "bb0_v0_field1"),
        "aggregate return field 1 should preserve the original aggregate field"
    );
}

#[test]
fn typed_chc_translation_combines_multiblock_direct_aggregate_return_call() {
    let mut mb = ModuleBuilder::new("test_multiblock_aggregate_call_chc");
    let pair_id = StructId::new(0);
    let pair_ty = Ty::Struct(pair_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: pair_id,
        name: "Pair".to_owned(),
        fields: vec![
            FieldDef { name: "x".to_owned(), ty: Ty::U32, offset: None },
            FieldDef { name: "flag".to_owned(), ty: Ty::Bool, offset: None },
        ],
        size: None,
        align: None,
    });
    let callee_ft =
        mb.add_func_type(vec![Ty::Bool, pair_ty.clone(), pair_ty.clone()], vec![pair_ty.clone()]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, pair_ty.clone(), pair_ty.clone()], vec![]);

    let mut fb = mb.function("choose_pair_chc", callee_ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let choose_lhs = fb.add_block_param(entry, Ty::Bool);
    let lhs = fb.add_block_param(entry, pair_ty.clone());
    let rhs = fb.add_block_param(entry, pair_ty.clone());
    let selected = fb.add_block_param(join, pair_ty.clone());
    fb.condbr(choose_lhs, join, vec![lhs], join, vec![rhs]);
    fb.switch_to_block(join);
    fb.ret(vec![selected]);
    fb.build();

    let mut fb = mb.function("caller_uses_choose_pair_chc", caller_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_choose_lhs = fb.add_block_param(entry, Ty::Bool);
    let caller_lhs = fb.add_block_param(entry, pair_ty.clone());
    let caller_rhs = fb.add_block_param(entry, pair_ty);
    let call_result =
        fb.call(trust_ir::value::FuncId::new(0), vec![caller_choose_lhs, caller_lhs, caller_rhs]);
    let result_x = fb.extract_field(Ty::U32, call_result, 0);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![result_x]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "supported multi-block aggregate direct call should lower without unsupported diagnostics"
    );
    let branch_arg = &head_arg_suffix(caller, "bb1", 1)[0];
    let ExprValue::Ite { cond, then_expr, else_expr } = branch_arg.value() else {
        panic!("aggregate return should lower to a field-wise ite, got {branch_arg:?}");
    };
    assert!(
        matches!(cond.value(), ExprValue::Var { name } if name == "bb0_v0"),
        "aggregate return guard should be expressed over the caller condition"
    );
    assert!(
        matches!(then_expr.value(), ExprValue::Var { name } if name == "bb0_v1_field0"),
        "then aggregate field should come from the caller lhs"
    );
    assert!(
        matches!(else_expr.value(), ExprValue::Var { name } if name == "bb0_v2_field0"),
        "else aggregate field should come from the caller rhs"
    );
}

#[test]
fn typed_chc_translation_now_models_nested_aggregate_stack_load() {
    // Trust (#46): a nested-aggregate stack cell (`((u32,),)` — a tuple whose field is
    // itself a tuple) is now PRECISELY MODELED rather than failing closed. The
    // `AggregateValue` representation is recursive (`Vec<ValueBinding>`), so the cell
    // is allocated with fresh-symbolic leaves (a sound over-approximation) and the
    // load returns the tracked nested aggregate — no MemoryAccessWithoutPreciseModel
    // error rule. This is the capability that unblocks `Option<(a,b)>` / `?` matches.
    let mut mb = ModuleBuilder::new("test_nested_aggregate_stack_memory_chc");
    let nested_ty = Ty::Tuple(vec![Ty::Tuple(vec![Ty::U32])]);
    let ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("nested_aggregate_stack_memory_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let slot = fb.alloca(nested_ty.clone());
    let _loaded = fb.load(nested_ty, slot);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel),
        "a nested aggregate stack load is now precisely modeled — no unsupported-memory diagnostic"
    );
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "nested aggregate stack loads no longer fail closed (recursive AggregateValue)"
    );
}

#[test]
fn typed_chc_translation_still_fails_closed_for_unknown_pointer_load() {
    let mut mb = ModuleBuilder::new("test_unknown_pointer_load_chc");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);

    let mut fb = mb.function("unknown_pointer_load_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let _loaded = fb.load(Ty::U32, ptr);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::MemoryProvenance);
    assert_eq!(
        output.diagnostics[0].reason,
        TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel
    );
    assert_eq!(output.diagnostics[0].function, "unknown_pointer_load_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "unknown pointer loads must keep failing closed"
    );
}

#[test]
fn typed_chc_translation_reports_unsupported_float_cast_reason() {
    let mut mb = ModuleBuilder::new("test_float_cast_chc_diagnostic");
    let ft = mb.add_func_type(vec![Ty::F64], vec![Ty::I64]);

    let mut fb = mb.function("float_cast_f64_i64_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::F64);
    let cast = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, input);
    fb.ret(vec![cast]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "unsupported cast must still fail closed in the CHC VC"
    );
    assert_eq!(output.diagnostics.len(), 1);
    assert_eq!(output.diagnostics[0].family, SemanticsFamily::Casts);
    assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::Cast);
    assert_eq!(output.diagnostics[0].function, "float_cast_f64_i64_chc");
    assert_eq!(output.diagnostics[0].block, entry);
    assert_eq!(output.diagnostics[0].instruction_index, 0);
    assert_eq!(output.diagnostics[0].result_values, vec![cast]);
}

#[test]
fn native_chc_bundle_retains_typed_unsupported_diagnostics() {
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let requested_function = native_trust_mc_request(&bundle).function;
    let function = bundle
        .module
        .functions
        .iter_mut()
        .find(|function| function.id == requested_function)
        .expect("fixture includes requested trust_mc function");
    let entry_id = function.entry;
    let entry = function
        .blocks
        .iter_mut()
        .find(|block| block.id == entry_id)
        .expect("fixture includes requested trust_mc entry block");
    let sum = entry.body[0].results[0];
    let cast_result = trust_ir::value::ValueId::new(99);
    entry.body.insert(
        1,
        trust_ir::InstrNode::new(trust_ir::Inst::Cast {
            op: CastOp::SIToFP,
            src_ty: Ty::I32,
            dst_ty: Ty::F64,
            operand: sum,
        })
        .with_result(cast_result),
    );
    refresh_native_trust_mc_bundle_module_identity(&mut bundle);

    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc CHC request should translate with diagnostics");

    assert_eq!(obligations.len(), 1);
    let diagnostics = &obligations[0].diagnostics;
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].family, SemanticsFamily::Casts);
    assert_eq!(diagnostics[0].reason, TrustIrChcUnsupportedReason::Cast);
    assert_eq!(diagnostics[0].function, "trust_mc_checked_add");
    assert_eq!(diagnostics[0].block, entry_id);
    assert_eq!(diagnostics[0].instruction_index, 1);
    assert_eq!(diagnostics[0].result_values, vec![cast_result]);
}

/// Build a module with a single function that adds two i32 parameters,
/// but with a `NoOverflow` proof annotation on the add instruction.
/// Expected: overflow VC still exists because bare proof annotations are metadata only.
#[test]
fn add_with_no_overflow_proof_still_generates_vc() {
    let mut mb = ModuleBuilder::new("test_add_proven");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("add_i32_proven", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let _a = fb.add_block_param(entry, Ty::I32);
    let _b = fb.add_block_param(entry, Ty::I32);

    // Emit add with NoOverflow proof using the low-level binop_with_proofs approach.
    // The FunctionBuilder doesn't have a direct "add_with_proof" method, so we
    // use the underlying instruction node API via the builder.
    // Actually, trust_ir-build only exposes emit_with_proofs for load_proven.
    // We need to construct the InstrNode manually.
    // Instead, we build the module directly.
    drop(fb);

    // Build the module manually to attach proofs to the add instruction.
    let mut module = mb.build();

    // Clear functions and rebuild with proof annotation.
    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "add_i32_proven",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));
    block.params.push((trust_ir::value::ValueId::new(1), Ty::I32));

    // Add instruction with NoOverflow proof.
    let add_node = trust_ir::InstrNode::new(trust_ir::Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::I32,
        lhs: trust_ir::value::ValueId::new(0),
        rhs: trust_ir::value::ValueId::new(1),
    })
    .with_result(trust_ir::value::ValueId::new(2))
    .with_proof(ProofAnnotation::NoOverflow);
    block.body.push(add_node);

    // Return.
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Bare NoOverflow metadata must not suppress the safety obligation.
    let overflow_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert!(
        !overflow_violations.is_empty(),
        "add with unchecked NoOverflow proof should still generate overflow check, got {} violations",
        overflow_violations.len()
    );
}

#[test]
fn wrapping_add_proof_suppresses_overflow_rule() {
    // Trust Gap 3: `u32::wrapping_add` lowers to a `BinOp::Add` tagged
    // `ProofAnnotation::Wrapping`. Wrap-around is defined behaviour, so the CHC
    // translator must NOT emit a no-overflow error rule for it — the obligation
    // is vacuously discharged. Contrast with
    // `typed_chc_translation_uses_unsigned_overflow_guard_for_u32_add`, which
    // asserts the guard IS present for a plain add.
    let mut mb = ModuleBuilder::new("test_u32_wrapping_add_chc");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("wrapping_add_u32", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    fb.add_block_param(entry, Ty::U32);
    fb.add_block_param(entry, Ty::U32);
    drop(fb);

    // Rebuild the function manually so the add carries a `Wrapping` proof.
    let mut module = mb.build();
    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "wrapping_add_u32",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );
    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::U32));
    block.params.push((trust_ir::value::ValueId::new(1), Ty::U32));
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: trust_ir::value::ValueId::new(0),
            rhs: trust_ir::value::ValueId::new(1),
        })
        .with_result(trust_ir::value::ValueId::new(2))
        .with_proof(ProofAnnotation::Wrapping),
    );
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));
    func.blocks.push(block);
    module.add_function(func);

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];

    let has_overflow_guard = output.vc.rules.iter().any(|rule| {
        rule.head.name == "error"
            && rule.body.constraints.iter().any(|constraint| {
                not_inner_matches(constraint, |inner| {
                    matches!(
                        inner,
                        ExprValue::BvAddNoOverflowUnsigned(_, _)
                            | ExprValue::BvAddNoOverflowSigned(_, _)
                    )
                })
            })
    });
    assert!(
        !has_overflow_guard,
        "wrapping add (Wrapping proof) must NOT emit a no-overflow error rule"
    );
}

#[test]
fn main_translate_models_signed_neg_precisely() {
    // The main translator's `Inst::UnOp(Neg)` arm: an integer negation in a
    // function's OWN body must be BOUND (`bvneg`), carry EXACTLY one guarded
    // `x == INT_MIN` error rule, and produce ZERO unsupported diagnostics.
    // The prior fresh-symbolic fall-through paired a HAVOCKED result with an
    // UNCONDITIONALLY REACHABLE error rule, so every function containing `-x`
    // had a vacuously satisfiable transport CHC — an admission failure
    // masquerading as a refutation.
    let mut mb = ModuleBuilder::new("test_main_translate_signed_neg_chc");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("neg_i64_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::I64);
    let neg = fb.unop(UnOp::Neg, Ty::I64, x);
    fb.ret(vec![neg]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(&mb.build(), &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        output.diagnostics.is_empty(),
        "an integer negation must lower precisely (no unsupported diagnostic), got {:?}",
        output.diagnostics
    );
    let error_rules: Vec<_> =
        output.vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
    assert_eq!(
        error_rules.len(),
        1,
        "signed negation carries exactly one trap obligation, got {:?}",
        error_rules
    );
    let guarded_by_operand = error_rules[0].body.constraints.iter().any(|constraint| {
        not_inner_matches(constraint, |inner| matches!(inner, ExprValue::BvNegNoOverflow(_)))
    });
    assert!(
        guarded_by_operand,
        "the neg trap must be GUARDED by `bvneg_no_overflow` (x == INT_MIN), never a bare \
         `true` error rule; constraints: {:?}",
        error_rules[0].body.constraints
    );
    let havocked = format!("{:?}", output.vc.rules).contains("unsupported_result");
    assert!(!havocked, "the negation result must be bound to `bvneg`, not havocked");
}

#[test]
fn wrapping_neg_proof_suppresses_overflow_rule() {
    // `wrapping_neg` lowers to `UnOp::Neg` tagged `ProofAnnotation::Wrapping`:
    // wrap-around is defined behaviour, so the precise `Neg` arm must emit NO
    // error rule at all while still binding the wrapped `bvneg` value.
    let mut mb = ModuleBuilder::new("test_wrapping_neg_chc");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("wrapping_neg_i64_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    fb.add_block_param(entry, Ty::I64);
    drop(fb);

    let mut module = mb.build();
    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "wrapping_neg_i64_chc",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );
    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I64));
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I64,
            operand: trust_ir::value::ValueId::new(0),
        })
        .with_result(trust_ir::value::ValueId::new(1))
        .with_proof(ProofAnnotation::Wrapping),
    );
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(1)],
    }));
    func.blocks.push(block);
    module.add_function(func);

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "wrapping neg lowers precisely");
    let error_rules: Vec<_> =
        output.vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
    assert!(
        error_rules.is_empty(),
        "wrapping neg (Wrapping proof) must NOT emit any error rule, got {:?}",
        error_rules
    );
}

/// Build a module with an assert instruction.
/// Expected: one assertion VC.
#[test]
fn assert_generates_assertion_vc() {
    let mut mb = ModuleBuilder::new("test_assert");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("check_assert", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(
        assertion_violations.len(),
        1,
        "assert should generate exactly one assertion violation"
    );
}

/// Build a module with a signed division.
/// Expected: one division-by-zero VC.
#[test]
fn sdiv_generates_div_by_zero_vc() {
    let mut mb = ModuleBuilder::new("test_div");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("div_i32", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let result = fb.sdiv(Ty::I32, a, b);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let div_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::DivisionByZero).collect();
    assert!(!div_violations.is_empty(), "sdiv should generate a division by zero check");
}

/// Build a module with a division that has DivNonZero proof.
/// Expected: division-by-zero VC still exists because bare proof annotations are metadata only.
#[test]
fn sdiv_with_divnonzero_proof_still_generates_vc() {
    let mut mb = ModuleBuilder::new("test_div_proven");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    // Build manually to attach proof.
    let _fb = mb.function("div_i32_proven", ft);
    // Drop the builder and build manually.
    drop(_fb);
    let mut module = mb.build();

    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "div_i32_proven",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));
    block.params.push((trust_ir::value::ValueId::new(1), Ty::I32));

    let div_node = trust_ir::InstrNode::new(trust_ir::Inst::BinOp {
        op: BinOp::SDiv,
        ty: Ty::I32,
        lhs: trust_ir::value::ValueId::new(0),
        rhs: trust_ir::value::ValueId::new(1),
    })
    .with_result(trust_ir::value::ValueId::new(2))
    .with_proof(ProofAnnotation::DivNonZero);
    block.body.push(div_node);

    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let div_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::DivisionByZero).collect();
    assert!(
        !div_violations.is_empty(),
        "sdiv with unchecked DivNonZero proof should still generate div-by-zero check"
    );
}

/// Build a module with a memory load (no InBounds proof).
/// Expected: one out-of-bounds VC.
#[test]
fn load_without_inbounds_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_load");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);

    let mut fb = mb.function("load_i32", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.load(Ty::I32, ptr);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "load without InBounds proof should generate bounds check"
    );
}

/// Build a module with a memory load that has InBounds proof.
/// Expected: out-of-bounds VC still exists because bare proof annotations are metadata only.
#[test]
fn load_with_inbounds_proof_still_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_load_proven");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);

    let mut fb = mb.function("load_i32_proven", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.load_proven(Ty::I32, ptr, vec![ProofAnnotation::InBounds]);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "load with unchecked InBounds proof should still generate bounds check"
    );
}

/// Build a module with an assume + assert pattern.
/// Expected: assume becomes a constraint, assert becomes a violation.
#[test]
fn assume_becomes_constraint_assert_becomes_violation() {
    let mut mb = ModuleBuilder::new("test_assume_assert");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("assume_then_assert", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.assume(cond);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have one constraint (from assume).
    assert_eq!(vc.constraints.len(), 1, "assume should generate one path constraint");

    // Should have one assertion violation.
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 1, "assert should generate one assertion violation");
}

/// Unsupported cast semantics must fail closed instead of producing an unchecked result.
#[test]
fn cast_semantics_fail_closed() {
    let mut mb = ModuleBuilder::new("test_cast_unsupported");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I64]);

    let mut fb = mb.function("cast_i32_i64", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::I32);
    let cast = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, input);
    fb.ret(vec![cast]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let unsupported_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::Other).collect();
    assert!(
        unsupported_violations.iter().any(|v| {
            v.message.as_deref().is_some_and(|message| message.contains("cast operation"))
        }),
        "cast should emit an unsupported-semantics violation"
    );
}

/// Acyclic conditional branching is now supported by the guarded-path BMC
/// encoding and must no longer fail closed.
#[test]
fn acyclic_condbr_no_longer_fails_closed_in_bmc() {
    let mut mb = ModuleBuilder::new("test_condbr_supported");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("branching", ft);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.condbr(cond, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    fb.ret(vec![]);
    fb.switch_to_block(else_block);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().all(|v| v.kind != PropertyKind::Other),
        "acyclic condbr must not emit unsupported-semantics violations, got {:?}",
        vcs[0].violations
    );
}

/// Loops (back-edges) must keep failing closed in BMC until bounded
/// unrolling lands.
#[test]
fn loop_back_edge_semantics_fail_closed_in_bmc() {
    let mut mb = ModuleBuilder::new("test_loop_unsupported");
    let ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("counting_loop", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let zero = fb.iconst(Ty::U32, 0);
    let i = fb.add_block_param(header, Ty::U32);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let ten = fb.iconst(Ty::U32, 10);
    let keep_going = fb.icmp(ICmpOp::Ult, Ty::U32, i, ten);
    fb.condbr(keep_going, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let one = fb.iconst(Ty::U32, 1);
    let next = fb.add(Ty::U32, i, one);
    // Back-edge: body → header.
    fb.br(header, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let unsupported_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::Other).collect();
    assert!(
        unsupported_violations.iter().any(|v| {
            v.message
                .as_deref()
                .is_some_and(|message| message.contains("path-sensitive control flow"))
        }),
        "loops must keep emitting an unsupported-semantics violation"
    );
}

/// Verify that disabling overflow checks via options suppresses VCs.
#[test]
fn options_disable_overflow_checks() {
    let mut mb = ModuleBuilder::new("test_no_overflow_check");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("add_no_check", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let sum = fb.add(Ty::I32, a, b);
    fb.ret(vec![sum]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions { check_signed_overflow: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let overflow_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert!(
        overflow_violations.is_empty(),
        "overflow checks disabled via options should produce no overflow VCs"
    );
}

/// Build a module with sub and mul — verify each generates its own overflow VC.
#[test]
fn sub_and_mul_generate_overflow_vcs() {
    let mut mb = ModuleBuilder::new("test_sub_mul");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("sub_mul", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let diff = fb.sub(Ty::I32, a, b);
    let _product = fb.mul(Ty::I32, diff, b);
    fb.ret(vec![_product]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let overflow_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert_eq!(
        overflow_violations.len(),
        2,
        "sub + mul should generate 2 overflow VCs, got {}",
        overflow_violations.len()
    );
}

/// Multiple functions in one module should produce one VC per function.
#[test]
fn multiple_functions_produce_multiple_vcs() {
    let mut mb = ModuleBuilder::new("test_multi");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Function 1: identity
    let mut fb1 = mb.function("identity", ft);
    let entry1 = fb1.create_block();
    fb1.switch_to_block(entry1);
    fb1.set_entry(entry1);
    let a = fb1.add_block_param(entry1, Ty::I32);
    fb1.ret(vec![a]);
    fb1.build();

    // Function 2: negate
    let mut fb2 = mb.function("negate", ft);
    let entry2 = fb2.create_block();
    fb2.switch_to_block(entry2);
    fb2.set_entry(entry2);
    let b = fb2.add_block_param(entry2, Ty::I32);
    let zero = fb2.iconst(Ty::I32, 0);
    let neg = fb2.sub(Ty::I32, zero, b);
    fb2.ret(vec![neg]);
    fb2.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 2, "should produce one VC per function");
    // First function (identity) should have no violations.
    assert!(vcs[0].violations.is_empty(), "identity should have no violations");
    // Second function (negate) should have an overflow violation from sub.
    assert!(!vcs[1].violations.is_empty(), "negate (0 - x) should have overflow violation");
}

// ============================================================================
// Memory model tests
// ============================================================================

/// Alloca creates a memory region that Load can read from (array select).
#[test]
fn alloca_store_load_roundtrip() {
    let mut mb = ModuleBuilder::new("test_mem");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("store_load", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let val = fb.add_block_param(entry, Ty::I32);
    let ptr = fb.alloca(Ty::I32);
    fb.store(Ty::I32, ptr, val);
    let loaded = fb.load(Ty::I32, ptr);
    fb.ret(vec![loaded]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions {
        check_memory_bounds: false, // Disable bounds checks for this test.
        ..TranslateOptions::default()
    };
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // With array-based memory, the alloca should create a memory region
    // declaration. Check that we have declarations (for the array and params).
    assert!(
        vc.decls.len() >= 2,
        "should have decls for param and memory array, got {}",
        vc.decls.len()
    );
}

/// Store + Load on an alloca with bounds checking enabled and unchecked InBounds proof.
#[test]
fn alloca_load_with_inbounds_still_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_mem_proven");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Build manually to attach InBounds proof to the load.
    let _fb = mb.function("load_proven", ft);
    drop(_fb);
    let mut module = mb.build();

    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "load_proven",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));

    // Alloca
    let alloca_node =
        trust_ir::InstrNode::new(trust_ir::Inst::Alloca { ty: Ty::I32, count: None, align: None })
            .with_result(trust_ir::value::ValueId::new(1));
    block.body.push(alloca_node);

    // Store with InBounds proof
    let store_node = trust_ir::InstrNode::new(trust_ir::Inst::Store {
        ty: Ty::I32,
        ptr: trust_ir::value::ValueId::new(1),
        value: trust_ir::value::ValueId::new(0),
        volatile: false,
        align: None,
    })
    .with_proof(ProofAnnotation::InBounds);
    block.body.push(store_node);

    // Load with InBounds proof
    let load_node = trust_ir::InstrNode::new(trust_ir::Inst::Load {
        ty: Ty::I32,
        ptr: trust_ir::value::ValueId::new(1),
        volatile: false,
        align: None,
    })
    .with_result(trust_ir::value::ValueId::new(2))
    .with_proof(ProofAnnotation::InBounds);
    block.body.push(load_node);

    // Return
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "load/store on alloca with unchecked InBounds proof should still generate bounds check, got {}",
        bounds_violations.len()
    );
}

#[test]
fn dynamic_alloca_count_fails_closed() {
    let mut mb = ModuleBuilder::new("test_dynamic_alloca");
    let ft = mb.add_func_type(vec![Ty::I64, Ty::I32], vec![Ty::I32]);

    let _fb = mb.function("dynamic_alloca", ft);
    drop(_fb);
    let mut module = mb.build();
    module.functions.clear();

    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "dynamic_alloca",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );
    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I64));
    block.params.push((trust_ir::value::ValueId::new(1), Ty::I32));
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Alloca {
            ty: Ty::I32,
            count: Some(trust_ir::value::ValueId::new(0)),
            align: None,
        })
        .with_result(trust_ir::value::ValueId::new(2)),
    );
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Store {
        ty: Ty::I32,
        ptr: trust_ir::value::ValueId::new(2),
        value: trust_ir::value::ValueId::new(1),
        volatile: false,
        align: None,
    }));
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Load {
            ty: Ty::I32,
            ptr: trust_ir::value::ValueId::new(2),
            volatile: false,
            align: None,
        })
        .with_result(trust_ir::value::ValueId::new(3)),
    );
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(3)],
    }));
    func.blocks.push(block);
    module.add_function(func);

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("dynamic alloca count"))
        }),
        "dynamic alloca count must be reported as unsupported instead of dropping bounds"
    );
}

#[test]
fn heap_alloc_and_global_addr_fail_closed_in_bmc() {
    let mut mb = ModuleBuilder::new("test_heap_global_bmc");
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("heap_global_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let heap = fb.heap_alloc(Ty::I32, None, None, trust_ir::inst::AllocOrigin::RustHeap);
    let _global = fb.global_addr(trust_ir::value::GlobalId::new(0));
    fb.ret(vec![heap]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let unsupported_messages = vcs[0]
        .violations
        .iter()
        .filter(|violation| violation.kind == PropertyKind::Other)
        .filter_map(|violation| violation.message.as_deref())
        .collect::<Vec<_>>();
    assert!(
        unsupported_messages.iter().any(|message| message.contains("heap allocation semantics")),
        "heap allocation must fail closed in BMC"
    );
    assert!(
        unsupported_messages.iter().any(|message| message.contains("global address semantics")),
        "global address must fail closed in BMC"
    );
}

#[test]
fn symbol_addr_constant_uses_pointer_sized_placeholder() {
    let expr = const_to_expr(
        &Ty::Ptr,
        &trust_ir::constant::Constant::SymbolAddr { symbol: "extern_fn".into(), addend: 8 },
    )
    .expect("symbol-address constants keep the opaque pointer-sized placeholder");

    assert_eq!(expr.sort().bitvec_width(), Some(64));
}

/// Load from a raw pointer (no alloca) generates a bounds check violation.
#[test]
fn load_from_raw_ptr_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_raw_load");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);

    let mut fb = mb.function("raw_load", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.load(Ty::I32, ptr);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(!bounds_violations.is_empty(), "load from raw pointer should generate bounds check");
}

// ============================================================================
// Postcondition tests
// ============================================================================

/// Return with BoundedOutput postcondition generates a postcondition VC.
#[test]
fn return_with_bounded_output_generates_postcondition_vc() {
    let mut mb = ModuleBuilder::new("test_postcond");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Build manually to attach BoundedOutput proof to the function.
    let _fb = mb.function("bounded_func", ft);
    drop(_fb);
    let mut module = mb.build();

    module.functions.clear();
    let func_ty_id = trust_ir::value::FuncTyId::new(0);
    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "bounded_func",
        func_ty_id,
        trust_ir::value::BlockId::new(0),
    );
    // Add postcondition: return value must be in [0, 100].
    func.proofs.push(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 100.0 });

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));

    // Return the parameter directly — may violate [0, 100].
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(0)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let postcond_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Postcondition).collect();
    assert!(
        !postcond_violations.is_empty(),
        "return should generate postcondition VC for BoundedOutput"
    );
}

/// Function without postcondition annotations generates no postcondition VCs.
#[test]
fn return_without_postcondition_no_vc() {
    let mut mb = ModuleBuilder::new("test_no_postcond");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let mut fb = mb.function("no_postcond", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let a = fb.add_block_param(entry, Ty::I32);
    fb.ret(vec![a]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    let postcond_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Postcondition).collect();
    assert!(
        postcond_violations.is_empty(),
        "function without postcondition should produce no postcondition VCs"
    );
}

// ============================================================================
// Interprocedural tests
// ============================================================================

/// Call to a Pure function does not inline from unchecked proof metadata.
#[test]
fn call_to_pure_function_uses_symbolic_return() {
    let mut mb = ModuleBuilder::new("test_inline");
    let callee_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let caller_ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    // Build the callee function manually (Pure, add two numbers).
    let _fb = mb.function("pure_add", callee_ft);
    drop(_fb);

    // Build the caller function that calls pure_add.
    let _fb2 = mb.function("caller", caller_ft);
    drop(_fb2);

    let mut module = mb.build();
    module.functions.clear();

    // Callee: pure_add(a, b) = a + b with Pure annotation.
    let mut callee_func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "pure_add",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );
    callee_func.proofs.push(ProofAnnotation::Pure);

    let mut callee_block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    callee_block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));
    callee_block.params.push((trust_ir::value::ValueId::new(1), Ty::I32));
    callee_block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: trust_ir::value::ValueId::new(0),
            rhs: trust_ir::value::ValueId::new(1),
        })
        .with_result(trust_ir::value::ValueId::new(2)),
    );
    callee_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));
    callee_func.blocks.push(callee_block);
    module.add_function(callee_func);

    // Caller: calls pure_add(x, y), asserts result > 0.
    let mut caller_func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(1),
        "caller",
        trust_ir::value::FuncTyId::new(1),
        trust_ir::value::BlockId::new(0),
    );

    let mut caller_block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    caller_block.params.push((trust_ir::value::ValueId::new(10), Ty::I32));
    caller_block.params.push((trust_ir::value::ValueId::new(11), Ty::I32));

    // Call pure_add.
    caller_block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Call {
            callee: trust_ir::value::FuncId::new(0),
            args: vec![trust_ir::value::ValueId::new(10), trust_ir::value::ValueId::new(11)],
        })
        .with_result(trust_ir::value::ValueId::new(12)),
    );

    // Compare result != 0 to get a Bool for the assert.
    caller_block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::I32,
            value: trust_ir::constant::Constant::Int(0),
        })
        .with_result(trust_ir::value::ValueId::new(13)),
    );
    caller_block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::ICmp {
            op: trust_ir::inst::ICmpOp::Ne,
            ty: Ty::I32,
            lhs: trust_ir::value::ValueId::new(12),
            rhs: trust_ir::value::ValueId::new(13),
        })
        .with_result(trust_ir::value::ValueId::new(14)),
    );

    // Assert result != 0.
    caller_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Assert {
        cond: trust_ir::value::ValueId::new(14),
    }));

    caller_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(12)],
    }));
    caller_func.blocks.push(caller_block);
    module.add_function(caller_func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    // Should have 2 VCs: one for pure_add, one for caller.
    assert_eq!(vcs.len(), 2, "should produce one VC per function");

    // The caller's VC should have an assertion violation, but no overflow
    // violation from inlining the callee solely because of unchecked Pure metadata.
    let caller_vc = &vcs[1];
    let assertion_violations: Vec<_> =
        caller_vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert!(!assertion_violations.is_empty(), "caller should have assertion violation");

    let overflow_violations: Vec<_> = caller_vc
        .violations
        .iter()
        .filter(|v| v.kind == PropertyKind::ArithmeticOverflow)
        .collect();
    assert!(
        overflow_violations.is_empty(),
        "unchecked Pure proof should not inline callee overflow checks into caller"
    );

    let callee_overflow_violations: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    assert!(
        !callee_overflow_violations.is_empty(),
        "callee body still has its own overflow obligation"
    );
}

/// Call to a function with unchecked postconditions creates symbolic return only.
#[test]
fn call_to_function_with_unchecked_postcondition_does_not_assume_it() {
    let mut mb = ModuleBuilder::new("test_symbolic_call");
    let callee_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let caller_ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let _fb = mb.function("bounded_callee", callee_ft);
    drop(_fb);
    let _fb2 = mb.function("caller", caller_ft);
    drop(_fb2);

    let mut module = mb.build();
    module.functions.clear();

    // Callee: has BoundedOutput [0, 100] but is NOT pure.
    let mut callee_func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "bounded_callee",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );
    callee_func.proofs.push(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 100.0 });

    let mut callee_block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    callee_block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));
    callee_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(0)],
    }));
    callee_func.blocks.push(callee_block);
    module.add_function(callee_func);

    // Caller: calls bounded_callee.
    let mut caller_func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(1),
        "caller",
        trust_ir::value::FuncTyId::new(1),
        trust_ir::value::BlockId::new(0),
    );

    let mut caller_block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    caller_block.params.push((trust_ir::value::ValueId::new(10), Ty::I32));

    caller_block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Call {
            callee: trust_ir::value::FuncId::new(0),
            args: vec![trust_ir::value::ValueId::new(10)],
        })
        .with_result(trust_ir::value::ValueId::new(11)),
    );

    caller_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(11)],
    }));
    caller_func.blocks.push(caller_block);
    module.add_function(caller_func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 2);
    let caller_vc = &vcs[1];

    // The caller's VC must not assume unchecked BoundedOutput metadata from the callee.
    assert!(
        caller_vc.constraints.is_empty(),
        "caller should not have postcondition constraints from unchecked callee metadata, got {}",
        caller_vc.constraints.len()
    );
}

/// Call to an unknown function (not in module) creates symbolic return.
#[test]
fn call_to_unknown_function_creates_symbolic() {
    let mut mb = ModuleBuilder::new("test_unknown_call");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Build manually — reference a callee that doesn't exist.
    let _fb = mb.function("caller", ft);
    drop(_fb);
    let mut module = mb.build();
    module.functions.clear();

    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "caller",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));

    // Call function ID 99 (doesn't exist in module).
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Call {
            callee: trust_ir::value::FuncId::new(99),
            args: vec![trust_ir::value::ValueId::new(0)],
        })
        .with_result(trust_ir::value::ValueId::new(1)),
    );

    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(1)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have declarations for the symbolic call result.
    assert!(vc.decls.len() >= 2, "should have decls for param and symbolic call result");

    let unsupported_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Other).collect();
    assert!(
        !unsupported_violations.is_empty(),
        "unknown direct call should emit an unsupported-semantics violation"
    );
}

// ============================================================================
// Atomic operation tests
// ============================================================================

/// AtomicLoad behaves like Load for sequential BMC.
#[test]
fn atomic_load_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_atomic_load");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);

    let mut fb = mb.function("atomic_load_fn", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.atomic_load(Ty::I32, ptr, trust_ir::Ordering::SeqCst);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // AtomicLoad from raw pointer should generate bounds check (same as Load).
    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "atomic_load from raw pointer should generate bounds check"
    );
}

/// AtomicStore behaves like Store for sequential BMC.
#[test]
fn atomic_store_generates_bounds_vc() {
    let mut mb = ModuleBuilder::new("test_atomic_store");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![]);

    let mut fb = mb.function("atomic_store_fn", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let val = fb.add_block_param(entry, Ty::I32);
    fb.atomic_store(Ty::I32, ptr, val, trust_ir::Ordering::SeqCst);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // AtomicStore to raw pointer should generate bounds check (same as Store).
    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "atomic_store to raw pointer should generate bounds check"
    );
}

/// CmpXchg generates two results: (value, success_flag).
#[test]
fn cmpxchg_generates_two_results() {
    let mut mb = ModuleBuilder::new("test_cmpxchg");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32, Ty::I32], vec![]);

    let _fb = mb.function("cmpxchg_fn", ft);
    drop(_fb);
    let mut module = mb.build();
    module.functions.clear();

    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "cmpxchg_fn",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::Ptr));
    block.params.push((trust_ir::value::ValueId::new(1), Ty::I32));
    block.params.push((trust_ir::value::ValueId::new(2), Ty::I32));

    // CmpXchg instruction.
    let cmpxchg_node = trust_ir::InstrNode::new(trust_ir::Inst::CmpXchg {
        ty: Ty::I32,
        ptr: trust_ir::value::ValueId::new(0),
        expected: trust_ir::value::ValueId::new(1),
        desired: trust_ir::value::ValueId::new(2),
        success: trust_ir::Ordering::SeqCst,
        failure: trust_ir::Ordering::SeqCst,
    })
    .with_result(trust_ir::value::ValueId::new(3)) // value
    .with_result(trust_ir::value::ValueId::new(4)); // success flag
    block.body.push(cmpxchg_node);

    // Assert the success flag.
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Assert {
        cond: trust_ir::value::ValueId::new(4),
    }));

    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![] }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have an assertion violation (cmpxchg success is not guaranteed).
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert!(!assertion_violations.is_empty(), "cmpxchg success flag assertion should produce a VC");
}

// ============================================================================
// GEP tests
// ============================================================================

/// GEP with alloca base computes pointer offset.
#[test]
fn gep_with_alloca_produces_declarations() {
    let mut mb = ModuleBuilder::new("test_gep");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);

    let mut fb = mb.function("gep_fn", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let idx = fb.add_block_param(entry, Ty::I64);

    // Alloca creates a memory region (we'll treat it as single-element).
    let ptr = fb.alloca(Ty::I32);

    // GEP: ptr + idx * sizeof(I32)
    let gep_ptr = fb.gep(Ty::I32, ptr, vec![idx]);

    // Load from the GEP result.
    let val = fb.load(Ty::I32, gep_ptr);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have declarations for: param, alloca_ptr, mem_array, gep result exprs.
    assert!(
        vc.decls.len() >= 2,
        "GEP with alloca should produce declarations, got {}",
        vc.decls.len()
    );
}

/// GEP bounds check fires when index is out of range.
#[test]
fn gep_bounds_check_on_single_alloca() {
    let mut mb = ModuleBuilder::new("test_gep_bounds");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);

    let mut fb = mb.function("gep_bounds_fn", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let idx = fb.add_block_param(entry, Ty::I64);
    let ptr = fb.alloca(Ty::I32); // Single element allocation.
    let gep_ptr = fb.gep(Ty::I32, ptr, vec![idx]);
    let val = fb.load(Ty::I32, gep_ptr);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let options = TranslateOptions::default(); // Bounds checking enabled.
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // The alloca creates a single-element region (count=1).
    // The GEP with arbitrary index should generate a bounds check (idx >= 1).
    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "GEP on single-element alloca should generate bounds check"
    );
}

/// STRUCTURAL FIDELITY (memory-bounds class): the GEP out-of-bounds obligation the encoder
/// emits is a `BvUGe(offset, count)` comparison — exactly the literal structure clean's
/// `memory_bounds_obligation.lean::gepBoundsObligation` models and proves evaluates to the
/// true OOB condition. This ties that clean memory-bounds proof to the real
/// `ay_bindings::Expr`, the same model↔literal link established for the arithmetic arms.
#[test]
fn gep_bounds_obligation_is_bvuge() {
    let mut mb = ModuleBuilder::new("test_gep_bounds_struct");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);
    let mut fb = mb.function("gep_bounds_struct_fn", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let idx = fb.add_block_param(entry, Ty::I64);
    let ptr = fb.alloca(Ty::I32); // single-element region, count = 1
    let gep_ptr = fb.gep(Ty::I32, ptr, vec![idx]);
    let val = fb.load(Ty::I32, gep_ptr);
    fb.ret(vec![val]);
    fb.build();

    let module = mb.build();
    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    let bounds: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(!bounds.is_empty(), "GEP must generate an out-of-bounds obligation");
    assert!(
        bounds.iter().any(|v| matches!(v.condition.value(), ExprValue::BvUGe(_, _))),
        "the GEP out-of-bounds obligation must be a `BvUGe(offset, count)` comparison — the \
         structure clean's gepBoundsObligation proves sound"
    );
}

// ============================================================================
// Integration tests
// ============================================================================

/// Complete flow: alloca, store, GEP, load, assert, return with postcondition.
#[test]
fn full_integration_alloca_store_gep_load_assert_postcond() {
    let mut mb = ModuleBuilder::new("test_integration");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let _fb = mb.function("integration", ft);
    drop(_fb);
    let mut module = mb.build();
    module.functions.clear();

    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "integration",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );
    func.proofs.push(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 255.0 });

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), Ty::I32));

    // alloca
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Alloca { ty: Ty::I32, count: None, align: None })
            .with_result(trust_ir::value::ValueId::new(1)),
    );
    // store (with InBounds proof)
    let store_node = trust_ir::InstrNode::new(trust_ir::Inst::Store {
        ty: Ty::I32,
        ptr: trust_ir::value::ValueId::new(1),
        value: trust_ir::value::ValueId::new(0),
        volatile: false,
        align: None,
    })
    .with_proof(ProofAnnotation::InBounds);
    block.body.push(store_node);
    // load (with InBounds proof)
    block.body.push(
        trust_ir::InstrNode::new(trust_ir::Inst::Load {
            ty: Ty::I32,
            ptr: trust_ir::value::ValueId::new(1),
            volatile: false,
            align: None,
        })
        .with_result(trust_ir::value::ValueId::new(2))
        .with_proof(ProofAnnotation::InBounds),
    );
    // return (triggers postcondition VC)
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(2)],
    }));

    func.blocks.push(block);
    module.add_function(func);

    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have a postcondition violation (input could be outside [0, 255]).
    let postcond_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Postcondition).collect();
    assert!(
        !postcond_violations.is_empty(),
        "return should generate postcondition VC from BoundedOutput"
    );

    // Bare InBounds metadata must not suppress bounds violations.
    let bounds_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::OutOfBounds).collect();
    assert!(
        !bounds_violations.is_empty(),
        "unchecked InBounds proof should not suppress bounds check, got {}",
        bounds_violations.len()
    );
}

// ============================================================================
// Guarded-path BMC encoding for acyclic multi-block CFGs
// ============================================================================

/// Solve `constraints ∧ violation.condition` for a translated BMC VC with the
/// in-process AY solver. Returns `true` when the violation is reachable (SAT)
/// and `false` when the property holds (UNSAT).
fn bmc_violation_is_satisfiable(
    vc: &trust_mc_core::bmc::BmcVc,
    violation: &trust_mc_core::violation::Violation,
) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic(vc.query.logic.as_deref().unwrap_or("QF_BV"));
    for decl in &vc.decls {
        if let trust_mc_core::decl::Decl::Const { name, sort } = decl {
            let _ = program.declare_const(name.clone(), sort.clone());
        }
    }
    for constraint in &vc.constraints {
        program.assert(constraint.clone());
    }
    program.assert(violation.condition.clone());
    program.check_sat();
    match ay_bindings::execute_direct::execute(&program)
        .expect("in-process AY execution should succeed")
    {
        ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
        ay_bindings::execute_direct::ExecuteResult::Verified => false,
        other => panic!("unexpected solver outcome: {other:?}"),
    }
}

/// Diamond CFG fixture:
///
/// ```text
/// entry(c: Bool, x: U32): condbr c → divide / skip
/// divide: q = 100 udiv x; br join [q]
/// skip:   br join [1]
/// join(p: U32): ret [p]
/// ```
///
/// When `pin_else` is true the entry block assumes `c == false`, restricting
/// execution to the `skip` leg.
fn diamond_udiv_module(pin_else: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_diamond_udiv");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::U32], vec![Ty::U32]);

    let mut fb = mb.function("diamond_udiv", ft);
    let entry = fb.create_block();
    let divide = fb.create_block();
    let skip = fb.create_block();
    let join = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let c = fb.add_block_param(entry, Ty::Bool);
    let x = fb.add_block_param(entry, Ty::U32);
    let p = fb.add_block_param(join, Ty::U32);
    if pin_else {
        let false_const = fb.bool_const(false);
        let is_false = fb.icmp(ICmpOp::Eq, Ty::Bool, c, false_const);
        fb.assume(is_false);
    }
    fb.condbr(c, divide, vec![], skip, vec![]);

    fb.switch_to_block(divide);
    let hundred = fb.iconst(Ty::U32, 100);
    let q = fb.binop(BinOp::UDiv, Ty::U32, hundred, x);
    fb.br(join, vec![q]);

    fb.switch_to_block(skip);
    let one = fb.iconst(Ty::U32, 1);
    fb.br(join, vec![one]);

    fb.switch_to_block(join);
    let _ = p;
    fb.ret(vec![p]);
    fb.build();

    mb.build()
}

/// (a) A violation inside one leg of a diamond is reported under its exact
/// path condition: reachable when the branch can be taken.
#[test]
fn diamond_branch_violation_found_on_feasible_path() {
    let vcs = trust_ir_to_bmc_vc(&diamond_udiv_module(false), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert!(
        vc.violations.iter().all(|v| v.kind != PropertyKind::Other),
        "acyclic diamond must not fail closed, got {:?}",
        vc.violations
    );
    let div_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::DivisionByZero).collect();
    assert_eq!(div_violations.len(), 1, "udiv should emit exactly one div-by-zero VC");
    assert!(
        bmc_violation_is_satisfiable(vc, div_violations[0]),
        "div-by-zero in the taken leg must be reachable (c = true, x = 0)"
    );
}

/// (a) The same violation becomes unreachable when the path into its leg is
/// excluded — the guard carries the exact path condition, so the property
/// proves on the remaining leg.
#[test]
fn diamond_branch_violation_unreachable_when_leg_excluded() {
    let vcs = trust_ir_to_bmc_vc(&diamond_udiv_module(true), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    let div_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::DivisionByZero).collect();
    assert_eq!(div_violations.len(), 1);
    assert!(
        !bmc_violation_is_satisfiable(vc, div_violations[0]),
        "div-by-zero in the excluded leg must be unreachable under assume(c == false)"
    );
}

/// Join-with-block-param fixture: `x = if c { 1 } else { 2 }` followed by
/// `assert x >= 1` (holds on both legs) and `assert x >= 2` (fails on the
/// then leg). When `pin_else` is true the entry assumes `c == false`.
fn join_param_module(pin_else: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_join_param");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("join_param", ft);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    let join = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let c = fb.add_block_param(entry, Ty::Bool);
    let p = fb.add_block_param(join, Ty::U32);
    if pin_else {
        let false_const = fb.bool_const(false);
        let is_false = fb.icmp(ICmpOp::Eq, Ty::Bool, c, false_const);
        fb.assume(is_false);
    }
    fb.condbr(c, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    let one = fb.iconst(Ty::U32, 1);
    fb.br(join, vec![one]);

    fb.switch_to_block(else_block);
    let two = fb.iconst(Ty::U32, 2);
    fb.br(join, vec![two]);

    fb.switch_to_block(join);
    let one_again = fb.iconst(Ty::U32, 1);
    let ge_one = fb.icmp(ICmpOp::Uge, Ty::U32, p, one_again);
    fb.assert(ge_one);
    let two_again = fb.iconst(Ty::U32, 2);
    let ge_two = fb.icmp(ICmpOp::Uge, Ty::U32, p, two_again);
    fb.assert(ge_two);
    fb.ret(vec![]);
    fb.build();

    mb.build()
}

/// (c) Values passed through block params across a join compute correctly:
/// `x >= 1` proves while `x >= 2` yields a counterexample.
#[test]
fn join_block_param_values_flow_per_edge() {
    let vcs = trust_ir_to_bmc_vc(&join_param_module(false), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert!(
        vc.violations.iter().all(|v| v.kind != PropertyKind::Other),
        "join through block params must not fail closed, got {:?}",
        vc.violations
    );
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 2, "two asserts should emit two assertion VCs");
    assert!(
        !bmc_violation_is_satisfiable(vc, assertion_violations[0]),
        "x >= 1 holds on both legs (x is 1 or 2) and must prove"
    );
    assert!(
        bmc_violation_is_satisfiable(vc, assertion_violations[1]),
        "x >= 2 fails on the then leg (x = 1) and must yield a counterexample"
    );
}

/// (c) Pinning the branch to the else leg makes `x >= 2` prove: the join
/// parameter is correlated with the path condition, not conflated.
#[test]
fn join_block_param_correlates_with_path_condition() {
    let vcs = trust_ir_to_bmc_vc(&join_param_module(true), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 2);
    assert!(
        !bmc_violation_is_satisfiable(vc, assertion_violations[1]),
        "under assume(c == false) only the else leg (x = 2) is feasible, so x >= 2 proves"
    );
}

/// Switch fixture mapping `s ∈ {0, 1, 2}` to `{1, 2, 3}` and everything else
/// (default) to `0`, then asserting `p <= 3` (holds everywhere) and `p >= 1`
/// (fails only via the default edge). When `exclude_default` is true the
/// entry assumes `s <= 2`, making the default edge infeasible.
fn switch_module(exclude_default: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_switch_bmc");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);

    let mut fb = mb.function("switch_bmc", ft);
    let entry = fb.create_block();
    let case0 = fb.create_block();
    let case1 = fb.create_block();
    let case2 = fb.create_block();
    let default = fb.create_block();
    let join = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let s = fb.add_block_param(entry, Ty::U32);
    let p = fb.add_block_param(join, Ty::U32);
    if exclude_default {
        let two = fb.iconst(Ty::U32, 2);
        let in_cases = fb.icmp(ICmpOp::Ule, Ty::U32, s, two);
        fb.assume(in_cases);
    }
    fb.switch(
        s,
        vec![
            SwitchCase { value: trust_ir::constant::Constant::Int(0), target: case0, args: vec![] },
            SwitchCase { value: trust_ir::constant::Constant::Int(1), target: case1, args: vec![] },
            SwitchCase { value: trust_ir::constant::Constant::Int(2), target: case2, args: vec![] },
        ],
        default,
        vec![],
    );

    fb.switch_to_block(case0);
    let v1 = fb.iconst(Ty::U32, 1);
    fb.br(join, vec![v1]);
    fb.switch_to_block(case1);
    let v2 = fb.iconst(Ty::U32, 2);
    fb.br(join, vec![v2]);
    fb.switch_to_block(case2);
    let v3 = fb.iconst(Ty::U32, 3);
    fb.br(join, vec![v3]);
    fb.switch_to_block(default);
    let v0 = fb.iconst(Ty::U32, 0);
    fb.br(join, vec![v0]);

    fb.switch_to_block(join);
    let three = fb.iconst(Ty::U32, 3);
    let le_three = fb.icmp(ICmpOp::Ule, Ty::U32, p, three);
    fb.assert(le_three);
    let one = fb.iconst(Ty::U32, 1);
    let ge_one = fb.icmp(ICmpOp::Uge, Ty::U32, p, one);
    fb.assert(ge_one);
    fb.ret(vec![]);
    fb.build();

    mb.build()
}

/// (b) A switch with three cases plus default lowers exactly: a property
/// holding on every leg proves, and a property failing only via the default
/// leg yields a counterexample.
#[test]
fn switch_three_cases_plus_default_lowers_exactly() {
    let vcs = trust_ir_to_bmc_vc(&switch_module(false), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert!(
        vc.violations.iter().all(|v| v.kind != PropertyKind::Other),
        "acyclic scalar switch must not fail closed, got {:?}",
        vc.violations
    );
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 2);
    assert!(
        !bmc_violation_is_satisfiable(vc, assertion_violations[0]),
        "p <= 3 holds on all four legs and must prove"
    );
    assert!(
        bmc_violation_is_satisfiable(vc, assertion_violations[1]),
        "p >= 1 fails via the default leg (p = 0) and must yield a counterexample"
    );
}

/// (b) The default edge condition is exactly \"none of the cases matched\":
/// excluding the default selector values makes the default-only failure
/// prove.
#[test]
fn switch_default_edge_condition_is_none_of_the_cases() {
    let vcs = trust_ir_to_bmc_vc(&switch_module(true), &TranslateOptions::default());

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 2);
    assert!(
        !bmc_violation_is_satisfiable(vc, assertion_violations[1]),
        "under assume(s <= 2) the default leg is infeasible, so p >= 1 proves"
    );
}

/// Unreachable fixture: `condbr c → ok / dead` where `dead` holds an
/// `Unreachable` instruction. When `pin_then` is true the entry assumes `c`.
fn guarded_unreachable_module(pin_then: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_guarded_unreachable");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("guarded_unreachable", ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let dead = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let c = fb.add_block_param(entry, Ty::Bool);
    if pin_then {
        fb.assume(c);
    }
    fb.condbr(c, ok, vec![], dead, vec![]);

    fb.switch_to_block(ok);
    fb.ret(vec![]);
    fb.switch_to_block(dead);
    fb.unreachable();
    fb.build();

    mb.build()
}

/// Unreachable-instruction violations are scoped to their block guard: the
/// VC is reachable exactly when some feasible path reaches the instruction.
#[test]
fn unreachable_violation_is_guarded_by_path_condition() {
    let reachable =
        trust_ir_to_bmc_vc(&guarded_unreachable_module(false), &TranslateOptions::default());
    assert_eq!(reachable.len(), 1);
    let unreachable_violations: Vec<_> =
        reachable[0].violations.iter().filter(|v| v.kind == PropertyKind::Unreachable).collect();
    assert_eq!(unreachable_violations.len(), 1);
    assert!(
        bmc_violation_is_satisfiable(&reachable[0], unreachable_violations[0]),
        "the dead block is feasible when c = false, so the VC must be reachable"
    );

    let pinned =
        trust_ir_to_bmc_vc(&guarded_unreachable_module(true), &TranslateOptions::default());
    assert_eq!(pinned.len(), 1);
    let pinned_violations: Vec<_> =
        pinned[0].violations.iter().filter(|v| v.kind == PropertyKind::Unreachable).collect();
    assert_eq!(pinned_violations.len(), 1);
    assert!(
        !bmc_violation_is_satisfiable(&pinned[0], pinned_violations[0]),
        "under assume(c) the dead block is infeasible: no false unreachable alarm"
    );
}

// ============================================================================
// Float soundness tests (0-unknown campaign: float constants must carry EXACT
// IEEE-754 bit patterns, and every op that would interpret those bits
// non-bit-accurately must fail closed — never falsely prove, never falsely
// refute).
// ============================================================================

/// (a) A float constant's encoding IS its IEEE-754 bit pattern — the old
/// `bitvec_const(0, width)` placeholder modeled 1.5 as +0.0 (wrong bits).
#[test]
fn float_constants_lower_to_exact_ieee_bit_patterns() {
    assert_eq!(
        const_to_expr(&Ty::F64, &trust_ir::constant::Constant::Float(1.5)),
        Some(Expr::bitvec_const(1.5f64.to_bits(), 64)),
        "an F64 constant must encode its exact bit pattern, not a zero placeholder"
    );
    // The f64 payload of an F32 constant is the exactly-widened f32 (bridge
    // contract); the demotion must recover the original f32 bit pattern.
    assert_eq!(
        const_to_expr(&Ty::F32, &trust_ir::constant::Constant::Float(f64::from(1.5f32))),
        Some(Expr::bitvec_const(u64::from(1.5f32.to_bits()), 32)),
        "an F32 constant must encode the demoted f32's exact bit pattern"
    );
    // NaN payload bits are preserved verbatim for F64 (bit-exact identity is
    // the trust-ir wire contract for float constants).
    assert_eq!(
        const_to_expr(&Ty::F64, &trust_ir::constant::Constant::Float(f64::NAN)),
        Some(Expr::bitvec_const(f64::NAN.to_bits(), 64)),
    );
}

/// (c-encoding) -0.0 and +0.0 are DIFFERENT bit patterns and must stay
/// distinct in the encoding (a placeholder collapsed both to the same bits,
/// which is exactly how a bit-equality comparison could falsely equate or
/// falsely distinguish them).
#[test]
fn negative_zero_and_positive_zero_keep_distinct_exact_encodings() {
    let neg = const_to_expr(&Ty::F64, &trust_ir::constant::Constant::Float(-0.0))
        .expect("-0.0 encodes exactly");
    let pos = const_to_expr(&Ty::F64, &trust_ir::constant::Constant::Float(0.0))
        .expect("+0.0 encodes exactly");
    assert_eq!(neg, Expr::bitvec_const((-0.0f64).to_bits(), 64));
    assert_eq!(pos, Expr::bitvec_const(0u64, 64));
    assert_ne!(neg, pos, "-0.0 and +0.0 must not collapse to the same bit pattern");
}

/// An F32 constant whose f64 payload is NOT an exactly-widened f32 has no
/// certified 32-bit encoding and must fail closed (None), never round.
/// F16 has no computable encoding at all. An ill-typed float constant
/// (float payload, integer destination type) also fails closed.
#[test]
fn inexact_float_constants_fail_closed_instead_of_rounding() {
    // 0.1f64 is not exactly representable in f32: demotion would ROUND.
    assert_eq!(const_to_expr(&Ty::F32, &trust_ir::constant::Constant::Float(0.1)), None);
    // A finite f64 beyond f32 range would demote to +inf: wrong value.
    assert_eq!(const_to_expr(&Ty::F32, &trust_ir::constant::Constant::Float(1e300)), None);
    // F16 bits cannot be computed on stable Rust: fail closed.
    assert_eq!(const_to_expr(&Ty::F16, &trust_ir::constant::Constant::Float(1.0)), None);
    // Ill-typed IR: float constant with an integer destination type.
    assert_eq!(const_to_expr(&Ty::I32, &trust_ir::constant::Constant::Float(1.0)), None);
    // Whatever Some(bits) is ever produced for an F32 constant must satisfy
    // the widening round-trip invariant (bit-certified demotion).
    for payload in [f64::from(f32::NAN), f64::from(-0.0f32), f64::from(f32::MAX)] {
        if let Some(expr) = const_to_expr(&Ty::F32, &trust_ir::constant::Constant::Float(payload)) {
            let ExprValue::BitVecConst { value, width } = expr.value() else {
                panic!("F32 constant must encode as a bitvector constant");
            };
            assert_eq!(*width, 32);
            let bits: u32 = value.to_string().parse().expect("32-bit pattern");
            assert_eq!(
                f64::from(f32::from_bits(bits)).to_bits(),
                payload.to_bits(),
                "emitted f32 bits must widen back to the exact f64 payload"
            );
        }
    }
}

/// Float VECTOR lanes pack exact per-lane bit patterns (the old encoding
/// zeroed every float lane).
#[test]
fn float_vector_constants_pack_exact_lane_bits() {
    let ty = Ty::Vector(Box::new(Ty::F32), 2);
    let value = trust_ir::constant::Constant::Vector(vec![
        trust_ir::constant::Constant::Float(f64::from(1.5f32)),
        trust_ir::constant::Constant::Float(f64::from(-0.0f32)),
    ]);
    let expr = const_to_expr(&ty, &value).expect("widened-f32 lanes pack exactly");
    assert_eq!(expr.sort().bitvec_width(), Some(64));
    assert_eq!(
        bitvec_concat_leaves(&expr),
        vec![
            (u64::from((-0.0f32).to_bits()).to_string(), 32),
            (u64::from(1.5f32.to_bits()).to_string(), 32),
        ]
    );

    // A lane that cannot be encoded exactly fails the WHOLE vector closed.
    let inexact = trust_ir::constant::Constant::Vector(vec![
        trust_ir::constant::Constant::Float(f64::from(1.5f32)),
        trust_ir::constant::Constant::Float(0.1),
    ]);
    assert_eq!(const_to_expr(&ty, &inexact), None);
}

/// (a-end-to-end) The exact constant bits flow into the BMC encoding: passing
/// `1.5f64` as a block argument pins the block parameter to the constant's
/// bit pattern in the VC constraints.
#[test]
fn float_constant_bits_reach_the_bmc_encoding_exactly() {
    let mut mb = ModuleBuilder::new("test_float_const_bits");
    let ft = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("float_const_flow", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let c = fb.fconst(Ty::F64, 1.5);
    let ret = fb.add_block_param(exit, Ty::F64);
    fb.br(exit, vec![c]);
    fb.switch_to_block(exit);
    fb.ret(vec![ret]);
    fb.build();

    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    let expected_bits = 1.5f64.to_bits().to_string();
    let pinned = vcs[0].constraints.iter().any(|constraint| {
        expr_tree_has(constraint, &|value| {
            matches!(value, ExprValue::BitVecConst { value, width: 64 }
                if value.to_string() == expected_bits)
        })
    });
    assert!(
        pinned,
        "the block-parameter binding must carry 1.5f64's exact bit pattern \
         ({expected_bits}), not a zero placeholder"
    );
    // No fail-closed VC: an exactly-encoded float constant flowing through
    // pure bit-preserving plumbing is fully supported.
    assert!(
        !vcs[0].violations.iter().any(|v| v.kind == PropertyKind::Other),
        "bit-preserving float plumbing must not fail closed"
    );
}

/// (b) The FCmp soundness decision: FCmp is NEVER lowered to bit-level
/// equality. `-0.0 == +0.0` is IEEE-true but bit-false — a bit-equality
/// model would falsely REFUTE `assert(-0.0 == +0.0)`. The lane must instead
/// havoc the comparison (contingent, undecidable either way) and emit an
/// always-failing unsupported-semantics VC.
#[test]
fn fcmp_eq_of_zero_signs_fails_closed_never_bit_decided() {
    let vc = translate_single_float_cmp_fn(|fb, lhs, rhs| {
        fb.fcmp(trust_ir::inst::FCmpOp::OEq, Ty::F64, lhs, rhs)
    });
    assert_float_comparison_fails_closed(&vc, "floating-point comparison");
}

/// (c) `-0.0 != +0.0` is IEEE-false but bit-true — a bit-equality model
/// would falsely PROVE `assert(-0.0 != +0.0)` (violation UNSAT). The
/// assertion obligation must remain contingent and the lane fail closed.
#[test]
fn fcmp_ne_of_zero_signs_cannot_be_falsely_proved() {
    let vc = translate_single_float_cmp_fn(|fb, lhs, rhs| {
        fb.fcmp(trust_ir::inst::FCmpOp::ONe, Ty::F64, lhs, rhs)
    });
    assert_float_comparison_fails_closed(&vc, "floating-point comparison");
}

/// (c) `NaN == NaN` is IEEE-false but bit-true (identical payloads) — a
/// bit-equality model would falsely PROVE `assert(NaN == NaN)`.
#[test]
fn fcmp_eq_of_nan_cannot_be_falsely_proved() {
    let mut mb = ModuleBuilder::new("test_fcmp_nan");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("float_cmp_nan", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let lhs = fb.fconst(Ty::F64, f64::NAN);
    let rhs = fb.fconst(Ty::F64, f64::NAN);
    let cmp = fb.fcmp(trust_ir::inst::FCmpOp::OEq, Ty::F64, lhs, rhs);
    fb.assert(cmp);
    fb.ret(vec![]);
    fb.build();
    let vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert_float_comparison_fails_closed(&vcs[0], "floating-point comparison");
}

/// (c) The IEEE trap applies identically to an (ill-typed) integer compare
/// over float operands: BMC must NOT bit-compare them — `ICmp Eq` over
/// `-0.0`/`+0.0` bits would falsely refute IEEE equality, and over identical
/// NaN payloads would falsely prove it. Mirrors translate_chc::eval_icmp's
/// float gate.
#[test]
fn icmp_on_float_type_fails_closed_never_bit_decided() {
    let vc = translate_single_float_cmp_fn(|fb, lhs, rhs| fb.icmp(ICmpOp::Eq, Ty::F64, lhs, rhs));
    assert_float_comparison_fails_closed(&vc, "floating-point comparison via ICmp");
}

/// Translate `assert(cmp(-0.0, +0.0))` for a caller-chosen comparison
/// instruction over exactly-encoded float constants.
fn translate_single_float_cmp_fn(
    build_cmp: impl FnOnce(
        &mut trust_ir_build::FunctionBuilder,
        trust_ir::value::ValueId,
        trust_ir::value::ValueId,
    ) -> trust_ir::value::ValueId,
) -> trust_mc_core::bmc::BmcVc {
    let mut mb = ModuleBuilder::new("test_float_cmp");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("float_cmp", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let lhs = fb.fconst(Ty::F64, -0.0);
    let rhs = fb.fconst(Ty::F64, 0.0);
    let cmp = build_cmp(&mut fb, lhs, rhs);
    fb.assert(cmp);
    fb.ret(vec![]);
    fb.build();
    let mut vcs = trust_ir_to_bmc_vc(&mb.build(), &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    vcs.pop().expect("one VC")
}

/// The fail-closed contract for a float comparison feeding an assertion:
/// 1. an always-failing unsupported-semantics VC names the construct, so the
///    function can never be reported proof-grade;
/// 2. the assertion obligation is CONTINGENT — satisfiable in both polarities
///    — so the solver can neither falsely prove (UNSAT) nor falsely refute
///    (VALID counterexample) it from comparison bits.
fn assert_float_comparison_fails_closed(vc: &trust_mc_core::bmc::BmcVc, expected_reason: &str) {
    let unsupported: Vec<_> = vc
        .violations
        .iter()
        .filter(|v| v.kind == PropertyKind::Other)
        .filter(|v| v.message.as_deref().is_some_and(|m| m.contains(expected_reason)))
        .collect();
    assert_eq!(
        unsupported.len(),
        1,
        "exactly one fail-closed VC naming {expected_reason:?} expected, violations: {:?}",
        vc.violations
    );
    assert!(
        bmc_violation_is_satisfiable(vc, unsupported[0]),
        "the fail-closed VC must actually fire (be satisfiable)"
    );

    let assertions: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertions.len(), 1, "the assert must produce exactly one obligation");
    assert!(
        bmc_violation_is_satisfiable(vc, assertions[0]),
        "the assertion obligation must not be falsely PROVED (UNSAT) from comparison bits"
    );
    assert!(
        bmc_condition_is_satisfiable(vc, assertions[0].condition.clone().not()),
        "the assertion obligation must not be falsely REFUTED (valid) from comparison bits"
    );
}

/// Solve `constraints ∧ condition` directly (both-polarity contingency pin).
fn bmc_condition_is_satisfiable(vc: &trust_mc_core::bmc::BmcVc, condition: Expr) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic(vc.query.logic.as_deref().unwrap_or("QF_BV"));
    for decl in &vc.decls {
        if let trust_mc_core::decl::Decl::Const { name, sort } = decl {
            let _ = program.declare_const(name.clone(), sort.clone());
        }
    }
    for constraint in &vc.constraints {
        program.assert(constraint.clone());
    }
    program.assert(condition);
    program.check_sat();
    match ay_bindings::execute_direct::execute(&program)
        .expect("in-process AY execution should succeed")
    {
        ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
        ay_bindings::execute_direct::ExecuteResult::Verified => false,
        other => panic!("unexpected solver outcome: {other:?}"),
    }
}

/// Whether any node in the expression tree satisfies `pred`.
fn expr_tree_has(expr: &Expr, pred: &dyn Fn(&ExprValue) -> bool) -> bool {
    if pred(expr.value()) {
        return true;
    }
    expr.value().children().any(|child| expr_tree_has(child, pred))
}

/// A `BoundedOutput` postcondition on a FLOAT-typed return has no exact
/// bitvector encoding (signed bitvector order over IEEE bits is not IEEE
/// order): it must fail closed in BOTH lanes instead of emitting a
/// wrong-semantics obligation. Previously this compared raw float bits with
/// `bvslt`/`bvsgt` against integer bounds — e.g. `return 50.0` (bits
/// 0x4049000000000000, a huge positive integer) was "out of [0, 100]": a
/// false refutation.
#[test]
fn bounded_output_on_float_return_fails_closed_in_both_lanes() {
    let module = bounded_output_module(Ty::F64, 0.0, 100.0);

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().all(|v| v.kind != PropertyKind::Postcondition),
        "no wrong-semantics postcondition VC may be emitted for a float return"
    );
    assert!(
        vcs[0].violations.iter().any(|v| {
            v.kind == PropertyKind::Other
                && v.message.as_deref().is_some_and(|m| m.contains("BoundedOutput"))
        }),
        "the float-return BoundedOutput must fail closed loudly"
    );

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0]
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedBoundedOutput),
        "CHC lane must report the typed UnsupportedBoundedOutput reason, got {:?}",
        outputs[0].diagnostics
    );
}

/// A fractional f64 bound over an INTEGER return also fails closed: `as i128`
/// truncation would check a DIFFERENT postcondition (lo = 0.5 truncated to 0
/// accepts a returned 0 that violates the annotated bound — a false proof).
#[test]
fn bounded_output_with_fractional_bound_fails_closed() {
    let module = bounded_output_module(Ty::I32, 0.5, 100.0);

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().all(|v| v.kind != PropertyKind::Postcondition),
        "a truncated-bound postcondition VC would prove the wrong property"
    );
    assert!(
        vcs[0].violations.iter().any(|v| {
            v.kind == PropertyKind::Other
                && v.message.as_deref().is_some_and(|m| m.contains("BoundedOutput"))
        }),
        "the fractional bound must fail closed loudly"
    );
}

/// Exact integer bounds on an UNSIGNED return use UNSIGNED comparisons.
/// (The old signed encoding misread any value with the top bit set as
/// negative: `u32` return 3_000_000_000 with bounds [0, 4_000_000_000] was
/// "too low" — a false refutation.)
#[test]
fn bounded_output_on_unsigned_return_uses_unsigned_comparisons() {
    let module = bounded_output_module(Ty::U32, 0.0, 4_000_000_000.0);

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    let postcond: Vec<_> =
        vcs[0].violations.iter().filter(|v| v.kind == PropertyKind::Postcondition).collect();
    assert_eq!(postcond.len(), 1, "exact in-range bounds must still emit the obligation");
    assert!(
        expr_tree_has(&postcond[0].condition, &|v| matches!(
            v,
            ExprValue::BvULt(_, _) | ExprValue::BvUGt(_, _)
        )),
        "unsigned return bounds must compare unsigned"
    );
    assert!(
        !expr_tree_has(&postcond[0].condition, &|v| matches!(
            v,
            ExprValue::BvSLt(_, _) | ExprValue::BvSGt(_, _)
        )),
        "unsigned return bounds must not compare signed"
    );
}

/// An F16 float constant (no computable bit pattern on stable Rust) fails
/// closed in both lanes with the typed `UnmodeledConstant` reason.
#[test]
fn f16_constant_fails_closed_in_both_lanes() {
    let mut mb = ModuleBuilder::new("test_f16_const");
    let ft = mb.add_func_type(vec![], vec![Ty::F16]);
    let mut fb = mb.function("f16_const", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let c = fb.fconst(Ty::F16, 1.0);
    fb.ret(vec![c]);
    fb.build();
    let module = mb.build();

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().any(|v| {
            v.kind == PropertyKind::Other
                && v.message
                    .as_deref()
                    .is_some_and(|m| m.contains("constant without an exact bit-level encoding"))
        }),
        "an F16 constant must fail closed in BMC, violations: {:?}",
        vcs[0].violations
    );

    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0]
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::UnmodeledConstant),
        "an F16 constant must fail closed in CHC with UnmodeledConstant, got {:?}",
        outputs[0].diagnostics
    );
}

/// Build `fn bounded(x: ret_ty) -> ret_ty { return x; }` carrying
/// `BoundedOutput { lo, hi }` (manual construction: the builder has no
/// function-proof API).
fn bounded_output_module(ret_ty: Ty, lo: f64, hi: f64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_bounded_output");
    let ft = mb.add_func_type(vec![ret_ty.clone()], vec![ret_ty.clone()]);
    let _fb = mb.function("bounded_fn", ft);
    drop(_fb);
    let mut module = mb.build();
    module.functions.clear();

    let mut func = trust_ir::Function::new(
        trust_ir::value::FuncId::new(0),
        "bounded_fn",
        trust_ir::value::FuncTyId::new(0),
        trust_ir::value::BlockId::new(0),
    );
    func.proofs.push(ProofAnnotation::BoundedOutput { lo, hi });

    let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));
    block.params.push((trust_ir::value::ValueId::new(0), ret_ty));
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(0)],
    }));
    func.blocks.push(block);
    module.add_function(func);
    module
}

/// Count `error`-headed rules in a CHC VC. Every unsupported construct and every
/// real violation feeds the same nullary `error` relation, which is exactly why
/// whole-function translation lets one unmodeled construct sink the function.
fn count_error_rules(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules.iter().filter(|rule| rule.head.name == "error").count()
}

/// Diamond CFG with an unsupported construct on ONE arm:
///
///        entry
///        /   \
///   A(bad)    B          A holds a relocatable SymbolAddr const (unsupported)
///        \   /
///        Join
///
/// Returns (module, func, target_the_site_CANNOT_precede, target_it_CAN).
/// `B` is the first: reachable from entry, but NOT from A. `Join` is the second.
fn narrowing_fixture_module()
-> (trust_ir::Module, trust_ir::value::FuncId, trust_ir::value::BlockId, trust_ir::value::BlockId) {
    use trust_ir::value::{BlockId, FuncId, ValueId};
    let mut module = trust_ir::Module::new("test_chc_narrowing");
    let ft = module.add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false });
    let (entry, a, b, join) = (BlockId::new(0), BlockId::new(1), BlockId::new(2), BlockId::new(3));
    let cond = ValueId::new(0);
    let bad = ValueId::new(1);
    let mut func = trust_ir::Function::new(FuncId::new(0), "narrowing_fixture", ft, entry);

    let mut e = trust_ir::Block::new(entry);
    e.body.push(
        trust_ir::node::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::Bool,
            value: trust_ir::constant::Constant::Int(1),
        })
        .with_result(cond),
    );
    e.body.push(trust_ir::node::InstrNode::new(trust_ir::Inst::CondBr {
        cond,
        then_target: a,
        then_args: vec![],
        else_target: b,
        else_args: vec![],
    }));
    func.blocks.push(e);

    // A: the unsupported construct, then join.
    let mut ba = trust_ir::Block::new(a);
    ba.body.push(
        trust_ir::node::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::Ptr,
            value: trust_ir::constant::Constant::SymbolAddr {
                symbol: "static_i32".to_string(),
                addend: 0,
            },
        })
        .with_result(bad),
    );
    ba.body.push(trust_ir::node::InstrNode::new(trust_ir::Inst::Br { target: join, args: vec![] }));
    func.blocks.push(ba);

    // B: clean sibling arm. NOT reachable from A.
    let mut bb = trust_ir::Block::new(b);
    bb.body.push(trust_ir::node::InstrNode::new(trust_ir::Inst::Br { target: join, args: vec![] }));
    func.blocks.push(bb);

    let mut bj = trust_ir::Block::new(join);
    bj.body.push(trust_ir::node::InstrNode::new(trust_ir::Inst::Return { values: vec![] }));
    func.blocks.push(bj);

    let id = func.id;
    module.functions.push(func);
    (module, id, b, join)
}

// ---------------------------------------------------------------------------
// PER-OBLIGATION CHC NARROWING
//
// Whole-function mode routes every unsupported construct's error rule into the
// single nullary `error` relation, so ONE unmodeled construct anywhere sinks
// EVERY trust-mc obligation of that function. `narrow_to_target_block` scopes
// that: a construct provably off every entry ->* site ->* target path cannot
// influence the states reaching `target`, so its rule is dropped for THAT
// obligation only.
//
// The pair is the point. `narrowing_keeps_rule_when_site_precedes_target` is the
// FAIL-CLOSED guard: if it ever stops seeing the error rule, the narrowing has
// begun dropping rules that CAN affect the obligation, which is a false PROVE.
// ---------------------------------------------------------------------------

#[test]
fn narrowing_drops_rule_for_unreachable_site() {
    let (module, func, target_after, _site_only) = narrowing_fixture_module();
    let mut opts = TranslateOptions::default();

    // Whole-function: the rule is present, so the obligation is sunk.
    let wide =
        trust_ir_function_to_chc_translation_output(&module, func, &opts).expect("translates");
    let wide_errors = count_error_rules(&wide.vc);

    // Narrowed to a target the unsupported site CANNOT precede.
    opts.narrow_to_target_block = Some(target_after);
    let narrow =
        trust_ir_function_to_chc_translation_output(&module, func, &opts).expect("translates");
    let narrow_errors = count_error_rules(&narrow.vc);

    assert!(
        narrow_errors < wide_errors,
        "narrowing must drop at least one error rule for a site off every \
         entry->target path (wide={wide_errors}, narrow={narrow_errors})"
    );
}

#[test]
fn narrowing_keeps_rule_when_site_precedes_target() {
    // FAIL-CLOSED GUARD. A site that CAN lie on an entry->target path must keep
    // its rule. If this ever passes with a dropped rule, the narrowing is
    // masking a construct that can affect the obligation -> false PROVE.
    let (module, func, _target_after, site_reachable_target) = narrowing_fixture_module();
    let mut opts = TranslateOptions::default();
    let wide =
        trust_ir_function_to_chc_translation_output(&module, func, &opts).expect("translates");
    opts.narrow_to_target_block = Some(site_reachable_target);
    let narrow =
        trust_ir_function_to_chc_translation_output(&module, func, &opts).expect("translates");
    assert_eq!(
        count_error_rules(&narrow.vc),
        count_error_rules(&wide.vc),
        "a site that can precede the target MUST keep its error rule"
    );
}

#[test]
fn narrowing_invalid_target_keeps_unsupported_rule() {
    let (module, func, _, _) = narrowing_fixture_module();
    let wide =
        trust_ir_function_to_chc_translation_output(&module, func, &TranslateOptions::default())
            .expect("translates");

    let opts = TranslateOptions {
        narrow_to_target_block: Some(trust_ir::value::BlockId::new(99)),
        ..TranslateOptions::default()
    };
    let narrow =
        trust_ir_function_to_chc_translation_output(&module, func, &opts).expect("translates");

    assert_eq!(
        count_error_rules(&narrow.vc),
        count_error_rules(&wide.vc),
        "a missing target is Unknown, not proof that the unsupported site is irrelevant"
    );
}

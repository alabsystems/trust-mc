// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for trust_ir → BmcVc translation.
//!
//! Uses `trust_ir-build` to construct test programs, then verifies the
//! generated VCs match expectations.

#[path = "tests/addressable_storage.rs"]
mod addressable_storage;
#[path = "tests/complete_aggregate_definedness.rs"]
mod complete_aggregate_definedness;
#[path = "tests/native_bool_resize.rs"]
mod native_bool_resize;
#[path = "tests/native_division_domain.rs"]
mod native_division_domain;
#[path = "tests/native_unary.rs"]
mod native_unary;
#[path = "tests/native_wire_identity.rs"]
mod native_wire_identity;
#[path = "tests/runtime_closure.rs"]
mod runtime_closure;
#[path = "tests/tensor_region.rs"]
pub(crate) mod tensor_region;
#[path = "tests/typed_signature_abi.rs"]
mod typed_signature_abi;
#[path = "tests/wire74.rs"]
mod wire74;

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
use crate::translate_chc::DIRECT_CALL_SUMMARY_MAX_DEPTH;
use crate::{
    CallSummaryOutcome, ChcTranslationOutput, NativeTrustMcBundleError, SEMANTICS_COVERAGE,
    SemanticsFamily, SemanticsStatus, TrustIrChcUnsupportedReason, coverage_for_family,
    family_for_inst, native_unmodeled_obligations, trust_ir_function_to_chc_translation_output,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_translation_outputs_per_block,
    trust_ir_to_chc_vc, trust_mc_bmc_vcs_from_native_bundle,
    trust_mc_chc_pdr_obligations_from_native_bundle,
};

/// Invalid fixtures stop at complete canonical preflight in both public lanes.
/// No instruction/site, SSA symbol or proof outcome is fabricated for them.
pub(crate) fn assert_canonical_refusal(module: &trust_ir::Module, expected: &str) {
    let errors = trust_ir_build::validate_module(module);
    assert!(
        errors.iter().any(|error| error.to_string().contains(expected)),
        "expected {expected:?}: {errors:?}"
    );
    let outputs = trust_ir_to_chc_translation_outputs(module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    assert_chc_canonical_refusal(&outputs[0], expected);
    let vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    assert!(vc.decls.is_empty());
    assert!(vc.constraints.is_empty());
    assert_eq!(vc.violations.len(), 1);
    let refusal = &vc.violations[0];
    assert_eq!(refusal.kind, PropertyKind::Other);
    assert!(refusal.message.as_deref().unwrap().contains(expected));
    assert_eq!(refusal.condition, Expr::true_());
}

fn assert_chc_canonical_refusal(output: &ChcTranslationOutput, expected: &str) {
    assert!(
        output.module_input_refusal.as_deref().is_some_and(|reason| reason.contains(expected)),
        "expected {expected:?}: {:?}",
        output.module_input_refusal
    );
    assert!(output.diagnostics.is_empty(), "module invalidity has no invented instruction site");
    assert_eq!(output.vc.rules.len(), 1);
    let rule = &output.vc.rules[0];
    assert_eq!(rule.head.name, "error");
    assert!(rule.body.relation.is_none());
    assert!(rule.body.constraints.is_empty());
    assert_eq!(output.vc.query.target.as_deref(), Some("error"));
}

pub(crate) fn fixture_target() -> trust_ir::TargetInfo {
    let module: trust_ir::Module =
        serde_json::from_str(include_str!("../tests/fixtures/typed_signature_abi.module.json"))
            .unwrap();
    module.target_info.unwrap()
}

fn add_dropped_struct(mb: &mut ModuleBuilder) -> Ty {
    Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Dropped".into(),
        fields: vec![FieldDef { name: "value".into(), ty: Ty::I64, offset: Some(0) }],
        size: Some(8),
        align: Some(8),
        repr: trust_ir::StructRepr::C,
        origin: None,
    }))
}

fn assert_canonical_module(module: &trust_ir::Module) {
    let report = trust_ir_build::validate_module_report(module);
    assert!(report.is_ok(), "canonical positive fixture must validate: {:?}", report.errors());
}

fn assert_no_module_refusal(outputs: &[ChcTranslationOutput]) {
    for output in outputs {
        assert!(
            output.module_input_refusal.is_none(),
            "unexpected module refusal: {:?}",
            output.module_input_refusal
        );
    }
}

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
        coverage_for_family(SemanticsFamily::BitIntrinsics).status,
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

/// trust-ir v43: an opaque runtime handle must get an UNINTERPRETED sort, not
/// a bitvector. A bitvector sort would let the solver pick one of 2^64
/// concrete values for a value the format says only a pinned external entry
/// point can produce.
#[test]
fn ty_to_sort_maps_handle_to_uninterpreted_sort_not_bitvec() {
    let handle = Ty::handle("Nat", "trust_bignum::Nat");
    let sort = ty_to_sort(&handle);

    // The load-bearing negative: NOT a bitvector (and so not an integer/bool
    // either), so no arithmetic, comparison or literal can apply to it.
    assert_eq!(sort.bitvec_width(), None, "a handle must not get a bitvector sort");
    assert!(!sort.is_bitvec());
    assert!(!sort.is_numeric());
    assert!(!sort.is_bool());
    assert!(matches!(sort.inner(), ay_bindings::SortInner::Uninterpreted(_)));

    // A handle is one pointer word wide, which is exactly the trap this test
    // guards: width equality with `Ptr` must NOT become sort equality.
    assert_eq!(handle.bit_width_with(64), Some(64));
    assert_eq!(ty_to_sort(&Ty::Ptr).bitvec_width(), Some(64));
    assert_ne!(sort, ty_to_sort(&Ty::Ptr), "a handle is never the same sort as a pointer");
    assert_ne!(sort, ty_to_sort(&Ty::U64));
    assert_ne!(sort, ty_to_sort(&Ty::Usize));
}

/// The sort is keyed on the full `(name, runtime)` identity, so two runtimes
/// cannot be conflated. Under a shared placeholder sort this crate's
/// sort-equality fences would accept a cross-runtime substitution.
#[test]
fn ty_to_sort_keys_handle_sort_on_name_and_runtime_identity() {
    let nat = ty_to_sort(&Ty::handle("Nat", "trust_bignum::Nat"));
    let other_runtime = ty_to_sort(&Ty::handle("Nat", "other_bignum::Nat"));
    let other_name = ty_to_sort(&Ty::handle("Int", "trust_bignum::Nat"));

    assert_ne!(nat, other_runtime, "same type name, different runtime: distinct sorts");
    assert_ne!(nat, other_name, "same runtime, different type name: distinct sorts");
    assert_ne!(other_runtime, other_name);

    // Identity is the pair, so the SAME pair is the SAME sort -- transport of
    // one runtime's handle through copy/select/call must still typecheck.
    assert_eq!(nat, ty_to_sort(&Ty::handle("Nat", "trust_bignum::Nat")));

    // The name carries both halves, and the pinned v1 runtime reads back
    // whole in a counterexample.
    let ay_bindings::SortInner::Uninterpreted(name) = nat.inner() else {
        panic!("a handle sort is uninterpreted");
    };
    assert_eq!(name, "handle<Nat, trust_bignum::Nat>");
}

/// No constant constructs a handle. `Ty::Handle`'s `bit_width_with` is one
/// pointer word, so without an explicit guard the integer arms of
/// `const_to_expr` would hand back a 64-bit literal -- fabricating the one
/// value the format reserves to a pinned entry point.
#[test]
fn const_to_expr_refuses_every_constant_at_handle_type() {
    use trust_ir::constant::Constant;

    let handle = Ty::handle("Nat", "trust_bignum::Nat");
    for value in [
        Constant::Int(0),
        Constant::Int(1),
        Constant::Int(0x7fff_ffff_ffff_ffff),
        Constant::u128(u128::from(u64::MAX) + 1),
        Constant::Bool(false),
        Constant::PhantomData,
        Constant::Aggregate(vec![Constant::Int(0)]),
    ] {
        assert!(
            const_to_expr(&handle, &value).is_none(),
            "a handle must have no constant encoding, got one for {value:?}"
        );
    }

    // Control: the same integer constant at a scalar type still encodes, so
    // the test is measuring the handle guard and not a dead code path.
    assert!(const_to_expr(&Ty::U64, &Constant::Int(1)).is_some());
}

/// `normalize_expr_to_ty` must not coerce anything INTO a handle: with no
/// bitvector width to target it returns the expression untouched, so the
/// caller's sort check is the thing that fails, loudly.
#[test]
fn normalize_expr_to_ty_leaves_a_handle_target_untouched() {
    let expr = Expr::bitvec_const(7, 64);
    let normalized =
        crate::translate::normalize_expr_to_ty(&expr, &Ty::handle("Nat", "trust_bignum::Nat"));

    assert_eq!(normalized, expr, "no bit-level coercion may produce a handle");
    assert_ne!(*normalized.sort(), ty_to_sort(&Ty::handle("Nat", "trust_bignum::Nat")));
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

pub(crate) fn native_digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

pub(crate) fn native_trust_mc_bundle(mode: TrustMcVerificationMode) -> NativeVerificationBundle {
    native_trust_mc_bundle_inner(mode, false)
}

/// The same fixture with the REQUESTED function's body switched to an `f64`
/// add — a construct the CHC translator cannot model precisely, so it lowers to
/// an unconditionally reachable error rule and records a
/// `FloatingPointArithmetic` diagnostic. Used to pin that the producer records
/// the DISTINCT typed reasons alongside the fail-closed site count.
pub(crate) fn native_trust_mc_bundle_with_fail_closed_lowering(
    mode: TrustMcVerificationMode,
) -> NativeVerificationBundle {
    native_trust_mc_bundle_inner(mode, true)
}

fn native_trust_mc_bundle_inner(
    mode: TrustMcVerificationMode,
    fail_closed_lowering: bool,
) -> NativeVerificationBundle {
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

    // `f64` arithmetic has no precise CHC model, so selecting it makes the
    // translation fail closed (an unconditionally reachable error rule plus a
    // `FloatingPointArithmetic` diagnostic) without changing anything else.
    let add_ty = if fail_closed_lowering { Ty::F64 } else { Ty::I32 };
    let add_ft = mb.add_func_type(vec![add_ty.clone(), add_ty.clone()], vec![add_ty.clone()]);
    {
        let mut fb = mb.function("trust_mc_checked_add", add_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let lhs = fb.add_block_param(entry, add_ty.clone());
        let rhs = fb.add_block_param(entry, add_ty.clone());
        let sum =
            if fail_closed_lowering { fb.fadd(add_ty, lhs, rhs) } else { fb.add(add_ty, lhs, rhs) };
        fb.ret(vec![sum]);
        fb.build();
    }

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let source_file =
        module.intern_file("native_trust_mc_bundle.rs").expect("Module::intern_file: test fixture");
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

pub(crate) fn native_obligation_identity(
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

pub(crate) fn trust_mc_request_provenance(
    mode: TrustMcVerificationMode,
) -> NativeRequestProvenance {
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

pub(crate) fn trust_mc_request_options(
    mode: TrustMcVerificationMode,
) -> trust_ir::TrustMcRequestOptions {
    let mut options = trust_ir::TrustMcRequestOptions::default();
    options.slicing = trust_ir::TrustMcSlicingMode::None;
    options.chc.engine = trust_ir::TrustMcChcEngine::NativePdr;
    options.chc.invariant_source = trust_ir::TrustMcInvariantSource::None;
    options.chc.pdr.enabled = true;
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

/// The last `suffix_len` arguments of the first transition rule into `relation`.
/// Tests reading a block's transition rules translate PER BLOCK
/// (`trust_ir_to_chc_translation_outputs_per_block`): in production an acyclic
/// function is one large-block query with no transition rule
/// (`translate_chc_large_block.rs`), built from the same block translation.
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

/// Two functions, `f` (bb0: `assert(c); br bb1`, bb1: `ret`) and `g`, and no
/// obligations yet.
fn obligation_scope_module() -> (trust_ir::Module, trust_ir::FuncId, trust_ir::FuncId) {
    let mut mb = ModuleBuilder::new("obligation_scope");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    for name in ["f", "g"] {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        fb.assert(cond);
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let id = |name: &str| module.functions.iter().find(|func| func.name == name).unwrap().id;
    let (f, g) = (id("f"), id("g"));
    (module, f, g)
}

fn scope_probe(
    id: u32,
    kind: ObligationKind,
    function: Option<trust_ir::FuncId>,
    site: Option<trust_ir::ObligationSite>,
) -> ProofObligation {
    let mut obligation =
        ProofObligation::new(ProofId::new(id), kind, ProofStatus::Pending, "probe");
    obligation.function = function;
    obligation.site = site;
    obligation
}

/// What the safety encoding of the requested function `f` answers. It answers
/// a panic-/memory-safety obligation about `f`, whole-function or sited at any
/// instruction of `f`, and nothing else: a contract or other non-safety kind,
/// a temporal property, an obligation about `g`, one bound to no function, or
/// one whose site does not resolve.
///
/// Before this, the answer depended on the kind alone: `ScopedToAnotherFunction`,
/// `SitedInAnotherFunction`, `Unscoped` and `SiteUnresolved` below came back
/// answered, and so did the five contract kinds.
#[test]
fn native_unmodeled_obligations_name_everything_the_safety_encoding_does_not_answer() {
    use crate::NativeUnmodeledReason as Why;

    let (mut module, f, g) = obligation_scope_module();
    let block = |function: trust_ir::FuncId, index: usize| {
        module.function_by_id(function).unwrap().blocks[index].id
    };
    let (f_bb0, f_bb1, g_bb0) = (block(f, 0), block(f, 1), block(g, 0));
    let site = |function, block, index| Some(trust_ir::ObligationSite::new(function, block, index));

    let kinds = [
        (ObligationKind::PanicFreedom, true),
        (ObligationKind::ArithmeticSafety, true),
        (ObligationKind::BoundsCheck, true),
        (ObligationKind::MemorySafety, true),
        (ObligationKind::Precondition, false),
        (ObligationKind::Postcondition, false),
        (ObligationKind::TypeInvariant, false),
        (ObligationKind::RefinementType, false),
        (ObligationKind::LoopInvariant, false),
        (ObligationKind::TranslationValidation, false),
        (ObligationKind::TemporalSafety, false),
        (ObligationKind::Liveness, false),
        (ObligationKind::GiveBackRefinement, false),
        (ObligationKind::Termination, false),
        (ObligationKind::Ownership, false),
        (
            ObligationKind::Custom {
                namespace: "trust.protocol".to_string(),
                name: "session".to_string(),
            },
            false,
        ),
    ];
    for (index, (kind, _)) in kinds.iter().enumerate() {
        module.proof_obligations.push(scope_probe(index as u32, kind.clone(), Some(f), None));
    }
    let requested: Vec<_> = (0..kinds.len() as u32).map(ProofId::new).collect();
    let unmodeled = native_unmodeled_obligations(&module, f, &requested);
    let expected: Vec<_> = kinds
        .iter()
        .enumerate()
        .filter(|(_, (_, answered))| !answered)
        .map(|(index, _)| (ProofId::new(index as u32), Why::KindNotAnswered))
        .collect();
    assert_eq!(
        unmodeled.iter().map(|u| (u.obligation, u.reason.clone())).collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        unmodeled[1].to_string(),
        "obligation #5 (Postcondition, kind not answered by a safety encoding)"
    );

    // Scope and site, all on the safety kind the encoding does answer.
    let cases = [
        ("whole-function, scoped to f", Some(f), None, None),
        ("sited in f, scoped to f", Some(f), site(f, f_bb0, 0), None),
        ("sited in f, scope from the site", None, site(f, f_bb1, 0), None),
        ("bound to no function", None, None, Some(Why::Unscoped)),
        ("scoped to g", Some(g), None, Some(Why::ScopedToAnotherFunction(g))),
        ("sited in g", None, site(g, g_bb0, 0), Some(Why::SitedInAnotherFunction(g))),
        (
            "site past the block's end",
            Some(f),
            site(f, f_bb0, 9),
            Some(Why::SiteUnresolved(trust_ir::ObligationSite::new(f, f_bb0, 9))),
        ),
    ];
    for (label, function, site, expected) in cases {
        module.proof_obligations =
            vec![scope_probe(0, ObligationKind::PanicFreedom, function, site)];
        let reasons = native_unmodeled_obligations(&module, f, &[ProofId::new(0)])
            .into_iter()
            .map(|u| u.reason)
            .collect::<Vec<_>>();
        assert_eq!(reasons, expected.into_iter().collect::<Vec<_>>(), "{label}");
    }

    // `spec` is modeled nowhere, and an id the module does not declare is
    // not an obligation anyone may credit.
    let mut temporal = scope_probe(10, ObligationKind::TemporalSafety, Some(f), None);
    temporal.spec = Some(trust_ir::proof::SpecObligationRef::new("Counter", "AlwaysBounded"));
    module.proof_obligations = vec![temporal];
    let with_spec = native_unmodeled_obligations(&module, f, &[ProofId::new(10), ProofId::new(99)]);
    assert_eq!(
        with_spec.iter().map(ToString::to_string).collect::<Vec<_>>(),
        vec![
            "obligation #10 (TemporalSafety, temporal property `Counter`::`AlwaysBounded`, \
             a temporal property is not a safety question)",
            "obligation #99 (not declared by the module)",
        ]
    );
}

/// A counterexample of `f`'s safety encoding shows that SOME error site of `f`
/// is reachable. It refutes a whole-function panic-freedom obligation of `f`
/// and nothing narrower: not one sited at a single check, not one about a
/// single class of check, not one about `g`.
#[test]
fn a_counterexample_refutes_only_whole_function_panic_freedom() {
    let (mut module, f, g) = obligation_scope_module();
    let f_bb0 = module.function_by_id(f).unwrap().blocks[0].id;
    module.proof_obligations = vec![
        scope_probe(0, ObligationKind::PanicFreedom, Some(f), None),
        scope_probe(
            1,
            ObligationKind::PanicFreedom,
            Some(f),
            Some(trust_ir::ObligationSite::new(f, f_bb0, 0)),
        ),
        scope_probe(2, ObligationKind::ArithmeticSafety, Some(f), None),
        scope_probe(3, ObligationKind::BoundsCheck, Some(f), None),
        scope_probe(4, ObligationKind::MemorySafety, Some(f), None),
        scope_probe(5, ObligationKind::PanicFreedom, Some(g), None),
        scope_probe(6, ObligationKind::PanicFreedom, None, None),
    ];
    let requested: Vec<_> = (0..8).map(ProofId::new).collect();
    assert_eq!(
        crate::native_obligations_not_refuted_by_a_counterexample(&module, f, &requested),
        (1..8).map(ProofId::new).collect::<Vec<_>>()
    );
}

/// The request's metadata class is the class ALL its obligations share. It was
/// read from the first one, so `[PanicFreedom, Postcondition]` was filed under
/// the L0 safety class and admitted to the bounded-unroll refutation lane.
#[test]
fn a_mixed_request_is_never_filed_under_the_safety_class() {
    let class_of = |bundle: &NativeVerificationBundle| {
        trust_mc_chc_pdr_obligations_from_native_bundle(bundle, &TranslateOptions::default())
            .expect("the fixture translates")[0]
            .obligation
            .kind
    };
    // The fixture's request asks for #1; it now asks for #1 (panic freedom)
    // and #0 (memory safety), then #0 becomes a postcondition.
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    bundle.module.proof_obligations[1].kind = ObligationKind::PanicFreedom;
    native_trust_mc_request_mut(&mut bundle).obligations = vec![ProofId::new(1), ProofId::new(0)];
    refresh_native_trust_mc_bundle_module_identity(&mut bundle);
    assert_eq!(class_of(&bundle), trust_mc_core::MirObligationKind::Assertion);

    bundle.module.proof_obligations[0].kind = ObligationKind::Postcondition;
    refresh_native_trust_mc_bundle_module_identity(&mut bundle);
    assert_eq!(class_of(&bundle), trust_mc_core::MirObligationKind::Protocol);
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
    // The requested obligation is TranslationValidation, which this function's
    // safety VC does not answer; the translation says so.
    assert_eq!(
        request_vc.unmodeled_obligations.iter().map(|u| u.obligation).collect::<Vec<_>>(),
        vec![ProofId::new(1)]
    );
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
    assert_eq!(
        request_obligation.unmodeled_obligations.iter().map(|u| u.obligation).collect::<Vec<_>>(),
        vec![ProofId::new(1)],
        "a TranslationValidation obligation is not answered by the safety CHC"
    );
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
        trust_mc_core::NativeTypedChcObligationMetadata::REQUEST_CONFIG_SCHEMA_VERSION
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

/// DIAGNOSTIC SURFACING (producer half). The fail-closed lowering COUNT already
/// reached the transport, so a demoted obligation could only say "N unsupported
/// trust_ir construct(s)" — with no way to learn WHICH of the ~50 typed reasons
/// blocked it short of re-running the translator. The producer must record the
/// DISTINCT reason labels next to the count.
///
/// This pins the LINK: the recorded labels must be exactly the sorted, deduped
/// labels of the diagnostics the very same translation produced.
#[test]
fn native_bundle_records_the_distinct_fail_closed_lowering_reasons() {
    let bundle = native_trust_mc_bundle_with_fail_closed_lowering(TrustMcVerificationMode::Chc);
    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc CHC request should translate");
    let translated = obligations.into_iter().next().expect("one native trust_mc CHC obligation");
    assert!(
        !translated.diagnostics.is_empty(),
        "the f64 fixture body must fail closed (else this test proves nothing)"
    );
    let metadata = translated
        .obligation
        .native_metadata
        .as_ref()
        .expect("typed native CHC obligation should carry bundle metadata");

    assert_eq!(
        metadata.fail_closed_lowering_site_count as usize,
        translated.diagnostics.len(),
        "the count must still be one per diagnostic"
    );

    let mut expected: Vec<String> =
        translated.diagnostics.iter().map(|d| d.reason.label()).collect();
    expected.sort();
    expected.dedup();
    assert_eq!(
        metadata.fail_closed_lowering_reasons, expected,
        "the recorded labels must be the distinct reasons of THIS translation"
    );
    assert!(
        metadata
            .fail_closed_lowering_reasons
            .contains(&TrustIrChcUnsupportedReason::FloatingPointArithmetic.label()),
        "the f64 add must surface as FloatingPointArithmetic, got {:?}",
        metadata.fail_closed_lowering_reasons
    );
}

/// The unchanged (integer) fixture must record NEITHER a count nor any reason —
/// the field is empty whenever the translation is exact, so it never appears in
/// the serialized metadata of a clean obligation.
#[test]
fn native_bundle_records_no_reasons_when_the_translation_is_exact() {
    let bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    let obligations =
        trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
            .expect("valid native trust_mc CHC request should translate");
    let translated = obligations.into_iter().next().expect("one native trust_mc CHC obligation");
    assert!(translated.diagnostics.is_empty(), "the i32 fixture body translates exactly");
    let metadata = translated.obligation.native_metadata.as_ref().expect("bundle metadata");
    assert_eq!(metadata.fail_closed_lowering_site_count, 0);
    assert!(metadata.fail_closed_lowering_reasons.is_empty());
    let json = serde_json::to_string(metadata).expect("serialize");
    assert!(
        !json.contains("fail_closed_lowering_reasons"),
        "an empty reason list must not appear in the serialized metadata: {json}"
    );
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "return arity mismatch: expected 1 values, got 0",
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
fn call_summary_declines_select_arm_with_wrong_carrier_without_panicking() {
    // Invalid callee input refuses the complete module even when only its caller
    // is selected; malformed branches never reach AY's ite constructor.
    let mut mb = ModuleBuilder::new("test_summary_select_wrong_carrier");
    let callee_ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool, Ty::U64], vec![Ty::U64]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool, Ty::U64], vec![Ty::U64]);

    let callee = {
        let mut fb = mb.function("summary_select_wrong_carrier_callee", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let wrong_then = fb.add_block_param(entry, Ty::Bool);
        let else_val = fb.add_block_param(entry, Ty::U64);
        let selected = fb.select(Ty::U64, cond, wrong_then, else_val);
        fb.ret(vec![selected]);
        fb.build()
    };

    let caller = {
        let mut fb = mb.function("summary_select_wrong_carrier_caller", caller_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let wrong_then = fb.add_block_param(entry, Ty::Bool);
        let else_val = fb.add_block_param(entry, Ty::U64);
        let selected = fb.call(callee, vec![cond, wrong_then, else_val]);
        fb.ret(vec![selected]);
        fb.build()
    };

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let selected =
        trust_ir_function_to_chc_translation_output(&module, caller, &TranslateOptions::default())
            .expect("caller exists");
    assert_chc_canonical_refusal(&selected, "select then type mismatch: expected u64, got bool");
    assert_canonical_refusal(&module, "select then type mismatch: expected u64, got bool");
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "schema attribute does not match version 1",
    );
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
    let canonical = mb.build().expect("ModuleBuilder::build: test fixture");

    let mut no_results = canonical.clone();
    let node = no_results.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(&node.inst, trust_ir::Inst::DialectOp(_)))
        .expect("TLS dialect node");
    node.results.clear();
    assert_canonical_refusal(&no_results, "dialect declares 0 SSA results, expected 1");

    let mut two_results = canonical;
    let node = two_results.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(&node.inst, trust_ir::Inst::DialectOp(_)))
        .expect("TLS dialect node");
    node.results.push(node.results[0]);
    assert_canonical_refusal(&two_results, "dialect declares 2 SSA results, expected 1");
}

#[test]
fn wrapping_add_body_lowers_to_modular_bvadd_not_fresh() {
    // A provided body with an explicit Wrapping-tagged Add must retain its
    // modular operation through the direct-call summary. A method name and
    // signature alone cannot replace a different body with arithmetic.
    let mut mb = ModuleBuilder::new("test_wrapping_add_intrinsic");
    let wrap_ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let f_ft = mb.add_func_type(vec![Ty::U64], vec![]);

    // The body states the actual operation; its spelling grants no semantics.
    let wrap_id = {
        let mut fb = mb.function("core::num::<impl u64>::wrapping_add", wrap_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        let sum = fb.binop(BinOp::Add, Ty::U64, a, b);
        fb.annotate_last(ProofAnnotation::Wrapping).expect("existing Add instruction");
        fb.ret(vec![sum]);
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

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
fn direct_call_boolean_negation_summary_binds_precise_result_not_fresh() {
    // Canonical scalar Bool negation is BXor with true. Both direct-call
    // summaries and inline translation must preserve the exact not(x) result.
    let mut mb = ModuleBuilder::new("test_not_body_summary");
    let g_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let f_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    // callee g(x) = !x (canonical Bool negation)
    let g_id = {
        let mut fb = mb.function("not_body_callee", g_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::Bool);
        let truth = fb.bool_const(true);
        let y = fb.binop(BinOp::BXor, Ty::Bool, x, truth);
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

    assert_no_module_refusal(&outputs);
    let caller = outputs
        .iter()
        .find(|o| o.vc.rules.iter().any(|rule| rule.head.name == "bb1"))
        .expect("the caller f has an entry->exit transition rule");
    let [result] = head_arg_suffix(caller, "bb1", 1) else {
        panic!("bb1 transition should forward the single summarized-call result arg");
    };
    assert!(
        not_inner_matches(
            result,
            |inner| matches!(inner, ExprValue::Eq(lhs, rhs) if matches!(lhs.value(), ExprValue::Var { name } if name == "bb0_v0") && rhs == &Expr::bool_const(true))
        ),
        "the summarized `!x` call result must be CONSTRAINED to not(x), got {:?}",
        result.value()
    );
}

#[test]
fn inline_boolean_negation_binds_precise_result_not_havoc() {
    // The inline twin of the direct-call test uses the same canonical Bool
    // operation and must preserve not(x), rather than an unconstrained result.
    let mut mb = ModuleBuilder::new("test_inline_not");
    let f_ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("inline_not_fn", f_ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::Bool);
    let truth = fb.bool_const(true);
    let r = fb.binop(BinOp::BXor, Ty::Bool, a, truth);
    fb.add_block_param(exit, Ty::Bool);
    fb.br(exit, vec![r]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());
    assert_no_module_refusal(&outputs);
    let f = outputs
        .iter()
        .find(|o| o.vc.rules.iter().any(|rule| rule.head.name == "bb1"))
        .expect("the fn has an entry->exit transition rule");
    let [result] = head_arg_suffix(f, "bb1", 1) else {
        panic!("bb1 transition should forward the single canonical Bool result arg");
    };
    assert!(
        not_inner_matches(
            result,
            |inner| matches!(inner, ExprValue::Eq(lhs, rhs) if matches!(lhs.value(), ExprValue::Var { name } if name == "bb0_v0") && rhs == &Expr::bool_const(true))
        ),
        "canonical inline `!x` must be CONSTRAINED to not(x), got {:?}",
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let vcs = trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default())
        .into_iter()
        .map(|output| output.vc)
        .collect::<Vec<_>>();

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

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "assume predicate must be bool, got u32",
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

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "condbr condition must be bool, got u32",
    );
}

#[test]
fn typed_chc_translation_fails_closed_on_select_arm_with_wrong_carrier() {
    // The builder permits this malformed shape, but complete canonical preflight
    // refuses the wrong Select arm before either public lane translates it.
    let mut mb = ModuleBuilder::new("test_select_wrong_carrier_chc");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool, Ty::U64], vec![Ty::U64]);

    let mut fb = mb.function("select_wrong_carrier_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let wrong_then = fb.add_block_param(entry, Ty::Bool);
    let else_val = fb.add_block_param(entry, Ty::U64);
    let selected = fb.select(Ty::U64, cond, wrong_then, else_val);
    fb.ret(vec![selected]);
    fb.build();

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "select then type mismatch: expected u64, got bool",
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "bool-to-integer cast should not fail closed");
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "supported bool-to-integer cast should not introduce unsupported error rules"
    );
    let branch_arg = &head_arg_suffix(output, "bb1", 1)[0];
    let one = Expr::bitvec_const(1u64, 1);
    let zero = Expr::bitvec_const(0u64, 1);
    assert!(
        matches!(
            branch_arg.value(),
            ExprValue::BvZeroExtend { extra_bits: 7, expr }
                if matches!(expr.value(), ExprValue::Ite { cond, then_expr, else_expr }
                    if matches!(cond.value(), ExprValue::Var { name } if name == "bb0_v0")
                        && then_expr == &one
                        && else_expr == &zero)
        ),
        "zext Bool to u8 must resize the canonical one-bit Boolean lane"
    );
}

#[test]
fn typed_chc_translation_lowers_same_width_integer_cast_without_unsupported_diagnostic() {
    let mut mb = ModuleBuilder::new("test_same_width_int_cast_chc");
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);

    let mut fb = mb.function("bitcast_i32_u32_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::I32);
    let cast = fb.cast(CastOp::Bitcast, Ty::I32, Ty::U32, input);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

    assert_no_module_refusal(&outputs);
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

/// A mismatched integer carrier is rejected before any AY cast expression is
/// constructed; the declared source type cannot relabel a wider SSA operand.
#[test]
fn typed_chc_translation_refuses_over_wide_operand_on_narrowing_cast() {
    let mut mb = ModuleBuilder::new("test_over_wide_trunc_operand_chc");
    let ft = mb.add_func_type(vec![Ty::U128], vec![]);

    let mut fb = mb.function("trunc_over_wide_carrier_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    // The value id is bound at the U128 carrier (128 bits) ...
    let input = fb.add_block_param(entry, Ty::U128);
    // ... but the cast declares a 64-bit source. 64 > 32, so the narrowing
    // obligation fires and used to compare BitVec128 against BitVec64.
    let cast = fb.cast(CastOp::Trunc, Ty::U64, Ty::U32, input);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "cast trunc operand type u128 does not match declared source type u64",
    );
}

/// The widening direction must stop at the same canonical operand-type check.
#[test]
fn typed_chc_translation_refuses_over_wide_operand_on_widening_cast() {
    let mut mb = ModuleBuilder::new("test_over_wide_zext_operand_chc");
    let ft = mb.add_func_type(vec![Ty::U128], vec![]);

    let mut fb = mb.function("zext_over_wide_carrier_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let input = fb.add_block_param(entry, Ty::U128);
    let cast = fb.cast(CastOp::ZExt, Ty::U64, Ty::U128, input);
    fb.add_block_param(exit, Ty::U128);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "cast zext operand type u128 does not match declared source type u64",
    );
}

/// Build `fn(bool)` whose Bool-sorted value id is read by an integer cast that
/// DECLARES an integer `src_ty`, and translate it through the CHC lowering.
fn chc_outputs_for_integer_cast_over_bool_binding(
    op: CastOp,
    src_ty: Ty,
    dst_ty: Ty,
) -> Vec<ChcTranslationOutput> {
    let mut mb = ModuleBuilder::new("test_bool_binding_integer_cast_chc");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("integer_cast_over_bool_binding_chc", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    // The value id is bound at the Bool carrier (SMT `Bool`, no bitvector width) ...
    let input = fb.add_block_param(entry, Ty::Bool);
    // ... but the cast declares an integer source.
    let cast = fb.cast(op, src_ty, dst_ty.clone(), input);
    fb.add_block_param(exit, dst_ty);
    fb.br(exit, vec![cast]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_refusal(&module, "operand type bool does not match declared source type");
    trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default())
}

/// A Bool operand cannot be relabeled as an integer source. Complete canonical
/// preflight refuses it before bitvector extraction or successor facts exist.
#[test]
fn typed_chc_translation_fails_closed_on_trunc_over_bool_sorted_binding() {
    let outputs = chc_outputs_for_integer_cast_over_bool_binding(CastOp::Trunc, Ty::U64, Ty::U32);
    assert_eq!(outputs.len(), 1);
    assert_chc_canonical_refusal(
        &outputs[0],
        "cast trunc operand type bool does not match declared source type u64",
    );
}

/// The widening arms of the same shape (`zero_extend`/`sign_extend` carry the
/// same `REQUIRES: BitVec` contract as `extract`) must fail closed identically.
#[test]
fn typed_chc_translation_fails_closed_on_extension_over_bool_sorted_binding() {
    for (op, src_ty, dst_ty) in [(CastOp::ZExt, Ty::U8, Ty::U64), (CastOp::SExt, Ty::I8, Ty::I64)] {
        let expected =
            format!("cast {op} operand type bool does not match declared source type {src_ty}");
        let outputs = chc_outputs_for_integer_cast_over_bool_binding(op, src_ty, dst_ty);
        assert_eq!(outputs.len(), 1);
        assert_chc_canonical_refusal(&outputs[0], &expected);
    }
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "modeled U64 metadata must not fail closed");
    let slice_len_syms =
        outputs[0].vc.vars().iter().filter(|var| var.name.contains("_slice_len_")).count();
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty());
    let slice_len_syms =
        outputs[0].vc.vars().iter().filter(|var| var.name.contains("_slice_len_")).count();
    assert_eq!(slice_len_syms, 2, "distinct fat values must keep independent length symbols");
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
        origin: None,
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "the usize<->newtype bit-identity legs must not fail closed: {:?}",
        outputs[0].diagnostics
    );
    let havoc_stand_ins =
        outputs[0].vc.vars().iter().filter(|var| var.name.contains("unsupported_result")).count();
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
    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "lacks valid layout evidence",
    );
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    let slice_len_syms =
        outputs[0].vc.vars().iter().filter(|var| var.name.contains("_slice_len_")).count();
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    let havoc_stand_ins =
        outputs[0].vc.vars().iter().filter(|var| var.name.contains("unsupported_result")).count();
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].diagnostics.is_empty(),
        "slice-length (U64) metadata is now soundly modeled, not unsupported: {:?}",
        outputs[0].diagnostics
    );
}

/// Whether any rule of `vc` carries a `_ <= isize::MAX` bitvector path constraint —
/// the slice-length bound `translate_node`'s `Inst::PtrMetadata` arm pushes.
fn chc_vc_has_isize_max_len_bound(vc: &trust_mc_core::chc::ChcVc) -> bool {
    let bound = Expr::bitvec_const(i64::MAX as i128, 64);
    vc.rules.iter().any(|rule| {
        rule.body
            .constraints
            .iter()
            .any(|c| matches!(c.value(), ExprValue::BvULe(_, rhs) if rhs == &bound))
    })
}

/// Build the EXACT witness function `pub fn f(s: &[T]) -> usize { s.len() + 1 }` —
/// `PtrMetadata` for the length, then a checked `Add` whose no-overflow obligation is
/// the thing the `len <= isize::MAX` path constraint discharges. `make_fat_ty` mints
/// the fat-pointer type INSIDE this module so a `FatPtrKind::Slice(TyId)` element
/// resolves against this module's own type table.
fn chc_slice_len_plus_one_vc(
    name: &str,
    make_fat_ty: impl FnOnce(&mut ModuleBuilder) -> Ty,
) -> ChcTranslationOutput {
    let mut mb = ModuleBuilder::new(name);
    let fat_ty = make_fat_ty(&mut mb);
    let ft = mb.add_func_type(vec![fat_ty.clone()], vec![Ty::U64]);
    let mut fb = mb.function(name, ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let ptr = fb.add_block_param(entry, fat_ty.clone());
    let metadata = fb.ptr_metadata(fat_ty, Ty::U64, ptr);
    let one = fb.iconst(Ty::U64, 1);
    let sum = fb.add(Ty::U64, metadata, one);
    fb.ret(vec![sum]);
    fb.build();
    let mut outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    outputs.remove(0)
}

/// Trust (P0 ZST-slice-length FALSE PROOF): a ZERO-SIZED element breaks the
/// `len <= isize::MAX` derivation. `isize::MAX` caps the total BYTE size, and only
/// `size_of::<T>() >= 1` turns that into an ELEMENT-count cap; `[(); usize::MAX]`
/// occupies zero bytes, so a `&[()]` length may legally reach `usize::MAX`.
///
/// WITNESS (the bound used to be pushed for EVERY `U64` metadata):
/// ```ignore
/// pub fn f(z: &[()]) -> usize { z.len() + 1 }   // proved no-overflow
/// let v: Vec<()> = vec![(); usize::MAX];        // ... and really overflows
/// ```
/// The ZST slice must now get an UNCONSTRAINED fresh symbolic (fail-closed: the free
/// value ranges over all of `u64` ⊇ the realizable lengths, so `len + 1` stays
/// refutable), while the non-ZST companion below keeps the bound.
#[test]
fn typed_chc_zst_slice_length_metadata_carries_no_isize_bound() {
    let output = chc_slice_len_plus_one_vc("zst_slice_len", |mb| {
        let unit_elem = mb.add_type(Ty::Unit);
        Ty::FatPtr(FatPtrKind::Slice(unit_elem))
    });
    assert!(
        !chc_vc_has_isize_max_len_bound(&output.vc),
        "a ZST-element slice length must NOT be bounded by isize::MAX (its length can \
         reach usize::MAX): {:?}",
        output.vc.rules
    );
}

/// `str` metadata is a BYTE length and every byte is one byte, so `len <= isize::MAX`
/// holds UNCONDITIONALLY — no element-type proof needed. Same split as
/// `trust_types::total_call_summaries::total_summary_len_bound`.
#[test]
fn typed_chc_str_byte_length_metadata_keeps_isize_bound() {
    let output = chc_slice_len_plus_one_vc("str_len", |_| Ty::FatPtr(FatPtrKind::Str));
    assert!(
        chc_vc_has_isize_max_len_bound(&output.vc),
        "a `str` byte-length keeps the unconditional `len <= isize::MAX` bound: {:?}",
        output.vc.rules
    );
}

/// Known-true companion to the ZST case: a `&[u8]` element IS provably non-ZST, so
/// `len <= isize::MAX` is a theorem and the bound must STILL be emitted — the fix
/// must not be a blanket disable of the slice-length model.
#[test]
fn typed_chc_nonzst_slice_length_metadata_keeps_isize_bound() {
    let output = chc_slice_len_plus_one_vc("nonzst_slice_len", |mb| {
        let u8_elem = mb.add_type(Ty::U8);
        Ty::FatPtr(FatPtrKind::Slice(u8_elem))
    });
    assert!(
        output.diagnostics.is_empty(),
        "a non-ZST slice length stays soundly modeled, not unsupported: {:?}",
        output.diagnostics
    );
    assert!(
        chc_vc_has_isize_max_len_bound(&output.vc),
        "a non-ZST (u8) slice length keeps its `len <= isize::MAX` bound: {:?}",
        output.vc.rules
    );
}

/// The non-ZST proof must recurse through aggregates exactly like the three sibling
/// gates: an all-ZST struct element (`struct Pad { a: (), b: () }`) is a ZST, so its
/// slice gets NO bound; a struct with one non-ZST field does.
#[test]
fn typed_chc_slice_length_bound_follows_aggregate_element_zst_ness() {
    for (struct_name, field_ty, expect_bound) in [("Pad", Ty::Unit, false), ("Cell", Ty::U32, true)]
    {
        let output = chc_slice_len_plus_one_vc("aggregate_slice_len", |mb| {
            let struct_id = mb.add_struct(StructDef {
                id: StructId::new(0),
                name: struct_name.to_string(),
                fields: vec![
                    FieldDef { name: "a".into(), ty: field_ty.clone(), offset: None },
                    FieldDef { name: "b".into(), ty: Ty::Unit, offset: None },
                ],
                size: None,
                align: None,
                repr: Default::default(),
                origin: None,
            });
            let elem = mb.add_type(Ty::Struct(struct_id));
            Ty::FatPtr(FatPtrKind::Slice(elem))
        });
        assert_eq!(
            chc_vc_has_isize_max_len_bound(&output.vc),
            expect_bound,
            "slice of `{struct_name}` (non-ZST field: {expect_bound}) bound mismatch"
        );
    }
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
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
    let ft = module
        .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
        .expect("Module::add_func_type: test fixture");
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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
        origin: None,
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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
        origin: None,
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
    let loaded = fb.load(pair_ty.clone(), slot);
    let loaded_x = fb.extract_field(Ty::U32, loaded, 0);
    let loaded_flag = fb.extract_field(Ty::Bool, loaded, 1);
    fb.add_block_param(exit, Ty::U32);
    fb.add_block_param(exit, Ty::Bool);
    fb.br(exit, vec![loaded_x, loaded_flag]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_legacy_source_ub_is_refused(
        &original,
        trust_ir::value::FuncId::new(0),
        vec![legacy_unwritten_pair(pair_ty)],
    );
    let (module, fields) = initialized_pair_entry_twin(&original, trust_ir::value::FuncId::new(0));
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

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
        matches!(transition_args[0].value(), ExprValue::Var { name } if name == &format!("bb0_v{}", fields[0][0].index())),
        "loaded struct field 0 should preserve the stored aggregate field"
    );
    assert!(
        matches!(transition_args[1].value(), ExprValue::Var { name } if name == &format!("bb0_v{}", fields[0][1].index())),
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

/// Trust (2026-09-14): a DIRECT SELF-call whose function passes the inductive-
/// hypothesis fence (pointer-free scalar signature, frame-local body, no entry
/// precondition) is modeled by the INDUCTIVE HYPOTHESIS: results havoc'd, NO
/// error rule, one `inductive_hypothesis_sites` row and no fail-closed
/// diagnostic. This flips the pre-2026-09-14 pin that every self-call fails
/// closed; the fence negatives below keep that old behaviour for everything the
/// fence refuses.
#[test]
fn typed_chc_translation_models_direct_self_call_by_inductive_hypothesis() {
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "no fail-closed diagnostic: {:?}", output.diagnostics);
    assert_eq!(output.inductive_hypothesis_sites.len(), 1);
    let site = &output.inductive_hypothesis_sites[0];
    assert_eq!(site.family, SemanticsFamily::Calls);
    assert_eq!(site.reason, TrustIrChcUnsupportedReason::RecursiveSelfCallInductiveHypothesis);
    assert_eq!(site.function, "countdown_recursive_chc");
    assert_eq!(site.block, entry);
    assert_eq!(site.instruction_index, 0);
    assert_eq!(site.result_values, vec![call_result]);
    assert!(
        !output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "a self-call modeled by the inductive hypothesis contributes NO error rule"
    );
}

/// The fence's negatives keep the historical fail-closed handling VERBATIM: a
/// pointer parameter, a pointer result, a mutual 2-cycle, a global address in the
/// body, a store through a non-frame pointer, and an entry `Assume` the evaluator
/// cannot re-instantiate. Each still carries the `RecursiveDirectCall` diagnostic
/// (or the mutual half's) and an `error` rule.
fn self_call_module(params: Vec<Ty>, returns: Vec<Ty>, shape: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_self_call_fence");
    let ft = mb.add_func_type(params.clone(), returns.clone());
    if shape == "global" {
        mb.add_global(trust_ir::Global {
            name: "G".to_string(),
            ty: Ty::U32,
            mutable: false,
            initializer: Some(trust_ir::constant::Constant::Int(7)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
    }
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let mut args = Vec::new();
    for ty in &params {
        args.push(fb.add_block_param(entry, ty.clone()));
    }
    match shape {
        "global" => {
            let g = fb.global_addr(trust_ir::value::GlobalId::new(0));
            let _ = fb.load(Ty::U32, g);
        }
        "wild_store" => {
            let p = fb.undef(Ty::Ptr);
            let v = fb.iconst(Ty::U32, 1);
            fb.store(Ty::U32, p, v);
        }
        "frame_store" => {
            let cell = fb.alloca(Ty::U32);
            let v = fb.iconst(Ty::U32, 1);
            fb.store(Ty::U32, cell, v);
        }
        "complete_aggregate_frame_store" | "complete_aggregate_wild_store" => {
            let ty = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
            let flag = fb.bool_const(true);
            let aggregate = fb.make_aggregate(ty.clone(), vec![args[0], flag]);
            let pointer = if shape == "complete_aggregate_frame_store" {
                fb.alloca(ty.clone())
            } else {
                fb.null_ptr()
            };
            fb.store(ty, pointer, aggregate);
        }
        "opaque_assume" => {
            // An entry Assume whose condition depends on a parameter through an
            // ADD — a shape the re-instantiation evaluator does not model.
            let one = fb.iconst(Ty::U32, 1);
            let t = fb.binop(BinOp::Add, Ty::U32, args[0], one);
            let c = fb.icmp(ICmpOp::Ugt, Ty::U32, t, one);
            fb.assume(c);
        }
        _ => {}
    }
    let result = fb.call(trust_ir::value::FuncId::new(0), args);
    if returns.is_empty() {
        fb.ret(vec![]);
    } else {
        fb.ret(vec![result]);
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn assert_self_call_fails_closed(module: &trust_ir::Module, why: &str) {
    let outputs = trust_ir_to_chc_translation_outputs(module, &TranslateOptions::default());
    let output = &outputs[0];
    assert!(output.inductive_hypothesis_sites.is_empty(), "{why}: no IH site may be admitted");
    assert!(
        output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall),
        "{why}: the historical RecursiveDirectCall diagnostic must stand, got {:?}",
        output.diagnostics
    );
    assert!(
        output.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "{why}: the unconditional error rule must stand"
    );
}

#[test]
fn self_call_inductive_hypothesis_fence_refuses_pointer_params_and_results() {
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::Ptr], vec![Ty::U32], "plain"),
        "pointer parameter",
    );
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::U32], vec![Ty::Ptr], "plain"),
        "pointer result",
    );
}

#[test]
fn self_call_inductive_hypothesis_fence_refuses_non_frame_local_bodies() {
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "global"),
        "global address",
    );
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "wild_store"),
        "store through a non-frame pointer",
    );
    // A store through the function's OWN alloca is frame-local and admitted.
    let outputs = trust_ir_to_chc_translation_outputs(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "frame_store"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs[0].inductive_hypothesis_sites.len(), 1, "a frame-local store is admitted");
}

#[test]
fn complete_aggregate_construction_does_not_hide_non_frame_writes_from_self_call_fence() {
    let complete = self_call_module(vec![Ty::U32], vec![Ty::U32], "complete_aggregate_frame_store");
    let output = trust_ir_to_chc_translation_outputs(&complete, &TranslateOptions::default());
    assert_eq!(output[0].inductive_hypothesis_sites.len(), 1);
    assert!(output[0].diagnostics.is_empty(), "{:?}", output[0].diagnostics);
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "complete_aggregate_wild_store"),
        "a pure complete constructor cannot authorize a store outside the frame",
    );
}

#[test]
fn self_call_inductive_hypothesis_fence_refuses_an_unmodeled_entry_assume() {
    assert_self_call_fails_closed(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "opaque_assume"),
        "entry assume over an arithmetic shape",
    );
}

#[test]
fn self_call_inductive_hypothesis_leaves_mutual_recursion_fail_closed() {
    let mut mb = ModuleBuilder::new("test_mutual_recursion");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    for (name, other) in [("ping", 1u32), ("pong", 0u32)] {
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let input = fb.add_block_param(entry, Ty::U32);
        let r = fb.call(trust_ir::value::FuncId::new(other), vec![input]);
        fb.ret(vec![r]);
        fb.build();
    }
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    for output in &outputs {
        assert!(
            output.inductive_hypothesis_sites.is_empty(),
            "mutual recursion is not the self-call arm"
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|d| d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall),
            "mutual recursion keeps the fail-closed diagnostic: {:?}",
            output.diagnostics
        );
    }
}

/// The OTHER half of the Hoare rule: every entry `Assume` (the bridge's spelling
/// of `requires`) is RE-ASSERTED over the actuals at the self-call. `f(n)`
/// requires `n > 0` and calls `f(n - 1)`: the VC gains an error rule reachable
/// exactly when `n - 1 > 0` is false on the path — the deeper activation's
/// input must satisfy the precondition, or the aggregate is not proved. A
/// `requires n == 0` body that calls `f(1)` (the "requires laundering" attack)
/// therefore carries an error rule whose condition is `not(1 == 0)` — true —
/// so the aggregate refutes instead of proving under the hypothesis.
#[test]
fn self_call_inductive_hypothesis_reasserts_entry_preconditions_over_the_actuals() {
    let build = |launder: bool| {
        let mut mb = ModuleBuilder::new("test_self_call_precondition");
        let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let n = fb.add_block_param(entry, Ty::U32);
        let zero = fb.iconst(Ty::U32, 0);
        let one = fb.iconst(Ty::U32, 1);
        let pre = if launder {
            fb.icmp(ICmpOp::Eq, Ty::U32, n, zero)
        } else {
            fb.icmp(ICmpOp::Ugt, Ty::U32, n, zero)
        };
        fb.assume(pre);
        let actual = if launder { one } else { fb.binop(BinOp::Sub, Ty::U32, n, one) };
        let r = fb.call(trust_ir::value::FuncId::new(0), vec![actual]);
        fb.ret(vec![r]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    for launder in [false, true] {
        let outputs =
            trust_ir_to_chc_translation_outputs(&build(launder), &TranslateOptions::default());
        let output = &outputs[0];
        assert!(output.diagnostics.is_empty(), "launder={launder}: no fail-closed diagnostic");
        assert_eq!(output.inductive_hypothesis_sites.len(), 1, "launder={launder}");
        let error_rules: Vec<String> = output
            .vc
            .rules
            .iter()
            .filter(|rule| rule.head.name == "error")
            .map(|rule| format!("{rule:?}"))
            .collect();
        eprintln!("launder={launder} error rules: {error_rules:#?}");
        // The `Debug` rendering wraps every operand in `Expr { sort: …, value: … }`,
        // so the shape checks are on operator presence within ONE rule.
        if launder {
            // `f(1)` under `requires n == 0`: the re-asserted precondition over the
            // actual is `1 == 0`; its negation (or its constant folding) is an error
            // rule reachable on every path that satisfies the entry assume.
            assert!(
                error_rules.iter().any(|r| {
                    r.contains("Not(")
                        && (r.contains("value: 1, width: 32") || r.contains("Bool(true)"))
                }),
                "launder: the re-asserted `1 == 0` must be an error rule, got {error_rules:#?}"
            );
        } else {
            // `f(n - 1)` under `requires n > 0`: the re-asserted precondition is
            // `n - 1 > 0`; its negation is an error rule beside the translator's own
            // underflow obligation on `n - 1`.
            assert!(
                error_rules
                    .iter()
                    .any(|r| r.contains("Not(") && r.contains("BvUGt(") && r.contains("BvSub(")),
                "the re-asserted `n - 1 > 0` must be an error rule, got {error_rules:#?}"
            );
        }
    }
}

/// The shape the BRIDGE actually emits (measured 2026-09-14 on
/// `tests/ui/trust/native_recursive_requires_fresh_context.rs`): the entry
/// block carries the `requires` assume and the parameter's range assume, both
/// spelled over entry-block CONSTANTS, and the self-call sits in a NON-ENTRY
/// block behind the recursion guard, with the actual computed by a checked
/// subtraction. `translate_block` clears the value map at every block, so an
/// evaluator that looked the constants up there missed every one of them and
/// the fence fell through to the historical error rule — this is the
/// regression test for that miss. The census must name the fence point when a
/// miss does happen, so the negative half checks the reason string too.
#[test]
fn self_call_in_a_non_entry_block_reinstantiates_entry_constants() {
    let mut mb = ModuleBuilder::new("test_self_call_non_entry_block");
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("recursive_requires", ft);
    let entry = fb.create_block();
    let recurse = fb.create_block();
    let done = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U32);
    // requires n > 0
    let zero = fb.iconst(Ty::U32, 0);
    let pre = fb.icmp(ICmpOp::Ugt, Ty::U32, n, zero);
    fb.assume(pre);
    // the parameter range assume, as the bridge spells it: select(n >= 0, n <= MAX, false)
    let zero2 = fb.iconst(Ty::U32, 0);
    let ge = fb.icmp(ICmpOp::Uge, Ty::U32, n, zero2);
    let max = fb.iconst(Ty::U32, u32::MAX as i128);
    let le = fb.icmp(ICmpOp::Ule, Ty::U32, n, max);
    let ff = fb.bool_const(false);
    let range = fb.select(Ty::Bool, ge, le, ff);
    fb.assume(range);
    // if n > 1 { recurse } else { done }
    let one = fb.iconst(Ty::U32, 1);
    let guard = fb.icmp(ICmpOp::Ugt, Ty::U32, n, one);
    fb.condbr(guard, recurse, vec![], done, vec![]);
    fb.switch_to_block(recurse);
    let one2 = fb.iconst(Ty::U32, 1);
    let (diff, _overflowed) = fb.overflow(OverflowOp::SubOverflow, Ty::U32, n, one2);
    // `call_void`: the builder's `call` mints a result even for a unit-returning
    // callee, which the arity fence (rightly) refuses.
    fb.call_void(trust_ir::value::FuncId::new(0), vec![diff]);
    fb.br(done, vec![]);
    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    let census =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &census,
    );
    let output = &outputs[0];
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall),
        "the self-call in a non-entry block must take the inductive hypothesis, got {:?}",
        output.diagnostics
    );
    assert_eq!(output.inductive_hypothesis_sites.len(), 1);
    assert!(
        output
            .call_summary_census
            .iter()
            .any(|a| a.outcome == CallSummaryOutcome::InductiveHypothesis),
        "census: {:?}",
        output.call_summary_census
    );
    // The re-asserted `requires` over the actual `n - 1`: an error rule on its negation.
    let error_rules: Vec<String> = output
        .vc
        .rules
        .iter()
        .filter(|rule| rule.head.name == "error")
        .map(|rule| format!("{rule:?}"))
        .collect();
    assert!(
        error_rules
            .iter()
            .any(|r| r.contains("Not(") && r.contains("BvUGt(") && r.contains("BvSub(")),
        "the re-asserted `n - 1 > 0` must be an error rule, got {error_rules:#?}"
    );
}

/// A fence miss is NAMED in the census: the `opaque_assume` shape (an entry
/// assume over an arithmetic the evaluator does not model) records
/// `ih_fence:entry_assume_unmodeled`, not the bare historical reason.
#[test]
fn self_call_inductive_hypothesis_fence_miss_is_named_in_the_census() {
    let census =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let outputs = trust_ir_to_chc_translation_outputs(
        &self_call_module(vec![Ty::U32], vec![Ty::U32], "opaque_assume"),
        &census,
    );
    let reasons: Vec<&str> = outputs[0]
        .call_summary_census
        .iter()
        .filter_map(|a| match &a.outcome {
            CallSummaryOutcome::NotAttempted { reason } => Some(*reason),
            _ => None,
        })
        .collect();
    assert_eq!(
        reasons,
        vec!["ih_fence:entry_assume_unmodeled"],
        "{:?}",
        outputs[0].call_summary_census
    );
    let outputs = trust_ir_to_chc_translation_outputs(
        &self_call_module(vec![Ty::Ptr], vec![Ty::U32], "plain"),
        &census,
    );
    let reasons: Vec<&str> = outputs[0]
        .call_summary_census
        .iter()
        .filter_map(|a| match &a.outcome {
            CallSummaryOutcome::NotAttempted { reason } => Some(*reason),
            _ => None,
        })
        .collect();
    assert_eq!(reasons, vec!["ih_fence:pointer_or_non_scalar_signature"]);
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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
    mb.add_global(trust_ir::Global {
        name: "defined_global".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(trust_ir::Constant::Int(0)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("heap_global_chc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let heap = fb.heap_alloc(Ty::I32, None, None, trust_ir::inst::AllocOrigin::RustHeap);
    let _global = fb.global_addr(trust_ir::value::GlobalId::new(0));
    fb.ret(vec![heap]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
fn typed_chc_translation_refuses_legacy_aggregate_undef_nested_wrapper() {
    nested_wrapper_summary(false, false);
}

#[test]
fn make_aggregate_summarizes_nested_wrapper_without_dropping_panic() {
    nested_wrapper_summary(true, true);
}

#[test]
fn initialized_insert_field_summarizes_nested_wrapper_without_dropping_panic() {
    nested_wrapper_summary(false, true);
}

fn nested_wrapper_summary(complete: bool, initialized_seed: bool) {
    // The operative `proc_macro2::Literal { inner: imp::Literal, _marker }` shape: a
    // callee that CONSTRUCTS a wrapper whose field is itself an aggregate, then reads
    // that field back out. BEFORE nested-aggregate field support in the call-summary
    // interpreter, `Inst::InsertField` bailed on the first non-scalar `value_ty` and
    // `Inst::ExtractField` bailed on a non-scalar result ty, so EVERY ordinary
    // newtype/wrapper constructor declined (UnsupportedDirectCallSummary) and its
    // caller was conservatively modeled as an unconditional may-panic. Both arms now
    // splice the nested `ValueBinding::Aggregate` that `resolve_field_binding` /
    // `fresh_call_summary_value` already build, so the callee summarizes and its
    // underflow obligation propagates as a GUARDED caller error rule — a real
    // underflow still refutes (no false PROVE), and the obligation is not deleted.
    let mut mb = ModuleBuilder::new("test_direct_call_nested_wrapper_chc");

    let inner_id = StructId::new(0);
    let inner_ty = Ty::Struct(inner_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: inner_id,
        name: "Inner".to_owned(),
        fields: vec![FieldDef { name: "v".to_owned(), ty: Ty::U32, offset: None }],
        size: None,
        align: None,
        origin: None,
    });

    let outer_id = StructId::new(1);
    let outer_ty = Ty::Struct(outer_id);
    mb.add_struct(StructDef {
        repr: Default::default(),
        id: outer_id,
        name: "Outer".to_owned(),
        fields: vec![
            FieldDef { name: "inner".to_owned(), ty: inner_ty.clone(), offset: None },
            FieldDef { name: "tag".to_owned(), ty: Ty::U32, offset: None },
        ],
        size: None,
        align: None,
        origin: None,
    });

    let callee_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32], vec![]);

    // callee wrap_dec(n): `Outer { inner: Inner { v: n }, tag: 0 }.inner.v - 1`, with
    // the underflow branching to an `Unreachable` panic block.
    let mut fb = mb.function("wrap_dec_chc", callee_ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U32);

    let zero = fb.iconst(Ty::U32, 0);
    let inner = if complete {
        fb.make_aggregate(inner_ty.clone(), vec![n])
    } else {
        let seed = if initialized_seed {
            fb.const_value(
                inner_ty.clone(),
                trust_ir::constant::Constant::Aggregate(vec![trust_ir::constant::Constant::Uninit]),
            )
        } else {
            fb.undef(inner_ty.clone())
        };
        fb.insert_field(inner_ty.clone(), seed, 0, n)
    };
    let outer = if complete {
        fb.make_aggregate(outer_ty.clone(), vec![inner, zero])
    } else {
        let seed = if initialized_seed {
            fb.const_value(
                outer_ty.clone(),
                trust_ir::constant::Constant::Aggregate(vec![
                    trust_ir::constant::Constant::Uninit;
                    2
                ]),
            )
        } else {
            fb.undef(outer_ty.clone())
        };
        let with_inner = fb.insert_field(outer_ty.clone(), seed, 0, inner);
        fb.insert_field(outer_ty.clone(), with_inner, 1, zero)
    };
    // The nested-aggregate RESULT extract — the mirror arm that used to bail.
    let read_inner = fb.extract_field(inner_ty.clone(), outer, 0);
    let v = fb.extract_field(Ty::U32, read_inner, 0);

    let one = fb.iconst(Ty::U32, 1);
    let (value, flag) = fb.overflow(OverflowOp::SubOverflow, Ty::U32, v, one);
    fb.condbr(flag, panic, vec![], ok, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![value]);
    fb.switch_to_block(panic);
    fb.unreachable();
    fb.build();

    // caller(n): `wrap_dec(n); ret` — forwards an unconstrained n.
    let mut fb = mb.function("caller_of_wrap_dec_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_n = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_n]);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    if !complete && !initialized_seed {
        for function in [0, 1] {
            assert_legacy_source_ub_is_refused(
                &module,
                trust_ir::value::FuncId::new(function),
                vec![trust_ir::interpret::InterpretValue::int(Ty::U32, 2).unwrap()],
            );
        }
        return;
    }
    for n in [0, 2] {
        let run = trust_ir::interpret::Interpreter::with_module(&module).execute_func(
            trust_ir::value::FuncId::new(1),
            [trust_ir::interpret::InterpretValue::int(Ty::U32, n).unwrap()],
        );
        if n == 0 {
            let error = run.unwrap_err();
            assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::UndefinedBehavior);
            assert_eq!(error.message, "executed unreachable");
        } else {
            run.unwrap();
        }
    }
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "a callee CONSTRUCTING and re-reading a nested wrapper aggregate must summarize \
         cleanly (no UnsupportedDirectCallSummary), got {:?}",
        caller.diagnostics
    );
    // The obligation must SURVIVE the widening: the callee's underflow still reaches
    // the caller as an error rule. An obligation that DISAPPEARS is not one that
    // proved, so this pins presence, and the guard pins that it is not vacuous.
    let error_rule = caller
        .vc
        .rules
        .iter()
        .find(|rule| rule.head.name == "error")
        .expect("the wrapped checked-sub underflow must propagate as a caller error rule");
    assert!(
        error_rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0")
            && format!("{:?}", error_rule.body.constraints).contains("bb0_v0"),
        "the panic must be GUARDED by the forwarded argument (reachable iff it \
         underflows), not unconditional; constraints: {:?}",
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
    // A missing terminator may hide a dropped panic edge. Canonical preflight
    // refuses the whole module rather than summarizing the leaf as a return.
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

    assert_canonical_refusal(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "has no terminator instruction",
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

    let outputs = trust_ir_to_chc_translation_outputs_per_block(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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
fn typed_chc_translation_summarizes_seeded_merge_value_return() {
    // Explicit block arguments preserve each path's value at the merge.
    let mut mb = ModuleBuilder::new("test_seeded_merge_value_return_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool], vec![]);

    let mut fb = mb.function("guarded_value_chc", callee_ft);
    let entry = fb.create_block();
    let then_b = fb.create_block();
    let else_b = fb.create_block();
    let merge = fb.create_block();
    let merged = fb.add_block_param(merge, Ty::U32);
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    fb.condbr(cond, then_b, vec![], else_b, vec![]);
    fb.switch_to_block(then_b);
    let then_val = fb.iconst(Ty::U32, 7);
    fb.br(merge, vec![then_val]);
    fb.switch_to_block(else_b);
    let else_val = fb.iconst(Ty::U32, 9);
    fb.br(merge, vec![else_val]);
    fb.switch_to_block(merge);
    fb.ret(vec![merged]);
    fb.build();

    let mut fb = mb.function("caller_discards_value_chc", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let caller_cond = fb.add_block_param(entry, Ty::Bool);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![caller_cond]);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_no_module_refusal(&outputs);
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "seeded-merge value return must summarize without unsupported diagnostics, got {:?}",
        caller.diagnostics
    );
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "a non-panicking callee returned through a seeded merge must not inject a spurious error rule"
    );
}

#[test]
fn typed_chc_translation_seeded_merge_preserves_branch_panic() {
    // Explicit block arguments preserve each path's value at the merge.
    let mut mb = ModuleBuilder::new("test_seeded_merge_panic_chc");
    let callee_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::Bool, Ty::U32, Ty::U32], vec![]);

    let mut fb = mb.function("maybe_subtracts_chc", callee_ft);
    let entry = fb.create_block();
    let safe_b = fb.create_block();
    let sub_b = fb.create_block();
    let merge = fb.create_block();
    let merged = fb.add_block_param(merge, Ty::U32);
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let x = fb.add_block_param(entry, Ty::U32);
    let y = fb.add_block_param(entry, Ty::U32);
    fb.condbr(cond, safe_b, vec![], sub_b, vec![]);
    fb.switch_to_block(safe_b);
    let safe = fb.iconst(Ty::U32, 0);
    fb.br(merge, vec![safe]);
    fb.switch_to_block(sub_b);
    let diff = fb.sub(Ty::U32, x, y); // unsigned underflow obligation when x < y
    fb.br(merge, vec![diff]);
    fb.switch_to_block(merge);
    fb.ret(vec![merged]);
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_no_module_refusal(&outputs);
    assert_eq!(outputs.len(), 2);
    let caller = &outputs[1];
    assert!(
        caller.diagnostics.is_empty(),
        "subtraction through a seeded merge should summarize without unsupported diagnostics, got {:?}",
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
        origin: None,
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

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_legacy_source_ub_is_refused(
        &original,
        trust_ir::value::FuncId::new(1),
        vec![
            legacy_unwritten_pair(pair_ty),
            trust_ir::interpret::InterpretValue::int(Ty::U32, 7).unwrap(),
        ],
    );
    let (module, fields) = initialized_pair_entry_twin(&original, trust_ir::value::FuncId::new(1));
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

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
        matches!(transition_args[1].value(), ExprValue::Var { name } if name == &format!("bb0_v{}", fields[0][1].index())),
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
        origin: None,
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
    let caller_rhs = fb.add_block_param(entry, pair_ty.clone());
    let call_result =
        fb.call(trust_ir::value::FuncId::new(0), vec![caller_choose_lhs, caller_lhs, caller_rhs]);
    let result_x = fb.extract_field(Ty::U32, call_result, 0);
    fb.add_block_param(exit, Ty::U32);
    fb.br(exit, vec![result_x]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_legacy_source_ub_is_refused(
        &original,
        trust_ir::value::FuncId::new(1),
        vec![
            trust_ir::interpret::InterpretValue::bool(true),
            legacy_unwritten_pair(pair_ty.clone()),
            legacy_unwritten_pair(pair_ty),
        ],
    );
    let (module, fields) = initialized_pair_entry_twin(&original, trust_ir::value::FuncId::new(1));
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());

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
        matches!(then_expr.value(), ExprValue::Var { name } if name == &format!("bb0_v{}", fields[0][0].index())),
        "then aggregate field should come from the caller lhs"
    );
    assert!(
        matches!(else_expr.value(), ExprValue::Var { name } if name == &format!("bb0_v{}", fields[1][0].index())),
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
    let build = |initialized: bool| {
        let mut mb = ModuleBuilder::new("test_nested_aggregate_stack_memory_chc");
        let inner = Ty::Tuple(vec![Ty::U32]);
        let nested_ty = Ty::Tuple(vec![inner.clone()]);
        let ft = mb.add_func_type(if initialized { vec![Ty::U32] } else { vec![] }, vec![]);
        let mut fb = mb.function("nested_aggregate_stack_memory_chc", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let initial = initialized.then(|| {
            let x = fb.add_block_param(entry, Ty::U32);
            let inner = fb.make_aggregate(inner, vec![x]);
            fb.make_aggregate(nested_ty.clone(), vec![inner])
        });
        let slot = fb.alloca(nested_ty.clone());
        if let Some(initial) = initial {
            fb.store(nested_ty.clone(), slot, initial);
        }
        let _loaded = fb.load(nested_ty, slot);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let original = build(false);
    assert_eq!(
        trust_ir::interpret::Interpreter::with_module(&original)
            .execute_func(trust_ir::FuncId::new(0), [])
            .unwrap_err()
            .code,
        trust_ir::interpret::InterpretErrorCode::UndefinedBehavior
    );
    for check_memory_bounds in [false, true] {
        let output = trust_ir_to_chc_translation_outputs(
            &original,
            &TranslateOptions { check_memory_bounds, ..TranslateOptions::default() },
        )
        .remove(0);
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
        );
    }
    let module = build(true);
    trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(
            trust_ir::FuncId::new(0),
            [trust_ir::interpret::InterpretValue::int(Ty::U32, 7).unwrap()],
        )
        .unwrap();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());

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
fn typed_chc_translation_models_cross_block_alloca_access_as_owned_stack() {
    // R3 (cross-block owned-stack consistency): an `Alloca` in the ENTRY block
    // whose Store/Load happen in LATER blocks — the `let r = if c { .. } else
    // { .. }` result-slot shape the bridge emits — is the SAME owned stack slot
    // in every block (SSA ids are function-unique), so the accesses must not
    // fail closed as unknown-pointer memory. The VALUE stays untracked across
    // blocks (the load below is a fresh symbolic — havoc ⊇ real), so nothing
    // becomes provable FROM the slot; only the spurious unconditional error
    // rules disappear.
    let mut mb = ModuleBuilder::new("test_cross_block_alloca_chc");
    let ft = mb.add_func_type(vec![], vec![]);

    // A STRUCT-typed slot: outside the mem2reg scalar-promotion fragment, so the
    // cross-block accesses exercise the function-scoped owned-stack seeding
    // itself (a scalar slot would be threaded precisely by promotion instead).
    let slot_ty = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
    let mut fb = mb.function("cross_block_alloca_chc", ft);
    let entry = fb.create_block();
    let mid = fb.create_block();
    let done = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let slot = fb.alloca(slot_ty.clone());
    fb.br(mid, vec![]);
    fb.switch_to_block(mid);
    let value = fb.undef(slot_ty.clone());
    fb.store(slot_ty.clone(), slot, value);
    fb.br(done, vec![]);
    fb.switch_to_block(done);
    let _loaded = fb.load(slot_ty, slot);
    fb.ret(vec![]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel),
        "cross-block accesses to the function's own alloca are owned-stack, not unknown memory: {:?}",
        output.diagnostics
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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );

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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
/// The earlier assumption makes the later assertion unreachable on false input.
#[test]
fn earlier_assumption_filters_the_later_assertion() {
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let options = TranslateOptions::default();
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have one assertion violation.
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertion_violations.len(), 1, "assert should generate one assertion violation");
    assert!(!bmc_violation_is_satisfiable(vc, assertion_violations[0]));
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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
    mb.add_global(trust_ir::Global {
        name: "defined_global".into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(trust_ir::Constant::Int(0)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let ft = mb.add_func_type(vec![], vec![Ty::Ptr]);

    let mut fb = mb.function("heap_global_bmc", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let heap = fb.heap_alloc(Ty::I32, None, None, trust_ir::inst::AllocOrigin::RustHeap);
    let _global = fb.global_addr(trust_ir::value::GlobalId::new(0));
    fb.ret(vec![heap]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_module(&module);
    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(callee_func).expect("Module::try_add_function: test fixture");

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
        kind: trust_ir::inst::AssertKind::Unspecified,
        site: None,
    }));

    caller_block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
        values: vec![trust_ir::value::ValueId::new(12)],
    }));
    caller_func.blocks.push(caller_block);
    module.try_add_function(caller_func).expect("Module::try_add_function: test fixture");

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

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(callee_func).expect("Module::try_add_function: test fixture");

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
    module.try_add_function(caller_func).expect("Module::try_add_function: test fixture");

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
fn call_to_unknown_function_refuses_module_without_symbolic_facts() {
    let mut mb = ModuleBuilder::new("test_unknown_call");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    // Build manually — reference a callee that doesn't exist.
    let _fb = mb.function("caller", ft);
    drop(_fb);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

    assert_canonical_refusal(&module, "callee function 99 not found");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
        weak: false,
    })
    .with_result(trust_ir::value::ValueId::new(3)) // value
    .with_result(trust_ir::value::ValueId::new(4)); // success flag
    block.body.push(cmpxchg_node);

    // Assert the success flag.
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Assert {
        cond: trust_ir::value::ValueId::new(4),
        kind: trust_ir::inst::AssertKind::Unspecified,
        site: None,
    }));

    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![] }));

    func.blocks.push(block);
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&module, &options);

    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    // Should have an assertion violation (cmpxchg success is not guaranteed).
    let assertion_violations: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert!(!assertion_violations.is_empty(), "cmpxchg success flag assertion should produce a VC");
}

/// `entry(x, y)`: store `x` into a fresh cell, compare-exchange the cell from
/// `x` to `y`, and assert that the exchange succeeded. The cell provably holds
/// the expected value, so only the instruction's strength decides the assertion.
/// `weak` sets the trust-ir v48 flag on the one `CmpXchg` node.
fn cmpxchg_on_a_cell_holding_expected(weak: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("test_cmpxchg_strength");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![]);
    let mut fb = mb.function("cmpxchg_strength", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::I32);
    let y = fb.add_block_param(entry, Ty::I32);
    let cell = fb.alloca(Ty::I32);
    fb.store(Ty::I32, cell, x);
    let (_old, exchanged) =
        fb.cmpxchg(Ty::I32, cell, x, y, trust_ir::Ordering::SeqCst, trust_ir::Ordering::SeqCst);
    fb.assert(exchanged);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");

    let mut flagged = 0;
    for node in module
        .functions
        .iter_mut()
        .flat_map(|function| function.blocks.iter_mut())
        .flat_map(|block| block.body.iter_mut())
    {
        if let trust_ir::Inst::CmpXchg { weak: flag, .. } = &mut node.inst {
            *flag = weak;
            flagged += 1;
        }
    }
    assert_eq!(flagged, 1, "the fixture must carry exactly one CmpXchg");
    module
}

/// The single `Assertion` violation of the one translated function.
fn only_assertion_violation(
    vc: &trust_mc_core::bmc::BmcVc,
) -> &trust_mc_core::violation::Violation {
    let assertions: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertions.len(), 1, "expected exactly one assertion violation, got {assertions:?}");
    assertions[0]
}

/// trust-ir v47 `Drop { ty, ptr }` runs drop glue whose body is not in the node.
/// Both lanes must refuse it BY NAME: treating it as a no-op would forget every
/// write and every panic the destructor can perform.
#[test]
fn test_drop_glue_fails_closed_by_name_in_both_lanes() {
    let mut mb = ModuleBuilder::new("test_drop_glue");
    let dropped = add_dropped_struct(&mut mb);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("drop_glue", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let place = fb.add_block_param(entry, Ty::Ptr);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let body = &mut module.functions[0].blocks[0].body;
    let ret = body.pop().expect("the fixture ends in its return");
    body.push(trust_ir::InstrNode::new(trust_ir::Inst::Drop { ty: dropped, ptr: place }));
    body.push(ret);

    assert_canonical_module(&module);
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let drop_rows: Vec<_> = outputs[0]
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::DropGlue)
        .collect();
    assert_eq!(drop_rows.len(), 1, "CHC must name the drop, got {:?}", outputs[0].diagnostics);
    assert_eq!(drop_rows[0].family, SemanticsFamily::Calls);
    assert!(
        outputs[0].vc.rules.iter().any(|rule| rule.head.name == "error"),
        "CHC must fail closed on drop glue with a reachable error rule"
    );

    let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("drop-glue semantics"))
        }),
        "BMC must fail closed on drop glue by name, got {:?}",
        vcs[0].violations
    );
}

/// The trust-ir instructions added between wire v53 and v56 that neither lane
/// models: the no-unwind boundary calls (v53) and the unwinding twins of
/// `Assert` (v54 `AssertInvoke`), `Drop` (v55 `DropInvoke`) and `CallIndirect`
/// (v56 `InvokeIndirect`).
#[derive(Clone, Copy, Debug)]
enum UnmodeledUnwindSurface {
    CallCannotUnwind,
    CallIndirectCannotUnwind,
    AssertInvoke,
    DropInvoke,
    InvokeIndirect,
}

/// `unwind_surface(p: Ptr, c: Bool)` whose entry block holds `surface`: a
/// non-terminating call before the entry's `ret`, or a terminator whose normal
/// edge returns and whose unwind edge enters a cleanup landing pad that resumes.
fn unmodeled_unwind_surface_module(surface: UnmodeledUnwindSurface) -> trust_ir::Module {
    use trust_ir::{AssertKind, CallingConv, Inst, InstrNode, PanicLocation, PanicSite};

    let mut mb = ModuleBuilder::new("test_unmodeled_unwind_surface");
    let dropped = add_dropped_struct(&mut mb);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Bool], vec![]);
    let callee = mb.declare_function("callee", ft);
    let panic_ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let panic_entry = mb.declare_function("panic_entry", panic_ft);
    let mut fb = mb.function("unwind_surface", ft);
    let entry = fb.create_block();
    let normal = fb.create_block();
    let pad = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let site = PanicSite { entry: panic_entry, location: PanicLocation::Value(ptr) };
    let call = match surface {
        UnmodeledUnwindSurface::CallCannotUnwind => {
            Some(Inst::CallCannotUnwind { callee, args: vec![ptr, cond] })
        }
        UnmodeledUnwindSurface::CallIndirectCannotUnwind => Some(Inst::CallIndirectCannotUnwind {
            callee: ptr,
            sig: ft,
            args: vec![ptr, cond],
            calling_conv: CallingConv::default(),
        }),
        UnmodeledUnwindSurface::AssertInvoke => {
            fb.assert_invoke(cond, AssertKind::Unspecified, site, normal, vec![], pad);
            None
        }
        UnmodeledUnwindSurface::DropInvoke => {
            fb.drop_invoke(dropped, ptr, normal, vec![], pad);
            None
        }
        UnmodeledUnwindSurface::InvokeIndirect => {
            fb.invoke_indirect_void(ptr, ft, vec![ptr, cond], normal, vec![], pad);
            None
        }
    };
    if call.is_some() {
        fb.ret(vec![]);
    }
    if call.is_none() {
        fb.switch_to_block(normal);
        fb.ret(vec![]);
        fb.switch_to_block(pad);
        let (exn, _selector) = fb.landingpad(true, vec![]);
        fb.resume(exn);
    }
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(fixture_target());
    if call.is_some() {
        module
            .functions
            .iter_mut()
            .find(|function| function.name == "unwind_surface")
            .unwrap()
            .blocks
            .retain(|block| block.id == entry);
    }
    if let Some(call) = call {
        let function = module
            .functions
            .iter_mut()
            .find(|function| function.name == "unwind_surface")
            .expect("the fixture defines unwind_surface");
        let body = &mut function.blocks[0].body;
        let ret = body.pop().expect("the call fixture's entry ends in its return");
        body.push(InstrNode::new(call));
        body.push(ret);
    }
    assert_canonical_module(&module);
    module
}

/// Every surface must refuse in both lanes. CHC names the instruction;
/// BMC rejects EH terminators at its earlier unsupported-CFG boundary and
/// names the two ordinary calls. Neither boundary can decide obligations
/// through unmodeled dispatch, glue or unwind edges.
#[test]
fn test_unwind_surfaces_fail_closed_at_each_lane_boundary() {
    let cases = [
        (
            UnmodeledUnwindSurface::CallCannotUnwind,
            TrustIrChcUnsupportedReason::NoUnwindCallBoundary,
            SemanticsFamily::Calls,
            "direct call with a no-unwind boundary",
        ),
        (
            UnmodeledUnwindSurface::CallIndirectCannotUnwind,
            TrustIrChcUnsupportedReason::NoUnwindCallBoundary,
            SemanticsFamily::Calls,
            "indirect call dispatch with a no-unwind boundary",
        ),
        (
            UnmodeledUnwindSurface::AssertInvoke,
            TrustIrChcUnsupportedReason::UnwindingCheck,
            SemanticsFamily::ControlFlow,
            "path-sensitive control flow (cyclic or structurally unsupported CFG)",
        ),
        (
            UnmodeledUnwindSurface::DropInvoke,
            TrustIrChcUnsupportedReason::DropGlue,
            SemanticsFamily::Calls,
            "path-sensitive control flow (cyclic or structurally unsupported CFG)",
        ),
        (
            UnmodeledUnwindSurface::InvokeIndirect,
            TrustIrChcUnsupportedReason::IndirectCall,
            SemanticsFamily::Calls,
            "path-sensitive control flow (cyclic or structurally unsupported CFG)",
        ),
    ];
    for (surface, reason, family, bmc_name) in cases {
        let module = unmodeled_unwind_surface_module(surface);
        let index = module
            .functions
            .iter()
            .position(|function| function.name == "unwind_surface")
            .expect("the fixture defines unwind_surface");
        let function = &module.functions[index];

        let output = trust_ir_function_to_chc_translation_output(
            &module,
            function.id,
            &TranslateOptions::default(),
        )
        .expect("CHC translates unwind_surface");
        let rows: Vec<_> =
            output.diagnostics.iter().filter(|diagnostic| diagnostic.reason == reason).collect();
        assert_eq!(rows.len(), 1, "{surface:?}: CHC must name it, got {:?}", output.diagnostics);
        assert_eq!(rows[0].family, family, "{surface:?}");
        assert_eq!(rows[0].block, function.entry, "{surface:?}");
        assert!(
            output.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "{surface:?}: CHC must fail closed with a reachable error rule"
        );

        // One VC per module function, in module order.
        let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
        let vc = &vcs[index];
        assert!(
            vc.violations.iter().any(|violation| {
                violation.kind == PropertyKind::Other
                    && violation
                        .message
                        .as_deref()
                        .is_some_and(|message| message.contains(bmc_name))
            }),
            "{surface:?}: BMC must name its actual refusal boundary, got {:?}",
            vc.violations
        );
    }
}

/// `Constant::Uninit` (trust-ir v49) is an unwritten lane, never a value: as a
/// whole constant it has no bits, so `const_to_expr` must refuse it rather than
/// invent a placeholder.
#[test]
fn test_const_to_expr_refuses_a_whole_uninit_constant() {
    use trust_ir::constant::Constant;
    assert!(const_to_expr(&Ty::I32, &Constant::Uninit).is_none());
    // CONTROL: the aggregate that legitimately carries an unwritten lane keeps
    // the opaque placeholder every aggregate constant gets.
    let with_lane = Constant::Aggregate(vec![Constant::Int(0), Constant::Uninit]);
    assert!(const_to_expr(&Ty::Tuple(vec![Ty::I32, Ty::I32]), &with_lane).is_some());
}

/// CONTROL: a STRONG compare-exchange on a cell that holds the expected value
/// always succeeds, so the assertion on its success flag is unreachable.
#[test]
fn test_cmpxchg_strong_on_cell_holding_expected_always_succeeds() {
    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&cmpxchg_on_a_cell_holding_expected(false), &options);
    assert_eq!(vcs.len(), 1);
    assert!(
        !bmc_violation_is_satisfiable(&vcs[0], only_assertion_violation(&vcs[0])),
        "a strong compare-exchange of a cell holding `expected` must succeed"
    );
}

/// A WEAK compare-exchange (trust-ir v48) may fail spuriously even when the
/// comparison holds, so the same assertion is refutable. Modeling the weak
/// instruction as the strong one would PROVE this assertion, which is false for
/// `compare_exchange_weak`.
#[test]
fn test_cmpxchg_weak_on_cell_holding_expected_may_fail_spuriously() {
    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let vcs = trust_ir_to_bmc_vc(&cmpxchg_on_a_cell_holding_expected(true), &options);
    assert_eq!(vcs.len(), 1);
    assert!(
        bmc_violation_is_satisfiable(&vcs[0], only_assertion_violation(&vcs[0])),
        "a weak compare-exchange may fail spuriously; asserting its success must be refutable"
    );
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");

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

    mb.build().expect("ModuleBuilder::build: test fixture")
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

    mb.build().expect("ModuleBuilder::build: test fixture")
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

    mb.build().expect("ModuleBuilder::build: test fixture")
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

    mb.build().expect("ModuleBuilder::build: test fixture")
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

    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
    let vcs = trust_ir_to_bmc_vc(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
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
    let module = single_float_cmp_module(|fb, lhs, rhs| fb.icmp(ICmpOp::Eq, Ty::F64, lhs, rhs));
    assert_canonical_refusal(&module, "icmp requires integer or pointer type, got f64");
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
    let module = single_float_cmp_module(build_cmp);
    assert_canonical_module(&module);
    let mut vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    vcs.pop().expect("one VC")
}

fn single_float_cmp_module(
    build_cmp: impl FnOnce(
        &mut trust_ir_build::FunctionBuilder,
        trust_ir::value::ValueId,
        trust_ir::value::ValueId,
    ) -> trust_ir::value::ValueId,
) -> trust_ir::Module {
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
    mb.build().expect("ModuleBuilder::build: test fixture")
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
    let module = mb.build().expect("ModuleBuilder::build: test fixture");

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
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
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
    module.try_add_function(func).expect("Module::try_add_function: test fixture");
    module
}

// ---------------------------------------------------------------------------
// `InsertElement` (array element WRITE) modeling, read back with `ExtractElement`.
//
// Arrays are SMT arrays (`translate_chc::ArrayValue`): a write is `store` and a
// read is `select`, exact at a constant and at a symbolic index, each access with
// its own in-bounds obligation. The shape that motivated the write arm is the
// `[core::fmt::rt::Argument; N]` array that every `format!`/`write!` builds: one
// `InsertElement` at a CONSTANT index per format argument (see
// `tests/format_args_insert_element_modeling.rs`, which runs on a verbatim
// `-Ztrust-dump=native-bundle` artifact). These fixtures read the lane back with
// `ExtractElement` — the only valid read of an array lane (TrustIR refuses
// `ExtractField` on an array).
// ---------------------------------------------------------------------------

/// How many `error`-head rules are UNCONDITIONALLY reachable — every constraint
/// folds to the constant `true`. A rule that stays symbolic is counted neither
/// way, so this distinguishes "modeled exactly" from "havoced" from "stale".
fn unconditionally_reachable_error_rules(vc: &trust_mc_core::chc::ChcVc) -> usize {
    vc.rules
        .iter()
        .filter(|rule| rule.head.name.as_str() == "error")
        .filter(|rule| {
            rule.body
                .constraints
                .iter()
                .all(|c| trust_mc_core::chc_const_prop::eval::try_eval_to_bool(c) == Some(true))
        })
        .count()
}

fn aggregate_update_diagnostics(output: &ChcTranslationOutput) -> usize {
    output
        .diagnostics
        .iter()
        .filter(|d| d.reason == TrustIrChcUnsupportedReason::AggregateUpdate)
        .count()
}

/// Keep the original hand-built source as a negative, rather than treating
/// aggregate Undef or an inspected unwritten scalar as initialized havoc.
fn assert_legacy_source_ub_is_refused(
    module: &trust_ir::Module,
    function: trust_ir::value::FuncId,
    args: Vec<trust_ir::interpret::InterpretValue>,
) {
    // The two constant-index UB fixtures intentionally exercise unchecked IR:
    // retain their exact static bounds refusals, with no other invalid shape.
    let validation = trust_ir_build::validate_module(module);
    assert!(
        validation.iter().all(|error| matches!(
            error,
            trust_ir_build::ValidationError::InvalidVectorElementOp { op, reason, .. }
                if op == "insert_element" && matches!(reason.as_str(),
                    "constant lane index 4 is out of range for 4 lanes"
                    | "constant lane index -1 is out of range for 256 lanes")
        )),
        "{validation:?}"
    );
    if !validation.is_empty() {
        assert_canonical_refusal(module, "invalid insert_element");
    }
    let error = trust_ir::interpret::Interpreter::with_module(module)
        .execute_func(function, args)
        .unwrap_err();
    assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::UndefinedBehavior, "{error:?}");
    for check_memory_bounds in [false, true] {
        let output = trust_ir_function_to_chc_translation_output(
            module,
            function,
            &TranslateOptions { check_memory_bounds, ..TranslateOptions::default() },
        )
        .expect("the original fixture retains an observable refusal");
        if !validation.is_empty() {
            assert_chc_canonical_refusal(&output, "invalid insert_element");
        } else {
            assert!(
                output.diagnostics.iter().any(|diagnostic| matches!(
                    diagnostic.reason,
                    TrustIrChcUnsupportedReason::OperandConsumption
                        | TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
                )),
                "{check_memory_bounds}: {:?}",
                output.diagnostics
            );
        }
        // Guards (including Boolean parameter domains) need not constant-fold.
        // The maintained solver helper requires actual SAT/UNSAT answers;
        // `None` means both the condition and its negation are SAT, not unknown.
        assert!(error_rule_solver_verdicts(&output.vc).iter().any(|result| *result != Some(false)));
    }
}

fn legacy_unwritten_pair(ty: Ty) -> trust_ir::interpret::InterpretValue {
    use trust_ir::interpret::{InterpretValue, InterpretValueKind};
    InterpretValue {
        ty,
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue { ty: Ty::U32, kind: InterpretValueKind::Uninit },
            InterpretValue { ty: Ty::Bool, kind: InterpretValueKind::Uninit },
        ]),
    }
}

/// A NEW positive with scalar entry inputs and explicit complete Pair values.
/// Preserve the selected function's original body, aggregate types, scalar
/// parameters, calls and assertions. The returned IDs identify the actual
/// independent inputs, so field-custody assertions do not accept fresh havoc.
fn initialized_pair_entry_twin(
    original: &trust_ir::Module,
    function: trust_ir::value::FuncId,
) -> (trust_ir::Module, Vec<[trust_ir::value::ValueId; 2]>) {
    let mut twin = original.clone();
    twin.name.push_str("_initialized_unknown_twin");
    let index = twin.functions.iter().position(|candidate| candidate.id == function).unwrap();
    let function = &mut twin.functions[index];
    function.name.push_str("_initialized_unknown_twin");
    let mut fresh = function
        .blocks
        .iter()
        .flat_map(|block| {
            block
                .params
                .iter()
                .map(|(value, _)| *value)
                .chain(block.body.iter().flat_map(|node| node.results.iter().copied()))
        })
        .map(|value| value.index())
        .max()
        .unwrap()
        + 1;
    let entry = function.blocks.iter_mut().find(|block| block.id == function.entry).unwrap();
    let mut parameters = Vec::new();
    let mut constructors = Vec::new();
    let mut fields = Vec::new();
    for (value, ty) in &entry.params {
        if let Ty::Struct(id) = ty {
            let definition = twin.structs.iter().find(|definition| definition.id == *id).unwrap();
            assert_eq!(
                definition.fields.iter().map(|field| field.ty.clone()).collect::<Vec<_>>(),
                vec![Ty::U32, Ty::Bool]
            );
            let pair_fields =
                [trust_ir::value::ValueId::new(fresh), trust_ir::value::ValueId::new(fresh + 1)];
            fresh += 2;
            parameters.push((pair_fields[0], Ty::U32));
            parameters.push((pair_fields[1], Ty::Bool));
            constructors.push(
                trust_ir::InstrNode::new(trust_ir::Inst::MakeAggregate {
                    ty: ty.clone(),
                    variant: None,
                    fields: pair_fields.to_vec(),
                })
                .with_result(*value),
            );
            fields.push(pair_fields);
        } else {
            parameters.push((*value, ty.clone()));
        }
    }
    assert!(!fields.is_empty());
    entry.params = parameters;
    entry.body.splice(0..0, constructors);
    let mut signature = twin.func_types[function.ty.as_usize()].clone();
    signature.params = entry.params.iter().map(|(_, ty)| ty.clone()).collect();
    function.ty = trust_ir::value::FuncTyId::new(u32::try_from(twin.func_types.len()).unwrap());
    twin.func_types.push(signature);
    assert!(trust_ir_build::validate_module(&twin).is_empty());
    (twin, fields)
}

/// A NEW, hand-built positive twin: replace the sole array Undef with a splat
/// of an initialized, unconstrained scalar input. Keep the array type and every
/// subsequent write, read and assertion. No particular initial lane value
/// supplies the expected result, including after the invalid-index write.
/// This is not a compiler capture or a reinterpretation of the original Undef.
fn initialized_array_undef_twin(original: &trust_ir::Module) -> trust_ir::Module {
    assert_eq!(original.functions.len(), 1);
    let function = &original.functions[0];
    let args = original
        .func_type(function.ty)
        .unwrap()
        .params
        .iter()
        .map(|ty| trust_ir::interpret::InterpretValue::int(ty.clone(), 0).unwrap())
        .collect();
    assert_legacy_source_ub_is_refused(original, function.id, args);

    let mut twin = original.clone();
    twin.name.push_str("_initialized_unknown_twin");
    let function = &mut twin.functions[0];
    function.name.push_str("_initialized_unknown_twin");
    let fresh = function
        .blocks
        .iter()
        .flat_map(|block| {
            block
                .params
                .iter()
                .map(|(value, _)| *value)
                .chain(block.body.iter().flat_map(|node| node.results.iter().copied()))
        })
        .map(|value| value.index())
        .max()
        .unwrap()
        + 1;
    let input = trust_ir::value::ValueId::new(fresh);
    let entry = function.blocks.iter_mut().find(|block| block.id == function.entry).unwrap();
    entry.params.push((input, Ty::U32));
    let mut replaced = 0;
    for node in &mut entry.body {
        if let trust_ir::Inst::Undef { ty: Ty::Array(element, _) } = &node.inst {
            assert_eq!(twin.types[element.as_usize()], Ty::U32);
            let trust_ir::Inst::Undef { ty } = &node.inst else { unreachable!() };
            node.inst = trust_ir::Inst::ArraySplat { ty: ty.clone(), value: input };
            replaced += 1;
        }
    }
    assert_eq!(replaced, 1);
    let mut signature = twin.func_types[function.ty.as_usize()].clone();
    signature.params.push(Ty::U32);
    function.ty = trust_ir::value::FuncTyId::new(u32::try_from(twin.func_types.len()).unwrap());
    twin.func_types.push(signature);
    assert_eq!(trust_ir_build::validate_module(&twin), trust_ir_build::validate_module(original));
    twin
}

/// `[u32; 4]` with lane 2 written to the constant `7`, then read back. The
/// `assert(lane == 5)` must be REFUTED (`!(7 == 5)` folds to `true`), which is
/// only possible if the element write AND the read are modeled EXACTLY — a havoc
/// leaves the constraint symbolic and this counts 0.
#[test]
fn insert_element_at_a_constant_index_is_modeled_exactly() {
    let mut mb = ModuleBuilder::new("insert_element_exact");
    let u32_ty = mb.add_type(Ty::U32);
    let arr_ty = Ty::Array(u32_ty, 4);
    let ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("insert_element_exact", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let arr0 = fb.undef(arr_ty.clone());
    let index = fb.iconst(Ty::I64, 2);
    let seven = fb.iconst(Ty::U32, 7);
    let arr1 = fb.insert_element(arr_ty, arr0, index, seven);
    let lane = fb.extract_element(Ty::U32, arr1, index);
    let five = fb.iconst(Ty::U32, 5);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane, five);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    let module = initialized_array_undef_twin(&original);
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");

    assert_eq!(
        output.diagnostics.len(),
        0,
        "a constant-index element write is exactly expressible and must NOT fail closed: {:?}",
        output.diagnostics
    );
    assert_eq!(
        error_rule_solver_verdicts(&output.vc),
        vec![Some(true)],
        "lane 2 holds exactly 7, so `assert(lane == 5)` must be an unconditionally reachable \
         error rule — and the in-bounds constant lane carries no bounds rule"
    );
}

/// THE STALE-VALUE TRAP. Lane 2 is written `7` and then OVERWRITTEN with `0`.
/// `assert(lane == 7)` must be REFUTED — the solver must not be able to prove the
/// value the function already overwrote. A model that dropped the second write
/// (or applied it to the wrong lane) folds `!(7 == 7)` to `false` and discharges
/// the assertion: a FALSE PROOF. A havoc leaves it symbolic and also counts 0, so
/// this pins exactness in both directions.
#[test]
fn insert_element_overwrite_does_not_leave_the_old_value_readable() {
    let mut mb = ModuleBuilder::new("insert_element_overwrite");
    let u32_ty = mb.add_type(Ty::U32);
    let arr_ty = Ty::Array(u32_ty, 4);
    let ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("insert_element_overwrite", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let arr0 = fb.undef(arr_ty.clone());
    let index = fb.iconst(Ty::I64, 2);
    let seven = fb.iconst(Ty::U32, 7);
    let arr1 = fb.insert_element(arr_ty.clone(), arr0, index, seven);
    let zero = fb.iconst(Ty::U32, 0);
    let arr2 = fb.insert_element(arr_ty, arr1, index, zero);
    let lane = fb.extract_element(Ty::U32, arr2, index);
    let old = fb.iconst(Ty::U32, 7);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane, old);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    let module = initialized_array_undef_twin(&original);
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");

    assert_eq!(
        output.diagnostics.len(),
        0,
        "both writes are constant-index and exactly expressible: {:?}",
        output.diagnostics
    );
    assert_eq!(
        error_rule_solver_verdicts(&output.vc),
        vec![Some(true)],
        "STALE READ: lane 2 was overwritten with 0, so `assert(lane == 7)` MUST be refuted — \
         proving the pre-overwrite 7 would be a false proof"
    );
}

/// An element write that makes the program genuinely panic must STILL be
/// refuted. Lane 0 is written the constant `0` and then used as a divisor, so the
/// divide-by-zero obligation must stay unconditionally reachable — modeling the
/// write must not let the divisor drift to something nonzero.
#[test]
fn a_division_by_a_freshly_written_zero_element_is_still_refuted() {
    let mut mb = ModuleBuilder::new("insert_element_div_zero");
    let u32_ty = mb.add_type(Ty::U32);
    let arr_ty = Ty::Array(u32_ty, 4);
    let ft = mb.add_func_type(vec![], vec![Ty::U32]);

    let mut fb = mb.function("insert_element_div_zero", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let arr0 = fb.undef(arr_ty.clone());
    let index = fb.iconst(Ty::I64, 0);
    let zero = fb.iconst(Ty::U32, 0);
    let arr1 = fb.insert_element(arr_ty, arr0, index, zero);
    let lane = fb.extract_element(Ty::U32, arr1, index);
    let hundred = fb.iconst(Ty::U32, 100);
    let quotient = fb.udiv(Ty::U32, hundred, lane);
    fb.ret(vec![quotient]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    let module = initialized_array_undef_twin(&original);
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");

    assert_eq!(
        output.diagnostics.len(),
        0,
        "the write is exactly expressible and must not fail closed: {:?}",
        output.diagnostics
    );
    assert!(
        error_rule_solver_verdicts(&output.vc).contains(&Some(true)),
        "`100 / a[0]` with `a[0] = 0` ALWAYS traps: modeling the element write must not \
         discharge the divide-by-zero obligation"
    );
}

/// A SYMBOLIC index is exact in the SMT-array model: the write is `store` at the
/// index and a read of the same index is `select` of that `store`, so
/// `assert(a[i] == 0)` after `a[i] = 0` can never fail — its error rule is dead.
/// What CAN fail is the access itself when `i` is out of bounds: the write
/// carries its own in-bounds error rule `!(i <u 4)`, reachable exactly for
/// `i >= 4`, and the path continues only under `i <u 4` — so the read's own
/// bounds rule, which asks the same question again, is dead too.
/// Before arrays were SMT arrays this write failed closed (`AggregateUpdate`).
#[test]
fn insert_element_at_a_symbolic_index_is_exact_with_its_own_bounds_obligation() {
    let mut mb = ModuleBuilder::new("insert_element_symbolic");
    let u32_ty = mb.add_type(Ty::U32);
    let arr_ty = Ty::Array(u32_ty, 4);
    let ft = mb.add_func_type(vec![Ty::I64], vec![]);

    let mut fb = mb.function("insert_element_symbolic", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let index = fb.add_block_param(entry, Ty::I64);
    let arr0 = fb.undef(arr_ty.clone());
    let zero = fb.iconst(Ty::U32, 0);
    let arr1 = fb.insert_element(arr_ty, arr0, index, zero);
    let lane = fb.extract_element(Ty::U32, arr1, index);
    let also_zero = fb.iconst(Ty::U32, 0);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane, also_zero);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    let module = initialized_array_undef_twin(&original);
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");

    assert!(
        output.diagnostics.is_empty(),
        "a symbolic element write and read are exactly expressible: {:?}",
        output.diagnostics
    );
    let conditions = error_rule_solver_verdicts(&output.vc);
    assert_eq!(
        conditions.iter().filter(|verdict| **verdict == Some(false)).count(),
        2,
        "the read-back assertion (`select(store(a, i, 0), i) == 0` in every model) and the \
         read's own bounds rule (already implied by the write's) are dead"
    );
    assert_eq!(
        conditions.iter().filter(|verdict| verdict.is_none()).count(),
        1,
        "the write carries one symbolic in-bounds rule `!(i <u 4)`"
    );
    assert!(!conditions.contains(&Some(true)), "nothing is unconditionally reachable");
}

/// Per `error` rule, decided by the in-process solver over the rule body:
/// `Some(true)` when it is VALID (reachable in every state of its body relation
/// — the exact-refutation signal a havoc cannot produce), `Some(false)` when it
/// is UNSATISFIABLE (dead), `None` when it is neither.
fn error_rule_solver_verdicts(vc: &trust_mc_core::chc::ChcVc) -> Vec<Option<bool>> {
    let satisfiable = |constraints: Vec<Expr>| -> bool {
        let mut program = ay_bindings::AYProgram::new();
        program.set_logic("QF_ABV");
        for var in vc.vars() {
            let _ = program.declare_const(var.name.to_string(), var.sort.clone());
        }
        for decl in &vc.decls {
            if let trust_mc_core::decl::Decl::Const { name, sort } = decl {
                let _ = program.declare_const(name.clone(), sort.clone());
            }
        }
        for constraint in constraints {
            program.assert(constraint);
        }
        program.check_sat();
        match ay_bindings::execute_direct::execute(&program)
            .expect("in-process AY execution should succeed")
        {
            ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
            ay_bindings::execute_direct::ExecuteResult::Verified => false,
            other => panic!("unexpected solver outcome: {other:?}"),
        }
    };
    vc.rules
        .iter()
        .filter(|rule| rule.head.name.as_str() == "error")
        .map(|rule| {
            let body: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
            if !satisfiable(body.clone()) {
                return Some(false);
            }
            let whole = Expr::and_many(body);
            if satisfiable(vec![whole.not()]) { None } else { Some(true) }
        })
        .collect()
}

/// A static out-of-bounds write is refused before either public translation.
/// Its separately initialized in-bounds twin remains modeled without a trap.
#[test]
fn insert_element_at_an_out_of_bounds_constant_index_is_an_unconditional_error() {
    let build = || {
        let mut mb = ModuleBuilder::new("insert_element_oob");
        let u32_ty = mb.add_type(Ty::U32);
        let arr_ty = Ty::Array(u32_ty, 4);
        let ft = mb.add_func_type(vec![], vec![]);

        let mut fb = mb.function("insert_element_oob", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let arr0 = fb.undef(arr_ty.clone());
        let index = fb.iconst(Ty::I64, 4);
        let zero = fb.iconst(Ty::U32, 0);
        let _arr1 = fb.insert_element(arr_ty, arr0, index, zero);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let original = build();
    assert_canonical_refusal(&original, "constant lane index 4 is out of range for 4 lanes");
    let mut module = initialized_array_undef_twin(&original);
    // A separate valid initialized twin writes the last REAL lane.
    let mut changed = 0;
    for node in &mut module.functions[0].blocks[0].body {
        if let trust_ir::Inst::Const { ty: Ty::I64, value: trust_ir::Constant::Int(index) } =
            &mut node.inst
            && *index == 4
        {
            *index = 3;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert_canonical_module(&module);
    let checked = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");
    assert_eq!(aggregate_update_diagnostics(&checked), 0, "{:?}", checked.diagnostics);
    assert_eq!(
        unconditionally_reachable_error_rules(&checked.vc),
        0,
        "the valid twin writes lane 3 of `[u32; 4]` without a bounds error"
    );

    let unchecked = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() },
    )
    .expect("translates");
    assert!(unchecked.diagnostics.is_empty(), "{:?}", unchecked.diagnostics);
    assert_eq!(unconditionally_reachable_error_rules(&unchecked.vc), 0);
}

/// A negative static index is canonically invalid, never a wrapped lane. Its
/// valid initialized twin writes lane 0 without constraining another lane.
#[test]
fn insert_element_at_a_negative_constant_index_is_an_error_and_writes_no_lane() {
    let mut mb = ModuleBuilder::new("insert_element_negative");
    let u32_ty = mb.add_type(Ty::U32);
    // 256 lanes so that the wrapped reading of `-1i8` (255) is IN BOUNDS and a
    // plain length check cannot be what rejects it.
    let arr_ty = Ty::Array(u32_ty, 256);
    let ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("insert_element_negative", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let arr0 = fb.undef(arr_ty.clone());
    let index = fb.iconst(Ty::I8, -1);
    let seven = fb.iconst(Ty::U32, 7);
    let arr1 = fb.insert_element(arr_ty, arr0, index, seven);
    let lane_255 = fb.iconst(Ty::I64, 255);
    let lane = fb.extract_element(Ty::U32, arr1, lane_255);
    let same = fb.iconst(Ty::U32, 7);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane, same);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();

    let original = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_canonical_refusal(&original, "constant lane index -1 is out of range for 256 lanes");
    let mut module = initialized_array_undef_twin(&original);
    // The valid twin writes lane 0 and reads the distinct lane 255. The
    // independent initialized input must remain unconstrained by that write.
    let mut changed = 0;
    for node in &mut module.functions[0].blocks[0].body {
        if let trust_ir::Inst::Const { ty: Ty::I8, value: trust_ir::Constant::Int(index) } =
            &mut node.inst
            && *index == -1
        {
            *index = 0;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert_canonical_module(&module);
    let checked = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");
    assert_eq!(aggregate_update_diagnostics(&checked), 0, "{:?}", checked.diagnostics);
    assert_eq!(
        error_rule_solver_verdicts(&checked.vc),
        vec![None],
        "writing lane 0 must not decide the independent lane 255"
    );

    let unchecked = trust_ir_function_to_chc_translation_output(
        &module,
        trust_ir::value::FuncId::new(0),
        &TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() },
    )
    .expect("translates");
    assert_eq!(
        error_rule_solver_verdicts(&unchecked.vc),
        vec![None],
        "the valid write to lane 0 must not decide lane 255; its assertion remains contingent"
    );
}

// R129 PIN (stale-read false-proof class): a store carrying
// `ProofAnnotation::RegionHavocStore` — a bulk write whose target set the
// producer could not bound — must FAIL CLOSED in the BMC lane. The array
// memory model would translate it as constraining a single symbolic index,
// leaving every other index at its pre-write value; a later read of an
// element the real bulk write overwrote would then return a STALE value.
// The control (same module, no marker) must translate normally, pinning
// that the refusal keys on the MARKER, not on the store shape.
#[test]
fn region_havoc_store_fails_closed_in_bmc_and_only_when_marked() {
    let build = |marked: bool| {
        let mut mb = ModuleBuilder::new("region_havoc_pin");
        let ft = mb.add_func_type(vec![], vec![]);
        let fb = mb.function("bulk_write", ft);
        drop(fb);
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.functions.clear();

        let func_ty_id = trust_ir::value::FuncTyId::new(0);
        let mut func = trust_ir::Function::new(
            trust_ir::value::FuncId::new(0),
            "bulk_write",
            func_ty_id,
            trust_ir::value::BlockId::new(0),
        );
        let mut block = trust_ir::Block::new(trust_ir::value::BlockId::new(0));

        let slot = trust_ir::value::ValueId::new(0);
        block.body.push(
            trust_ir::InstrNode::new(trust_ir::Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: None,
            })
            .with_result(slot),
        );
        let value = trust_ir::value::ValueId::new(1);
        block.body.push(
            trust_ir::InstrNode::new(trust_ir::Inst::Undef { ty: Ty::U8 })
                .with_result(value)
                .with_proof(ProofAnnotation::FreshSymbolicHavoc),
        );
        let mut store = trust_ir::InstrNode::new(trust_ir::Inst::Store {
            ty: Ty::U8,
            ptr: slot,
            value,
            volatile: false,
            align: None,
        });
        if marked {
            store = store.with_proof(ProofAnnotation::RegionHavocStore);
        }
        block.body.push(store);
        block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![] }));

        func.blocks.push(block);
        module.try_add_function(func).expect("Module::try_add_function: test fixture");
        module
    };

    let refused = |module: &trust_ir::Module| {
        let vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
        assert_eq!(vcs.len(), 1, "expected one BMC VC");
        vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("region-havoc store"))
        })
    };

    assert!(
        refused(&build(true)),
        "a RegionHavocStore-marked store must fail closed in the array memory model"
    );
    assert!(
        !refused(&build(false)),
        "an unmarked store must keep the ordinary translation — the refusal keys on the marker"
    );
}

// ============================================================================
// Return-slot call summaries (Alloca / Store / Load / Assume / Switch / nested
// Call). This is the lowering `core`'s `Option` combinators are compiled into;
// before these arms the interpreter met `Alloca` at its catch-all and every
// caller of `Option::and_then`/`is_some_and`/`map`/`map_or` got an
// unconditional `UnsupportedDirectCallSummary` may-panic rule.
// ============================================================================

/// Build the combinator-wrapper shape:
///
/// ```text
///   wrapper(discr, payload):
///     %slot = Alloca<U32>
///     [Assume(discr == 0 || discr == 1)]      // present iff `assume_valid_discr`
///     Switch discr { 0 => none_arm, 1 => some_arm, default => bb_unreachable }
///     none_arm: Store %slot, 0        ; Br join
///     some_arm: %r = Call inner(payload)  ; Store %slot, %r ; Br join
///     join:     %out = Load %slot ; Return %out
/// ```
///
/// `inner(payload)` is `payload - 1` as a checked `SubOverflow` branching to an
/// `Unreachable` panic block, so the nested callee carries a REAL, guarded panic
/// obligation (`payload == 0`).
///
/// `leak_slot_address` additionally passes `%slot` as an argument to `inner`,
/// which is the aliasing shape the slot model must refuse.
fn build_return_slot_wrapper_module(
    assume_valid_discr: bool,
    leak_slot_address: bool,
) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("return_slot_wrapper");
    let inner_ft = if leak_slot_address {
        mb.add_func_type(vec![Ty::U32, Ty::Ptr], vec![Ty::U32])
    } else {
        mb.add_func_type(vec![Ty::U32], vec![Ty::U32])
    };
    let wrapper_ft = mb.add_func_type(vec![Ty::I64, Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::I64, Ty::U32], vec![]);

    // inner(payload) = payload.checked_sub(1) with the overflow arm unreachable.
    let mut fb = mb.function("slot_inner", inner_ft);
    let entry = fb.create_block();
    let ok = fb.create_block();
    let panic = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let payload = fb.add_block_param(entry, Ty::U32);
    if leak_slot_address {
        fb.add_block_param(entry, Ty::Ptr);
    }
    let one = fb.iconst(Ty::U32, 1);
    let (value, flag) = fb.overflow(OverflowOp::SubOverflow, Ty::U32, payload, one);
    fb.condbr(flag, panic, vec![], ok, vec![]);
    fb.switch_to_block(ok);
    fb.ret(vec![value]);
    fb.switch_to_block(panic);
    fb.unreachable();
    fb.build();

    // wrapper(discr, payload) — the return-slot shape.
    let mut fb = mb.function("slot_wrapper", wrapper_ft);
    let entry = fb.create_block();
    let none_arm = fb.create_block();
    let some_arm = fb.create_block();
    let join = fb.create_block();
    let dead = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let discr = fb.add_block_param(entry, Ty::I64);
    let payload = fb.add_block_param(entry, Ty::U32);
    let slot = fb.alloca(Ty::U32);
    if assume_valid_discr {
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, discr, zero);
        let is_one = fb.icmp(ICmpOp::Eq, Ty::I64, discr, one);
        let valid = fb.binop(BinOp::Or, Ty::Bool, is_zero, is_one);
        fb.assume(valid);
    }
    fb.switch(
        discr,
        vec![
            SwitchCase { value: trust_ir::Constant::Int(0), target: none_arm, args: vec![] },
            SwitchCase { value: trust_ir::Constant::Int(1), target: some_arm, args: vec![] },
        ],
        dead,
        vec![],
    );
    fb.switch_to_block(none_arm);
    let zero_u32 = fb.iconst(Ty::U32, 0);
    fb.store(Ty::U32, slot, zero_u32);
    fb.br(join, vec![]);
    fb.switch_to_block(some_arm);
    let called = if leak_slot_address {
        fb.call(trust_ir::value::FuncId::new(0), vec![payload, slot])
    } else {
        fb.call(trust_ir::value::FuncId::new(0), vec![payload])
    };
    fb.store(Ty::U32, slot, called);
    fb.br(join, vec![]);
    fb.switch_to_block(join);
    let out = fb.load(Ty::U32, slot);
    fb.ret(vec![out]);
    fb.switch_to_block(dead);
    fb.unreachable();
    fb.build();

    // caller(discr, payload): forwards both unconstrained.
    let mut fb = mb.function("slot_caller", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let d = fb.add_block_param(entry, Ty::I64);
    let p = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(1), vec![d, p]);
    fb.ret(vec![]);
    fb.build();

    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn slot_caller_output(module: &trust_ir::Module) -> ChcTranslationOutput {
    let outputs = trust_ir_to_chc_translation_outputs(module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 3, "inner + wrapper + caller");
    outputs.into_iter().nth(2).expect("caller is the third function")
}

/// Is ANY of `output`'s `error` rules SATISFIABLE — i.e. does the translation
/// actually leave a panic REACHABLE?
///
/// Existence of an error rule is NOT that question and must never be asserted in
/// its place: a fold that quietly replaces a real panic condition with `false`
/// still emits a rule, so an existence assert survives the very mutation it
/// exists to catch (measured: four of the six tests below were inert until this
/// helper replaced their existence asserts).
///
/// The caller fixtures here are single-entry and their entry relation is
/// unconstrained, so asserting the rule's own constraints is the reachability
/// question for them.
fn some_error_rule_is_satisfiable(output: &ChcTranslationOutput) -> bool {
    output.vc.rules.iter().filter(|rule| rule.head.name == "error").any(|rule| {
        let mut program = ay_bindings::AYProgram::new();
        program.set_logic("QF_BV");
        for var in output.vc.vars() {
            let _ = program.declare_const(var.name.to_string(), var.sort.clone());
        }
        for decl in &output.vc.decls {
            if let trust_mc_core::decl::Decl::Const { name, sort } = decl {
                let _ = program.declare_const(name.clone(), sort.clone());
            }
        }
        for constraint in &rule.body.constraints {
            program.assert(constraint.clone());
        }
        program.check_sat();
        matches!(
            ay_bindings::execute_direct::execute(&program),
            Ok(ay_bindings::execute_direct::ExecuteResult::Counterexample { .. })
        )
    })
}

fn declined_direct_call_summary(output: &ChcTranslationOutput) -> bool {
    output
        .diagnostics
        .iter()
        .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
}

#[test]
fn return_slot_combinator_wrapper_is_summarized_not_declined() {
    // THE COMPLETENESS CLAIM. The whole shape — a return-slot `Alloca`, the
    // enum-validity `Assume`, the discriminant `Switch`, a `Store` per arm, the
    // join `Load`, and a nested `Call` into the "closure" — must summarize.
    let caller = slot_caller_output(&build_return_slot_wrapper_module(true, false));
    assert!(
        !declined_direct_call_summary(&caller),
        "the return-slot combinator shape must summarize (no UnsupportedDirectCallSummary), \
         got {:?}",
        caller.diagnostics
    );
}

#[test]
fn return_slot_summary_keeps_the_nested_callees_panic_refutable() {
    // THE SOUNDNESS CLAIM, and the one that separates a summary from a deletion:
    // `slot_inner` really panics at `payload == 0`, and that obligation must
    // survive the fold into the caller as a GUARDED error rule — not vanish
    // with the decline it replaced.
    let caller = slot_caller_output(&build_return_slot_wrapper_module(true, false));
    // SATISFIABLE, not merely present. The `Assume` makes the switch default's
    // `Unreachable` UNSAT, so the ONLY reachable panic left in this fixture is
    // the nested callee's underflow — drop it and nothing here is satisfiable.
    assert!(
        some_error_rule_is_satisfiable(&caller),
        "the nested callee's checked-sub underflow must reach the caller as a \
         SATISFIABLE error rule; rules: {:?}",
        caller
            .vc
            .rules
            .iter()
            .filter(|r| r.head.name == "error")
            .map(|r| &r.body.constraints)
            .collect::<Vec<_>>()
    );
    // ...and guarded by the caller's own arguments, never unconditional.
    assert!(
        caller.vc.rules.iter().any(|rule| {
            rule.head.name == "error"
                && rule.body.relation.as_ref().is_some_and(|rel| rel.name == "bb0")
                && !rule.body.constraints.is_empty()
        }),
        "the folded panic must be GUARDED by the call's arguments, not unconditional"
    );
}

#[test]
fn a_slot_whose_address_escapes_into_a_call_is_refused() {
    // THE ALIASING GUARD. Hand `slot_inner` the slot's ADDRESS and the model can
    // no longer claim to see every writer, so the whole summary must decline —
    // NOT quietly keep reading the id-keyed cell (that read would return the
    // pre-call value: a fabricated fact, i.e. a false proof).
    let caller = slot_caller_output(&build_return_slot_wrapper_module(true, true));
    assert!(
        declined_direct_call_summary(&caller),
        "an alloca whose address reaches a call argument must decline the summary"
    );
}

#[test]
fn switch_default_edge_is_explored_rather_than_pruned() {
    // `exhaustive_enum_unreachable` is never consulted, so the default edge is
    // ALWAYS explored. With no `Assume` bounding the discriminant, the default
    // block's `Unreachable` is reachable and the caller must carry a refutable
    // error rule — the switch must not silently assume its cases are exhaustive.
    let caller = slot_caller_output(&build_return_slot_wrapper_module(false, false));
    assert!(
        !declined_direct_call_summary(&caller),
        "the shape still summarizes without the Assume, got {:?}",
        caller.diagnostics
    );
    // DIFFERENTIAL, and the direction is what matters. Both modules are the same
    // wrapper; only the enum-validity `Assume` differs. Dropping it must ADD a
    // satisfiable error rule — the default edge reaching `Unreachable` with a
    // discriminant outside {0,1}. A translation that PRUNED the default (by
    // trusting `exhaustive_enum_unreachable`) emits the same rules either way,
    // so this comparison is what fails when the flag becomes load-bearing.
    let assumed = slot_caller_output(&build_return_slot_wrapper_module(true, false));
    let sat_rules = |o: &ChcTranslationOutput| {
        o.vc.rules
            .iter()
            .filter(|r| r.head.name == "error")
            .filter(|r| {
                let mut program = ay_bindings::AYProgram::new();
                program.set_logic("QF_BV");
                for var in o.vc.vars() {
                    let _ = program.declare_const(var.name.to_string(), var.sort.clone());
                }
                for constraint in &r.body.constraints {
                    program.assert(constraint.clone());
                }
                program.check_sat();
                matches!(
                    ay_bindings::execute_direct::execute(&program),
                    Ok(ay_bindings::execute_direct::ExecuteResult::Counterexample { .. })
                )
            })
            .count()
    };
    let without = sat_rules(&caller);
    let with = sat_rules(&assumed);
    assert!(
        without > with,
        "an unbounded discriminant must leave the switch default (Unreachable) \
         REACHABLE: satisfiable error rules without the Assume = {without}, with = {with}"
    );
}

#[test]
fn a_call_chain_deeper_than_the_budget_declines_rather_than_dropping_a_callee() {
    // TERMINATION + FAIL-CLOSED. A chain longer than
    // `DIRECT_CALL_SUMMARY_MAX_DEPTH` must DECLINE (the caller keeps its
    // conservative may-panic rule), never summarize the prefix and drop the tail.
    let mut mb = ModuleBuilder::new("deep_call_chain");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let void_ft = mb.add_func_type(vec![Ty::U32], vec![]);

    // f0 panics unconditionally; f1..fN each forward to the previous one.
    let mut fb = mb.function("chain0", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let _ = fb.add_block_param(entry, Ty::U32);
    fb.unreachable();
    fb.build();

    let links = DIRECT_CALL_SUMMARY_MAX_DEPTH + 3;
    for index in 1..=links {
        let mut fb = mb.function(&format!("chain{index}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let n = fb.add_block_param(entry, Ty::U32);
        let r = fb.call(trust_ir::value::FuncId::new((index - 1) as u32), vec![n]);
        fb.ret(vec![r]);
        fb.build();
    }

    let mut fb = mb.function("chain_caller", void_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(links as u32), vec![n]);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let outputs = trust_ir_to_chc_translation_outputs(&module, &options);
    let caller = outputs.last().expect("caller output");
    assert!(
        declined_direct_call_summary(caller),
        "a call chain deeper than the depth budget must decline, got {:?}",
        caller.diagnostics
    );
    // Pin the EXIT, not just the fact of declining. Almost anything makes this
    // fixture decline (`chain0` never returns, so the returns are uncombinable);
    // only the depth guard makes it decline by meeting a `Call` it refuses to
    // follow. Without this the test survives removing the budget entirely.
    let sites: Vec<_> = caller
        .call_summary_census
        .iter()
        .filter_map(|row| match &row.outcome {
            CallSummaryOutcome::Declined { site, detail } => Some((site.tag, detail.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(
        sites,
        vec![("unmodeled_instruction", Some("Call".to_owned()))],
        "the decline must be the DEPTH guard refusing to follow a `Call`"
    );
}

#[test]
fn an_unwritten_slot_consumption_is_refused_not_given_a_default() {
    // Preserve the original source. A plain load transports poison, and the
    // comparison consumes it: canonical UB, not an initialized unknown value.
    let mut mb = ModuleBuilder::new("unwritten_slot");
    let callee_ft = mb.add_func_type(vec![], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![], vec![]);

    let mut fb = mb.function("reads_unwritten_slot", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let slot = fb.alloca(Ty::U32);
    let value = fb.load(Ty::U32, slot);
    let zero = fb.iconst(Ty::U32, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, value, zero);
    fb.assert(is_zero);
    fb.ret(vec![value]);
    fb.build();

    let mut fb = mb.function("caller_of_unwritten", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![]);
    fb.ret(vec![]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    for function in [0, 1] {
        assert_legacy_source_ub_is_refused(&module, trust_ir::value::FuncId::new(function), vec![]);
    }
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    let caller = outputs.last().expect("caller output");
    assert!(
        declined_direct_call_summary(caller),
        "the original unwritten-slot consumer must retain a summary refusal, got {:?}",
        caller.diagnostics
    );
    assert!(
        some_error_rule_is_satisfiable(caller),
        "the original poison inspection must retain a reachable error"
    );
}

#[test]
fn an_initialized_unknown_slot_is_not_given_a_default() {
    // A separately constructed positive stores a genuine unknown scalar before
    // the original load/comparison/assertion/return. It is not the old capture.
    let mut mb = ModuleBuilder::new("initialized_unknown_slot");
    let callee_ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("reads_initialized_unknown_slot", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U32);
    let slot = fb.alloca(Ty::U32);
    fb.store(Ty::U32, slot, input);
    let value = fb.load(Ty::U32, slot);
    let zero = fb.iconst(Ty::U32, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, value, zero);
    fb.assert(is_zero);
    fb.ret(vec![value]);
    fb.build();
    let mut fb = mb.function("caller_of_initialized_unknown", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U32);
    let _ = fb.call(trust_ir::value::FuncId::new(0), vec![input]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    let caller = outputs.last().expect("caller output");
    assert!(!declined_direct_call_summary(caller), "{:?}", caller.diagnostics);
    assert!(
        some_error_rule_is_satisfiable(caller),
        "asserting `initialized_unknown_slot == 0` must stay SATISFIABLE; a default would fabricate a proof"
    );
    for value in [0, 1] {
        let run = trust_ir::interpret::Interpreter::with_module(&module).execute_func(
            trust_ir::value::FuncId::new(1),
            [trust_ir::interpret::InterpretValue::int(Ty::U32, value).unwrap()],
        );
        if value == 0 {
            run.unwrap();
        } else {
            assert_eq!(run.unwrap_err().code, trust_ir::interpret::InterpretErrorCode::Panic);
        }
    }
}

// ---------------------------------------------------------------------------
// trust-ir v40 `FatPtrKind::ContainerVtable` — the `dyn`-tail container pointer
// (`*const ArcInner<dyn Any>` inside `Arc<dyn Any>`). Its metadata is an opaque
// VTABLE WORD, never a length; nothing dispatches through it. Every test below
// pins that this translator handles or refuses the kind BY NAME rather than
// folding it into a neighbour.
// ---------------------------------------------------------------------------

/// A `PtrMetadata` read of a `ContainerVtable` pointer with its honest metadata
/// type (`Ty::Ptr`, the vtable word) is refused fail-closed as
/// `PointerMetadata`, exactly as `&dyn Trait` is: the word has no model.
#[test]
fn typed_chc_translation_refuses_container_vtable_metadata_by_name() {
    let mut mb = ModuleBuilder::new("container_vtable_metadata");
    let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
    let ft = mb.add_func_type(vec![fat.clone()], vec![Ty::Ptr]);
    let mut fb = mb.function("container_vtable_metadata", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let ptr = fb.add_block_param(entry, fat.clone());
    let metadata = fb.ptr_metadata(fat, Ty::Ptr, ptr);
    fb.ret(vec![metadata]);
    fb.build();

    let outputs = trust_ir_to_chc_translation_outputs(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &TranslateOptions::default(),
    );
    assert_eq!(outputs.len(), 1);
    let reasons: Vec<_> = outputs[0].diagnostics.iter().map(|d| d.reason).collect();
    assert_eq!(
        reasons,
        vec![TrustIrChcUnsupportedReason::PointerMetadata],
        "a container-vtable metadata read must be refused as PointerMetadata, nothing else"
    );
}

/// A vtable word incorrectly spelled as U64 fails canonical preflight before
/// length symbols or bounds can exist. Its valid `ContainerLen`
/// twin, whose metadata IS a length, keeps the length model (unbounded, since the
/// kind carries no element type), which pins that the split is on metadata
/// meaning rather than a blanket refusal of container-tail kinds.
#[test]
fn typed_chc_container_vtable_metadata_is_never_read_as_a_length() {
    let vtable = chc_slice_len_plus_one_vc("container_vtable_as_len", |_| {
        Ty::FatPtr(FatPtrKind::ContainerVtable)
    });
    assert_chc_canonical_refusal(&vtable, "metadata must be ptr, got u64");
    assert!(
        !chc_vc_has_isize_max_len_bound(&vtable.vc),
        "no length bound may be pushed on a vtable word: {:?}",
        vtable.vc.rules
    );

    let len =
        chc_slice_len_plus_one_vc("container_len_as_len", |_| Ty::FatPtr(FatPtrKind::ContainerLen));
    assert!(
        len.diagnostics.is_empty(),
        "the ContainerLen twin's metadata IS a length and stays modeled: {:?}",
        len.diagnostics
    );
    assert!(
        !chc_vc_has_isize_max_len_bound(&len.vc),
        "ContainerLen carries no element type, so its length stays UNBOUNDED: {:?}",
        len.vc.rules
    );
}

/// An unused ContainerVtable argument can cross a direct-call summary as an
/// opaque typed token. Returning a constant does not inspect its vtable or
/// invent a length; metadata inspection remains covered by the refusal above.
#[test]
fn call_summary_carries_container_vtable_parameter_without_interpreting_it() {
    let mut mb = ModuleBuilder::new("container_vtable_census");
    let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
    let callee_ft = mb.add_func_type(vec![fat.clone()], vec![Ty::U32]);
    let caller_ft = mb.add_func_type(vec![fat.clone()], vec![Ty::U32]);

    let mut fb = mb.function("takes_container_vtable", callee_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let _p = fb.add_block_param(entry, fat.clone());
    let one = fb.iconst(Ty::U32, 1);
    fb.ret(vec![one]);
    fb.build();

    let mut fb = mb.function("calls_with_container_vtable", caller_ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let p = fb.add_block_param(entry, fat.clone());
    let r = fb.call(trust_ir::value::FuncId::new(0), vec![p]);
    fb.ret(vec![r]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let outputs = trust_ir_to_chc_translation_outputs(&module, &options);
    let caller = outputs.last().expect("caller output");
    assert!(
        caller.diagnostics.is_empty(),
        "an unused opaque container-vtable parameter must not block a constant return: {:?}",
        caller.diagnostics
    );
    assert_eq!(caller.call_summary_census.len(), 1);
    assert!(matches!(caller.call_summary_census[0].outcome, CallSummaryOutcome::Summarized));
    assert!(
        !caller.vc.rules.iter().any(|rule| rule.head.name == "error"),
        "the constant-returning callee has no error condition"
    );
}

/// CHC models a complete tuple exactly; the BMC lane still has no aggregate
/// value model and must retain its reachable refusal even for an unused result.
#[test]
fn make_aggregate_tracks_fields_in_chc_and_retains_bmc_refusal() {
    let mut builder = ModuleBuilder::new("make_aggregate_refusal");
    let aggregate_ty = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    let function_ty = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("construct", function_ty);
    let entry = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    let seven = function.iconst(Ty::I64, 7);
    let nine = function.iconst(Ty::I64, 9);
    let _result = function.make_aggregate(aggregate_ty, vec![seven, nine]);
    function.ret(vec![]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let options = TranslateOptions::default();
    let bmc = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(bmc.len(), 1);
    assert_eq!(bmc[0].violations.len(), 1);
    let violation = &bmc[0].violations[0];
    assert_eq!(violation.kind, PropertyKind::Other);
    assert!(violation.message.as_deref().unwrap().contains("MakeAggregate construction"));
    assert_eq!(
        trust_mc_core::chc_const_prop::eval::try_eval_to_bool(&violation.condition),
        Some(true),
    );

    let chc = trust_ir_to_chc_translation_outputs(&module, &options);
    assert_eq!(chc.len(), 1);
    assert!(chc[0].diagnostics.is_empty(), "{:?}", chc[0].diagnostics);
    assert_eq!(unconditionally_reachable_error_rules(&chc[0].vc), 0);
}

#[test]
fn unused_runtime_closure_retains_both_lane_refusals() {
    let (module, host, _, _, result) =
        crate::translate_chc::liveness_tests::runtime_closure_fixture();
    let options = TranslateOptions::default();
    let bmc = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(bmc.len(), 2);
    let violation = &bmc.last().unwrap().violations;
    assert_eq!(violation.len(), 1, "unused construction must not erase its refusal");
    assert_eq!(violation[0].kind, PropertyKind::Other);
    assert!(violation[0].message.as_deref().unwrap().contains("MakeClosure construction"));
    assert_eq!(
        trust_mc_core::chc_const_prop::eval::try_eval_to_bool(&violation[0].condition),
        Some(true),
    );
    assert!(bmc_violation_is_satisfiable(bmc.last().unwrap(), &violation[0]));

    for per_block in [false, true] {
        let output = if per_block {
            crate::translate_chc::trust_ir_function_to_chc_translation_output_per_block(
                &module, host, &options,
            )
        } else {
            trust_ir_function_to_chc_translation_output(&module, host, &options)
        }
        .unwrap();
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].family, SemanticsFamily::Closures);
        assert_eq!(output.diagnostics[0].reason, TrustIrChcUnsupportedReason::ClosureConstruction);
        assert_eq!(output.diagnostics[0].result_values, vec![result]);
        // The large-block path retains definitional guard equalities. Decide
        // their real constraints instead of expecting a literal constant.
        // This helper's None means both polarities are SAT, never solver-unknown.
        let verdicts = error_rule_solver_verdicts(&output.vc);
        assert_eq!(verdicts.len(), 1);
        assert_ne!(verdicts[0], Some(false), "construction refusal must not be dead");
        if per_block {
            assert!(unconditionally_reachable_error_rules(&output.vc) >= 1);
        }
    }
}

#[test]
fn make_aggregate_retains_refusal_for_untracked_fields() {
    let mut builder = ModuleBuilder::new("make_aggregate_opaque_field");
    let opaque = Ty::FatPtr(trust_ir::ty::FatPtrKind::ContainerVtable);
    let aggregate_ty = Ty::Tuple(vec![opaque.clone()]);
    let function_ty = builder.add_func_type(vec![opaque.clone()], vec![]);
    let mut function = builder.function("construct", function_ty);
    let entry = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    let field = function.add_block_param(entry, opaque);
    let result = function.make_aggregate(aggregate_ty, vec![field]);
    function.ret(vec![]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let chc = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert_eq!(chc.len(), 1);
    assert_eq!(chc[0].diagnostics.len(), 1);
    let diagnostic = &chc[0].diagnostics[0];
    assert_eq!(diagnostic.family, SemanticsFamily::Aggregates);
    assert_eq!(diagnostic.reason, TrustIrChcUnsupportedReason::AggregateOpaqueValue);
    assert_eq!(diagnostic.result_values, vec![result]);
    assert!(unconditionally_reachable_error_rules(&chc[0].vc) >= 1);
}

#[test]
fn make_aggregate_preserves_symbolic_field_order_and_duplicates() {
    for wrong_first_field in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_symbolic_fields");
        let aggregate_ty = Ty::Tuple(vec![Ty::I64, Ty::I64, Ty::I64]);
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![]);
        let mut fb = mb.function("fields", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let x = fb.add_block_param(entry, Ty::I64);
        let y = fb.add_block_param(entry, Ty::I64);
        let aggregate = fb.make_aggregate(aggregate_ty, vec![x, y, x]);
        for (field, expected) in
            [if wrong_first_field { y } else { x }, y, x].into_iter().enumerate()
        {
            let actual = fb.extract_field(Ty::I64, aggregate, field as u32);
            let equal = fb.icmp(ICmpOp::Eq, Ty::I64, actual, expected);
            fb.assert(equal);
        }
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
        assert_eq!(outputs.len(), 1);
        assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
        let verdicts = error_rule_solver_verdicts(&outputs[0].vc);
        assert_eq!(
            verdicts,
            vec![if wrong_first_field { None } else { Some(false) }, Some(false), Some(false)]
        );
        // `None` here means BOTH the error condition and its negation are
        // actually SAT (the helper rejects solver-unknown outcomes). Pin the
        // concrete distinct-input counterexample in the canonical interpreter.
        let run = trust_ir::interpret::Interpreter::with_module(&module).execute_func(
            trust_ir::value::FuncId::new(0),
            [
                trust_ir::interpret::InterpretValue::int(Ty::I64, 7).unwrap(),
                trust_ir::interpret::InterpretValue::int(Ty::I64, 9).unwrap(),
            ],
        );
        if wrong_first_field {
            assert_eq!(run.unwrap_err().code, trust_ir::interpret::InterpretErrorCode::Panic);
        } else {
            run.unwrap();
        }
    }
}

#[test]
fn make_aggregate_cross_block_value_keeps_computed_fields() {
    let mut mb = ModuleBuilder::new("make_aggregate_cross_block");
    let pair_ty = Ty::Tuple(vec![Ty::I64, Ty::Bool]);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("checked_pair", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let seven = fb.iconst(Ty::I64, 7);
    let flag = fb.bool_const(false);
    let pair = fb.make_aggregate(pair_ty, vec![seven, flag]);
    // Deliberately no block argument: carry the immutable SSA definition.
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    let result = fb.extract_field(Ty::I64, pair, 0);
    let flag = fb.extract_field(Ty::Bool, pair, 1);
    let expected_flag = fb.bool_const(false);
    let no_overflow = fb.icmp(ICmpOp::Eq, Ty::Bool, flag, expected_flag);
    fb.assert(no_overflow);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let outputs =
        trust_ir_to_chc_translation_outputs_per_block(&module, &TranslateOptions::default());
    assert_eq!(outputs.len(), 1);
    let output = &outputs[0];
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    let fields = head_arg_suffix(output, "bb1", 2);
    assert_eq!(fields[0], ay_bindings::Expr::bitvec_const(7u64, 64));
    assert_eq!(fields[1], ay_bindings::Expr::bool_const(false));
}

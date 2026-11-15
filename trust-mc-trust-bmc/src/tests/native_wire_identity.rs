// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native translation must refuse non-wire metadata before hashing it, without
//! erasing it. Wire-encodable certificate bindings remain part of canonical
//! identity. These are diagnostic translation tests, not certificate proofs.

use super::*;

const MODES: [TrustMcVerificationMode; 3] = [
    TrustMcVerificationMode::BoundedModelCheck,
    TrustMcVerificationMode::Chc,
    TrustMcVerificationMode::Pdr,
];

fn translate(
    bundle: &NativeVerificationBundle,
    mode: TrustMcVerificationMode,
) -> Result<(), NativeTrustMcBundleError> {
    let options = TranslateOptions::default();
    match mode {
        TrustMcVerificationMode::BoundedModelCheck => {
            trust_mc_bmc_vcs_from_native_bundle(bundle, &options).map(|rows| {
                assert_eq!(rows.len(), 1);
            })
        }
        TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {
            trust_mc_chc_pdr_obligations_from_native_bundle(bundle, &options).map(|rows| {
                assert_eq!(rows.len(), 1);
            })
        }
    }
}

fn assert_translation_preserves_identity(
    bundle: &NativeVerificationBundle,
    mode: TrustMcVerificationMode,
) {
    let before = bundle.clone();
    let digest = bundle.module.stable_digest();
    assert_eq!(bundle.trust_ir_module_digest, digest);
    translate(bundle, mode).expect("encodable diagnostic bundle should translate");
    assert_eq!(*bundle, before, "translation must preserve the entire bundle");
    assert_eq!(bundle.module.stable_digest(), digest, "canonical identity must not change");
}

fn assert_non_wire_refusal(
    bundle: &NativeVerificationBundle,
    mode: TrustMcVerificationMode,
    location: &str,
    construct: &'static str,
) {
    // Do not compute a digest of a non-wire module, even in the test: that is
    // exactly the infallible operation the admission boundary must avoid.
    let before = bundle.clone();
    let error = translate(bundle, mode).expect_err("non-wire metadata must be refused");
    let NativeTrustMcBundleError::InvalidBundle(errors) = error else {
        panic!("expected upstream bundle refusal, got {error:?}");
    };
    assert!(
        errors.iter().any(|error| matches!(error,
            trust_ir::NativeVerificationBundleError::TrustIrModuleHasNoWireIdentity {
                location: found_location,
                construct: found_construct,
            } if found_location == location && *found_construct == construct
        )),
        "expected exact {construct} refusal at {location}: {errors:?}"
    );
    assert!(
        !errors.iter().any(|error| matches!(
            error,
            trust_ir::NativeVerificationBundleError::TrustIrModuleDigestMismatch { .. }
        )),
        "an unencodable module must not receive an invented expected digest"
    );
    assert_eq!(*bundle, before, "refusal must retain all input metadata");
}

fn append_unbound_transport_certificate(bundle: &mut NativeVerificationBundle) -> usize {
    let index = bundle.module.proof_certificates.len();
    // Intentionally synthetic, non-authoritative transport data. No obligation
    // is marked proved and no request asks to consume this certificate.
    bundle.module.proof_certificates.push(trust_ir::ProofCertificate {
        obligation: ProofId::new(1),
        prover: "synthetic transport fixture; not certified".to_string(),
        evidence: trust_ir::ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage: native_digest(0x71),
            kernel_recheck: Some(trust_ir::CleanCicKernelRecheck {
                module: "TransportFixture".to_string(),
                theorems: vec![],
                anchor: "transport-fixture".to_string(),
                allowed_axioms: vec![],
                binding: None,
            }),
        },
        assurance: None,
    });
    refresh_native_trust_mc_bundle_module_identity(bundle);
    index
}

#[test]
fn native_wire_identity_preserves_ordinary_bundle_and_canonical_digest() {
    for mode in MODES {
        for ordinary_scopes in [false, true] {
            let mut bundle = native_trust_mc_bundle(mode);
            if ordinary_scopes {
                bundle.module.functions[0].scopes = Some(vec![
                    trust_ir::ScopeData::new(None, None),
                    trust_ir::ScopeData::new(
                        Some(0),
                        Some(trust_ir::SourceSpan { file: 0, line: 10, col: 5 }),
                    ),
                ]);
                refresh_native_trust_mc_bundle_module_identity(&mut bundle);
            }
            assert_translation_preserves_identity(&bundle, mode);
        }
    }
}

#[test]
fn native_wire_identity_preserves_unbound_certificate_control() {
    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        append_unbound_transport_certificate(&mut bundle);
        assert!(bundle.module.first_certificate_binding().is_none());
        assert_translation_preserves_identity(&bundle, mode);
    }
}

#[test]
fn native_wire_identity_preserves_v46_carrier_without_forcing_v38() {
    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        let mut spec = trust_ir::SpecModule::new("IdentityControl");
        spec.vars.push(
            trust_ir::SpecVar::new("ready", "Bool").with_sort(trust_ir::proof::ClauseSort::Bool),
        );
        bundle.module.spec_modules.push(spec);
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_translation_preserves_identity(&bundle, mode);
    }
}

#[test]
fn native_wire_identity_refuses_inline_chain_before_hashing_without_erasure() {
    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        let requested = native_trust_mc_request(&bundle).function;
        // The hash covers the entire module, including functions the request
        // does not select. Reverse storage order so the reported FuncId cannot
        // accidentally be an index in the functions vector.
        bundle.module.functions.reverse();
        let (position, body) = bundle
            .module
            .functions
            .iter_mut()
            .enumerate()
            .find(|(_, body)| body.id != requested)
            .expect("fixture includes an unrequested function");
        let function = body.id;
        assert_ne!(function.index() as usize, position);
        body.scopes = Some(vec![
            trust_ir::ScopeData::new(None, None),
            trust_ir::ScopeData {
                parent: Some(0),
                span: None,
                inlined_at: Some(trust_ir::InlinedAt {
                    span: trust_ir::SourceSpan { file: 0, line: 20, col: 9 },
                    callee: "Clean::transport_fixture".to_string(),
                }),
            },
        ]);
        let before = bundle.clone();
        let error = translate(&bundle, mode).expect_err("inline chains have no wire identity");
        assert_eq!(
            error,
            NativeTrustMcBundleError::InlinedScopeChainUnencodable {
                function: function.index(),
                scope: 1,
            }
        );
        assert_eq!(bundle, before, "the inline chain and declared identity must remain intact");
    }
}

#[test]
fn native_wire_identity_refuses_every_completeness_claim_without_erasure() {
    for mode in MODES {
        for claim in [
            trust_ir::ModuleCompleteness::Complete,
            trust_ir::ModuleCompleteness::Partial(vec![]),
            trust_ir::ModuleCompleteness::Partial(vec![trust_ir::UnloweredRow {
                symbol: "unlowered".to_string(),
                display_path: None,
                reason: "synthetic refusal".to_string(),
            }]),
        ] {
            for otherwise_valid in [true, false] {
                let mut bundle = native_trust_mc_bundle(mode);
                bundle.module.completeness = Some(claim.clone());
                if !otherwise_valid {
                    bundle.schema_version = 0;
                    bundle.requests.clear();
                }
                assert_non_wire_refusal(&bundle, mode, "module", "Module.completeness");
            }
        }
    }
}

#[test]
fn native_wire_identity_binds_certificate_without_erasure_and_refuses_stale_digest() {
    use trust_ir::binary::{
        BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
        deserialize_module, serialize_module,
    };

    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        let certificate = append_unbound_transport_certificate(&mut bundle);
        let trust_ir::ProofEvidence::CleanCic { kernel_recheck: Some(recheck), .. } =
            &mut bundle.module.proof_certificates[certificate].evidence
        else {
            panic!("fixture supplies a synthetic kernel-recheck transport row");
        };
        recheck.binding = Some(Box::new(trust_ir::CertificateBinding::new(
            native_digest(0x72),
            native_digest(0x73),
        )));
        let before = bundle.clone();
        assert_eq!(bundle.module.first_certificate_binding(), Some((certificate, ProofId::new(1))));
        // Since TrustIR v61 a binding has a canonical wire image. Modern
        // encoding must retain it; explicitly projecting to v38 must refuse.
        let bytes = serialize_module(&bundle.module).expect("modern binding encoding");
        assert_eq!(deserialize_module(&bytes).unwrap(), bundle.module);
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions { body, ..Default::default() };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&bundle.module, options).err(),
                Some(BinaryProjectionError::CertificateBindingRequiresV61),
            );
        }
        let actual = bundle.module.stable_digest();
        assert_ne!(
            actual, bundle.trust_ir_module_digest,
            "the added binding changes canonical identity"
        );
        let error = translate(&bundle, mode).expect_err("a stale module identity must be refused");
        let NativeTrustMcBundleError::InvalidBundle(errors) = error else {
            panic!("expected bundle identity refusal, got {error:?}");
        };
        assert!(
            errors.iter().any(|error| matches!(error,
                trust_ir::NativeVerificationBundleError::TrustIrModuleDigestMismatch {
                    expected, actual: supplied,
                } if *expected == actual && *supplied == bundle.trust_ir_module_digest
            )),
            "the binding is hashed, never silently unbound: {errors:?}"
        );
        assert_eq!(
            bundle, before,
            "refusal retains the complete synthetic, non-authoritative carrier"
        );
        assert!(!errors.iter().any(|error| matches!(
            error,
            trust_ir::NativeVerificationBundleError::TrustIrModuleHasNoWireIdentity { .. }
        )));

        // A producer refresh admits the same bound carrier without erasing it.
        let stale_digest = bundle.trust_ir_module_digest;
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_ne!(bundle.trust_ir_module_digest, stale_digest, "the binding is hashed");
        assert_eq!(bundle.module.first_certificate_binding(), Some((certificate, ProofId::new(1))));
        assert_translation_preserves_identity(&bundle, mode);
    }
}

#[test]
fn native_wire_identity_preserves_certificate_binding_and_refuses_stale_identity() {
    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        let certificate = append_unbound_transport_certificate(&mut bundle);
        let unbound_digest = bundle.trust_ir_module_digest;
        let trust_ir::ProofEvidence::CleanCic { kernel_recheck: Some(recheck), .. } =
            &mut bundle.module.proof_certificates[certificate].evidence
        else {
            panic!("fixture supplies a synthetic kernel-recheck transport row");
        };
        recheck.binding = Some(Box::new(trust_ir::CertificateBinding::new(
            native_digest(0x72),
            native_digest(0x73),
        )));
        // Since wire v61, binding metadata has a canonical carrier. Keeping
        // the unbound digest must fail; accepting the binding is not a proof
        // claim and must not erase it to recover that stale identity.
        assert_eq!(bundle.module.first_certificate_binding(), Some((certificate, ProofId::new(1))));
        let bound_digest = bundle.module.stable_digest();
        assert_ne!(bound_digest, unbound_digest, "the binding must enter the module identity");
        let before = bundle.clone();
        let error = translate(&bundle, mode).expect_err("the unbound module digest is stale");
        let NativeTrustMcBundleError::InvalidBundle(errors) = error else {
            panic!("expected upstream stale-identity refusal, got {error:?}");
        };
        assert_eq!(
            errors,
            vec![trust_ir::NativeVerificationBundleError::TrustIrModuleDigestMismatch {
                expected: bound_digest,
                actual: unbound_digest,
            }]
        );
        assert_eq!(bundle, before, "stale-identity refusal must retain all input metadata");

        // A producer changing the module must update both the envelope and
        // its lineage roots. Diagnostic translation then keeps the binding.
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_eq!(bundle.trust_ir_module_digest, bound_digest);
        assert_eq!(bundle.module.first_certificate_binding(), Some((certificate, ProofId::new(1))));
        assert_translation_preserves_identity(&bundle, mode);
    }
}

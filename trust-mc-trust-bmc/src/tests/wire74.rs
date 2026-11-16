// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Wire-74 values and provenance cannot create pointer bits or proof authority.

use super::*;
use crate::translate::{UnsupportedSort, checked_ty_to_sort};
use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot};
use trust_ir::constant::Constant;

fn nominal_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("nominal_function_item");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("item", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    fb.ret(vec![]);
    let item = fb.build();
    let mut module = mb.build().unwrap();
    module.types.push(Ty::FnItem(item));
    module
}

#[test]
fn nominal_function_item_has_no_pointer_integer_or_aggregate_placeholder() {
    let item = trust_ir::FuncId::new(0);
    assert_eq!(
        family_for_inst(&trust_ir::Inst::Const {
            ty: Ty::FnItem(item),
            value: Constant::FnItem(item),
        }),
        SemanticsFamily::Calls
    );
    assert_eq!(checked_ty_to_sort(&Ty::FnItem(item)), Err(UnsupportedSort::FunctionItem));
    assert!(const_to_expr(&Ty::FnItem(item), &Constant::FnItem(item)).is_none());
    assert!(const_to_expr(&Ty::Ptr, &Constant::FnItem(item)).is_none());
    assert!(
        const_to_expr(
            &Ty::Tuple(vec![Ty::FnItem(item)]),
            &Constant::Aggregate(vec![Constant::FnItem(item)]),
        )
        .is_none()
    );
    assert_eq!(checked_ty_to_sort(&Ty::U64), Ok(ay_bindings::Sort::bitvec(64)));
    assert_eq!(const_to_expr(&Ty::U64, &Constant::Int(7)), Some(Expr::bitvec_const(7u64, 64)));
}

#[test]
fn unused_nominal_type_refuses_before_any_smt_symbols_in_both_lanes() {
    let module = nominal_module();
    assert_canonical_module(&module);
    let options = TranslateOptions::default();
    let bmc = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(bmc.len(), 1);
    assert!(bmc[0].decls.is_empty());
    assert!(bmc[0].constraints.is_empty());
    assert_eq!(bmc[0].violations.len(), 1);
    assert_eq!(bmc[0].violations[0].condition, Expr::true_());
    assert!(bmc[0].violations[0].message.as_deref().unwrap().contains("Ty::FnItem"));
    for outputs in [
        trust_ir_to_chc_translation_outputs(&module, &options),
        trust_ir_to_chc_translation_outputs_per_block(&module, &options),
    ] {
        assert_eq!(outputs.len(), 1);
        let output = &outputs[0];
        assert!(output.module_input_refusal.as_deref().unwrap().contains("Ty::FnItem"));
        assert!(output.vc.decls.is_empty());
        assert_eq!(output.work.instructions_translated, 0);
        assert_eq!(output.vc.rules.len(), 1);
        assert_eq!(output.vc.rules[0].head.name, "error");
        assert!(output.vc.rules[0].body.relation.is_none());
    }
}

#[test]
fn native_modes_refuse_nominal_items_with_their_own_typed_reason() {
    for mode in [
        TrustMcVerificationMode::BoundedModelCheck,
        TrustMcVerificationMode::Chc,
        TrustMcVerificationMode::Pdr,
    ] {
        let mut bundle = native_trust_mc_bundle(mode);
        bundle.module.types.push(Ty::FnItem(bundle.module.functions[0].id));
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_eq!(bundle.validate(), Ok(()));
        let options = TranslateOptions::default();
        let error = match mode {
            TrustMcVerificationMode::BoundedModelCheck => {
                trust_mc_bmc_vcs_from_native_bundle(&bundle, &options).unwrap_err()
            }
            _ => trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &options).unwrap_err(),
        };
        assert_eq!(error, NativeTrustMcBundleError::FunctionItemNotModeled);
    }
}

fn boxed_module(fact: Option<BoxValidityFact>) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("box_validity_admission");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function("subject", ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let result = match fact {
        Some(fact) => fb.box_deref(Ty::I64, pointer, fact),
        None => pointer,
    };
    fb.ret(vec![result]);
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    fb.build();
    mb.build().unwrap()
}

fn box_fact() -> BoxValidityFact {
    BoxValidityFact::premise(
        BoxDerefSite { item: [0xab; 16], ordinal: 0 },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ParamByValue,
    )
}

#[test]
fn valid_box_assumption_does_not_become_a_load_or_checked_validity() {
    let control = boxed_module(None);
    let module = boxed_module(Some(box_fact()));
    assert_canonical_module(&control);
    assert_canonical_module(&module);
    for check_memory_bounds in [true, false] {
        let options = TranslateOptions { check_memory_bounds, ..TranslateOptions::default() };
        let ordinary = trust_ir_to_chc_translation_outputs(&control, &options);
        assert!(ordinary.iter().all(|out| out.diagnostics.is_empty()));
        let bmc = trust_ir_to_bmc_vc(&module, &options);
        assert!(bmc.iter().flat_map(|vc| &vc.violations).any(|violation| {
            violation.kind == PropertyKind::Other
                && violation.message.as_deref().is_some_and(|message| message.contains("BoxDeref"))
        }));
        for outputs in [
            trust_ir_to_chc_translation_outputs(&module, &options),
            trust_ir_to_chc_translation_outputs_per_block(&module, &options),
        ] {
            assert!(outputs.iter().all(|out| out.module_input_refusal.is_none()));
            assert!(outputs.iter().flat_map(|out| &out.diagnostics).any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::BoxDerefValidity
                    && diagnostic.family == SemanticsFamily::MemoryProvenance
            }));
        }
    }
}

#[test]
fn incomplete_box_fact_keeps_canonical_refusal_without_an_invented_site() {
    let mut module = boxed_module(Some(box_fact()));
    let fact = module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            trust_ir::Inst::BoxDeref { fact, .. } => Some(fact),
            _ => None,
        })
        .unwrap();
    fact.evidence.pop();
    let errors = trust_ir_build::validate_module(&module);
    let error = errors
        .iter()
        .find(|error| {
            matches!(error, trust_ir_build::ValidationError::BoxDerefConjunctCover { .. })
        })
        .expect("the missing conjunct retains its typed canonical error");
    assert_canonical_refusal(&module, &error.to_string());
}

#[test]
fn thir_metadata_retains_distinct_kind_exact_digest_and_unmodeled_obligations() {
    for mode in [TrustMcVerificationMode::Chc, TrustMcVerificationMode::Pdr] {
        let mut bundle = native_trust_mc_bundle(mode);
        let source = bundle.source_digest().unwrap();
        bundle.input = NativeAdapterInput::RustThir { source_digest: source };
        // This is an identity-transport fixture, not a source-refinement proof.
        bundle.lineage.nodes[0].transform = ProofTransform::new(
            ProofTransformStage::Frontend,
            "test-thir-identity-transport",
            "tRust",
            "native-request-schema-v1",
        );
        assert_eq!(bundle.validate(), Ok(()));
        let rows =
            trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default())
                .unwrap();
        assert_eq!(rows.len(), 1);
        let metadata = rows[0].obligation.native_metadata.as_ref().unwrap();
        assert_eq!(metadata.adapter_input, "rust-thir");
        assert_eq!(
            metadata.source_digest,
            Some(trust_mc_core::NativeArtifactDigest::new("sha256", "51".repeat(32)))
        );
        assert_ne!(metadata.source_digest.as_ref().unwrap(), &metadata.trust_ir_module_digest);
        assert!(!rows[0].unmodeled_obligations.is_empty());

        bundle.input = NativeAdapterInput::RustThir { source_digest: native_digest(0x99) };
        assert!(matches!(
            trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &TranslateOptions::default()),
            Err(NativeTrustMcBundleError::InvalidBundle(_))
        ));
    }
}

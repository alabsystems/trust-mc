// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact-module proof/replay controls. These synthetic modules claim no Rust
//! source correspondence; the compiler's live source binding is a separate gate.

use super::*;

#[path = "../../../../trust-mc-trust-bmc/tests/fixtures/dataless_enum.rs"]
mod fixture;

fn bundle_for(
    module: trust_ir::Module,
    function: trust_ir::FuncId,
) -> trust_ir::NativeVerificationBundle {
    let mut bundle = panic_free_compiler_bundle();
    let mut obligations = std::mem::take(&mut bundle.module.proof_obligations);
    for obligation in &mut obligations {
        obligation.function = Some(function);
    }
    bundle.module = module;
    bundle.module.proof_obligations = obligations;
    for fact in &mut bundle.compiler_facts.monomorphizations {
        fact.function = Some(function);
    }
    for source in &mut bundle.compiler_facts.obligation_sources {
        source.function = Some(function);
    }
    for request in &mut bundle.requests {
        if let trust_ir::NativeVerificationRequest::TrustMc(request) = request {
            request.function = function;
        }
    }
    refresh_native_test_bundle_module_identity(&mut bundle);
    assert!(trust_ir_build::validate_module(&bundle.module).is_empty());
    bundle
}

fn runner() -> NativeTrustIrChcPdrRunner {
    NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
            .with_timeout(Duration::from_secs(10)),
    )
}

#[test]
fn dataless_enum_calls_gain_live_exact_module_proofs_with_checked_replay() {
    for make in [false, true] {
        for nested in [false, true] {
            let factories: [fn(bool, bool, i128) -> (trust_ir::Module, trust_ir::FuncId); 2] =
                [fixture::symbolic_fixture, fixture::summarized_select_fixture];
            for factory in factories {
                let (module, function) = factory(make, nested, 7);
                let bundle = bundle_for(module, function);
                let evidence = runner().solve_bundle_native_proof_grade(&bundle).unwrap();
                assert_eq!(evidence.obligations.len(), 1, "{make}/{nested}: {evidence:?}");
                assert!(evidence.not_proved.is_empty());
                let verification = &evidence.obligations[0].verification;
                verification.authorized_native_proof().expect("fresh exact-module proof authority");
                let record = verification.native_proof_transport_record().unwrap();
                assert!(!record.replay_artifacts.is_empty());
                assert!(!record.check_artifacts.is_empty());
                println!(
                    "dataless enum {make}/{nested}: {:?} {}",
                    verification.route,
                    serde_json::to_string(&record).unwrap()
                );
                // Public records cannot replace the live capability, even when all
                // genuine bytes and solver/checker artifacts are retained.
                let reloaded: NativeTypedChcPdrProofTransport =
                    serde_json::from_slice(&serde_json::to_vec(&record).unwrap()).unwrap();
                assert_eq!(reloaded, record);
                // The live response is deliberately not serializable; its public
                // Clone is diagnostic-only and must lose the affine capability.
                assert!(verification.clone().authorized_native_proof().is_err());
            }
        }
    }
}

#[test]
fn dataless_enum_wrong_bounds_and_changed_callee_bodies_never_authorize() {
    for nested in [false, true] {
        let (module, function) = fixture::symbolic_fixture(true, nested, 6);
        let evidence =
            runner().solve_bundle_native_proof_grade(&bundle_for(module, function)).unwrap();
        assert!(evidence.obligations.is_empty(), "a reachable wrong bound cannot earn proof");
        assert!(!evidence.not_proved.is_empty() || !evidence.refuted.is_empty());
    }
    let (mut module, function) = fixture::fixture(false, false, 7);
    module.functions.iter_mut().find(|f| f.name == "read_tag").unwrap().blocks[0].body[0].inst =
        trust_ir::Inst::Const { ty: trust_ir::Ty::I16, value: trust_ir::Constant::Int(-5) };
    let evidence = runner().solve_bundle_native_proof_grade(&bundle_for(module, function)).unwrap();
    assert!(evidence.obligations.is_empty(), "the exact callee body, not its name, governs proof");
    assert!(!evidence.not_proved.is_empty() || !evidence.refuted.is_empty());
}

#[test]
fn dataless_enum_raw_entry_inspection_still_has_no_proof_authority() {
    let (module, _) = fixture::fixture(false, false, 7);
    let bundle = bundle_for(module, trust_ir::FuncId::new(0));
    let evidence = runner().solve_bundle_native_proof_grade(&bundle).unwrap();
    assert!(evidence.obligations.is_empty(), "Enum Ty alone supplies no entry shape/width fact");
    assert!(!evidence.not_proved.is_empty());
}

#[test]
fn dataless_enum_scalar_twin_still_authorizes() {
    let (module, function) = fixture::scalar_fixture(true, 7);
    let evidence = runner().solve_bundle_native_proof_grade(&bundle_for(module, function)).unwrap();
    assert_eq!(evidence.obligations.len(), 1);
    evidence.obligations[0].verification.authorized_native_proof().unwrap();
}

#[test]
fn dataless_enum_block_parameter_phi_proves_only_the_true_bound() {
    for nested in [false, true] {
        let (module, function) = fixture::phi_fixture(true, nested, 7);
        let evidence =
            runner().solve_bundle_native_proof_grade(&bundle_for(module, function)).unwrap();
        assert_eq!(evidence.obligations.len(), 1, "{evidence:?}");
        evidence.obligations[0].verification.authorized_native_proof().unwrap();
        let (module, function) = fixture::phi_fixture(true, nested, 6);
        let evidence =
            runner().solve_bundle_native_proof_grade(&bundle_for(module, function)).unwrap();
        assert!(evidence.obligations.is_empty(), "one bad branch cannot be erased");
    }
}

#[test]
fn dataless_enum_discarded_tag_mutations_and_nominal_mismatch_do_not_authorize() {
    for inside in [false, true] {
        let (invalid, function) = fixture::tag_write_fixture(inside);
        let (valid, _) = fixture::fixture(false, false, 7);
        let mut bundle = bundle_for(valid, function);
        let obligations = std::mem::take(&mut bundle.module.proof_obligations);
        bundle.module = invalid;
        bundle.module.proof_obligations = obligations;
        let errors = trust_ir_build::validate_module(&bundle.module);
        assert!(format!("{errors:?}").contains("cannot rewrite an enum discriminant"));
        refresh_native_test_bundle_module_identity(&mut bundle);
        assert!(
            runner().solve_bundle_native_proof_grade(&bundle).is_err(),
            "even discarded tag updates must fail typed input admission"
        );
    }
    let (module, function) = fixture::fixture(false, false, 7);
    let mut bundle = bundle_for(module, function);
    let mut other = bundle.module.enums[0].clone();
    other.id = trust_ir::EnumId::new(1);
    bundle.module.enums.push(other);
    let caller = bundle.module.functions.iter_mut().find(|f| f.id == function).unwrap();
    let trust_ir::Inst::Const { ty, .. } = &mut caller.blocks[0].body[0].inst else {
        unreachable!()
    };
    *ty = trust_ir::Ty::Enum(trust_ir::EnumId::new(1));
    assert!(!trust_ir_build::validate_module(&bundle.module).is_empty());
    refresh_native_test_bundle_module_identity(&mut bundle);
    assert!(
        runner().solve_bundle_native_proof_grade(&bundle).is_err(),
        "same-shaped distinct nominal types cannot cross a call"
    );
}

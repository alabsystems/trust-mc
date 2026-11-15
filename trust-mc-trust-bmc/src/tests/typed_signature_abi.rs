// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust-ir wire v60's typed signature ABI is refused at every trust-mc entry
//! (`crate::signature_abi`). Each test runs a control first: the same input
//! with the record taken away translates exactly, so the refusal is the
//! record's and nothing else's.

use super::*;
use crate::first_typed_signature_abi;
use crate::trust_ir_function_to_bmc_vc;

/// trust-ir's v60 conformance golden (`tests/fixtures/typed_signature_abi.md`):
/// its one function type, which records a typed ABI trust-ir's validator
/// accepts, and the target it was recorded for.
fn golden_typed_signature() -> (trust_ir::TargetInfo, FuncTy) {
    let module: trust_ir::Module =
        serde_json::from_str(include_str!("../../tests/fixtures/typed_signature_abi.module.json"))
            .expect("the trust-ir v60 golden is a JSON module");
    let signature = module.func_types[0].clone();
    assert!(signature.abi.is_some(), "the golden records a typed ABI");
    (module.target_info.expect("the golden records its target"), signature)
}

fn unrecorded(signature: &FuncTy) -> FuncTy {
    FuncTy { abi: None, ..signature.clone() }
}

const MODES: [TrustMcVerificationMode; 3] = [
    TrustMcVerificationMode::BoundedModelCheck,
    TrustMcVerificationMode::Chc,
    TrustMcVerificationMode::Pdr,
];

fn translate(
    bundle: &NativeVerificationBundle,
    mode: TrustMcVerificationMode,
) -> Result<usize, NativeTrustMcBundleError> {
    let options = TranslateOptions::default();
    match mode {
        TrustMcVerificationMode::BoundedModelCheck => {
            trust_mc_bmc_vcs_from_native_bundle(bundle, &options).map(|rows| rows.len())
        }
        TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {
            trust_mc_chc_pdr_obligations_from_native_bundle(bundle, &options).map(|rows| rows.len())
        }
    }
}

/// The record sits on a row no function and no pointer names, in a bundle
/// trust-ir itself accepts: the boundary still refuses the bundle, by name and
/// before any request is translated, and leaves the bundle as it was.
#[test]
fn a_typed_signature_abi_refuses_the_native_bundle_before_translation() {
    let (target, signature) = golden_typed_signature();
    for mode in MODES {
        let mut bundle = native_trust_mc_bundle(mode);
        bundle.module.target_info = Some(target.clone());
        bundle
            .module
            .add_func_type(unrecorded(&signature))
            .expect("Module::add_func_type: test fixture");
        let row = bundle.module.func_types.len() - 1;
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_eq!(first_typed_signature_abi(&bundle.module), None);
        assert_eq!(translate(&bundle, mode), Ok(1), "{mode:?}: the unrecorded control");

        bundle.module.func_types[row] = signature.clone();
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_eq!(bundle.validate(), Ok(()), "{mode:?}: trust-ir accepts the record");
        let before = bundle.clone();
        assert_eq!(
            translate(&bundle, mode),
            Err(NativeTrustMcBundleError::TypedSignatureAbiNotModeled { func_ty: row }),
            "{mode:?}"
        );
        assert_eq!(bundle, before, "{mode:?}: the refusal keeps the record");
    }
}

/// The direct translators carry no refusal channel, so they fail closed: the
/// CHC encoding of a function that is safe without the record gets an
/// unconditional `error` rule and one diagnostic naming the reason, and its BMC
/// encoding one always-failing violation naming it. The record is again on a
/// row the function does not use.
#[test]
fn a_typed_signature_abi_makes_the_direct_translators_fail_closed() {
    let (target, signature) = golden_typed_signature();
    let mut mb = ModuleBuilder::new("typed_signature_abi_direct");
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    let mut fb = mb.function("identity", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U8);
    fb.ret(vec![x]);
    let function = fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(target);
    let row = module.func_types.len();
    module.add_func_type(unrecorded(&signature)).expect("Module::add_func_type: test fixture");
    let options = TranslateOptions::default();

    let is_error_fact = |rule: &trust_mc_core::chc::Rule| {
        rule.head.name == "error"
            && rule.body.relation.is_none()
            && rule.body.constraints.is_empty()
    };
    let chc = trust_ir_function_to_chc_translation_output(&module, function, &options)
        .expect("the function exists");
    assert!(chc.diagnostics.is_empty(), "control: {:?}", chc.diagnostics);
    assert!(!chc.vc.rules.iter().any(|rule| rule.head.name == "error"), "control");
    let bmc =
        trust_ir_function_to_bmc_vc(&module, function, &options).expect("the function exists");
    assert!(bmc.violations.is_empty(), "control: {:?}", bmc.violations);

    module.func_types[row] = signature;
    let chc = trust_ir_function_to_chc_translation_output(&module, function, &options)
        .expect("the function exists");
    assert_eq!(
        chc.diagnostics.iter().map(|diagnostic| diagnostic.reason).collect::<Vec<_>>(),
        vec![TrustIrChcUnsupportedReason::TypedSignatureAbiTransport]
    );
    assert_eq!(chc.vc.rules.iter().filter(|rule| is_error_fact(rule)).count(), 1);
    let bmc =
        trust_ir_function_to_bmc_vc(&module, function, &options).expect("the function exists");
    assert_eq!(bmc.violations.len(), 1, "{:?}", bmc.violations);
    assert_eq!(bmc.violations[0].condition, Expr::true_());
    let message = bmc.violations[0].message.as_deref().unwrap_or_default();
    assert!(
        message.contains(&format!("typed signature ABI transport (function type #{row})")),
        "{message}"
    );
}

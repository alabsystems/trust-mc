// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Allocation geometry must never become an initialized solver value.

use super::*;
use crate::translate::{UnsupportedSort, checked_ty_to_sort};

fn storage() -> Ty {
    Ty::Storage(trust_ir::StorageLayout::new(16, 8))
}

fn allocation(ty: Ty) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("storage_admission");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("subject", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let no = fb.bool_const(false);
    fb.assume(no);
    fb.alloca(ty);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("allocation geometry is valid IR")
}

fn refusal(module: &trust_ir::Module, invalid: bool) {
    let options = TranslateOptions::default();
    let bmc = trust_ir_to_bmc_vc(module, &options);
    assert_eq!(bmc.len(), 1);
    assert!(bmc[0].decls.is_empty());
    assert!(bmc[0].constraints.is_empty(), "a false assumption cannot hide refusal");
    assert_eq!(bmc[0].violations.len(), 1);
    assert_eq!(bmc[0].violations[0].kind, PropertyKind::Other);
    assert_eq!(bmc[0].violations[0].condition, Expr::true_());
    let outputs = [
        trust_ir_to_chc_translation_outputs(module, &options),
        trust_ir_to_chc_translation_outputs_per_block(module, &options),
    ];
    for outputs in outputs {
        assert_eq!(outputs.len(), 1);
        let output = &outputs[0];
        let reason = output.module_input_refusal.as_deref().expect("explicit refusal");
        assert!(
            reason.starts_with(if invalid {
                "invalid trust_ir module"
            } else {
                "unsupported trust_ir module"
            }),
            "{reason}"
        );
        assert!(output.vc.decls.is_empty());
        assert_eq!(output.work.instructions_translated, 0);
        assert_eq!(output.vc.rules.len(), 1);
        let fact = &output.vc.rules[0];
        assert_eq!(fact.head.name, "error");
        assert!(fact.body.relation.is_none());
        assert!(fact.body.constraints.is_empty());
    }
    for function in &module.functions {
        let selected = crate::trust_ir_function_to_bmc_vc(module, function.id, &options).unwrap();
        assert_eq!(selected.violations[0].condition, Expr::true_());
        assert!(
            trust_ir_function_to_chc_translation_output(module, function.id, &options)
                .unwrap()
                .module_input_refusal
                .is_some()
        );
    }
    assert!(
        crate::trust_ir_function_to_bmc_vc(module, trust_ir::FuncId::new(999), &options).is_none()
    );
    assert!(
        trust_ir_function_to_chc_translation_output(module, trust_ir::FuncId::new(999), &options)
            .is_none()
    );
}

#[test]
fn storage_has_no_sort_or_constant_encoding() {
    assert_eq!(checked_ty_to_sort(&storage()), Err(UnsupportedSort::AddressableStorage));
    assert_eq!(checked_ty_to_sort(&Ty::U64), Ok(ay_bindings::Sort::bitvec(64)));
    assert!(const_to_expr(&storage(), &trust_ir::constant::Constant::Int(0)).is_none());
    assert!(
        const_to_expr(&Ty::Tuple(vec![storage()]), &trust_ir::constant::Constant::Int(0)).is_none()
    );
}

#[test]
fn valid_storage_allocation_refuses_before_any_ssa_or_array_mapping() {
    let control = allocation(Ty::U64);
    assert!(trust_ir_build::validate_module(&control).is_empty());
    let ordinary = trust_ir_to_bmc_vc(&control, &TranslateOptions::default());
    assert!(!ordinary[0].decls.is_empty(), "the initialized scalar control translates");
    let module = allocation(storage());
    assert!(trust_ir_build::validate_module(&module).is_empty());
    refusal(&module, false);
}

#[test]
fn unused_storage_in_empty_module_is_not_an_empty_success_batch() {
    let mut module = ModuleBuilder::new("unused_storage").build().unwrap();
    module.types.push(Ty::PtrConst(Box::new(storage())));
    assert!(trust_ir_build::validate_module(&module).is_empty());
    refusal(&module, false);
}

#[test]
fn unused_by_value_storage_signature_keeps_canonical_invalidity() {
    let mut module = allocation(Ty::U64);
    module.add_func_type(FuncTy::unrecorded(vec![storage()], vec![], false)).unwrap();
    assert!(
        trust_ir_build::validate_module(&module).iter().any(|error| matches!(
            error,
            trust_ir_build::ValidationError::InvalidStorageUse { .. }
        ))
    );
    refusal(&module, true);
}

#[test]
fn native_bmc_chc_and_pdr_refuse_storage_with_a_typed_error() {
    for mode in [
        TrustMcVerificationMode::BoundedModelCheck,
        TrustMcVerificationMode::Chc,
        TrustMcVerificationMode::Pdr,
    ] {
        let mut bundle = native_trust_mc_bundle(mode);
        bundle.module.types.push(storage());
        refresh_native_trust_mc_bundle_module_identity(&mut bundle);
        assert_eq!(bundle.validate(), Ok(()));
        let options = TranslateOptions::default();
        let error = match mode {
            TrustMcVerificationMode::BoundedModelCheck => {
                trust_mc_bmc_vcs_from_native_bundle(&bundle, &options).unwrap_err()
            }
            _ => trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &options).unwrap_err(),
        };
        assert_eq!(error, NativeTrustMcBundleError::AddressableStorageNotModeled);
    }
}

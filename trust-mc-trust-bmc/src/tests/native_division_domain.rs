// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Native opcode-defined division domains, paired with the canonical interpreter.

use super::*;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};

fn constant(fb: &mut trust_ir_build::FunctionBuilder<'_>, ty: &Ty, raw: u8) -> trust_ir::ValueId {
    if ty.is_signed() {
        fb.iconst(ty.clone(), i128::from(raw as i8))
    } else {
        fb.uconst(ty.clone(), u128::from(raw))
    }
}

fn division_module(ty: Ty, op: BinOp, lhs: u8, rhs: u8, wrapping: bool) -> trust_ir::Module {
    division_module_with_caller(ty, op, lhs, rhs, wrapping, false)
}

fn division_module_with_caller(
    ty: Ty,
    op: BinOp,
    lhs: u8,
    rhs: u8,
    wrapping: bool,
    caller: bool,
) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("native_division_domain");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("division", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let lhs = constant(&mut fb, &ty, lhs);
    let rhs = constant(&mut fb, &ty, rhs);
    let proofs = if wrapping { vec![ProofAnnotation::Wrapping] } else { vec![] };
    let result = fb.binop_proven(op, ty.clone(), lhs, rhs, proofs);
    fb.ret(vec![result]);
    let callee = fb.build();
    if caller {
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let result = fb.call(callee, vec![]);
        fb.ret(vec![result]);
        fb.build();
    }
    let module = mb.build().expect("division fixture");
    assert_canonical_module(&module);
    module
}

fn assert_original_ub(module: &trust_ir::Module, function: trust_ir::FuncId) {
    let error = Interpreter::with_module(module).execute_func(function, []).unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
}

#[test]
fn native_division_domain_u8_bmc() {
    for op in [BinOp::SDiv, BinOp::SRem] {
        let module = division_module(Ty::U8, op, 128, 255, false);
        assert_original_ub(&module, trust_ir::FuncId::new(0));
        let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
        let overflow: Vec<_> = vcs[0]
            .violations
            .iter()
            .filter(|v| v.kind == PropertyKind::ArithmeticOverflow)
            .collect();
        assert_eq!(overflow.len(), 1, "{op:?} has a signed domain even on U8");
        assert!(bmc_violation_is_satisfiable(&vcs[0], overflow[0]));
    }
}

#[test]
fn native_division_domain_u8_chc() {
    for op in [BinOp::SDiv, BinOp::SRem] {
        let module = division_module(Ty::U8, op, 128, 255, false);
        assert_original_ub(&module, trust_ir::FuncId::new(0));
        let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
        assert!(outputs[0].diagnostics.is_empty());
        assert!(
            outputs[0].vc.rules.iter().any(|rule| rule.head.name == "error"
                && rule.body.constraints.iter().any(|constraint| expr_tree_has(
                    constraint,
                    &|value| matches!(value, ExprValue::BvSdivNoOverflow(_, _))
                ))),
            "{op:?} has a signed domain even on U8"
        );
        assert!(some_error_rule_is_satisfiable(&outputs[0]));
    }
}

fn policies() -> [TranslateOptions; 2] {
    [
        TranslateOptions::default(),
        TranslateOptions {
            check_signed_overflow: false,
            check_unsigned_overflow: false,
            check_div_by_zero: false,
            ..TranslateOptions::default()
        },
    ]
}

fn check_case(module: &trust_ir::Module, options: &TranslateOptions, expected: Option<u8>) {
    if let Some(expected) = expected {
        let result = Interpreter::with_module(module)
            .execute_func(trust_ir::FuncId::new(0), [])
            .expect("canonical division is defined");
        assert_eq!(result.host_calls, 0);
        assert_eq!(result.returns.len(), 1);
        assert_eq!(result.returns[0].as_int().unwrap().raw, u128::from(expected));
    } else {
        assert_original_ub(module, trust_ir::FuncId::new(0));
    }
    let vcs = trust_ir_to_bmc_vc(module, options);
    assert_eq!(vcs.len(), 1);
    assert!(vcs[0].violations.iter().all(|v| v.kind != PropertyKind::Other));
    let actual_error = vcs[0].violations.iter().any(|v| bmc_violation_is_satisfiable(&vcs[0], v));
    assert_eq!(actual_error, expected.is_none(), "BMC must match canonical definedness");
    let outputs = trust_ir_to_chc_translation_outputs(module, options);
    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].module_input_refusal.is_none());
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    assert_eq!(
        some_error_rule_is_satisfiable(&outputs[0]),
        expected.is_none(),
        "CHC must match canonical definedness"
    );
}

#[test]
fn native_division_domain_minimum_overflow_matrix() {
    for ty in [Ty::U8, Ty::I8] {
        for op in [BinOp::SDiv, BinOp::SRem] {
            for wrapping in [false, true] {
                let module = division_module(ty.clone(), op, 128, 255, wrapping);
                for options in policies() {
                    check_case(&module, &options, None);
                }
            }
        }
    }
}

#[test]
fn native_division_domain_safe_and_unsigned_controls() {
    for ty in [Ty::U8, Ty::I8] {
        for (op, rhs, result) in [
            (BinOp::SDiv, 1, 128),
            (BinOp::SRem, 1, 0),
            (BinOp::SDiv, 2, 192),
            (BinOp::SRem, 3, 254),
            (BinOp::UDiv, 255, 0),
            (BinOp::URem, 255, 128),
        ] {
            for wrapping in [false, true] {
                let module = division_module(ty.clone(), op, 128, rhs, wrapping);
                for options in policies() {
                    check_case(&module, &options, Some(result));
                }
            }
        }
    }
}

#[test]
fn native_division_domain_zero_is_mandatory() {
    for ty in [Ty::U8, Ty::I8] {
        for op in [BinOp::SDiv, BinOp::SRem, BinOp::UDiv, BinOp::URem] {
            for wrapping in [false, true] {
                let module = division_module(ty.clone(), op, 128, 0, wrapping);
                for options in policies() {
                    check_case(&module, &options, None);
                }
            }
        }
    }
}

#[test]
fn native_division_domain_chc_direct_call_summary() {
    for ty in [Ty::U8, Ty::I8] {
        for (op, rhs, undefined) in [
            (BinOp::SDiv, 255, true),
            (BinOp::SRem, 255, true),
            (BinOp::SDiv, 0, true),
            (BinOp::SRem, 0, true),
            (BinOp::UDiv, 0, true),
            (BinOp::URem, 0, true),
            (BinOp::SDiv, 1, false),
            (BinOp::SRem, 1, false),
            (BinOp::UDiv, 255, false),
            (BinOp::URem, 255, false),
        ] {
            for wrapping in [false, true] {
                let module = division_module_with_caller(ty.clone(), op, 128, rhs, wrapping, true);
                assert_canonical_module(&module);
                let canonical =
                    Interpreter::with_module(&module).execute_func(trust_ir::FuncId::new(1), []);
                if undefined {
                    assert_eq!(canonical.unwrap_err().code, InterpretErrorCode::UndefinedBehavior);
                } else {
                    canonical.expect("defined original caller");
                }
                for options in policies() {
                    let output = trust_ir_function_to_chc_translation_output(
                        &module,
                        trust_ir::FuncId::new(1),
                        &options,
                    )
                    .expect("caller selected");
                    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
                    assert!(!declined_direct_call_summary(&output));
                    assert_eq!(
                        some_error_rule_is_satisfiable(&output),
                        undefined,
                        "callee {op:?}/{ty:?} wrapping={wrapping} domain must survive call summary"
                    );
                }
            }
        }
    }
}

#[test]
fn native_division_domain_bundle_admission_keeps_safety_obligations() {
    for ty in [Ty::U8, Ty::I8] {
        for op in [BinOp::SDiv, BinOp::SRem] {
            let original = division_module(ty.clone(), op, 128, 255, true);
            for mode in [TrustMcVerificationMode::BoundedModelCheck, TrustMcVerificationMode::Chc] {
                let mut bundle = native_trust_mc_bundle(mode);
                let mut function = original.functions[0].clone();
                function.id = trust_ir::FuncId::new(1);
                function.ty = bundle.module.functions[1].ty;
                bundle.module.func_types[function.ty.as_usize()] = original.func_types[0].clone();
                bundle.module.functions[1] = function;
                refresh_native_trust_mc_bundle_module_identity(&mut bundle);
                bundle.validate().expect("original typed native bundle must validate");
                assert_canonical_module(&bundle.module);
                assert_original_ub(&bundle.module, trust_ir::FuncId::new(1));
                match mode {
                    TrustMcVerificationMode::BoundedModelCheck => {
                        let vcs = trust_mc_bmc_vcs_from_native_bundle(&bundle, &policies()[1])
                            .expect("native BMC admission");
                        assert_eq!(vcs.len(), 1);
                        let overflow = vcs[0]
                            .vc
                            .violations
                            .iter()
                            .find(|v| v.kind == PropertyKind::ArithmeticOverflow)
                            .expect("original signed-div/rem overflow obligation");
                        assert!(bmc_violation_is_satisfiable(&vcs[0].vc, overflow));
                    }
                    TrustMcVerificationMode::Chc => {
                        let obligations = trust_mc_chc_pdr_obligations_from_native_bundle(
                            &bundle,
                            &policies()[1],
                        )
                        .expect("native CHC admission");
                        assert_eq!(obligations.len(), 1);
                        assert!(obligations[0].obligation.vc.rules.iter().any(
                            |rule| rule.head.name == "error"
                                && rule.body.constraints.iter().any(|expr| expr_tree_has(
                                    expr,
                                    &|value| matches!(value, ExprValue::BvSdivNoOverflow(_, _))
                                ))
                        ));
                    }
                    TrustMcVerificationMode::Pdr => unreachable!(),
                }
            }
        }
    }
}

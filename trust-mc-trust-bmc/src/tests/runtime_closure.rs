// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{Block, BlockId, ClosureTy, FuncId, Function, Inst, InstrNode, Module, ValueId};

/// An unused runtime closure still consumes its captures. Its target has the
/// required physical signature (captures followed by apparent parameters).
fn fixture(capture_count: usize, poison: bool, construct: bool) -> Module {
    let mut mb = ModuleBuilder::new("runtime_closure_refusal");
    let apparent = mb.add_func_type(vec![], vec![]);
    let physical = mb.add_func_type(vec![Ty::I64; capture_count], vec![]);
    let host = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let closure = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::I64; capture_count],
    });
    let mut module = mb.build().unwrap();
    let mut function = Function::new(FuncId::new(0), "host", host, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::I64));
    let capture = if poison {
        block.body.push(InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(ValueId::new(1)));
        ValueId::new(1)
    } else {
        ValueId::new(0)
    };
    if construct {
        block.body.push(
            InstrNode::new(Inst::MakeClosure {
                ty: closure,
                func: FuncId::new(1),
                captures: vec![capture; capture_count],
            })
            .with_result(ValueId::new(2)),
        );
    }
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let mut target = Function::new(FuncId::new(1), "closure_target", physical, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = (0..capture_count)
        .map(|index| (ValueId::new(u32::try_from(index).unwrap()), Ty::I64))
        .collect();
    block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    target.blocks.push(block);
    module.try_add_function(target).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn check_refusal(module: &Module) {
    let outputs = trust_ir_to_chc_translation_outputs(module, &TranslateOptions::default());
    let diagnostics: Vec<_> = outputs[0]
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::ClosureConstruction)
        .collect();
    assert_eq!(diagnostics.len(), 1, "{:?}", outputs[0].diagnostics);
    assert_eq!(diagnostics[0].family, SemanticsFamily::Closures);
    assert_eq!(diagnostics[0].result_values, vec![ValueId::new(2)]);
    assert_eq!(error_rule_solver_verdicts(&outputs[0].vc), vec![Some(true)]);
    let vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    let violations: Vec<_> = vcs[0]
        .violations
        .iter()
        .filter(|violation| {
            violation.kind == PropertyKind::Other
                && violation.message.as_deref().is_some_and(|m| m.contains("MakeClosure construction"))
        })
        .collect();
    assert_eq!(violations.len(), 1, "{:?}", vcs[0].violations);
    assert_eq!(violations[0].condition, Expr::true_());
}

#[test]
fn runtime_closure_unused_construction_refuses_empty_and_repeated_captures() {
    assert_eq!(
        coverage_for_family(SemanticsFamily::Closures).status,
        SemanticsStatus::FailClosedUnsupported
    );
    for capture_count in [0, 1, 3] {
        let module = fixture(capture_count, false, true);
        let run = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [InterpretValue::int(Ty::I64, 21).unwrap()])
            .unwrap();
        assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 21);
        check_refusal(&module);
    }
}

#[test]
fn runtime_closure_unused_poison_capture_is_real_ub_and_refused() {
    let module = fixture(1, true, true);
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [InterpretValue::int(Ty::I64, 21).unwrap()])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
    check_refusal(&module);
}

#[test]
fn runtime_closure_absent_constructor_keeps_the_scalar_control_supported() {
    let module = fixture(1, false, false);
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    assert!(error_rule_solver_verdicts(&outputs[0].vc).is_empty());
    assert!(trust_ir_to_bmc_vc(&module, &TranslateOptions::default())[0].violations.is_empty());
}

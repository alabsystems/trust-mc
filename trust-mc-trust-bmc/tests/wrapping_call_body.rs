// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::proof::ProofAnnotation;
use trust_ir::{FuncId, Module, Ty};
use trust_ir_build::ModuleBuilder;
use trust_mc_trust_bmc::{
    ChcTranslationOutput, TranslateOptions, trust_ir_function_to_chc_translation_output,
};

// These fixtures have one straight-line entry block and no input parameters.
// Its entry relation is a fact, so each error clause is reachable exactly when
// its constraints are satisfiable. Use the real AY bitvector solver; this is a
// runtime differential control, not a source/kernel correspondence certificate.
fn error_reachable(output: &ChcTranslationOutput) -> bool {
    if output.module_input_refusal.is_some() {
        assert_eq!(output.vc.rules.len(), 1, "input refusal is one ownerless error fact");
        let rule = &output.vc.rules[0];
        assert_eq!(rule.head.name, "error");
        assert!(rule.body.relation.is_none());
        assert!(rule.body.constraints.is_empty());
        return true;
    }
    let entries: Vec<_> = output
        .vc
        .rules
        .iter()
        .filter(|rule| {
            rule.head.name != "error"
                && rule.body.relation.is_none()
                && rule.body.constraints.is_empty()
        })
        .collect();
    assert_eq!(entries.len(), 1, "one unconditional entry fact is required");
    let entry = &entries[0].head;
    assert!(entry.args.is_empty(), "the fixture must have no input parameters");
    output.vc.rules.iter().filter(|rule| rule.head.name == "error").any(|rule| {
        assert_eq!(
            rule.body.relation.as_ref(),
            Some(entry),
            "an error may depend only on the unconditional entry fact"
        );
        let mut program = ay_bindings::AYProgram::new();
        program.set_logic("QF_BV");
        for variable in output.vc.vars() {
            let _ = program.declare_const(&*variable.name, variable.sort.clone());
        }
        for condition in &rule.body.constraints {
            program.assert(condition.clone());
        }
        program.check_sat();
        match ay_bindings::execute_direct::execute(&program).unwrap() {
            ay_bindings::execute_direct::ExecuteResult::Verified => false,
            ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
            other => panic!("native error query was incomplete: {other:?}"),
        }
    })
}

fn translate(module: &Module, function: FuncId) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output(module, function, &TranslateOptions::default())
        .unwrap()
}

fn named_call(
    name: &str,
    declaration: bool,
    (lhs, rhs): (i128, i128),
    expected: i128,
) -> (Module, FuncId) {
    let mut builder = ModuleBuilder::new("named_wrapping_body");
    let signature = builder.add_func_type(vec![Ty::U8, Ty::U8], vec![Ty::U8]);
    let callee = if declaration {
        builder.declare_function(name, signature)
    } else {
        let mut callee = builder.function(name, signature);
        let entry = callee.create_block();
        callee.add_block_param(entry, Ty::U8);
        callee.add_block_param(entry, Ty::U8);
        callee.switch_to_block(entry);
        let zero = callee.iconst(Ty::U8, 0);
        callee.ret(vec![zero]);
        callee.build()
    };
    let signature = builder.add_func_type(vec![], vec![]);
    let mut caller = builder.function("caller", signature);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    let lhs = caller.iconst(Ty::U8, lhs);
    let rhs = caller.iconst(Ty::U8, rhs);
    let actual = caller.call(callee, vec![lhs, rhs]);
    let expected = caller.iconst(Ty::U8, expected);
    let matches = caller.icmp(ICmpOp::Eq, Ty::U8, actual, expected);
    caller.assert(matches);
    caller.ret(vec![]);
    let caller = caller.build();
    (builder.build().unwrap(), caller)
}

#[test]
fn exact_b8d_counterexample_must_reach_the_error_query() {
    let (module, caller) = named_call("fake::wrapping_add", false, (1, 1), 2);
    assert_eq!(
        Interpreter::with_module(&module).execute_func(caller, []).unwrap_err().code,
        InterpretErrorCode::Panic
    );
    let output = translate(&module, caller);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert!(error_reachable(&output));
}

#[test]
fn user_wrapping_names_obey_their_body_not_arithmetic_guessed_from_a_name() {
    for (name, guessed) in
        [("fake::wrapping_add", 4), ("fake::wrapping_sub", 2), ("fake::wrapping_mul", 3)]
    {
        for expected in [0, guessed] {
            let (module, caller) = named_call(name, false, (3, 1), expected);
            let runtime = Interpreter::with_module(&module).execute_func(caller, []);
            if expected == 0 {
                runtime.unwrap();
            } else {
                assert_eq!(runtime.unwrap_err().code, InterpretErrorCode::Panic);
            }
            let output = translate(&module, caller);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert_eq!(error_reachable(&output), expected != 0, "{name}, expected={expected}");
        }
    }
}

#[test]
fn even_core_looking_wrapping_declarations_are_not_authenticated_intrinsics() {
    for name in [
        "fake::wrapping_add",
        "core::num::<impl u8>::wrapping_add",
        "core::num::<impl u8>::wrapping_sub",
        "core::num::<impl u8>::wrapping_mul",
    ] {
        let (module, caller) = named_call(name, true, (3, 1), 4);
        // A bodyless local declaration has no authenticated external import.
        // The whole-module gate refuses it before call-summary translation.
        assert!(!trust_ir_build::validate_module(&module).is_empty());
        let output = translate(&module, caller);
        assert!(output.module_input_refusal.is_some(), "{name}");
        assert!(output.diagnostics.is_empty(), "invalidity has no invented call site");
        assert!(error_reachable(&output), "a declaration must not manufacture safety: {name}");
    }
}

#[test]
fn wrapping_tagged_arithmetic_keeps_modular_semantics_directly_and_in_bodies() {
    for (op, lhs, rhs, wrapped) in
        [(BinOp::Add, 255, 1, 0), (BinOp::Sub, 0, 1, 255), (BinOp::Mul, 128, 2, 0)]
    {
        for via_callee in [false, true] {
            let mut builder = ModuleBuilder::new("real_wrapping_operation");
            let callee = if via_callee {
                let signature = builder.add_func_type(vec![Ty::U8, Ty::U8], vec![Ty::U8]);
                let mut function = builder.function("ordinary_arithmetic_body", signature);
                let entry = function.create_block();
                let a = function.add_block_param(entry, Ty::U8);
                let b = function.add_block_param(entry, Ty::U8);
                function.switch_to_block(entry);
                let value = function.binop(op, Ty::U8, a, b);
                function.annotate_last(ProofAnnotation::Wrapping).unwrap();
                function.ret(vec![value]);
                Some(function.build())
            } else {
                None
            };
            let signature = builder.add_func_type(vec![], vec![]);
            let mut caller = builder.function("caller", signature);
            let entry = caller.create_block();
            caller.switch_to_block(entry);
            let lhs = caller.iconst(Ty::U8, lhs);
            let rhs = caller.iconst(Ty::U8, rhs);
            let actual = if let Some(callee) = callee {
                caller.call(callee, vec![lhs, rhs])
            } else {
                let value = caller.binop(op, Ty::U8, lhs, rhs);
                caller.annotate_last(ProofAnnotation::Wrapping).unwrap();
                value
            };
            let expected = caller.iconst(Ty::U8, wrapped);
            let matches = caller.icmp(ICmpOp::Eq, Ty::U8, actual, expected);
            caller.assert(matches);
            caller.ret(vec![]);
            let caller = caller.build();
            let module = builder.build().unwrap();
            Interpreter::with_module(&module).execute_func(caller, []).unwrap();
            let output = translate(&module, caller);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert!(!error_reachable(&output), "{op:?}, via_callee={via_callee}");
        }
    }
}

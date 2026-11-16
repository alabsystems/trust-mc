// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Opcode-defined Bool resize values, paired with the canonical IR interpreter.
//! These are translator diagnostics; no native proof-admission gate is widened.

use super::*;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};

fn expected_raw(op: CastOp, input: bool, width: u32) -> u128 {
    if !input {
        0
    } else if op == CastOp::SExt {
        if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
    } else {
        1
    }
}

fn integer_constant(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    ty: &Ty,
    raw: u128,
) -> trust_ir::ValueId {
    if ty.is_signed() {
        let width = ty.bit_width_with(64).unwrap();
        let value = if width == 128 {
            raw as i128
        } else {
            ((raw << (128 - width)) as i128) >> (128 - width)
        };
        fb.iconst(ty.clone(), value)
    } else {
        fb.uconst(ty.clone(), raw)
    }
}

fn resize_module(op: CastOp, ty: Ty, input: bool, claim: u128, caller: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("native_bool_resize");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("resize", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let boolean = fb.bool_const(input);
    let result = fb.cast(op, Ty::Bool, ty.clone(), boolean);
    if !caller {
        let expected = integer_constant(&mut fb, &ty, claim);
        let equals = fb.icmp(ICmpOp::Eq, ty.clone(), result, expected);
        fb.assert(equals);
    }
    fb.ret(vec![result]);
    let callee = fb.build();
    if caller {
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let result = fb.call(callee, vec![]);
        let expected = integer_constant(&mut fb, &ty, claim);
        let equals = fb.icmp(ICmpOp::Eq, ty, result, expected);
        fb.assert(equals);
        fb.ret(vec![result]);
        fb.build();
    }
    let module = mb.build().expect("Bool resize fixture");
    assert_canonical_module(&module);
    module
}

// These fixtures have one unconstrained entry and no branches. Their error
// constraints are the complete reachability question; a nonterminal solver
// outcome must never count as a safe value.
fn error_is_satisfiable(output: &ChcTranslationOutput) -> bool {
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
        match ay_bindings::execute_direct::execute(&program).expect("actual AY resize query") {
            ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
            ay_bindings::execute_direct::ExecuteResult::Verified => false,
            other => panic!("nonterminal resize query: {other:?}"),
        }
    })
}

fn check(op: CastOp, ty: Ty, input: bool, claim: u128, caller: bool) {
    let width = ty.bit_width_with(64).unwrap();
    let expected = expected_raw(op, input, width);
    let module = resize_module(op, ty, input, claim, caller);
    let function = trust_ir::FuncId::new(u32::from(caller));
    let canonical = Interpreter::with_module(&module).execute_func(function, []);
    if claim == expected {
        let outcome = canonical.expect("canonical resize satisfies this exact value");
        assert_eq!(outcome.host_calls, 0);
        assert_eq!(outcome.returns[0].as_int().unwrap().raw, expected);
    } else {
        assert_eq!(canonical.unwrap_err().code, InterpretErrorCode::Panic);
    }
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        function,
        &TranslateOptions::default(),
    )
    .unwrap();
    assert!(output.module_input_refusal.is_none());
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert_eq!(
        error_is_satisfiable(&output),
        claim != expected,
        "CHC must preserve the canonical cast's value, including a false-claim error"
    );
}

#[test]
fn chc_bool_sign_extension_refutes_zero_extension_claim() {
    // The old opcode-agnostic bool arm returned one and made this real
    // canonical panic disappear. This is not a source-authority claim.
    check(CastOp::SExt, Ty::I8, true, 1, false);
}

#[test]
fn chc_bool_resize_matches_canonical_true_false_and_widths() {
    for ty in [Ty::I8, Ty::U8, Ty::I16, Ty::U16, Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in [CastOp::ZExt, CastOp::SExt] {
            for input in [false, true] {
                let expected = expected_raw(op, input, ty.bit_width_with(64).unwrap());
                check(op, ty.clone(), input, expected, false);
                check(op, ty.clone(), input, expected ^ 1, false);
            }
        }
    }
}

#[test]
fn chc_bool_resize_direct_call_summary_uses_the_same_opcode_rules() {
    for ty in [Ty::I8, Ty::U8, Ty::I64, Ty::U64] {
        for op in [CastOp::ZExt, CastOp::SExt] {
            for input in [false, true] {
                let expected = expected_raw(op, input, ty.bit_width_with(64).unwrap());
                check(op, ty.clone(), input, expected, true);
                check(op, ty.clone(), input, expected ^ 1, true);
            }
        }
    }
}

#[test]
fn bmc_bool_resize_keeps_its_existing_explicit_refusal() {
    for op in [CastOp::ZExt, CastOp::SExt] {
        let module = resize_module(op, Ty::I8, true, expected_raw(op, true, 8), false);
        let vcs = trust_ir_to_bmc_vc(&module, &TranslateOptions::default());
        assert_eq!(vcs.len(), 1);
        assert!(vcs[0].violations.iter().any(|violation| {
            violation.kind == PropertyKind::Other
                && violation
                    .message
                    .as_deref()
                    .is_some_and(|message| message.contains("cast operation"))
        }));
    }
}

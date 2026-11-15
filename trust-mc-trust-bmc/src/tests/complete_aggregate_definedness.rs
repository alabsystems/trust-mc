// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::value::FuncId;

fn checked_outputs(module: &trust_ir::Module) -> Vec<ChcTranslationOutput> {
    assert!(trust_ir_build::validate_module(module).is_empty());
    trust_ir_to_chc_translation_outputs(
        module,
        &TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() },
    )
}

fn refuses_definedness(output: &ChcTranslationOutput) {
    assert!(
        output.diagnostics.iter().any(|diagnostic| {
            diagnostic.reason == TrustIrChcUnsupportedReason::AggregateOperandDefinedness
        }),
        "{:?}",
        output.diagnostics
    );
    assert!(unconditionally_reachable_error_rules(&output.vc) >= 1);
}

fn interpreter_ub(module: &trust_ir::Module, function: FuncId) {
    let error = Interpreter::with_module(module).execute_func(function, []).unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
}

#[test]
fn make_aggregate_scalar_undef_copied_operand_is_real_ub_and_refused() {
    let mut mb = ModuleBuilder::new("make_aggregate_poison_copy");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("poison", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let poison = fb.undef(Ty::I64);
    let copied = fb.copy(Ty::I64, poison);
    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![copied]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    interpreter_ub(&module, FuncId::new(0));
    refuses_definedness(&outputs[0]);
}

#[test]
fn make_aggregate_nested_uninit_projection_is_real_ub_and_refused() {
    let mut mb = ModuleBuilder::new("make_aggregate_nested_uninit");
    let inner_ty = Ty::Tuple(vec![Ty::I64]);
    let outer_ty = Ty::Tuple(vec![inner_ty.clone()]);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("unwritten", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let inner = fb.const_value(inner_ty.clone(), Constant::Aggregate(vec![Constant::Uninit]));
    let copied = fb.copy(inner_ty.clone(), inner);
    let outer = fb.make_aggregate(outer_ty, vec![copied]);
    let inner = fb.extract_field(inner_ty, outer, 0);
    let unwritten = fb.extract_field(Ty::I64, inner, 0);
    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![unwritten]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    // Embedding the partial inner value transports it; its lane read is the
    // canonical UB. Conservative refusal may occur before that read.
    interpreter_ub(&module, FuncId::new(0));
    refuses_definedness(&outputs[0]);
}

#[test]
fn make_aggregate_complete_initialization_and_projections_execute_and_prove() {
    let mut mb = ModuleBuilder::new("make_aggregate_defined_nested");
    let inner_ty = Ty::Tuple(vec![Ty::I64, Ty::Bool]);
    let outer_ty = Ty::Tuple(vec![inner_ty.clone()]);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("complete", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let seven = fb.iconst(Ty::I64, 7);
    let flag = fb.bool_const(false);
    let inner = fb.make_aggregate(inner_ty.clone(), vec![seven, flag]);
    let copied = fb.copy(inner_ty.clone(), inner);
    let outer = fb.make_aggregate(outer_ty, vec![copied]);
    let inner = fb.extract_field(inner_ty, outer, 0);
    let result = fb.extract_field(Ty::I64, inner, 0);
    let equal = fb.icmp(ICmpOp::Eq, Ty::I64, result, seven);
    fb.assert(equal);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    let run = Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
    assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    assert_eq!(error_rule_solver_verdicts(&outputs[0].vc), vec![Some(false)]);
}

#[test]
fn make_aggregate_phi_checks_every_predecessor_including_poison() {
    for poison in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_phi_definedness");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("phi", ft);
        let entry = fb.create_block();
        let good = fb.create_block();
        let bad = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);
        let incoming = fb.add_block_param(join, Ty::I64);
        fb.switch_to_block(entry);
        let cond = fb.bool_const(false);
        fb.condbr(cond, good, vec![], bad, vec![]);
        fb.switch_to_block(good);
        let seven = fb.iconst(Ty::I64, 7);
        fb.br(join, vec![seven]);
        fb.switch_to_block(bad);
        let other = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 9) };
        fb.br(join, vec![other]);
        fb.switch_to_block(join);
        fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![incoming]);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if poison {
            interpreter_ub(&module, FuncId::new(0));
            assert!(outputs[0].diagnostics.iter().any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::AggregateOperandDefinedness
            }));
        } else {
            Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
            assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
        }
    }
}

#[test]
fn make_aggregate_cyclic_phi_does_not_assume_initialized() {
    let mut mb = ModuleBuilder::new("make_aggregate_cycle");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("cycle", ft);
    let entry = fb.create_block();
    let again = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let carried = fb.add_block_param(again, Ty::I64);
    fb.switch_to_block(entry);
    let seven = fb.iconst(Ty::I64, 7);
    fb.br(again, vec![seven]);
    fb.switch_to_block(again);
    let cond = fb.bool_const(false);
    fb.condbr(cond, again, vec![carried], exit, vec![]);
    fb.switch_to_block(exit);
    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![carried]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
    assert!(
        outputs[0].diagnostics.is_empty(),
        "an initialized seed supports the actual recurrence"
    );
    let mut module = module;
    module.functions[0].blocks[0].body[0].inst = trust_ir::Inst::Undef { ty: Ty::I64 };
    interpreter_ub(&module, FuncId::new(0));
    let outputs = checked_outputs(&module);
    assert!(
        outputs[0].diagnostics.iter().any(|diagnostic| {
            diagnostic.reason == TrustIrChcUnsupportedReason::AggregateOperandDefinedness
        }),
        "a back edge never establishes its own initialization"
    );
}

#[test]
fn make_aggregate_summary_keeps_actual_definedness_through_nested_calls() {
    for poison in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_nested_call_definedness");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("construct", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = fb.add_block_param(entry, Ty::I64);
        let made = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![input]);
        let result = fb.extract_field(Ty::I64, made, 0);
        fb.ret(vec![result]);
        fb.build();
        let mut fb = mb.function("forward", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = fb.add_block_param(entry, Ty::I64);
        let result = fb.call(FuncId::new(0), vec![input]);
        fb.ret(vec![result]);
        fb.build();
        let caller_ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("caller", caller_ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let actual = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 7) };
        fb.call(FuncId::new(1), vec![actual]);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if poison {
            interpreter_ub(&module, FuncId::new(2));
            assert!(
                outputs[2].diagnostics.iter().any(|diagnostic| {
                    diagnostic.reason == TrustIrChcUnsupportedReason::CallArgumentTransport
                }),
                "fresh scalar summary bindings must not erase poison actuals"
            );
            assert!(unconditionally_reachable_error_rules(&outputs[2].vc) >= 1);
        } else {
            Interpreter::with_module(&module).execute_func(FuncId::new(2), []).unwrap();
            assert!(outputs.iter().all(|output| output.diagnostics.is_empty()));
        }
    }
}

#[test]
fn make_aggregate_refuses_recursively_opaque_parameter_fields() {
    for array in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_nested_opaque");
        let opaque = Ty::FatPtr(FatPtrKind::ContainerVtable);
        let field_ty = if array {
            let opaque_id = mb.add_type(opaque);
            Ty::Array(opaque_id, 2)
        } else {
            Ty::Tuple(vec![opaque])
        };
        let aggregate_ty = Ty::Tuple(vec![field_ty.clone()]);
        let ft = mb.add_func_type(vec![field_ty.clone()], vec![]);
        let mut fb = mb.function("opaque", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let field = fb.add_block_param(entry, field_ty);
        fb.make_aggregate(aggregate_ty, vec![field]);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        assert_eq!(outputs[0].diagnostics.len(), 1);
        assert_eq!(
            outputs[0].diagnostics[0].reason,
            TrustIrChcUnsupportedReason::AggregateOpaqueValue
        );
        assert!(unconditionally_reachable_error_rules(&outputs[0].vc) >= 1);
    }
}

#[test]
fn make_aggregate_completed_partial_seed_executes_and_preserves_written_fields() {
    let mut mb = ModuleBuilder::new("make_aggregate_completed_partial");
    let inner_ty = Ty::Tuple(vec![Ty::I64, Ty::Bool]);
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("complete_partial", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let seed = fb.const_value(inner_ty.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
    let seven = fb.iconst(Ty::I64, 7);
    let flag = fb.bool_const(false);
    let initialized = fb.insert_field(inner_ty.clone(), seed, 0, seven);
    let initialized = fb.insert_field(inner_ty.clone(), initialized, 1, flag);
    let outer = fb.make_aggregate(Ty::Tuple(vec![inner_ty.clone()]), vec![initialized]);
    let inner = fb.extract_field(inner_ty, outer, 0);
    let result = fb.extract_field(Ty::I64, inner, 0);
    let equal = fb.icmp(ICmpOp::Eq, Ty::I64, result, seven);
    fb.assert(equal);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    let run = Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
    assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
    assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
    assert_eq!(error_rule_solver_verdicts(&outputs[0].vc), vec![Some(false)]);
}

#[test]
fn make_aggregate_overwritten_aggregate_undef_is_not_a_valid_seed() {
    let mut mb = ModuleBuilder::new("make_aggregate_invalid_undef_seed");
    let inner_ty = Ty::Tuple(vec![Ty::I64]);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("invalid_seed", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let seed = fb.undef(inner_ty.clone());
    let seven = fb.iconst(Ty::I64, 7);
    let initialized = fb.insert_field(inner_ty.clone(), seed, 0, seven);
    fb.make_aggregate(Ty::Tuple(vec![inner_ty]), vec![initialized]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    interpreter_ub(&module, FuncId::new(0));
    refuses_definedness(&outputs[0]);
}

#[test]
fn make_aggregate_callee_poison_return_does_not_become_initialized() {
    let mut mb = ModuleBuilder::new("make_aggregate_poison_return");
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("poison_return", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let poison = fb.undef(Ty::I64);
    fb.ret(vec![poison]);
    fb.build();
    let caller_ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("caller", caller_ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let actual = fb.call(FuncId::new(0), vec![]);
    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![actual]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    interpreter_ub(&module, FuncId::new(1));
    refuses_definedness(&outputs[1]);
}

#[test]
fn make_aggregate_aggregate_parameter_needs_actual_initialization_custody() {
    for unwritten in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_partial_parameter");
        let input_ty = Ty::Tuple(vec![Ty::I64]);
        let ft = mb.add_func_type(vec![input_ty.clone()], vec![Ty::I64]);
        let mut fb = mb.function("project_and_construct", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = fb.add_block_param(entry, input_ty.clone());
        let lane = fb.extract_field(Ty::I64, input, 0);
        let result = fb.make_aggregate(input_ty.clone(), vec![lane]);
        let result = fb.extract_field(Ty::I64, result, 0);
        fb.ret(vec![result]);
        fb.build();
        let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("caller", caller_ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = if unwritten {
            fb.const_value(input_ty, Constant::Aggregate(vec![Constant::Uninit]))
        } else {
            let seven = fb.iconst(Ty::I64, 7);
            fb.make_aggregate(input_ty, vec![seven])
        };
        let result = fb.call(FuncId::new(0), vec![input]);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        // A standalone aggregate argument can transport an unwritten lane;
        // its declared type is not initialization evidence for the projection.
        refuses_definedness(&outputs[0]);
        if unwritten {
            interpreter_ub(&module, FuncId::new(1));
            assert!(outputs[1].diagnostics.iter().any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
            }));
        } else {
            let run = Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap();
            assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
            assert!(outputs[1].diagnostics.is_empty(), "{:?}", outputs[1].diagnostics);
        }
    }
}

#[test]
fn make_aggregate_unused_poison_call_argument_cannot_disappear() {
    for mode in 0..3 {
        for poison in [false, true] {
            let mut mb = ModuleBuilder::new("make_aggregate_unused_argument");
            let inner_ft = mb.add_func_type(vec![], vec![Ty::I64]);
            let mut fb = mb.function("inner_constructor", inner_ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let seven = fb.iconst(Ty::I64, 7);
            let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
            let result = fb.extract_field(Ty::I64, aggregate, 0);
            fb.ret(vec![result]);
            fb.build();
            let callee_ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("ignores_argument", callee_ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            fb.add_block_param(entry, Ty::I64);
            let seven = fb.iconst(Ty::I64, 7);
            let result = match mode {
                0 => seven,
                1 => {
                    let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
                    fb.extract_field(Ty::I64, aggregate, 0)
                }
                2 => fb.call(FuncId::new(0), vec![]),
                _ => unreachable!(),
            };
            fb.ret(vec![result]);
            fb.build();
            let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
            let mut fb = mb.function("caller", caller_ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let argument = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 9) };
            let returned = fb.call(FuncId::new(1), vec![argument]);
            let result = if mode == 0 {
                let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![returned]);
                fb.extract_field(Ty::I64, aggregate, 0)
            } else {
                returned
            };
            fb.ret(vec![result]);
            fb.build();
            let module = mb.build().unwrap();
            let outputs = checked_outputs(&module);
            if poison {
                interpreter_ub(&module, FuncId::new(2));
                if mode == 0 {
                    refuses_definedness(&outputs[2]);
                } else {
                    assert!(
                        outputs[2].diagnostics.iter().any(|diagnostic| {
                            diagnostic.reason == TrustIrChcUnsupportedReason::CallArgumentTransport
                        }),
                        "ancestor call consumption cannot disappear before a nested constructor"
                    );
                }
            } else {
                let run =
                    Interpreter::with_module(&module).execute_func(FuncId::new(2), []).unwrap();
                assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
                assert!(outputs.iter().all(|output| output.diagnostics.is_empty()));
            }
        }
    }
}

#[test]
fn make_aggregate_discarded_earlier_call_keeps_poison_transport_refusal() {
    for poison in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_discarded_call");
        let ignored_ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("ignores", ignored_ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        fb.add_block_param(entry, Ty::I64);
        let seven = fb.iconst(Ty::I64, 7);
        fb.ret(vec![seven]);
        fb.build();
        let ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("construct_after_discarded_call", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let actual = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 9) };
        let _discarded = fb.call(FuncId::new(0), vec![actual]);
        let seven = fb.iconst(Ty::I64, 7);
        let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
        let result = fb.extract_field(Ty::I64, aggregate, 0);
        fb.ret(vec![result]);
        fb.build();
        let mut fb = mb.function("outer_caller", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let result = fb.call(FuncId::new(1), vec![]);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if poison {
            for function in [FuncId::new(1), FuncId::new(2)] {
                interpreter_ub(&module, function);
            }
            assert!(outputs[1].diagnostics.iter().any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::CallArgumentTransport
            }));
            assert!(unconditionally_reachable_error_rules(&outputs[1].vc) >= 1);
            assert!(outputs[2].diagnostics.iter().any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
            }));
            assert!(unconditionally_reachable_error_rules(&outputs[2].vc) >= 1);
        } else {
            let run = Interpreter::with_module(&module).execute_func(FuncId::new(2), []).unwrap();
            assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
            assert!(outputs.iter().all(|output| output.diagnostics.is_empty()));
        }
    }
}

#[test]
fn make_aggregate_ignored_partial_aggregate_transport_does_not_invent_initialization() {
    let mut mb = ModuleBuilder::new("make_aggregate_partial_transport");
    let partial_ty = Ty::Tuple(vec![Ty::I64]);
    let ft = mb.add_func_type(vec![partial_ty.clone()], vec![Ty::I64]);
    let mut fb = mb.function("ignore_partial", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.add_block_param(entry, partial_ty.clone());
    let seven = fb.iconst(Ty::I64, 7);
    let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
    let result = fb.extract_field(Ty::I64, aggregate, 0);
    fb.ret(vec![result]);
    fb.build();
    let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("caller", caller_ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let partial = fb.const_value(partial_ty, Constant::Aggregate(vec![Constant::Uninit]));
    let result = fb.call(FuncId::new(0), vec![partial]);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().unwrap();
    let outputs = checked_outputs(&module);
    let run = Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap();
    assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
    assert!(outputs.iter().all(|output| output.diagnostics.is_empty()));
}

#[test]
fn make_aggregate_storing_poison_does_not_establish_call_transport() {
    for poison in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_loaded_call_argument");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("ignores", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        fb.add_block_param(entry, Ty::I64);
        let seven = fb.iconst(Ty::I64, 7);
        fb.ret(vec![seven]);
        fb.build();
        let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("caller", caller_ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let ptr = fb.alloca(Ty::I64);
        let stored = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 9) };
        fb.store(Ty::I64, ptr, stored);
        let loaded = fb.load(Ty::I64, ptr);
        fb.call(FuncId::new(0), vec![loaded]);
        let seven = fb.iconst(Ty::I64, 7);
        let aggregate = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
        let result = fb.extract_field(Ty::I64, aggregate, 0);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if poison {
            interpreter_ub(&module, FuncId::new(1));
            assert!(outputs[1].diagnostics.iter().any(|diagnostic| {
                diagnostic.reason == TrustIrChcUnsupportedReason::CallArgumentTransport
            }));
            assert!(unconditionally_reachable_error_rules(&outputs[1].vc) >= 1);
        } else {
            let run = Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap();
            assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
            assert!(outputs.iter().all(|output| output.diagnostics.is_empty()));
        }
    }
}

#[test]
fn make_aggregate_discarded_unwritten_projection_cannot_be_hidden_by_constant_return() {
    for unwritten in [false, true] {
        let mut mb = ModuleBuilder::new("make_aggregate_discarded_projection");
        let input_ty = Ty::Tuple(vec![Ty::I64]);
        let ft = mb.add_func_type(vec![input_ty.clone()], vec![Ty::I64]);
        let mut fb = mb.function("discard_projection", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = fb.add_block_param(entry, input_ty.clone());
        let _discarded = fb.extract_field(Ty::I64, input, 0);
        let seven = fb.iconst(Ty::I64, 7);
        fb.ret(vec![seven]);
        fb.build();
        let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("caller", caller_ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let input = if unwritten {
            fb.const_value(input_ty, Constant::Aggregate(vec![Constant::Uninit]))
        } else {
            let seven = fb.iconst(Ty::I64, 7);
            fb.make_aggregate(input_ty, vec![seven])
        };
        let returned = fb.call(FuncId::new(0), vec![input]);
        let result = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![returned]);
        let result = fb.extract_field(Ty::I64, result, 0);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if unwritten {
            interpreter_ub(&module, FuncId::new(1));
            assert!(
                outputs[1].diagnostics.iter().any(|diagnostic| {
                    diagnostic.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
                }),
                "a discarded unwritten-lane read must still refuse its caller"
            );
            assert!(unconditionally_reachable_error_rules(&outputs[1].vc) >= 1);
        } else {
            let run = Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap();
            assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
            assert!(outputs[1].diagnostics.is_empty(), "{:?}", outputs[1].diagnostics);
        }
    }
}

#[test]
fn make_aggregate_discarded_consumers_keep_actual_poison_errors() {
    for mode in 0..4 {
        for poison in [false, true] {
            let mut mb = ModuleBuilder::new("make_aggregate_discarded_consumer");
            let i64_ty = mb.add_type(Ty::I64);
            let array_ty = Ty::Array(i64_ty, 2);
            let ft = mb.add_func_type(
                if mode == 3 { vec![array_ty.clone()] } else { vec![] },
                vec![Ty::I64],
            );
            let mut fb = mb.function("discard_then_return_constant", ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let array = (mode == 3).then(|| fb.add_block_param(entry, array_ty.clone()));
            let operand = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 9) };
            match mode {
                0 => {
                    fb.binop(BinOp::Xor, Ty::I64, operand, operand);
                }
                1 => {
                    fb.icmp(ICmpOp::Eq, Ty::I64, operand, operand);
                }
                2 => {
                    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![operand]);
                }
                3 => {
                    let index = if poison { fb.undef(Ty::I64) } else { fb.iconst(Ty::I64, 0) };
                    fb.extract_element(Ty::I64, array.unwrap(), index);
                }
                _ => unreachable!(),
            }
            let seven = fb.iconst(Ty::I64, 7);
            fb.ret(vec![seven]);
            fb.build();
            let caller_ft = mb.add_func_type(vec![], vec![Ty::I64]);
            let mut fb = mb.function("caller", caller_ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let arguments = if mode == 3 {
                vec![fb.const_value(
                    array_ty,
                    Constant::Array(vec![Constant::Int(7), Constant::Int(9)]),
                )]
            } else {
                vec![]
            };
            let returned = fb.call(FuncId::new(0), arguments);
            let result = fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![returned]);
            let result = fb.extract_field(Ty::I64, result, 0);
            fb.ret(vec![result]);
            fb.build();
            let module = mb.build().unwrap();
            let outputs = checked_outputs(&module);
            if poison {
                interpreter_ub(&module, FuncId::new(1));
                if mode != 3 {
                    interpreter_ub(&module, FuncId::new(0));
                }
                assert!(
                    outputs[0].diagnostics.iter().any(|diagnostic| {
                        diagnostic.reason == TrustIrChcUnsupportedReason::OperandConsumption
                    }),
                    "unused arithmetic/comparison/index/constructor still consumes poison, mode {mode}"
                );
                assert!(unconditionally_reachable_error_rules(&outputs[0].vc) >= 1);
                assert!(
                    outputs[1].diagnostics.iter().any(|diagnostic| {
                        diagnostic.reason
                            == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
                    }),
                    "callee consumption must survive a constant return, mode {mode}"
                );
                // Array bindings retain satisfiable equalities to their exact
                // source image; syntactic constant folding alone does not
                // establish reachability. This helper panics on solver Unknown.
                assert!(
                    error_rule_solver_verdicts(&outputs[1].vc)
                        .iter()
                        .any(|verdict| *verdict != Some(false)),
                    "mode {mode}"
                );
            } else {
                let run =
                    Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap();
                assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
                assert!(
                    outputs[1].diagnostics.is_empty(),
                    "mode {mode}: {:?}; {:?}",
                    outputs[1].diagnostics,
                    outputs[1].call_summary_census
                );
            }
        }
    }
}

#[test]
fn make_aggregate_discarded_aggregate_undef_is_ub_at_definition() {
    let mut mb = ModuleBuilder::new("discarded_aggregate_undef");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("bad_definition", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.undef(Ty::Tuple(vec![Ty::I64]));
    let seven = fb.iconst(Ty::I64, 7);
    fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
    fb.ret(vec![]);
    fb.build();
    let mut fb = mb.function("caller", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.call_void(FuncId::new(0), vec![]);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().unwrap();
    for id in [FuncId::new(0), FuncId::new(1)] {
        interpreter_ub(&module, id);
    }
    let outputs = checked_outputs(&module);
    assert!(
        outputs[0]
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::OperandConsumption)
    );
    assert!(
        outputs[1].diagnostics.iter().any(|diagnostic| diagnostic.reason
            == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
    );
    for output in outputs {
        assert!(unconditionally_reachable_error_rules(&output.vc) >= 1);
    }
}

#[test]
fn make_aggregate_discarded_alloca_checks_consumption_extent_and_alignment() {
    for mode in 0..6 {
        let mut mb = ModuleBuilder::new("discarded_alloca");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("allocation_before_constant_constructor", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let count = match mode {
            0 => fb.undef(Ty::I64),
            1 => fb.iconst(Ty::I64, 0),
            3 => fb.iconst(Ty::I64, i128::from(i64::MAX)),
            _ => fb.iconst(Ty::I64, 2),
        };
        fb.alloca(Ty::I64);
        let seven = fb.iconst(Ty::I64, 7);
        fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
        fb.ret(vec![]);
        fb.build();
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        fb.call_void(FuncId::new(0), vec![]);
        fb.ret(vec![]);
        fb.build();
        let mut module = mb.build().unwrap();
        let allocation = module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, trust_ir::Inst::Alloca { .. }))
            .unwrap();
        let trust_ir::Inst::Alloca { count: allocation_count, align, .. } = &mut allocation.inst
        else {
            unreachable!()
        };
        *allocation_count = (mode != 5).then_some(count);
        *align = Some(if mode == 2 { 0 } else { 8 });
        if mode == 2 {
            super::assert_canonical_refusal(&module, "align 0 must be a positive power of two");
            continue;
        }
        let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
        for id in [FuncId::new(0), FuncId::new(1)] {
            let execution = Interpreter::with_module(&module).execute_func(id, []);
            if mode >= 4 {
                execution.unwrap();
            } else {
                let error = execution.unwrap_err();
                assert_eq!(
                    error.code,
                    if mode == 2 {
                        InterpretErrorCode::TypeError
                    } else {
                        InterpretErrorCode::UndefinedBehavior
                    }
                );
            }
        }
        if mode == 5 {
            assert!(outputs.iter().all(|output| output.diagnostics.is_empty()), "{:?}", outputs);
        } else if mode == 4 {
            assert!(outputs[0].diagnostics.is_empty());
            // Counted allocations remain outside the existing bounded summary.
            assert!(outputs[1].diagnostics.iter().any(|diagnostic| diagnostic.reason
                == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary));
        } else {
            assert!(
                outputs[0].diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            assert!(outputs[1].diagnostics.iter().any(|diagnostic| diagnostic.reason
                == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary));
            for output in outputs {
                assert!(unconditionally_reachable_error_rules(&output.vc) >= 1);
            }
        }
    }
}

#[test]
fn make_aggregate_bulk_zero_count_preserves_canonical_consumption_order() {
    for mode in 0..6 {
        let mut mb = ModuleBuilder::new("bulk_zero_count_consumption");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("bulk_before_constructor", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let pointer = if matches!(mode, 2 | 4) { fb.undef(Ty::Ptr) } else { fb.null_ptr() };
        let count = if matches!(mode, 1 | 5) { fb.undef(Ty::U64) } else { fb.iconst(Ty::U64, 0) };
        if mode >= 4 {
            fb.memcopy(pointer, pointer, count, false);
        } else {
            let byte = if mode == 0 { fb.undef(Ty::U8) } else { fb.iconst(Ty::U8, 0) };
            fb.memset(pointer, byte, count);
        }
        let seven = fb.iconst(Ty::I64, 7);
        fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let outputs = checked_outputs(&module);
        if matches!(mode, 0 | 1 | 5) {
            interpreter_ub(&module, FuncId::new(0));
            assert!(
                outputs[0].diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            assert!(unconditionally_reachable_error_rules(&outputs[0].vc) >= 1);
        } else {
            Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
            assert!(outputs[0].diagnostics.is_empty(), "mode {mode}: {:?}", outputs[0].diagnostics);
        }
    }
}

#[test]
fn make_aggregate_field_written_memory_retains_real_initialization_evidence() {
    for mode in 0..4 {
        let mut mb = ModuleBuilder::new("field_written_initialization");
        let id = mb.add_struct(trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "Pair".into(),
            fields: vec![
                trust_ir::FieldDef { name: "x".into(), ty: Ty::I64, offset: Some(0) },
                trust_ir::FieldDef { name: "y".into(), ty: Ty::I64, offset: Some(8) },
            ],
            size: Some(16),
            align: Some(8),
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        });
        let ty = Ty::Struct(id);
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![]);
        let mut fb = mb.function("copy_initialized_unknown_fields", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let x = fb.add_block_param(entry, Ty::I64);
        let y = fb.add_block_param(entry, Ty::I64);
        let source = fb.alloca(ty.clone());
        let destination = fb.alloca(ty.clone());
        let bytes = fb.iconst(Ty::U64, 16);
        let mut source_fields = Vec::new();
        for field in 0..2 {
            let index = fb.iconst(Ty::I64, field);
            source_fields.push(fb.gep(Ty::I64, source, vec![index]));
            let destination_field = fb.gep(Ty::I64, destination, vec![index]);
            let zero = fb.iconst(Ty::I64, 0);
            fb.store(Ty::I64, destination_field, zero);
        }
        if mode == 3 {
            fb.memcopy(destination, source, bytes, false);
        }
        fb.store(Ty::I64, source_fields[0], x);
        if mode != 1 {
            let value = if mode == 2 { fb.undef(Ty::I64) } else { y };
            fb.store(Ty::I64, source_fields[1], value);
        }
        if mode != 3 {
            fb.memcopy(destination, source, bytes, false);
        }
        let loaded = fb.load(ty, destination);
        let read_x = fb.extract_field(Ty::I64, loaded, 0);
        let read_y = fb.extract_field(Ty::I64, loaded, 1);
        fb.make_aggregate(Ty::Tuple(vec![Ty::I64, Ty::I64]), vec![read_x, read_y]);
        let correct_x = fb.icmp(ICmpOp::Eq, Ty::I64, read_x, x);
        let correct_y = fb.icmp(ICmpOp::Eq, Ty::I64, read_y, y);
        fb.assert(correct_x);
        fb.assert(correct_y);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let output = checked_outputs(&module).remove(0);
        let execution = Interpreter::with_module(&module).execute_func(
            FuncId::new(0),
            [
                trust_ir::interpret::InterpretValue::int(Ty::I64, 7).unwrap(),
                trust_ir::interpret::InterpretValue::int(Ty::I64, 9).unwrap(),
            ],
        );
        if mode == 0 {
            execution.unwrap();
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert!(
                error_rule_solver_verdicts(&output.vc)
                    .iter()
                    .all(|verdict| *verdict == Some(false))
            );
        } else {
            assert_eq!(execution.unwrap_err().code, InterpretErrorCode::UndefinedBehavior);
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption),
                "mode {mode}"
            );
            assert!(
                error_rule_solver_verdicts(&output.vc)
                    .iter()
                    .any(|verdict| *verdict != Some(false))
            );
        }
    }
}

#[test]
fn make_aggregate_phi_initialization_requires_seed_and_every_update() {
    for mode in 0..3 {
        let mut mb = ModuleBuilder::new("seeded_phi_initialization");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("bounded_counter", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let seed = if mode == 1 { fb.undef(Ty::U32) } else { fb.iconst(Ty::U32, 2) };
        fb.br(header, vec![seed]);
        fb.switch_to_block(header);
        let counter = fb.add_block_param(header, Ty::U32);
        fb.make_aggregate(Ty::Tuple(vec![Ty::U32]), vec![counter]);
        let zero = fb.iconst(Ty::U32, 0);
        let done = fb.icmp(ICmpOp::Eq, Ty::U32, counter, zero);
        fb.condbr(done, exit, vec![], body, vec![]);
        fb.switch_to_block(body);
        let next = if mode == 2 {
            fb.undef(Ty::U32)
        } else {
            let one = fb.iconst(Ty::U32, 1);
            fb.binop(BinOp::Sub, Ty::U32, counter, one)
        };
        fb.br(header, vec![next]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().unwrap();
        let output = checked_outputs(&module).remove(0);
        let execution = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
        if mode == 0 {
            execution.unwrap();
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        } else {
            assert_eq!(execution.unwrap_err().code, InterpretErrorCode::UndefinedBehavior);
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
        }
    }

    // A valid but unreachable self-phi has no initialized incoming seed. Do
    // not infer initializedness merely by assuming the predecessor cycle.
    let mut mb = ModuleBuilder::new("unseeded_phi");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("unreachable_cycle", ft);
    let entry = fb.create_block();
    let cycle = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.switch_to_block(cycle);
    let unseeded = fb.add_block_param(cycle, Ty::U32);
    fb.make_aggregate(Ty::Tuple(vec![Ty::U32]), vec![unseeded]);
    fb.br(cycle, vec![unseeded]);
    fb.build();
    let module = mb.build().unwrap();
    Interpreter::with_module(&module).execute_func(FuncId::new(0), []).unwrap();
    super::assert_canonical_refusal(&module, "unreachable from entry");
}

#[test]
fn make_aggregate_summary_partial_carrier_survives_copy_and_nested_return() {
    for nested in [false, true] {
        for missing in [false, true] {
            let mut mb = ModuleBuilder::new("summary_partial_carrier");
            let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
            let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![pair.clone()]);
            let mut fb = mb.function("fill_partial_carrier", ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let x = fb.add_block_param(entry, Ty::I64);
            let y = fb.add_block_param(entry, Ty::I64);
            let seed = fb.const_value(pair.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
            let filled = fb.insert_field(pair.clone(), seed, 0, x);
            let filled = if missing { filled } else { fb.insert_field(pair.clone(), filled, 1, y) };
            let copied = fb.copy(pair.clone(), filled);
            fb.ret(vec![copied]);
            fb.build();
            let mut fb = mb.function("forward_partial_carrier", ft);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let x = fb.add_block_param(entry, Ty::I64);
            let y = fb.add_block_param(entry, Ty::I64);
            let returned = fb.call(FuncId::new(0), vec![x, y]);
            let copied = fb.copy(pair.clone(), returned);
            fb.ret(vec![copied]);
            fb.build();
            let caller_ty = mb.add_func_type(vec![], vec![Ty::I64]);
            let mut fb = mb.function("consume_completed_fields", caller_ty);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let seven = fb.iconst(Ty::I64, 7);
            let nine = fb.iconst(Ty::I64, 9);
            let returned = fb.call(FuncId::new(u32::from(nested)), vec![seven, nine]);
            let x = fb.extract_field(Ty::I64, returned, 0);
            let y = fb.extract_field(Ty::I64, returned, 1);
            fb.make_aggregate(pair, vec![x, y]);
            let x_is_seven = fb.icmp(ICmpOp::Eq, Ty::I64, x, seven);
            let y_is_nine = fb.icmp(ICmpOp::Eq, Ty::I64, y, nine);
            fb.assert(x_is_seven);
            fb.assert(y_is_nine);
            fb.ret(vec![x]);
            fb.build();
            let module = mb.build().unwrap();
            let outputs = checked_outputs(&module);
            // Partial aggregate returns/copies themselves are valid transport.
            assert!(outputs[0].diagnostics.is_empty(), "{:?}", outputs[0].diagnostics);
            assert!(outputs[1].diagnostics.is_empty(), "{:?}", outputs[1].diagnostics);
            if missing {
                interpreter_ub(&module, FuncId::new(2));
                assert!(outputs[2].diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption));
                assert!(
                    error_rule_solver_verdicts(&outputs[2].vc)
                        .iter()
                        .any(|verdict| *verdict != Some(false))
                );
            } else {
                let run =
                    Interpreter::with_module(&module).execute_func(FuncId::new(2), []).unwrap();
                assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
                assert!(
                    outputs.iter().all(|output| output.diagnostics.is_empty()),
                    "{:?}",
                    outputs
                );
                assert!(
                    error_rule_solver_verdicts(&outputs[2].vc)
                        .iter()
                        .all(|verdict| *verdict == Some(false))
                );
            }
        }
    }
}

#[test]
fn make_aggregate_discarded_load_preserves_definition_time_initialization_checks() {
    for mode in 0..5 {
        let aggregate = mode < 2;
        let initialized = matches!(mode, 1 | 4);
        let strict = mode >= 3;
        let mut mb = ModuleBuilder::new("discarded_load_initialization");
        let ty = if aggregate { Ty::Tuple(vec![Ty::I64]) } else { Ty::I64 };
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("discard_load_then_construct", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let slot = fb.alloca(ty.clone());
        if initialized {
            let value = fb.const_value(
                ty.clone(),
                if aggregate {
                    Constant::Aggregate(vec![Constant::Int(7)])
                } else {
                    Constant::Int(7)
                },
            );
            fb.store(ty.clone(), slot, value);
        }
        fb.load(ty, slot);
        let seven = fb.iconst(Ty::I64, 7);
        fb.make_aggregate(Ty::Tuple(vec![Ty::I64]), vec![seven]);
        fb.ret(vec![]);
        fb.build();
        let mut module = mb.build().unwrap();
        let load = module.functions[0].blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(node.inst, trust_ir::Inst::Load { .. }))
            .unwrap();
        if let trust_ir::Inst::Load { volatile, .. } = &mut load.inst {
            *volatile = strict;
        }
        if mode == 0 {
            load.proofs.push(trust_ir::proof::ProofAnnotation::ValidBorrow);
        }
        let output = checked_outputs(&module).remove(0);
        let execution = Interpreter::with_module(&module).execute_func(FuncId::new(0), []);
        if mode == 0 || mode == 3 {
            assert_eq!(execution.unwrap_err().code, InterpretErrorCode::UndefinedBehavior);
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            assert!(unconditionally_reachable_error_rules(&output.vc) >= 1);
        } else {
            execution.unwrap();
            assert!(output.diagnostics.is_empty(), "mode {mode}: {:?}", output.diagnostics);
        }
    }
}

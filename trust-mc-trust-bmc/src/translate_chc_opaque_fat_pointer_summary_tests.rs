// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::inst::AssertKind;
use trust_ir::value::FuncTyId;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;

// Retain the actual compiler-emitted callee without altering its instructions,
// type tables, or Assume. This is translation diagnostics; native admission
// separately requires live authority for the Assume in this saved fixture.
fn partial_entry_unwrap_or_caller() -> Module {
    let mut module: Module = serde_json::from_str(include_str!(
        "../tests/fixtures/option_str_unwrap_or_seal9178.module.json"
    ))
    .expect("source-generated unwrap_or");
    let callee = &module.functions[0];
    let callee_id = callee.id;
    let mut signature = module.func_types[callee.ty.as_usize()].clone();
    signature.returns.clear();
    let signature_id = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(signature.clone());
    let mut caller =
        Function::new(FuncId::new(0), "unwrap_or_caller", signature_id, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params = signature
        .params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty))
        .collect();
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: callee_id,
            args: vec![ValueId::new(0), ValueId::new(1)],
        })
        .with_result(ValueId::new(2)),
    );
    entry.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    caller.blocks.push(entry);
    module.functions.push(caller);
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    module
}

/// Keep every archived callee instruction/type/Assume unchanged. This NEW
/// caller establishes its own initialized physical fields from independent
/// unknown scalar/fat-pointer inputs; it gives the archived entry no premise.
fn source_generated_unwrap_or_caller() -> Module {
    let mut module = partial_entry_unwrap_or_caller();
    let callee_before = module.function_by_id(FuncId::new(1)).unwrap().clone();
    let callee_signature = module.func_types[callee_before.ty.as_usize()].clone();
    let aggregate = callee_signature.params[0].clone();
    let fat = callee_signature.params[1].clone();
    let mut signature = callee_signature;
    signature.params = vec![Ty::I64, fat.clone(), fat.clone()];
    signature.returns.clear();
    let ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(signature);
    let caller =
        module.functions.iter_mut().find(|function| function.id == FuncId::new(0)).unwrap();
    caller.ty = ty;
    let entry = &mut caller.blocks[0];
    entry.params =
        vec![(ValueId::new(4), Ty::I64), (ValueId::new(1), fat.clone()), (ValueId::new(3), fat)];
    let mut prefix = vec![
        InstrNode::new(Inst::Const {
            ty: aggregate.clone(),
            value: Constant::Aggregate(vec![Constant::Uninit; 2]),
        })
        .with_result(ValueId::new(5)),
        InstrNode::new(Inst::InsertField {
            ty: aggregate.clone(),
            aggregate: ValueId::new(5),
            field: 0,
            value: ValueId::new(4),
        })
        .with_result(ValueId::new(6)),
        InstrNode::new(Inst::InsertField {
            ty: aggregate,
            aggregate: ValueId::new(6),
            field: 1,
            value: ValueId::new(3),
        })
        .with_result(ValueId::new(0)),
    ];
    prefix.append(&mut entry.body);
    entry.body = prefix;
    assert_eq!(&callee_before, module.function_by_id(FuncId::new(1)).unwrap());
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    module
}

#[test]
fn source_generated_unwrap_or_uninitialized_entry_tag_is_refused() {
    use trust_ir::interpret::{
        InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
    };
    let module = partial_entry_unwrap_or_caller();
    let signature =
        &module.func_types[module.function_by_id(FuncId::new(0)).unwrap().ty.as_usize()];
    let fat = || InterpretValue {
        ty: signature.params[1].clone(),
        kind: InterpretValueKind::FatPtr {
            data: Box::new(InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::NullPtr }),
            metadata: Box::new(InterpretValue::int(Ty::U64, 0).unwrap()),
        },
    };
    let partial = InterpretValue {
        ty: signature.params[0].clone(),
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue { ty: Ty::I64, kind: InterpretValueKind::Uninit },
            fat(),
        ]),
    };
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [partial, fat()])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    let output = translate_caller(&module);
    assert!(
        output.diagnostics.iter().any(|diagnostic| diagnostic.reason
            == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
    );
}

fn translate_caller(module: &Module) -> ChcTranslationOutput {
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    translate_function(module.function_by_id(FuncId::new(0)).unwrap(), module, &options)
}

#[test]
fn source_generated_unwrap_or_call_summary_translates_real_body() {
    let module = source_generated_unwrap_or_caller();
    let output = translate_caller(&module);
    assert_eq!(output.call_summary_census.len(), 1);
    let row = &output.call_summary_census[0];
    eprintln!("actual unwrap_or call summary: {:?}", row.outcome);
    assert_eq!(row.outcome, CallSummaryOutcome::Summarized);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
}

fn add_assertion(block: &mut Block, assertion: bool, at: usize) {
    block.body.insert(
        at,
        InstrNode::new(Inst::Assert {
            cond: ValueId::new(1000),
            kind: AssertKind::Unspecified,
            site: None,
        }),
    );
    block.body.insert(
        at,
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(assertion) })
            .with_result(ValueId::new(1000)),
    );
}

#[test]
fn opaque_fat_pointer_summary_keeps_caller_and_callee_assertions() {
    for in_callee in [false, true] {
        for assertion in [false, true] {
            let mut module = source_generated_unwrap_or_caller();
            let function_id = FuncId::new(if in_callee { 1 } else { 0 });
            let function = module.functions.iter_mut().find(|f| f.id == function_id).unwrap();
            let at = if in_callee { 0 } else { function.blocks[0].body.len() - 1 };
            add_assertion(&mut function.blocks[0], assertion, at);
            assert!(trust_ir_build::validate_module_report(&module).is_ok());
            let output = translate_caller(&module);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert_eq!(output.call_summary_census[0].outcome, CallSummaryOutcome::Summarized);
            let unconditional_error = output.vc.rules.iter().any(|rule| {
                rule.head.name == ERROR_REL
                    && rule
                        .body
                        .constraints
                        .iter()
                        .all(|condition| try_eval_to_bool(condition) == Some(true))
            });
            assert_eq!(unconditional_error, !assertion, "callee={in_callee}");
        }
    }
}

#[test]
fn opaque_fat_pointer_summary_never_proves_unknown_metadata_equals_zero() {
    let mut module = source_generated_unwrap_or_caller();
    let function = module.functions.iter_mut().find(|f| f.id == FuncId::new(1)).unwrap();
    let fat = module.func_types[function.ty.as_usize()].params[1].clone();
    let body = &mut function.blocks[0].body;
    let prefix = vec![
        InstrNode::new(Inst::PtrMetadata {
            ptr_ty: fat,
            metadata_ty: Ty::U64,
            ptr: ValueId::new(1),
        })
        .with_result(ValueId::new(1000)),
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
            .with_result(ValueId::new(1001)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U64,
            lhs: ValueId::new(1000),
            rhs: ValueId::new(1001),
        })
        .with_result(ValueId::new(1002)),
        InstrNode::new(Inst::Assert {
            cond: ValueId::new(1002),
            kind: AssertKind::Unspecified,
            site: None,
        }),
    ];
    body.splice(0..0, prefix);
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    let output = translate_caller(&module);
    assert!(matches!(&output.call_summary_census[0].outcome,
        CallSummaryOutcome::Declined { site, detail }
            if site.tag == "unmodeled_instruction" && detail.as_deref() == Some("PtrMetadata")));
    assert!(
        output.diagnostics.iter().any(|diagnostic| diagnostic.reason
            == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
    );
}

/// The PROPERTY the test above is named for, pinned independently of the
/// MECHANISM that currently delivers it.
///
/// `opaque_fat_pointer_summary_never_proves_unknown_metadata_equals_zero`
/// asserts that the summary DECLINES with `unmodeled_instruction/PtrMetadata`.
/// That is one way to keep the property and not the only one: if the
/// interpreter ever models a metadata read as a fresh symbolic value, the
/// summary succeeds and the `Assert` arm pushes `path AND NOT cond` as an error
/// condition, which stays satisfiable for a fresh value — so the caller remains
/// unprovable for a different reason.
///
/// A test that pins the decline cannot tell those apart, so it turns a modelling
/// question into a re-bless of a soundness pin. This one asks the question that
/// actually matters — can the caller be proved panic-free through a callee
/// whose body asserts an unknown metadata is zero — and answers it by SOLVING
/// the generated error rules rather than by inspecting which exit fired.
///
/// It passes under the current declining behaviour, where the unsupported error
/// rule is reachable. It is written to keep passing under a fresh-value model,
/// where the assertion's own error rule is reachable instead. If it ever fails,
/// something has made that caller provable, and THAT is the false proof both
/// tests exist to prevent.
#[test]
fn a_caller_is_never_proved_through_an_unknown_metadata_assertion() {
    let mut module = source_generated_unwrap_or_caller();
    let function = module.functions.iter_mut().find(|f| f.id == FuncId::new(1)).unwrap();
    let fat = module.func_types[function.ty.as_usize()].params[1].clone();
    let body = &mut function.blocks[0].body;
    let prefix = vec![
        InstrNode::new(Inst::PtrMetadata {
            ptr_ty: fat,
            metadata_ty: Ty::U64,
            ptr: ValueId::new(1),
        })
        .with_result(ValueId::new(1000)),
        InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
            .with_result(ValueId::new(1001)),
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::U64,
            lhs: ValueId::new(1000),
            rhs: ValueId::new(1001),
        })
        .with_result(ValueId::new(1002)),
        InstrNode::new(Inst::Assert {
            cond: ValueId::new(1002),
            kind: AssertKind::Unspecified,
            site: None,
        }),
    ];
    body.splice(0..0, prefix);
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    let output = translate_caller(&module);

    use ay_bindings::execute_direct::{ExecuteResult, execute};

    let errors: Vec<_> =
        output.vc.rules.iter().filter(|rule| rule.head.name == ERROR_REL).collect();
    assert!(!errors.is_empty(), "a caller that cannot be discharged must carry an error rule");

    // At least one error rule must be REACHABLE. Its constraints are exactly its
    // reachability question for this caller, whose single block has
    // unconstrained entry parameters.
    let mut any_reachable = false;
    for rule in &errors {
        let mut program = ay_bindings::AYProgram::new();
        program.set_logic("QF_BV");
        for var in output.vc.vars() {
            let _ = program.declare_const(var.name.to_string(), var.sort.clone());
        }
        for constraint in rule.body.constraints.iter() {
            program.assert(constraint.clone());
        }
        program.check_sat();
        match execute(&program).expect("solve an error rule's reachability") {
            ExecuteResult::Counterexample { .. } => any_reachable = true,
            ExecuteResult::Verified => {}
            other => panic!("unexpected solver outcome: {other:?}"),
        }
    }
    assert!(
        any_reachable,
        "the caller must NOT be provable through a callee asserting that an unknown \
         metadata is zero; every error rule came back unreachable"
    );
}

#[test]
fn opaque_fat_pointer_summary_rejects_kind_confusion() {
    let mut module = source_generated_unwrap_or_caller();
    let function = module.functions.iter_mut().find(|f| f.id == FuncId::new(1)).unwrap();
    for block in &mut function.blocks {
        for node in &mut block.body {
            if let Inst::Copy { ty, .. } = &mut node.inst {
                *ty = Ty::FatPtr(FatPtrKind::Str);
            }
        }
    }
    assert!(!trust_ir_build::validate_module_report(&module).is_ok());
    let output = translate_caller(&module);
    // The native gate rejects the malformed module first. The summary's own
    // typed token check also refuses to reinterpret Slice as Str.
    assert!(matches!(&output.call_summary_census[0].outcome,
        CallSummaryOutcome::Declined { site, .. } if site.tag == "copy_operand_unbound"));
}

#[test]
fn opaque_fat_pointer_summary_transports_nested_call_results() {
    let mut module = source_generated_unwrap_or_caller();
    let mut wrapper = module.function_by_id(FuncId::new(0)).unwrap().clone();
    wrapper.id = FuncId::new(2);
    wrapper.name = "unwrap_or_wrapper".into();
    let mut signature = module.func_types[wrapper.ty.as_usize()].clone();
    signature.returns = module.func_types
        [module.function_by_id(FuncId::new(1)).unwrap().ty.as_usize()]
    .returns
    .clone();
    wrapper.ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(signature);
    *wrapper.blocks[0].body.last_mut().unwrap() =
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] });
    let caller = module.functions.iter_mut().find(|f| f.id == FuncId::new(0)).unwrap();
    let arguments = caller.blocks[0].params.iter().map(|(value, _)| *value).collect();
    let call = caller.blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Call { .. }))
        .unwrap();
    if let Inst::Call { callee, args } = &mut call.inst {
        *callee = wrapper.id;
        *args = arguments;
    }
    module.functions.push(wrapper);
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    let output = translate_caller(&module);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert_eq!(output.call_summary_census[0].outcome, CallSummaryOutcome::Summarized);
}

#[test]
fn opaque_fat_pointer_summary_aggregate_return_preserves_only_known_scalar_facts() {
    use ay_bindings::execute_direct::{ExecuteResult, execute};
    use trust_ir_build::ModuleBuilder;

    let fat = Ty::FatPtr(FatPtrKind::Str);
    let pair = Ty::Tuple(vec![fat.clone(), fat.clone()]);
    let outer = Ty::Tuple(vec![pair.clone(), Ty::U32]);
    let mut builder = ModuleBuilder::new("opaque_aggregate_return");
    let callee_ty = builder.add_func_type(vec![outer.clone()], vec![outer.clone()]);
    let caller_ty = builder.add_func_type(vec![outer.clone()], vec![]);

    // Import both fat-pointer leaves through an aggregate argument, preserve
    // them inside the nested field, and return a precisely known ordinary tag.
    let mut callee = builder.function("set_tag", callee_ty);
    let entry = callee.create_block();
    callee.switch_to_block(entry);
    callee.set_entry(entry);
    let input = callee.add_block_param(entry, outer.clone());
    let seven = callee.iconst(Ty::U32, 7);
    let result = callee.insert_field(outer.clone(), input, 1, seven);
    callee.ret(vec![result]);
    callee.build();

    let mut caller = builder.function("inspect_returned_aggregate", caller_ty);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    caller.set_entry(entry);
    let input = caller.add_block_param(entry, outer.clone());
    let result = caller.call(FuncId::new(0), vec![input]);
    let tag = caller.extract_field(Ty::U32, result, 1);
    let seven = caller.iconst(Ty::U32, 7);
    let tag_is_seven = caller.icmp(ICmpOp::Eq, Ty::U32, tag, seven);
    caller.assert(tag_is_seven);

    let returned_pair = caller.extract_field(pair.clone(), result, 0);
    let left = caller.extract_field(fat.clone(), returned_pair, 0);
    let right = caller.extract_field(fat.clone(), returned_pair, 1);
    let left_len = caller.ptr_metadata(fat.clone(), Ty::U64, left);
    let right_len = caller.ptr_metadata(fat.clone(), Ty::U64, right);
    let zero = caller.iconst(Ty::U64, 0);
    for (lhs, rhs) in [(left_len, zero), (right_len, zero), (left_len, right_len)] {
        let claim = caller.icmp(ICmpOp::Eq, Ty::U64, lhs, rhs);
        caller.assert(claim);
    }
    caller.ret(vec![]);
    caller.build();

    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    {
        use trust_ir::interpret::{
            InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
        };
        let initialized_fat = || InterpretValue {
            ty: fat.clone(),
            kind: InterpretValueKind::FatPtr {
                data: Box::new(InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::NullPtr }),
                metadata: Box::new(InterpretValue::int(Ty::U64, 0).unwrap()),
            },
        };
        let partial = InterpretValue {
            ty: outer.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue {
                    ty: pair.clone(),
                    kind: InterpretValueKind::Aggregate(vec![
                        InterpretValue { ty: fat.clone(), kind: InterpretValueKind::Uninit },
                        initialized_fat(),
                    ]),
                },
                InterpretValue::int(Ty::U32, 0).unwrap(),
            ]),
        };
        assert_eq!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(1), [partial])
                .unwrap_err()
                .code,
            InterpretErrorCode::UndefinedBehavior
        );
        let output = translate_function(
            module.function_by_id(FuncId::new(1)).unwrap(),
            &module,
            &TranslateOptions::default(),
        );
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
        );
    }
    // The same original assertions over an explicitly initialized unknown
    // pair, preserving both independent opaque leaves and all inner types.
    let old_ty = module.function_by_id(FuncId::new(1)).unwrap().ty;
    let mut signature = module.func_types[old_ty.as_usize()].clone();
    signature.params = vec![fat.clone(), fat.clone(), Ty::U32];
    let caller_ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(signature);
    let caller =
        module.functions.iter_mut().find(|function| function.id == FuncId::new(1)).unwrap();
    caller.ty = caller_ty;
    caller.blocks[0].params = vec![
        (ValueId::new(100), fat.clone()),
        (ValueId::new(101), fat),
        (ValueId::new(102), Ty::U32),
    ];
    let mut prefix = vec![
        InstrNode::new(Inst::Const {
            ty: pair.clone(),
            value: Constant::Aggregate(vec![Constant::Uninit; 2]),
        })
        .with_result(ValueId::new(103)),
        InstrNode::new(Inst::InsertField {
            ty: pair.clone(),
            aggregate: ValueId::new(103),
            field: 0,
            value: ValueId::new(100),
        })
        .with_result(ValueId::new(104)),
        InstrNode::new(Inst::InsertField {
            ty: pair,
            aggregate: ValueId::new(104),
            field: 1,
            value: ValueId::new(101),
        })
        .with_result(ValueId::new(105)),
        InstrNode::new(Inst::Const {
            ty: outer.clone(),
            value: Constant::Aggregate(vec![Constant::Uninit; 2]),
        })
        .with_result(ValueId::new(106)),
        InstrNode::new(Inst::InsertField {
            ty: outer.clone(),
            aggregate: ValueId::new(106),
            field: 0,
            value: ValueId::new(105),
        })
        .with_result(ValueId::new(107)),
        InstrNode::new(Inst::InsertField {
            ty: outer,
            aggregate: ValueId::new(107),
            field: 1,
            value: ValueId::new(102),
        })
        .with_result(ValueId::new(0)),
    ];
    prefix.append(&mut caller.blocks[0].body);
    caller.blocks[0].body = prefix;
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let output =
        translate_function(module.function_by_id(FuncId::new(1)).unwrap(), &module, &options);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert_eq!(output.call_summary_census.len(), 1);
    assert_eq!(output.call_summary_census[0].outcome, CallSummaryOutcome::Summarized);

    let errors: Vec<_> =
        output.vc.rules.iter().filter(|rule| rule.head.name == ERROR_REL).collect();
    assert_eq!(errors.len(), 4, "one error condition for each assertion");
    // This caller has one block with unconstrained entry parameters: solving
    // an error rule's constraints is exactly its reachability question. Check
    // both truth values of each claim, rather than merely counting symbols.
    for (index, rule) in errors.iter().enumerate() {
        let constraints: Vec<_> = rule.body.constraints.iter().cloned().collect();
        let (violation, bounds) = constraints.split_last().unwrap();
        for negate_violation in [false, true] {
            let mut program = ay_bindings::AYProgram::new();
            program.set_logic("QF_BV");
            for var in output.vc.vars() {
                let _ = program.declare_const(var.name.to_string(), var.sort.clone());
            }
            for bound in bounds {
                program.assert(bound.clone());
            }
            program.assert(if negate_violation {
                violation.clone().not()
            } else {
                violation.clone()
            });
            program.check_sat();
            let satisfiable = match execute(&program).expect("solve aggregate-return condition") {
                ExecuteResult::Counterexample { .. } => true,
                ExecuteResult::Verified => false,
                other => panic!("unexpected solver outcome: {other:?}"),
            };
            assert_eq!(
                satisfiable,
                index != 0 || negate_violation,
                "claim {index}, negate_violation={negate_violation}: only tag == 7 is known; \
                 each length can be zero or nonzero and the lengths can agree or differ"
            );
        }
    }
}

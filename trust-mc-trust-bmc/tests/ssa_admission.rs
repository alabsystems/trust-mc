// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Invalid SSA is an input refusal, never a free symbolic source value.

use ay_bindings::{AYProgram, Expr, execute_direct};
use trust_ir::inst::Inst;
use trust_ir::value::ValueId;
use trust_ir::{Module, Ty};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::decl::Decl;
use trust_mc_core::violation::PropertyKind;
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_function_to_bmc_vc, trust_ir_to_bmc_vc};

// Ask AY about exactly the public VC: constraints AND any generated charge.
// A satisfiable Other charge is a refusal, not a program counterexample or
// proof-grade result. Unknown/incomplete outcomes are never a test pass.
fn satisfiable(vc: &BmcVc) -> bool {
    let mut query = AYProgram::new();
    query.set_logic("QF_BV");
    for declaration in &vc.decls {
        let Decl::Const { name, sort } = declaration else {
            panic!("scalar fixture unexpectedly needs a nonconstant declaration");
        };
        let _ = query.declare_const(name.clone(), sort.clone());
    }
    for constraint in &vc.constraints {
        query.assert(constraint.clone());
    }
    let charges = vc.violations.iter().map(|v| v.condition.clone()).collect::<Vec<_>>();
    query.assert(if charges.is_empty() { Expr::false_() } else { Expr::or_many(charges) });
    query.check_sat();
    match execute_direct::execute(&query).expect("in-process AY executes") {
        execute_direct::ExecuteResult::Counterexample { .. } => true,
        execute_direct::ExecuteResult::Verified => false,
        other => panic!("incomplete BMC query outcome: {other:?}"),
    }
}

fn vcs(module: &Module) -> Vec<BmcVc> {
    let options = TranslateOptions::default();
    let all = trust_ir_to_bmc_vc(module, &options);
    assert_eq!(all.len(), module.functions.len());
    for function in &module.functions {
        let selected = trust_ir_function_to_bmc_vc(module, function.id, &options)
            .expect("actual function id is present");
        let from_all = &all[module.functions.iter().position(|f| f.id == function.id).unwrap()];
        assert_eq!(satisfiable(&selected), satisfiable(from_all));
    }
    all
}

fn refuses(module: &Module) {
    let all = vcs(module);
    for vc in all {
        check_refusal_vc(&vc);
    }
}

fn check_refusal_vc(vc: &BmcVc) {
    let charged = satisfiable(vc);
    assert!(charged, "invalid input query was reported Verified");
    assert_eq!(vc.violations.len(), 1, "one complete input refusal, not guessed execution");
    assert_eq!(vc.violations[0].kind, PropertyKind::Other);
    assert_eq!(vc.violations[0].condition, Expr::true_());
    assert!(vc.decls.is_empty(), "invalid input must not mint source symbols");
    assert!(vc.constraints.is_empty(), "assumptions cannot hide input invalidity");
}

fn invalid(module: &Module, matches: impl Fn(&ValidationError) -> bool) {
    let errors = validate_module(module);
    assert!(!errors.is_empty(), "hostile fixture must actually be invalid canonical IR");
    assert!(errors.iter().any(matches), "wrong invalidity boundary: {errors:?}");
    refuses(module);
}

fn straight() -> Module {
    let mut builder = ModuleBuilder::new("ssa_input");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let yes = function.bool_const(true);
    function.assume(yes);
    function.assert(yes);
    function.ret(vec![]);
    function.build();
    builder.build().unwrap()
}

#[test]
fn undefined_return_is_not_verified_without_safety_obligations() {
    let mut builder = ModuleBuilder::new("undefined_return");
    let signature = builder.add_func_type(vec![], vec![Ty::Bool]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let yes = function.bool_const(true);
    function.ret(vec![yes]);
    function.build();
    let mut module = builder.build().unwrap();
    module.functions[0].blocks[0].body.last_mut().unwrap().inst =
        Inst::Return { values: vec![ValueId::new(999)] };
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDef { .. }));
}

#[test]
fn undefined_condition_refuses_even_after_a_false_assumption() {
    let mut module = straight();
    let body = &mut module.functions[0].blocks[0].body;
    if let Inst::Const { value, .. } = &mut body[0].inst {
        *value = trust_ir::constant::Constant::Bool(false);
    }
    let Inst::Assert { cond, .. } = &mut body[2].inst else { panic!("fixture assert") };
    *cond = ValueId::new(999);
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDef { .. }));
}

#[test]
fn forward_definition_is_not_a_free_assumed_symbol() {
    let mut module = straight();
    let body = &mut module.functions[0].blocks[0].body;
    let definition = body.remove(0);
    body.insert(2, definition);
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDefInBlock { .. }));
}

#[test]
fn sibling_definition_is_not_available_in_the_other_arm() {
    let mut builder = ModuleBuilder::new("sibling_source");
    let signature = builder.add_func_type(vec![Ty::Bool], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let input = function.add_block_param(entry, Ty::Bool);
    let left = function.create_block();
    let right = function.create_block();
    function.switch_to_block(entry);
    function.condbr(input, left, vec![], right, vec![]);
    function.switch_to_block(left);
    let sibling = function.bool_const(true);
    function.ret(vec![]);
    function.switch_to_block(right);
    function.assume(sibling);
    function.assert(sibling);
    function.ret(vec![]);
    function.build();
    let module = builder.build().unwrap();
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDefInBlock { .. }));
}

#[test]
fn join_parameter_is_not_available_before_its_block() {
    let mut builder = ModuleBuilder::new("join_parameter_source");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let join = function.create_block();
    let joined = function.add_block_param(join, Ty::Bool);
    function.switch_to_block(entry);
    function.assume(joined);
    function.assert(joined);
    let yes = function.bool_const(true);
    function.br(join, vec![yes]);
    function.switch_to_block(join);
    function.ret(vec![]);
    function.build();
    invalid(&builder.build().unwrap(), |e| {
        matches!(e, ValidationError::UseBeforeDefInBlock { .. })
    });
}

#[test]
fn duplicate_results_cannot_overwrite_a_failing_value() {
    let mut builder = ModuleBuilder::new("duplicate_results");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let no = function.bool_const(false);
    function.bool_const(true);
    function.assert(no);
    function.ret(vec![]);
    function.build();
    let mut module = builder.build().unwrap();
    module.functions[0].blocks[0].body[1].results[0] = no;
    invalid(&module, |e| matches!(e, ValidationError::DuplicateValueDef { .. }));
}

#[test]
fn instruction_result_cannot_overwrite_an_entry_parameter() {
    let mut builder = ModuleBuilder::new("duplicate_parameter");
    let signature = builder.add_func_type(vec![Ty::Bool], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let input = function.add_block_param(entry, Ty::Bool);
    function.switch_to_block(entry);
    function.bool_const(true);
    function.assert(input);
    function.ret(vec![]);
    function.build();
    let mut module = builder.build().unwrap();
    module.functions[0].blocks[0].body[0].results[0] = input;
    invalid(&module, |e| matches!(e, ValidationError::DuplicateValueDef { .. }));
}

#[test]
fn typed_input_refusal_is_not_filtered_by_an_assumption() {
    let mut module = straight();
    let body = &mut module.functions[0].blocks[0].body;
    let mut value = body[0].clone();
    value.results[0] = ValueId::new(55);
    value.inst = Inst::Const { ty: Ty::U64, value: trust_ir::constant::Constant::Int(1) };
    body.insert(1, value);
    if let Inst::Const { value, .. } = &mut body[0].inst {
        *value = trust_ir::constant::Constant::Bool(false);
    }
    let Inst::Assert { cond, .. } = &mut body[3].inst else { panic!("fixture assert") };
    *cond = ValueId::new(55);
    invalid(&module, |_| true);
}

fn diamond(pin_left: bool, permuted: bool) -> Module {
    let mut builder = ModuleBuilder::new("valid_diamond");
    let signature = builder.add_func_type(vec![Ty::Bool], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let input = function.add_block_param(entry, Ty::Bool);
    let left = function.create_block();
    let right = function.create_block();
    let join = function.create_block();
    let joined = function.add_block_param(join, Ty::Bool);
    function.switch_to_block(entry);
    if pin_left {
        function.assume(input);
    }
    function.condbr(input, left, vec![], right, vec![]);
    function.switch_to_block(left);
    let yes = function.bool_const(true);
    function.br(join, vec![yes]);
    function.switch_to_block(right);
    let no = function.bool_const(false);
    function.br(join, vec![no]);
    function.switch_to_block(join);
    function.assert(joined);
    function.ret(vec![]);
    function.build();
    let mut module = builder.build().unwrap();
    if permuted {
        module.functions[0].blocks.reverse();
    }
    assert!(validate_module(&module).is_empty(), "positive must be canonical valid IR");
    module
}

#[test]
fn valid_dag_block_parameters_and_positional_assumptions_keep_precision() {
    for pin in [false, true] {
        for permuted in [false, true] {
            let module = diamond(pin, permuted);
            for vc in vcs(&module) {
                assert!(!vc.violations.iter().any(|v| v.kind == PropertyKind::Other));
                assert_eq!(satisfiable(&vc), !pin);
            }
        }
    }
}

#[test]
fn valid_straight_line_and_missing_function_selection_keep_their_contract() {
    let module = straight();
    assert!(validate_module(&module).is_empty());
    for vc in vcs(&module) {
        assert!(!vc.violations.iter().any(|v| v.kind == PropertyKind::Other));
        assert!(!satisfiable(&vc));
    }
    assert!(
        trust_ir_function_to_bmc_vc(
            &module,
            trust_ir::value::FuncId::new(999),
            &TranslateOptions::default()
        )
        .is_none()
    );
}

#[test]
fn invalid_empty_module_has_a_module_refusal_without_a_fictitious_function() {
    let mut builder = ModuleBuilder::new("invalid_empty_library");
    builder.add_func_type(vec![Ty::Error], vec![]);
    let module = builder.build().unwrap();
    assert!(module.functions.is_empty());
    assert!(!validate_module(&module).is_empty());
    let options = TranslateOptions { timeout_ms: Some(5000), ..TranslateOptions::default() };
    let all = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(all.len(), 1, "an invalid empty module must not become empty success");
    check_refusal_vc(&all[0]);
    assert_eq!(all[0].query.timeout_ms, Some(5000));
    assert_eq!(all[0].query.logic.as_deref(), Some("QF_BV"));
    assert!(all[0].query.produce_model);
    assert!(
        trust_ir_function_to_bmc_vc(&module, trust_ir::value::FuncId::new(0), &options).is_none(),
        "absent selection is refusal to translate, never an invented function"
    );
}

#[test]
fn valid_empty_library_has_no_function_obligations_or_selection() {
    let module = ModuleBuilder::new("valid_empty_library").build().unwrap();
    assert!(validate_module(&module).is_empty());
    assert!(trust_ir_to_bmc_vc(&module, &TranslateOptions::default()).is_empty());
    assert!(
        trust_ir_function_to_bmc_vc(
            &module,
            trust_ir::value::FuncId::new(0),
            &TranslateOptions::default()
        )
        .is_none()
    );
}

#[test]
fn selected_function_does_not_bypass_complete_module_validity() {
    let mut module = straight();
    let mut bad = module.functions[0].clone();
    bad.id = trust_ir::value::FuncId::new(1);
    bad.name = "bad_other".to_owned();
    let Inst::Assert { cond, .. } = &mut bad.blocks[0].body[2].inst else {
        panic!("fixture assert")
    };
    *cond = ValueId::new(999);
    module.functions.push(bad);
    assert!(
        validate_module(&module).iter().any(|e| matches!(e, ValidationError::UseBeforeDef { .. }))
    );
    let options = TranslateOptions::default();
    let all = trust_ir_to_bmc_vc(&module, &options);
    assert_eq!(all.len(), 1, "one module refusal, not two fabricated body results");
    check_refusal_vc(&all[0]);
    for function in &module.functions {
        check_refusal_vc(&trust_ir_function_to_bmc_vc(&module, function.id, &options).unwrap());
    }
}

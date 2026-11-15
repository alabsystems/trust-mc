// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Canonical module validity precedes CHC path reachability and source values.
//! This fixture is source-only until the designated owner executes it.

use ay_bindings::AYProgram;
use ay_bindings::execute_direct::{self, ExecuteResult};
use trust_ir::inst::Inst;
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Module, Ty};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};
use trust_mc_core::chc::ChcVc;
use trust_mc_trust_bmc::{
    TranslateOptions, trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block, trust_ir_function_to_chc_vc,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_translation_outputs_per_block,
    trust_ir_to_chc_vc,
};

// Actual AY query of an error rule's local scalar conditions, using the same
// bounded helper contract as translate_chc_smt_array_tests. This is not a CHC
// fixed-point solver or a claim of global reachability for arbitrary VCs.
fn local_error_possible(vc: &ChcVc) -> bool {
    vc.rules.iter().filter(|rule| rule.head.name.as_str() == "error").any(|rule| {
        let mut program = AYProgram::new();
        program.set_logic("QF_BV");
        for variable in vc.vars() {
            let _ = program.declare_const(variable.name.to_string(), variable.sort.clone());
        }
        for constraint in rule.body.constraints.iter() {
            program.assert(constraint.clone());
        }
        program.check_sat();
        match execute_direct::execute(&program).expect("actual in-process AY scalar query") {
            ExecuteResult::Counterexample { .. } => true,
            ExecuteResult::Verified => false,
            other => panic!("incomplete scalar answer is not a test pass: {other:?}"),
        }
    })
}

fn refusal(vc: &ChcVc) {
    assert!(local_error_possible(vc), "malformed module has no satisfiable error charge");
    assert!(vc.decls.is_empty(), "invalid input must not declare source symbols");
    assert!(vc.vars().is_empty(), "invalid input must not invent SSA havoc");
    assert_eq!(vc.relations.len(), 1);
    assert_eq!(vc.relations[0].name.as_str(), "error");
    assert!(vc.relations[0].arg_sorts.is_empty());
    assert_eq!(vc.rules.len(), 1);
    let fact = &vc.rules[0];
    assert!(fact.body.relation.is_none());
    assert!(fact.body.constraints.is_empty(), "no assumption may hide invalidity");
    assert_eq!(fact.head.name.as_str(), "error");
    assert!(fact.head.args.is_empty());
    assert_eq!(vc.query.target.as_deref(), Some("error"));
}

fn invalid(module: &Module, predicate: impl Fn(&ValidationError) -> bool) {
    let errors = validate_module(module);
    assert!(!errors.is_empty(), "hostile fixture must be canonically invalid");
    assert!(errors.iter().any(predicate), "wrong invalidity: {errors:?}");
    let options = TranslateOptions { timeout_ms: Some(5000), ..TranslateOptions::default() };
    let all = trust_ir_to_chc_vc(module, &options);
    assert_eq!(all.len(), 1, "one module refusal, even with zero functions");
    refusal(&all[0]);
    assert_eq!(all[0].query.timeout_ms, Some(5000));
    for outputs in [
        trust_ir_to_chc_translation_outputs(module, &options),
        trust_ir_to_chc_translation_outputs_per_block(module, &options),
    ] {
        assert_eq!(outputs.len(), 1);
        refusal(&outputs[0].vc);
        assert!(
            outputs[0]
                .module_input_refusal
                .as_deref()
                .unwrap()
                .starts_with("invalid trust_ir module")
        );
        assert!(outputs[0].diagnostics.is_empty(), "no fictitious instruction ownership");
        assert!(outputs[0].inductive_hypothesis_sites.is_empty());
        assert!(outputs[0].call_summary_census.is_empty());
        assert_eq!(outputs[0].work.instructions_translated, 0);
        assert!(outputs[0].large_block.is_none());
    }
    for function in &module.functions {
        refusal(&trust_ir_function_to_chc_vc(module, function.id, &options).unwrap());
        for output in [
            trust_ir_function_to_chc_translation_output(module, function.id, &options).unwrap(),
            trust_ir_function_to_chc_translation_output_per_block(module, function.id, &options)
                .unwrap(),
        ] {
            refusal(&output.vc);
            assert!(output.module_input_refusal.is_some());
            assert!(output.diagnostics.is_empty());
        }
    }
}

fn straight() -> Module {
    let mut mb = ModuleBuilder::new("chc_input");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let no = fb.bool_const(false);
    fb.assume(no);
    let yes = fb.bool_const(true);
    fb.assert(yes);
    fb.ret(vec![]);
    fb.build();
    mb.build().unwrap()
}

#[test]
fn false_assumption_cannot_hide_undefined_predicate() {
    let mut module = straight();
    let Inst::Assert { cond, .. } = &mut module.functions[0].blocks[0].body[3].inst else {
        panic!("assert fixture")
    };
    *cond = ValueId::new(999);
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDef { .. }));
}

#[test]
fn false_assumption_cannot_hide_forward_definition() {
    let mut module = straight();
    let body = &mut module.functions[0].blocks[0].body;
    let definition = body.remove(2);
    body.insert(3, definition);
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDefInBlock { .. }));
}

#[test]
fn duplicate_result_cannot_overwrite_a_failing_assertion() {
    let mut mb = ModuleBuilder::new("chc_duplicate");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let no = fb.bool_const(false);
    fb.bool_const(true);
    fb.assert(no);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().unwrap();
    module.functions[0].blocks[0].body[1].results[0] = no;
    invalid(&module, |e| matches!(e, ValidationError::DuplicateValueDef { .. }));
}

#[test]
fn sibling_definition_cannot_supply_another_arms_assumption() {
    let mut mb = ModuleBuilder::new("chc_sibling");
    let ty = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    let input = fb.add_block_param(entry, Ty::Bool);
    let left = fb.create_block();
    let right = fb.create_block();
    fb.switch_to_block(entry);
    fb.condbr(input, left, vec![], right, vec![]);
    fb.switch_to_block(left);
    let sibling = fb.bool_const(true);
    fb.ret(vec![]);
    fb.switch_to_block(right);
    fb.assume(sibling);
    fb.assert(sibling);
    fb.ret(vec![]);
    fb.build();
    invalid(&mb.build().unwrap(), |e| matches!(e, ValidationError::UseBeforeDefInBlock { .. }));
}

#[test]
fn invalid_empty_module_has_a_real_error_query_without_a_function() {
    let mut mb = ModuleBuilder::new("chc_invalid_empty");
    mb.add_func_type(vec![Ty::Error], vec![]);
    let module = mb.build().unwrap();
    assert!(module.functions.is_empty());
    invalid(&module, |_| true);
    assert!(
        trust_ir_function_to_chc_vc(&module, FuncId::new(0), &TranslateOptions::default())
            .is_none()
    );
}

#[test]
fn canonical_invalidity_of_another_function_refuses_the_whole_module() {
    let mut module = straight();
    let mut other = module.functions[0].clone();
    other.id = FuncId::new(1);
    other.name = "other_invalid".into();
    let Inst::Assert { cond, .. } = &mut other.blocks[0].body[3].inst else {
        panic!("assert fixture")
    };
    *cond = ValueId::new(999);
    module.functions.push(other);
    invalid(&module, |e| matches!(e, ValidationError::UseBeforeDef { .. }));
}

#[test]
fn valid_empty_library_and_missing_selection_grant_no_function_result() {
    let module = ModuleBuilder::new("chc_valid_empty").build().unwrap();
    assert!(validate_module(&module).is_empty());
    let options = TranslateOptions::default();
    assert!(trust_ir_to_chc_vc(&module, &options).is_empty());
    assert!(trust_ir_to_chc_translation_outputs_per_block(&module, &options).is_empty());
    assert!(
        trust_ir_function_to_chc_translation_output(&module, FuncId::new(0), &options).is_none()
    );
}

#[test]
fn valid_dag_precision_and_permuted_storage_are_preserved() {
    for fails in [false, true] {
        let mut mb = ModuleBuilder::new("chc_valid_dag");
        let ty = mb.add_func_type(vec![Ty::Bool], vec![]);
        let mut fb = mb.function("subject", ty);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, Ty::Bool);
        let left = fb.create_block();
        let right = fb.create_block();
        fb.switch_to_block(entry);
        fb.condbr(input, left, vec![], right, vec![]);
        fb.switch_to_block(left);
        let yes = fb.bool_const(true);
        fb.assert(yes);
        fb.ret(vec![]);
        fb.switch_to_block(right);
        let value = fb.bool_const(!fails);
        fb.assert(value);
        fb.ret(vec![]);
        fb.build();
        let mut module = mb.build().unwrap();
        for permuted in [false, true] {
            if permuted {
                module.functions[0].blocks.swap(1, 2);
            }
            assert!(validate_module(&module).is_empty());
            let options = TranslateOptions::default();
            for outputs in [
                trust_ir_to_chc_translation_outputs(&module, &options),
                trust_ir_to_chc_translation_outputs_per_block(&module, &options),
            ] {
                assert_eq!(outputs.len(), 1);
                assert!(outputs[0].module_input_refusal.is_none());
                assert!(outputs[0].diagnostics.is_empty());
                // This fixture has no assumptions; both arms are inhabited
                // by a free entry Bool, and the check values are constants.
                assert_eq!(local_error_possible(&outputs[0].vc), fails);
            }
        }
    }
}

#[cfg(feature = "legacy-liveness-oracle")]
#[test]
fn legacy_oracle_does_not_bypass_the_same_module_boundary() {
    let mut module = straight();
    let Inst::Assert { cond, .. } = &mut module.functions[0].blocks[0].body[3].inst else {
        panic!("assert fixture")
    };
    *cond = ValueId::new(999);
    assert!(!validate_module(&module).is_empty());
    let output =
        trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_with_legacy_liveness(
            &module,
            module.functions[0].id,
            &TranslateOptions::default(),
        )
        .unwrap();
    refusal(&output.vc);
    assert!(output.module_input_refusal.is_some());
    assert!(output.diagnostics.is_empty());
}

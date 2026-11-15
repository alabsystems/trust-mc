// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact constructed enum arguments, without assumptions about arbitrary entry values.

#[path = "fixtures/dataless_enum.rs"]
mod fixture;
use fixture::{
    fixture, phi_fixture, scalar_fixture, summarized_select_fixture, symbolic_fixture,
    tag_write_fixture,
};

use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{EnumId, FuncId};
use trust_mc_trust_bmc::{
    CallSummaryOutcome, TranslateOptions, trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block,
};

#[test]
fn constructed_sparse_enum_calls_validate_execute_and_summarize() {
    for make in [false, true] {
        for nested in [false, true] {
            let (module, main) = fixture(make, nested, 7);
            let run = Interpreter::with_module(&module).execute_func(main, []).unwrap();
            assert_eq!(run.host_calls, 0);
            assert_eq!(run.returns, vec![InterpretValue::int(Ty::I16, 7).unwrap()]);
            let options = TranslateOptions {
                collect_call_summary_census: true,
                ..TranslateOptions::default()
            };
            for output in [
                trust_ir_function_to_chc_translation_output(&module, main, &options).unwrap(),
                trust_ir_function_to_chc_translation_output_per_block(&module, main, &options)
                    .unwrap(),
            ] {
                assert!(output.diagnostics.is_empty(), "{make}/{nested}: {:?}", output.diagnostics);
                assert!(!output.call_summary_census.is_empty());
                assert!(
                    output
                        .call_summary_census
                        .iter()
                        .all(|attempt| { attempt.outcome == CallSummaryOutcome::Summarized }),
                    "{make}/{nested}: {:?}",
                    output.call_summary_census
                );
            }
        }
    }
}

#[test]
fn a_typed_enum_entry_does_not_assert_membership_or_tag_shape() {
    let (module, _) = fixture(false, false, 7);
    let ty = Ty::Enum(EnumId::new(0));
    // The interpreter accepts a non-variant tag supplied at an entry. A
    // translator must never turn the enum's variant list into an assumption.
    let arbitrary = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue::int(Ty::I16, 99).unwrap()]),
    };
    let run = Interpreter::with_module(&module).execute_func(FuncId::new(0), [arbitrary]).unwrap();
    assert_eq!(run.returns, vec![InterpretValue::int(Ty::I16, 99).unwrap()]);
    // Even the outer enum type does not establish an initialized, correctly
    // shaped tag. These inputs cross entry but must fail when inspected.
    for kind in [
        InterpretValueKind::Bool(true),
        InterpretValueKind::Aggregate(vec![]),
        InterpretValueKind::Aggregate(vec![InterpretValue::bool(true)]),
        InterpretValueKind::Aggregate(vec![InterpretValue {
            ty: Ty::I16,
            kind: InterpretValueKind::Uninit,
        }]),
    ] {
        assert!(
            Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [InterpretValue { ty: ty.clone(), kind }])
                .is_err()
        );
    }
    let forged = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue {
            ty: Ty::I16,
            kind: InterpretValueKind::Int(trust_ir::interpret::InterpretInt {
                bits: 64,
                signed: false,
                raw: 100_000,
            }),
        }]),
    };
    // A nominal enum entry still grants no variant-membership assumption, but
    // its integer payload must have the declared width and signedness.
    let error =
        Interpreter::with_module(&module).execute_func(FuncId::new(0), [forged]).unwrap_err();
    assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::TypeError);
    assert!(error.message.contains("malformed i16 integer payload"), "{error:?}");
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .unwrap();
    assert!(!output.diagnostics.is_empty(), "raw enum entry inspection stays refused");
}

#[test]
fn scalar_twins_and_symbolic_constructor_choices_execute_without_host_help() {
    for nested in [false, true] {
        let (scalar, main) = scalar_fixture(nested, 7);
        let run = Interpreter::with_module(&scalar).execute_func(main, []).unwrap();
        assert_eq!(run.host_calls, 0);
        assert_eq!(run.returns, vec![InterpretValue::int(Ty::I16, 7).unwrap()]);
        let output = trust_ir_function_to_chc_translation_output(
            &scalar,
            main,
            &TranslateOptions::default(),
        )
        .unwrap();
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        for make in [false, true] {
            let (module, main) = symbolic_fixture(make, nested, 7);
            assert!(trust_ir_build::validate_module(&module).is_empty());
            for choice in [false, true] {
                let run = Interpreter::with_module(&module)
                    .execute_func(main, [InterpretValue::bool(choice)])
                    .unwrap();
                assert_eq!(run.host_calls, 0);
                assert_eq!(
                    run.returns,
                    vec![InterpretValue::int(Ty::I16, if choice { 7 } else { -5 },).unwrap()]
                );
            }
            let output = trust_ir_function_to_chc_translation_output(
                &module,
                main,
                &TranslateOptions::default(),
            )
            .unwrap();
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        }
    }
}

#[test]
fn wrong_relations_and_different_same_signature_bodies_really_fail() {
    let (module, main) = fixture(true, true, -5);
    assert!(Interpreter::with_module(&module).execute_func(main, []).is_err());
    let (module, main) = symbolic_fixture(false, true, 6);
    assert!(
        Interpreter::with_module(&module).execute_func(main, [InterpretValue::bool(true)]).is_err()
    );
    assert!(
        Interpreter::with_module(&module).execute_func(main, [InterpretValue::bool(false)]).is_ok()
    );
    let (mut module, main) = fixture(false, false, 7);
    let reader = module.functions.iter_mut().find(|f| f.name == "read_tag").unwrap();
    reader.blocks[0].body[0].inst =
        trust_ir::Inst::Const { ty: Ty::I16, value: trust_ir::Constant::Int(-5) };
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert!(Interpreter::with_module(&module).execute_func(main, []).is_err());
}

#[test]
fn enum_phi_joins_preserve_both_constructed_discriminants() {
    for nested in [false, true] {
        let (module, main) = phi_fixture(true, nested, 7);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        for choice in [false, true] {
            let run = Interpreter::with_module(&module)
                .execute_func(main, [InterpretValue::bool(choice)])
                .unwrap();
            assert_eq!(run.returns[0].as_int().unwrap().as_signed(), if choice { 7 } else { -5 });
        }
        for output in [
            trust_ir_function_to_chc_translation_output(
                &module,
                main,
                &TranslateOptions::default(),
            )
            .unwrap(),
            trust_ir_function_to_chc_translation_output_per_block(
                &module,
                main,
                &TranslateOptions::default(),
            )
            .unwrap(),
        ] {
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        }
    }
}

#[test]
fn even_unused_tag_updates_remain_undefined_and_refused_in_callees() {
    for inside in [false, true] {
        let (module, main) = tag_write_fixture(inside);
        let errors = trust_ir_build::validate_module(&module);
        assert!(
            format!("{errors:?}").contains("cannot rewrite an enum discriminant"),
            "the typed validator must reject tag updates: {errors:?}"
        );
        let error = Interpreter::with_module(&module).execute_func(main, []).unwrap_err();
        assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::UndefinedBehavior);
        let output = trust_ir_function_to_chc_translation_output(
            &module,
            main,
            &TranslateOptions::default(),
        )
        .unwrap();
        assert!(output.module_input_refusal.is_some(), "dead tag writes must not disappear");
        assert!(output.diagnostics.is_empty(), "invalidity has no invented instruction site");
        assert_eq!(output.vc.rules.len(), 1);
        let rule = &output.vc.rules[0];
        assert_eq!(rule.head.name, "error");
        assert!(rule.body.relation.is_none());
        assert!(rule.body.constraints.is_empty());
    }
}

#[test]
fn enum_select_inside_a_summarized_callee_preserves_its_tag() {
    for make in [false, true] {
        for nested in [false, true] {
            let (module, main) = summarized_select_fixture(make, nested, 7);
            assert!(trust_ir_build::validate_module(&module).is_empty());
            for choice in [false, true] {
                let run = Interpreter::with_module(&module)
                    .execute_func(main, [InterpretValue::bool(choice)])
                    .unwrap();
                assert_eq!(
                    run.returns[0].as_int().unwrap().as_signed(),
                    if choice { 7 } else { -5 }
                );
            }
            let output = trust_ir_function_to_chc_translation_output(
                &module,
                main,
                &TranslateOptions::default(),
            )
            .unwrap();
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        }
    }
}

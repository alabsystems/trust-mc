// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::{
    SourceReferenceFacts, SourceReferenceLoadFact, SourceReferenceParameterFact,
    SourceReferenceValueFact,
};
use trust_ir::{NativeVerificationBundle, SourceGenerationAuthority};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy)]
enum Actual {
    Parameter,
    InitializedCell,
    PoisonCell,
    StoreAfterCall,
    PartialAggregate,
    Null,
    Fabricated,
}

fn fixture(actual: Actual, nested: bool, zero_divisor: bool) -> (NativeVerificationBundle, FuncId) {
    let mut mb = ModuleBuilder::new("source_reference_consumption");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("read_with_own_assertion", ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    let divisor = fb.add_block_param(entry, Ty::U32);
    let loaded = fb.load(Ty::U32, pointer);
    let zero = fb.iconst(Ty::U32, 0);
    let nonzero = fb.icmp(ICmpOp::Ne, Ty::U32, divisor, zero);
    fb.assert(nonzero);
    fb.ret(vec![loaded]);
    fb.build();
    if nested {
        let mut fb = mb.function("forward_reference", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        let divisor = fb.add_block_param(entry, Ty::U32);
        let result = fb.call(FuncId::new(0), vec![pointer, divisor]);
        fb.ret(vec![result]);
        fb.build();
    }
    let root = FuncId::new(if nested { 2 } else { 1 });
    let root_ft = mb.add_func_type(
        if matches!(actual, Actual::Parameter) { vec![Ty::Ptr] } else { vec![] },
        vec![Ty::U32],
    );
    let mut fb = mb.function("root", root_ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let pointer = match actual {
        Actual::Parameter => {
            let value = fb.add_block_param(entry, Ty::Ptr);
            fb.copy(Ty::Ptr, value)
        }
        Actual::InitializedCell | Actual::PoisonCell => {
            let cell = fb.alloca(Ty::U32);
            let value = if matches!(actual, Actual::PoisonCell) {
                fb.undef(Ty::U32)
            } else {
                fb.iconst(Ty::U32, 7)
            };
            fb.store(Ty::U32, cell, value);
            cell
        }
        Actual::StoreAfterCall => fb.alloca(Ty::U32),
        Actual::PartialAggregate => {
            let ty = Ty::Tuple(vec![Ty::U32, Ty::U32]);
            let cell = fb.alloca(ty.clone());
            let value = fb.const_value(
                ty.clone(),
                Constant::Aggregate(vec![Constant::Int(7), Constant::Uninit]),
            );
            fb.store(ty, cell, value);
            cell
        }
        Actual::Null => fb.null_ptr(),
        Actual::Fabricated => {
            let bits = fb.iconst(Ty::U64, 4096);
            fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, bits)
        }
    };
    let divisor = fb.iconst(Ty::U32, if zero_divisor { 0 } else { 2 });
    let result = fb.call(FuncId::new(if nested { 1 } else { 0 }), vec![pointer, divisor]);
    if matches!(actual, Actual::StoreAfterCall) {
        let seven = fb.iconst(Ty::U32, 7);
        fb.store(Ty::U32, pointer, seven);
    }
    fb.ret(vec![result]);
    fb.build();
    let mut module = mb.build().unwrap();
    for node in module.functions[0].blocks.iter_mut().flat_map(|block| &mut block.body) {
        if matches!(&node.inst, Inst::Load { .. }) {
            node.proofs.push(ProofAnnotation::ValidBorrow);
        }
    }
    (crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1), root)
}

fn records(
    bundle: &NativeVerificationBundle,
) -> (Vec<SourceReferenceParameterFact>, Vec<SourceReferenceLoadFact>) {
    let mut parameters = Vec::new();
    let mut loads = Vec::new();
    for function in &bundle.module.functions {
        let Some(entry) = function.block(function.entry) else { continue };
        for (position, (value, ty)) in entry.params.iter().enumerate() {
            if *ty == Ty::Ptr {
                parameters.push(SourceReferenceParameterFact {
                    function: function.id,
                    parameter_index: position as u32,
                    value: *value,
                    pointee: Ty::U32,
                });
            }
        }
        for block in &function.blocks {
            for (position, node) in block.body.iter().enumerate() {
                if let Inst::Load { ty, ptr, .. } = &node.inst {
                    loads.push(SourceReferenceLoadFact {
                        function: function.id,
                        block: block.id,
                        instruction_index: position as u32,
                        result: node.results[0],
                        pointer: *ptr,
                        pointee: ty.clone(),
                    });
                }
            }
        }
    }
    (parameters, loads)
}

fn live_output(
    bundle: &NativeVerificationBundle,
    root: FuncId,
    facts: &SourceReferenceFacts<'_>,
) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output_with_source_references(
        &bundle.module,
        root,
        &TranslateOptions::default(),
        facts,
    )
    .unwrap()
}

#[test]
fn explicit_live_reference_facts_restore_direct_and_nested_load_consumption() {
    for nested in [false, true] {
        let (mut bundle, root) = fixture(Actual::Parameter, nested, false);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let old = trust_ir_function_to_chc_translation_output(
            &bundle.module,
            root,
            &TranslateOptions::default(),
        )
        .unwrap();
        assert!(
            old.diagnostics
                .iter()
                .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary)
        );
        let output = live_output(&bundle, root, &facts);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(!smt_array_tests::error_reachable(&output));
    }
}

#[test]
fn reference_parameter_facts_require_initialized_correctly_typed_actual_pointees() {
    for actual in [
        Actual::InitializedCell,
        Actual::PoisonCell,
        Actual::StoreAfterCall,
        Actual::PartialAggregate,
        Actual::Null,
        Actual::Fabricated,
    ] {
        let (mut bundle, root) = fixture(actual, true, false);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = live_output(&bundle, root, &facts);
        if matches!(actual, Actual::InitializedCell) {
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert!(!smt_array_tests::error_reachable(&output));
        } else {
            assert!(
                output
                    .diagnostics
                    .iter()
                    .any(|d| d.reason == TrustIrChcUnsupportedReason::CallArgumentTransport)
            );
            assert!(smt_array_tests::error_reachable(&output));
        }
    }
}

#[test]
fn load_and_parameter_claims_are_both_required_and_do_not_discharge_assertions() {
    for omit in [0, 1, 2] {
        let (mut bundle, root) = fixture(Actual::Parameter, true, false);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (mut parameters, mut loads) = records(&bundle);
        if omit != 1 {
            parameters.clear();
        }
        if omit != 0 {
            loads.clear();
        }
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = live_output(&bundle, root, &facts);
        assert!(!output.diagnostics.is_empty());
        assert!(smt_array_tests::error_reachable(&output));
    }
    let (mut bundle, root) = fixture(Actual::Parameter, true, true);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let (parameters, loads) = records(&bundle);
    let facts =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
            .unwrap();
    let output = live_output(&bundle, root, &facts);
    assert!(output.diagnostics.is_empty());
    assert!(
        smt_array_tests::error_reachable(&output),
        "a genuine failed assertion stays reachable"
    );
}

#[test]
fn initialized_load_memo_is_scoped_to_each_actual_reference_context() {
    let (mut bundle, root) = fixture(Actual::Parameter, false, false);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let (parameters, loads) = records(&bundle);
    let loaded = loads[0].result;
    let facts =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
            .unwrap();
    let analysis =
        construction_definedness::Analysis::with_source_references(&bundle.module, root, &facts);
    let callee = &bundle.module.functions[0];
    for initialized in [true, false, true, false] {
        let _scope = analysis.enter_reference_arguments(callee.id, vec![initialized, false]);
        assert_eq!(
            construction_definedness::value_is_defined(
                &analysis,
                &bundle.module,
                callee,
                loaded,
                Some(&[true, true]),
            ),
            initialized
        );
    }
    {
        let _outer = analysis.enter_reference_arguments(callee.id, vec![true, false]);
        {
            let _inner = analysis.enter_reference_arguments(callee.id, vec![false, false]);
            assert!(!construction_definedness::value_is_defined(
                &analysis,
                &bundle.module,
                callee,
                loaded,
                Some(&[true, true]),
            ));
        }
        assert!(construction_definedness::value_is_defined(
            &analysis,
            &bundle.module,
            callee,
            loaded,
            Some(&[true, true]),
        ));
    }
    assert!(!construction_definedness::value_is_defined(
        &analysis,
        &bundle.module,
        callee,
        loaded,
        Some(&[true, true]),
    ));
}

#[test]
fn the_same_nested_callee_keeps_good_and_poisoned_actuals_distinct_in_both_orders() {
    for bad_first in [false, true] {
        let (bundle, root) = fixture(Actual::Parameter, true, false);
        let mut module = bundle.module;
        let function = module.functions.iter_mut().find(|function| function.id == root).unwrap();
        let block = function.block_mut(function.entry).unwrap();
        let call_position =
            block.body.iter().position(|node| matches!(node.inst, Inst::Call { .. })).unwrap();
        let Inst::Call { callee, args } = &block.body[call_position].inst else { unreachable!() };
        let target = *callee;
        let divisor = args[1];
        let next = block
            .body
            .iter()
            .flat_map(|node| &node.results)
            .map(|value| value.index())
            .max()
            .unwrap()
            + 1;
        let pointer = ValueId::new(next);
        let poison = ValueId::new(next + 1);
        let result = ValueId::new(next + 2);
        let extra = [
            InstrNode::new(Inst::Alloca { ty: Ty::U32, count: None, align: None })
                .with_result(pointer),
            InstrNode::new(Inst::Undef { ty: Ty::U32 }).with_result(poison),
            InstrNode::new(Inst::Store {
                ty: Ty::U32,
                ptr: pointer,
                value: poison,
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Call { callee: target, args: vec![pointer, divisor] })
                .with_result(result),
        ];
        let insert = call_position + usize::from(!bad_first);
        block.body.splice(insert..insert, extra);
        module.proof_obligations.clear();
        let mut bundle =
            crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let options = TranslateOptions { collect_call_summary_census: true, ..Default::default() };
        let output = trust_ir_function_to_chc_translation_output_with_source_references(
            &bundle.module,
            root,
            &options,
            &facts,
        )
        .unwrap();
        assert_eq!(
            output
                .call_summary_census
                .iter()
                .filter(|attempt| matches!(attempt.outcome, CallSummaryOutcome::Summarized))
                .count(),
            1
        );
        assert_eq!(
            output
                .call_summary_census
                .iter()
                .filter(|attempt| matches!(
                    attempt.outcome,
                    CallSummaryOutcome::NotAttempted { reason: "call_argument_transport" }
                ))
                .count(),
            1
        );
        assert!(smt_array_tests::error_reachable(&output));
    }
}

#[test]
fn source_reference_context_rejects_replay_wrong_authority_and_mismatched_sites() {
    let (mut bundle, _) = fixture(Actual::Parameter, false, false);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let (parameters, loads) = records(&bundle);
    let facts =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
            .unwrap();
    let copied = bundle.clone();
    assert!(!facts.authorizes_bundle(&copied, &authority));
    let decoded: NativeVerificationBundle =
        serde_json::from_slice(&serde_json::to_vec(&bundle).unwrap()).unwrap();
    assert!(!facts.authorizes_bundle(&decoded, &authority));
    let (mut other, _) = fixture(Actual::Parameter, false, false);
    let other_authority = SourceGenerationAuthority::mint_from_live_lowering(&mut other).unwrap();
    assert!(!facts.authorizes_bundle(&bundle, &other_authority));
    for case in 0..6 {
        let (mut parameters, mut loads) = records(&bundle);
        match case {
            0 => parameters[0].pointee = Ty::U64,
            1 => loads[0].pointee = Ty::U64,
            2 => loads[0].pointer = ValueId::new(999),
            3 => loads[0].result = ValueId::new(999),
            4 => loads[0].instruction_index = u32::MAX,
            _ => parameters[0].value = ValueId::new(999),
        }
        let result =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads);
        assert!(result.is_err(), "case {case}");
    }
}

#[test]
fn an_explicit_load_claim_cannot_override_poison_in_a_known_local_cell() {
    for poisoned in [false, true] {
        let mut mb = ModuleBuilder::new("source_reference_local_poison");
        let ft = mb.add_func_type(vec![], vec![Ty::U32]);
        let mut fb = mb.function("local_load", ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let pointer = fb.alloca(Ty::U32);
        let value = if poisoned { fb.undef(Ty::U32) } else { fb.iconst(Ty::U32, 7) };
        fb.store(Ty::U32, pointer, value);
        let loaded = fb.load(Ty::U32, pointer);
        fb.ret(vec![loaded]);
        fb.build();
        let mut module = mb.build().unwrap();
        for node in &mut module.functions[0].blocks[0].body {
            if matches!(node.inst, Inst::Load { .. }) {
                node.proofs.push(ProofAnnotation::ValidBorrow);
            }
        }
        let mut bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
            module,
            FuncId::new(0),
            1,
        );
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = live_output(&bundle, FuncId::new(0), &facts);
        if poisoned {
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            assert!(smt_array_tests::error_reachable(&output));
        } else {
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert!(!smt_array_tests::error_reachable(&output));
        }
    }
}

#[test]
fn entry_reference_premises_do_not_survive_parameter_poison_or_opaque_mutation() {
    for nested in [false, true] {
        for mutation in 0..3 {
            let (bundle, outer) = fixture(Actual::Parameter, nested, false);
            let mut module = bundle.module;
            let reader = &module.functions[0];
            let pointer = reader.blocks[0].params[0].0;
            let divisor = reader.blocks[0].params[1].0;
            let fresh = reader.blocks[0]
                .body
                .iter()
                .flat_map(|node| &node.results)
                .map(|value| value.index())
                .max()
                .unwrap()
                + 1;
            if mutation != 0 {
                let mut mutator = reader.clone();
                mutator.id = FuncId::new(99);
                mutator.name = "separate_parameter_mutator".to_string();
                if mutation == 2 {
                    // A declaration can mutate through the argument or another
                    // alias. Its missing body is never a read-only certificate.
                    mutator.blocks.clear();
                    module.target_info = Some(crate::tests::fixture_target());
                } else {
                    mutator.blocks[0].body = vec![
                        InstrNode::new(Inst::Undef { ty: Ty::U32 })
                            .with_result(ValueId::new(fresh)),
                        InstrNode::new(Inst::Store {
                            ty: Ty::U32,
                            ptr: pointer,
                            value: ValueId::new(fresh),
                            volatile: false,
                            align: None,
                        })
                        .with_proof(ProofAnnotation::ValidBorrow),
                        InstrNode::new(Inst::Return { values: vec![divisor] }),
                    ];
                }
                module.functions.push(mutator);
            }
            let reader = &mut module.functions[0];
            let before = if mutation == 0 {
                vec![
                    InstrNode::new(Inst::Undef { ty: Ty::U32 }).with_result(ValueId::new(fresh)),
                    InstrNode::new(Inst::Store {
                        ty: Ty::U32,
                        ptr: pointer,
                        value: ValueId::new(fresh),
                        volatile: false,
                        align: None,
                    })
                    .with_proof(ProofAnnotation::ValidBorrow),
                ]
            } else {
                vec![
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(99),
                        args: vec![pointer, divisor],
                    })
                    .with_result(ValueId::new(fresh)),
                ]
            };
            reader.blocks[0].body.splice(0..0, before);
            module.proof_obligations.clear();
            let selected = if nested { outer } else { FuncId::new(0) };
            let mut bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
                module, selected, 1,
            );
            let authority =
                SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
            let (parameters, loads) = records(&bundle);
            let loaded = loads[0].result;
            let facts = SourceReferenceFacts::from_live_source_lowering(
                &bundle, &authority, parameters, loads,
            )
            .unwrap();
            let analysis = construction_definedness::Analysis::with_source_references(
                &bundle.module,
                selected,
                &facts,
            );
            let _scope = nested
                .then(|| analysis.enter_reference_arguments(FuncId::new(0), vec![true, false]));
            assert!(
                !construction_definedness::value_is_defined(
                    &analysis,
                    &bundle.module,
                    &bundle.module.functions[0],
                    loaded,
                    Some(&[true, true]),
                ),
                "nested={nested} mutation={mutation}"
            );
            let output = live_output(&bundle, selected, &facts);
            assert!(!output.diagnostics.is_empty(), "nested={nested} mutation={mutation}");
            assert!(smt_array_tests::error_reachable(&output));
        }
    }
}

fn reference_value_fixture(
    mode: u8,
) -> (NativeVerificationBundle, FuncId, SourceReferenceValueFact) {
    let mut mb = ModuleBuilder::new("initialized_reference_value");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U32]);
    for function in 0..2 {
        let mut fb =
            mb.function(if function == 0 { "ignore_reference_bits" } else { "forward_value" }, ft);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        let result = if function == 0 {
            fb.iconst(Ty::U32, 7)
        } else {
            fb.call(FuncId::new(0), vec![pointer])
        };
        fb.ret(vec![result]);
        fb.build();
    }
    let root = FuncId::new(2);
    let root_ft = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("reference_value_root", root_ft);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let opaque = fb.undef(Ty::Ptr);
    let pointer = fb.copy(Ty::Ptr, opaque);
    let result = match mode {
        1 | 2 => fb.load(Ty::U32, pointer),
        3 | 4 => {
            let null = fb.null_ptr();
            let predicate =
                fb.icmp(if mode == 3 { ICmpOp::Ne } else { ICmpOp::Eq }, Ty::Ptr, pointer, null);
            fb.assert(predicate);
            fb.iconst(Ty::U32, 7)
        }
        _ => {
            let result = fb.call(FuncId::new(1), vec![pointer]);
            let seven = fb.iconst(Ty::U32, 7);
            let equal = fb.icmp(ICmpOp::Eq, Ty::U32, result, seven);
            fb.assert(equal);
            result
        }
    };
    fb.ret(vec![result]);
    fb.build();
    let mut module = mb.build().unwrap();
    for node in &mut module.functions[2].blocks[0].body {
        if node.results.contains(&opaque) {
            node.proofs.push(ProofAnnotation::FreshSymbolicHavoc);
        }
        if mode == 2 && matches!(node.inst, Inst::Load { .. }) {
            node.proofs.push(ProofAnnotation::ValidBorrow);
        }
    }
    let fact = SourceReferenceValueFact {
        function: root,
        block: entry,
        instruction_index: 0,
        result: opaque,
    };
    let bundle =
        crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1);
    (bundle, root, fact)
}

#[test]
fn separately_issued_reference_value_fact_only_establishes_nested_value_transport() {
    let (mut bundle, root, value) = reference_value_fixture(0);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let marker_only =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, vec![], vec![])
            .unwrap();
    assert_eq!(marker_only.reference_value_count(), 0);
    let refused = live_output(&bundle, root, &marker_only);
    assert!(
        refused
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason
                == TrustIrChcUnsupportedReason::CallArgumentTransport)
    );
    let issued = SourceReferenceFacts::from_live_source_lowering_with_values(
        &bundle,
        &authority,
        vec![],
        vec![],
        vec![value],
    )
    .unwrap();
    assert_eq!(issued.reference_value_count(), 1);
    let output = live_output(&bundle, root, &issued);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert!(!smt_array_tests::error_reachable(&output));
    let public = trust_ir_function_to_chc_translation_output(
        &bundle.module,
        root,
        &TranslateOptions::default(),
    )
    .unwrap();
    assert!(
        public
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason
                == TrustIrChcUnsupportedReason::CallArgumentTransport)
    );
}

#[test]
fn reference_value_fact_never_supplies_a_pointee_permission_or_pointer_bit_constraint() {
    for mode in 1..=4 {
        let (mut bundle, root, value) = reference_value_fixture(mode);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let load_claims = if mode == 2 { records(&bundle).1 } else { vec![] };
        let facts = SourceReferenceFacts::from_live_source_lowering_with_values(
            &bundle,
            &authority,
            vec![],
            load_claims,
            vec![value],
        )
        .unwrap();
        let output = live_output(&bundle, root, &facts);
        if mode <= 2 {
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            if mode == 1 {
                assert!(output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel));
            }
        } else {
            assert!(output.diagnostics.is_empty());
        }
        assert!(smt_array_tests::error_reachable(&output), "mode {mode}: no memory/bit assumption");
    }
}

#[test]
fn reference_value_record_rejects_replay_mismatch_duplicates_and_unmarked_or_wrong_typed_sites() {
    for case in 0..9 {
        let (mut bundle, _, mut value) = reference_value_fixture(0);
        if case == 6 {
            bundle.module.functions[2].blocks[0].body[0].proofs.clear();
        }
        if case == 7 {
            bundle.module.functions[2].blocks[0].body = vec![
                InstrNode::new(Inst::Undef { ty: Ty::U64 })
                    .with_result(value.result)
                    .with_proof(ProofAnnotation::FreshSymbolicHavoc),
                InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(7) })
                    .with_result(ValueId::new(value.result.index() + 1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(value.result.index() + 1)],
                }),
            ];
        }
        // Rebuild identity before the live mint for mutated-but-well-bound sites.
        if case >= 6 {
            let mut module = bundle.module;
            module.proof_obligations.clear();
            bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
                module,
                FuncId::new(2),
                1,
            );
        }
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        match case {
            0 => value.function = FuncId::new(999),
            1 => value.block = BlockId::new(999),
            2 => value.instruction_index = 1,
            3 => value.result = ValueId::new(999),
            _ => {}
        }
        let mut values = vec![];
        if case == 4 {
            values.push(SourceReferenceValueFact {
                function: value.function,
                block: value.block,
                instruction_index: value.instruction_index,
                result: value.result,
            });
        }
        values.push(value);
        let copied = if case == 8 {
            serde_json::from_slice(&serde_json::to_vec(&bundle).unwrap()).unwrap()
        } else {
            bundle.clone()
        };
        let input = if case == 5 || case == 8 { &copied } else { &bundle };
        assert!(
            SourceReferenceFacts::from_live_source_lowering_with_values(
                input,
                &authority,
                vec![],
                vec![],
                values,
            )
            .is_err(),
            "case {case}"
        );
    }
}

#[test]
fn initialized_reference_value_does_not_satisfy_a_callee_pointee_requirement() {
    let (mut bundle, root, value) = reference_value_fixture(0);
    let parameter = bundle.module.functions[1].blocks[0].params[0].0;
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let facts = SourceReferenceFacts::from_live_source_lowering_with_values(
        &bundle,
        &authority,
        vec![SourceReferenceParameterFact {
            function: FuncId::new(1),
            parameter_index: 0,
            value: parameter,
            pointee: Ty::U32,
        }],
        vec![],
        vec![value],
    )
    .unwrap();
    let output = live_output(&bundle, root, &facts);
    assert!(
        output
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason
                == TrustIrChcUnsupportedReason::CallArgumentTransport)
    );
    assert!(smt_array_tests::error_reachable(&output));
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Consumer tests for explicit live-source finite-product claims. These fixtures
//! do not issue or qualify the compiler's original-source-type certificates.

use super::*;
use crate::{SourceReferenceFacts, SourceReferenceLoadFact, SourceReferenceParameterFact};
use trust_ir::{NativeVerificationBundle, SourceGenerationAuthority};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug)]
enum Actual {
    Reference,
    Initialized,
    Partial,
    Poison,
    StoreAfterCall,
    Fabricated,
}

fn fixture(
    actual: Actual,
    nested: bool,
    wrong_assertion: bool,
) -> (NativeVerificationBundle, FuncId, Ty) {
    let mut mb = ModuleBuilder::new("source_reference_product");
    let fields = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
    // Padding is deliberately present: the claim is about logical fields only.
    let id = mb.add_struct(trust_ir::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Handle".into(),
        fields: vec![
            trust_ir::FieldDef { name: "fields".into(), ty: fields.clone(), offset: Some(0) },
            trust_ir::FieldDef { name: "unused".into(), ty: Ty::U32, offset: Some(8) },
        ],
        size: Some(12),
        align: Some(4),
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    });
    let pointee = Ty::Struct(id);
    let signature = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U32]);
    let mut fb = mb.function("read_product", signature);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    let loaded = fb.load(pointee.clone(), pointer);
    let pair = fb.extract_field(fields, loaded, 0);
    let result = fb.extract_field(Ty::U32, pair, 0);
    if wrong_assertion {
        let eight = fb.iconst(Ty::U32, 8);
        let claimed = fb.icmp(ICmpOp::Eq, Ty::U32, result, eight);
        fb.assert(claimed);
    }
    fb.ret(vec![result]);
    fb.build();
    if nested {
        let mut fb = mb.function("forward_product", signature);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        let result = fb.call(FuncId::new(0), vec![pointer]);
        fb.ret(vec![result]);
        fb.build();
    }
    let root = FuncId::new(if nested { 2 } else { 1 });
    let root_signature = mb.add_func_type(
        if matches!(actual, Actual::Reference) { vec![Ty::Ptr] } else { vec![] },
        vec![Ty::U32],
    );
    let mut fb = mb.function("root", root_signature);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let contents = Constant::Aggregate(vec![
        Constant::Aggregate(vec![Constant::Int(7), Constant::Bool(false)]),
        if matches!(actual, Actual::Partial) { Constant::Uninit } else { Constant::Int(9) },
    ]);
    let pointer = match actual {
        Actual::Reference => {
            let parameter = fb.add_block_param(entry, Ty::Ptr);
            fb.copy(Ty::Ptr, parameter)
        }
        Actual::Initialized | Actual::Partial | Actual::Poison => {
            let cell = fb.alloca(pointee.clone());
            let value = if matches!(actual, Actual::Poison) {
                fb.undef(pointee.clone())
            } else {
                fb.const_value(pointee.clone(), contents.clone())
            };
            fb.store(pointee.clone(), cell, value);
            cell
        }
        Actual::StoreAfterCall => fb.alloca(pointee.clone()),
        Actual::Fabricated => {
            let bits = fb.iconst(Ty::U64, 4096);
            fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, bits)
        }
    };
    let result = fb.call(FuncId::new(if nested { 1 } else { 0 }), vec![pointer]);
    if matches!(actual, Actual::StoreAfterCall) {
        let contents = fb.const_value(pointee.clone(), contents);
        fb.store(pointee.clone(), pointer, contents);
    }
    fb.ret(vec![result]);
    fb.build();
    let mut module = mb.build().unwrap();
    for node in module.functions[0].blocks.iter_mut().flat_map(|block| &mut block.body) {
        if matches!(&node.inst, Inst::Load { .. }) {
            node.proofs.push(ProofAnnotation::ValidBorrow);
        }
    }
    let validation = trust_ir_build::validate_module(&module);
    assert!(validation.is_empty(), "{actual:?}: {validation:?}");
    (
        crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1),
        root,
        pointee,
    )
}

fn records(
    bundle: &NativeVerificationBundle,
    pointee: &Ty,
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
                    pointee: pointee.clone(),
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

fn output(
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
fn live_product_facts_restore_nested_field_loads_without_public_authority() {
    for nested in [false, true] {
        for actual in [Actual::Reference, Actual::Initialized] {
            let (mut bundle, root, pointee) = fixture(actual, nested, false);
            let authority =
                SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
            if matches!(actual, Actual::Initialized) {
                let run = trust_ir::interpret::Interpreter::with_module(&bundle.module)
                    .execute_func(root, [])
                    .unwrap();
                assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 7);
            }
            let public = trust_ir_function_to_chc_translation_output(
                &bundle.module,
                root,
                &TranslateOptions::default(),
            )
            .unwrap();
            assert!(!public.diagnostics.is_empty());
            let (parameters, loads) = records(&bundle, &pointee);
            let facts = SourceReferenceFacts::from_live_source_lowering(
                &bundle, &authority, parameters, loads,
            )
            .unwrap();
            let output = output(&bundle, root, &facts);
            assert!(
                output.diagnostics.is_empty(),
                "{actual:?}, nested={nested}: {:?}",
                output.diagnostics
            );
            assert!(!smt_array_tests::error_reachable(&output));
        }
    }
}

#[test]
fn product_reference_requires_every_field_initialized_before_the_call() {
    for actual in [Actual::Partial, Actual::Poison, Actual::StoreAfterCall, Actual::Fabricated] {
        let (mut bundle, root, pointee) = fixture(actual, true, false);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle, &pointee);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = output(&bundle, root, &facts);
        assert!(!output.diagnostics.is_empty(), "{actual:?}");
        assert!(smt_array_tests::error_reachable(&output), "{actual:?}");
    }
}

#[test]
fn product_reference_does_not_establish_numeric_field_values() {
    let (mut bundle, root, pointee) = fixture(Actual::Initialized, true, true);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let (parameters, loads) = records(&bundle, &pointee);
    let facts =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
            .unwrap();
    let output = output(&bundle, root, &facts);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    assert!(smt_array_tests::error_reachable(&output));
}

#[test]
fn product_field_paths_and_memo_follow_the_current_actual_reference() {
    let (mut bundle, root, pointee) = fixture(Actual::Reference, false, false);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let (parameters, loads) = records(&bundle, &pointee);
    let loaded = loads[0].result;
    let facts =
        SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
            .unwrap();
    assert!(facts.load(FuncId::new(0), loaded, &[0, 0]).is_some());
    assert!(facts.load(FuncId::new(0), loaded, &[0, 1]).is_some());
    assert!(facts.load(FuncId::new(0), loaded, &[1]).is_some());
    for path in [vec![2], vec![0, 2], vec![0, 0, 0]] {
        assert!(facts.load(FuncId::new(0), loaded, &path).is_none());
    }
    let analysis =
        construction_definedness::Analysis::with_source_references(&bundle.module, root, &facts);
    let callee = &bundle.module.functions[0];
    let returned = callee.blocks[0].body.last().unwrap();
    let Inst::Return { values } = &returned.inst else { panic!("return fixture") };
    for initialized in [true, false, true, false] {
        let _scope = analysis.enter_reference_arguments(callee.id, vec![initialized]);
        assert_eq!(
            construction_definedness::value_is_defined(
                &analysis,
                &bundle.module,
                callee,
                values[0],
                Some(&[true]),
            ),
            initialized
        );
    }
}

#[test]
fn product_load_and_parameter_facts_are_both_required() {
    for omit_parameter in [true, false] {
        let (mut bundle, root, pointee) = fixture(Actual::Reference, true, false);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (mut parameters, mut loads) = records(&bundle, &pointee);
        if omit_parameter {
            parameters.clear();
        } else {
            loads.clear();
        }
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = output(&bundle, root, &facts);
        assert!(!output.diagnostics.is_empty());
        assert!(smt_array_tests::error_reachable(&output));
    }
}

#[test]
fn product_reference_premise_is_withheld_for_writes_before_or_after_load() {
    for after in [true, false] {
        let (mut bundle, root, pointee) = fixture(Actual::Reference, false, false);
        let block = &mut bundle.module.functions[0].blocks[0];
        let pointer = block.params[0].0;
        let load_position =
            block.body.iter().position(|node| matches!(node.inst, Inst::Load { .. })).unwrap();
        let poison = ValueId::new(1000);
        block.body.splice(
            load_position + usize::from(after)..load_position + usize::from(after),
            [
                InstrNode::new(Inst::Undef { ty: pointee.clone() }).with_result(poison),
                InstrNode::new(Inst::Store {
                    ty: pointee.clone(),
                    ptr: pointer,
                    value: poison,
                    volatile: false,
                    align: None,
                }),
            ],
        );
        let validation = trust_ir_build::validate_module(&bundle.module);
        assert!(validation.is_empty(), "after={after}: {validation:?}");
        // Rebuild the canonical envelope after changing the fixture's module;
        // never bypass the authority's module-digest binding.
        assert_eq!(bundle.module.proof_obligations.len(), 1);
        assert_eq!(bundle.module.proof_obligations[0].id, trust_ir::ProofId::new(0));
        assert_eq!(bundle.module.proof_obligations[0].function, Some(root));
        assert_eq!(bundle.requests.len(), 1);
        bundle.module.proof_obligations.clear();
        let mut bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
            bundle.module,
            root,
            1,
        );
        assert_eq!(bundle.module.proof_obligations.len(), 1);
        assert_eq!(bundle.module.proof_obligations[0].id, trust_ir::ProofId::new(0));
        assert_eq!(bundle.module.proof_obligations[0].function, Some(root));
        assert_eq!(bundle.requests.len(), 1);
        assert_eq!(bundle.validate(), Ok(()));
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let (parameters, loads) = records(&bundle, &pointee);
        let facts =
            SourceReferenceFacts::from_live_source_lowering(&bundle, &authority, parameters, loads)
                .unwrap();
        let output = output(&bundle, root, &facts);
        assert!(!output.diagnostics.is_empty(), "after={after}");
        assert!(smt_array_tests::error_reachable(&output), "after={after}");
    }
}

#[test]
fn product_shape_validation_refuses_pointer_leaves_missing_structs_and_depth_exhaustion() {
    let (mut bundle, _, pointee) = fixture(Actual::Reference, false, false);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let mut too_deep = Ty::U32;
    for _ in 0..65 {
        too_deep = Ty::Tuple(vec![too_deep]);
    }
    for unsupported in [
        Ty::Tuple(vec![Ty::Ptr]),
        Ty::Struct(trust_ir::value::StructId::new(999)),
        too_deep,
        Ty::Tuple(vec![Ty::Bool; 16_385]),
    ] {
        let (mut parameters, _) = records(&bundle, &pointee);
        parameters[0].pointee = unsupported;
        assert!(
            SourceReferenceFacts::from_live_source_lowering(
                &bundle,
                &authority,
                parameters,
                vec![]
            )
            .is_err()
        );
    }
}

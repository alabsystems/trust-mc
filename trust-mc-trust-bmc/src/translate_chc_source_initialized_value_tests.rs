// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Consumer tests for the live source seam's INITIALIZED fresh-value records
//! (`SourceInitializedValueFact`). These fixtures do not issue or qualify the
//! compiler's certificate; they check what the consumer does with a record:
//! a certified fresh value is consumable at its definition and every use, its
//! value stays unconstrained, and nothing else (an unmarked or uncertified
//! `Undef`, a pointer, a float, a replayed bundle, a mismatched site) gains it.

use super::*;
use crate::{
    SourceInitializedParameterFact, SourceInitializedValueFact, SourceReferenceFacts,
    SourceReferenceValueFact,
};
use trust_ir::{NativeVerificationBundle, SourceGenerationAuthority};
use trust_ir_build::ModuleBuilder;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Shape {
    /// `v: u32` fresh; `ret v & 0xff`. Nothing can fail.
    Scalar,
    /// `v: u32` fresh; `assert(v != 7)`. Fails for `v == 7`.
    ScalarRefutable,
    /// `s: {u32, bool}` fresh; `ret s.0`. Nothing can fail.
    Product,
    /// The fresh value is defined in a CALLEE the root summarises.
    Nested,
    /// `s: Sequence<u8>` fresh (the `Vec<u8>` grow post-state); `ret s`.
    Sequence,
    /// `s: Sequence<f64>` fresh: a type no record may name.
    FloatSequence,
}

struct Fixture {
    bundle: NativeVerificationBundle,
    root: FuncId,
    fact: SourceInitializedValueFact,
}

fn product_ty(mb: &mut ModuleBuilder) -> Ty {
    let id = mb.add_struct(trust_ir::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            trust_ir::FieldDef { name: "count".into(), ty: Ty::U32, offset: Some(0) },
            trust_ir::FieldDef { name: "flag".into(), ty: Ty::Bool, offset: Some(4) },
        ],
        size: Some(8),
        align: Some(4),
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    });
    Ty::Struct(id)
}

fn fixture(shape: Shape) -> Fixture {
    let mut mb = ModuleBuilder::new("source_initialized_value");
    let product = product_ty(&mut mb);
    let returns_u32 = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut root = FuncId::new(0);
    let (fresh, fresh_block) = match shape {
        Shape::Scalar | Shape::ScalarRefutable | Shape::Nested => {
            let mut fb = mb.function("fresh_u32", returns_u32);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let fresh = fb.undef(Ty::U32);
            let result = if shape == Shape::ScalarRefutable {
                let seven = fb.iconst(Ty::U32, 7);
                let differs = fb.icmp(ICmpOp::Ne, Ty::U32, fresh, seven);
                fb.assert(differs);
                fresh
            } else {
                let mask = fb.iconst(Ty::U32, 0xff);
                fb.binop(BinOp::And, Ty::U32, fresh, mask)
            };
            fb.ret(vec![result]);
            fb.build();
            if shape == Shape::Nested {
                let mut fb = mb.function("call_fresh_u32", returns_u32);
                let entry = fb.create_block();
                fb.set_entry(entry);
                fb.switch_to_block(entry);
                let result = fb.call(FuncId::new(0), vec![]);
                fb.ret(vec![result]);
                fb.build();
                root = FuncId::new(1);
            }
            (fresh, entry)
        }
        Shape::Sequence | Shape::FloatSequence => {
            let element = mb.add_type(if shape == Shape::Sequence { Ty::U8 } else { Ty::F64 });
            let sequence = Ty::Sequence(element);
            let returns_sequence = mb.add_func_type(vec![], vec![sequence.clone()]);
            let mut fb = mb.function("fresh_bytes", returns_sequence);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let fresh = fb.undef(sequence);
            fb.ret(vec![fresh]);
            fb.build();
            (fresh, entry)
        }
        Shape::Product => {
            let mut fb = mb.function("fresh_pair", returns_u32);
            let entry = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let fresh = fb.undef(product.clone());
            let count = fb.extract_field(Ty::U32, fresh, 0);
            fb.ret(vec![count]);
            fb.build();
            (fresh, entry)
        }
    };
    // The fresh value is always defined in the module's first function.
    let havoc_function = FuncId::new(0);
    let mut module = mb.build().unwrap();
    let instruction_index = module.functions[havoc_function.as_usize()]
        .blocks
        .iter()
        .find(|block| block.id == fresh_block)
        .unwrap()
        .body
        .iter()
        .position(|node| node.results.contains(&fresh))
        .unwrap();
    module.functions[havoc_function.as_usize()].blocks[0].body[instruction_index]
        .proofs
        .push(ProofAnnotation::FreshSymbolicHavoc);
    assert_eq!(module.functions[havoc_function.as_usize()].id, havoc_function);
    let fact = SourceInitializedValueFact {
        function: havoc_function,
        block: fresh_block,
        instruction_index: instruction_index as u32,
        result: fresh,
    };
    let bundle =
        crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1);
    Fixture { bundle, root, fact }
}

fn facts<'a>(
    bundle: &'a NativeVerificationBundle,
    authority: &'a SourceGenerationAuthority,
    initialized: Vec<SourceInitializedValueFact>,
) -> SourceReferenceFacts<'a> {
    SourceReferenceFacts::from_live_source_lowering_with_initialized_values(
        bundle,
        authority,
        vec![],
        vec![],
        vec![],
        initialized,
        vec![],
    )
    .unwrap()
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

fn refused(output: &ChcTranslationOutput) -> bool {
    output.diagnostics.iter().any(|diagnostic| {
        matches!(
            diagnostic.reason,
            TrustIrChcUnsupportedReason::OperandConsumption
                | TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary
        )
    })
}

#[test]
fn an_uncertified_fresh_value_stays_refused_on_every_path() {
    for shape in [Shape::Scalar, Shape::Product, Shape::Nested, Shape::Sequence] {
        let Fixture { mut bundle, root, .. } = fixture(shape);
        let public = trust_ir_function_to_chc_translation_output(
            &bundle.module,
            root,
            &TranslateOptions::default(),
        )
        .unwrap();
        // A bare FreshSymbolicHavoc marker is not initializedness: the public
        // path keeps today's refusal (scalar consumption; aggregate definition).
        assert!(refused(&public), "{shape:?}: {:?}", public.diagnostics);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        // A live context with NO initialized-value record changes nothing.
        let empty = facts(&bundle, &authority, vec![]);
        assert_eq!(empty.initialized_value_count(), 0);
        let output = live_output(&bundle, root, &empty);
        assert!(refused(&output), "{shape:?}: {:?}", output.diagnostics);
        assert!(smt_array_tests::error_reachable(&output), "{shape:?}");
    }
}

#[test]
fn a_certified_fresh_value_is_consumable_but_never_constrained() {
    for shape in [Shape::Scalar, Shape::Product, Shape::Nested, Shape::Sequence] {
        let Fixture { mut bundle, root, fact } = fixture(shape);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let issued = facts(&bundle, &authority, vec![fact]);
        assert_eq!(issued.initialized_value_count(), 1);
        let output = live_output(&bundle, root, &issued);
        assert!(!refused(&output), "{shape:?}: {:?}", output.diagnostics);
        assert!(output.diagnostics.is_empty(), "{shape:?}: {:?}", output.diagnostics);
        assert!(!smt_array_tests::error_reachable(&output), "{shape:?}");
    }
    // The record selects only the initialized reading: `v != 7` is still
    // refuted, because the fresh value may be 7.
    let Fixture { mut bundle, root, fact } = fixture(Shape::ScalarRefutable);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let issued = facts(&bundle, &authority, vec![fact]);
    let output = live_output(&bundle, root, &issued);
    assert!(!refused(&output), "{:?}", output.diagnostics);
    assert!(smt_array_tests::error_reachable(&output), "the value must stay unconstrained");
}

#[test]
fn initialized_value_record_rejects_replay_mismatch_duplicates_and_unsupported_sites() {
    for case in 0..12 {
        let Fixture { mut bundle, mut fact, .. } = fixture(Shape::Scalar);
        let body = &mut bundle.module.functions[0].blocks[0].body;
        match case {
            // An unmarked Undef: the marker is required, never sufficient.
            6 => body[0].proofs.clear(),
            // A pointer: its only value record is SourceReferenceValueFact.
            7 => body[0].inst = Inst::Undef { ty: Ty::Ptr },
            // A float, a char and an enum carry no certificate shape.
            8 => body[0].inst = Inst::Undef { ty: Ty::F64 },
            9 => body[0].inst = Inst::Undef { ty: Ty::Char },
            // A non-Undef definition at the site.
            10 => body[0].inst = Inst::Const { ty: Ty::U32, value: Constant::Int(7) },
            _ => {}
        }
        if (6..=10).contains(&case) {
            let mut module = bundle.module;
            module.proof_obligations.clear();
            bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
                module,
                FuncId::new(0),
                1,
            );
        }
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        match case {
            0 => fact.function = FuncId::new(999),
            1 => fact.block = BlockId::new(999),
            2 => fact.instruction_index = 1,
            3 => fact.result = ValueId::new(999),
            _ => {}
        }
        let mut records = vec![];
        if case == 4 {
            records.push(SourceInitializedValueFact {
                function: fact.function,
                block: fact.block,
                instruction_index: fact.instruction_index,
                result: fact.result,
            });
        }
        records.push(fact);
        let copied = if case == 5 {
            serde_json::from_slice(&serde_json::to_vec(&bundle).unwrap()).unwrap()
        } else {
            bundle.clone()
        };
        let input = if case == 5 || case == 11 { &copied } else { &bundle };
        assert!(
            SourceReferenceFacts::from_live_source_lowering_with_initialized_values(
                input,
                &authority,
                vec![],
                vec![],
                vec![],
                records,
                vec![],
            )
            .is_err(),
            "case {case}"
        );
    }
}

#[test]
fn a_sequence_of_a_type_outside_the_record_shape_is_rejected() {
    let Fixture { mut bundle, fact, .. } = fixture(Shape::FloatSequence);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    assert!(
        SourceReferenceFacts::from_live_source_lowering_with_initialized_values(
            &bundle,
            &authority,
            vec![],
            vec![],
            vec![],
            vec![fact],
            vec![],
        )
        .is_err()
    );
}

#[test]
fn a_pointer_value_record_and_an_initialized_record_cannot_name_one_site() {
    let Fixture { mut bundle, fact, .. } = fixture(Shape::Scalar);
    bundle.module.functions[0].blocks[0].body[0].inst = Inst::Undef { ty: Ty::Ptr };
    let mut module = bundle.module;
    module.proof_obligations.clear();
    let mut bundle = crate::native_bundle::translate_once_tests::one_request_per_obligation(
        module,
        FuncId::new(0),
        1,
    );
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let value = SourceReferenceValueFact {
        function: fact.function,
        block: fact.block,
        instruction_index: fact.instruction_index,
        result: fact.result,
    };
    assert!(
        SourceReferenceFacts::from_live_source_lowering_with_initialized_values(
            &bundle,
            &authority,
            vec![],
            vec![],
            vec![value],
            vec![fact],
            vec![],
        )
        .is_err()
    );
}

// ---------------------------------------------------------------------------
// INITIALIZED by-value root parameters (`SourceInitializedParameterFact`)
// ---------------------------------------------------------------------------

/// `Tag { __tag: i64 }`, the flat shape of a fieldless enum.
fn tag_ty(mb: &mut ModuleBuilder) -> Ty {
    let id = mb.add_struct(trust_ir::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Linkage".into(),
        fields: vec![trust_ir::FieldDef { name: "__tag".into(), ty: Ty::I64, offset: None }],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::Rust,
        origin: None,
    });
    Ty::Struct(id)
}

struct ParameterFixture {
    bundle: NativeVerificationBundle,
    root: FuncId,
    /// `is_private(p) = p.__tag == 0`, function 0, parameter 0.
    callee: SourceInitializedParameterFact,
    /// `forward(p) = is_private(p)`, function 1, parameter 0.
    caller: SourceInitializedParameterFact,
}

/// Function 0 reads its parameter's tag lane; function 1 forwards its own
/// parameter to function 0. `root` selects which one the translation roots at.
fn parameter_fixture(param_ty: fn(&mut ModuleBuilder) -> Ty, root: FuncId) -> ParameterFixture {
    let mut mb = ModuleBuilder::new("source_initialized_parameter");
    let param = param_ty(&mut mb);
    let reads = mb.add_func_type(vec![param.clone()], vec![Ty::Bool]);
    let mut fb = mb.function("is_private", reads);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let p = fb.add_block_param(entry, param.clone());
    let result = if matches!(param, Ty::Struct(_)) {
        let tag = fb.extract_field(Ty::I64, p, 0);
        let zero = fb.iconst(Ty::I64, 0);
        fb.icmp(ICmpOp::Eq, Ty::I64, tag, zero)
    } else {
        // An unsupported parameter type is only ever rejected; the body need not read it.
        let zero = fb.iconst(Ty::I64, 0);
        fb.icmp(ICmpOp::Eq, Ty::I64, zero, zero)
    };
    fb.ret(vec![result]);
    let callee = fb.build();
    let mut fb = mb.function("forward", reads);
    let entry = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let q = fb.add_block_param(entry, param);
    let forwarded = fb.call(callee, vec![q]);
    fb.ret(vec![forwarded]);
    let caller = fb.build();
    let module = mb.build().unwrap();
    let bundle =
        crate::native_bundle::translate_once_tests::one_request_per_obligation(module, root, 1);
    ParameterFixture {
        bundle,
        root,
        callee: SourceInitializedParameterFact { function: callee, parameter_index: 0, value: p },
        caller: SourceInitializedParameterFact { function: caller, parameter_index: 0, value: q },
    }
}

fn parameter_facts<'a>(
    bundle: &'a NativeVerificationBundle,
    authority: &'a SourceGenerationAuthority,
    initialized_parameters: Vec<SourceInitializedParameterFact>,
) -> Result<SourceReferenceFacts<'a>, crate::SourceReferenceFactsError> {
    SourceReferenceFacts::from_live_source_lowering_with_initialized_values(
        bundle,
        authority,
        vec![],
        vec![],
        vec![],
        vec![],
        initialized_parameters,
    )
}

#[test]
fn an_uncertified_aggregate_root_parameter_stays_refused() {
    for root in [FuncId::new(0), FuncId::new(1)] {
        let ParameterFixture { mut bundle, root, .. } = parameter_fixture(tag_ty, root);
        let public = trust_ir_function_to_chc_translation_output(
            &bundle.module,
            root,
            &TranslateOptions::default(),
        )
        .unwrap();
        assert!(refused(&public), "{root:?}: {:?}", public.diagnostics);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let empty = parameter_facts(&bundle, &authority, vec![]).unwrap();
        assert_eq!(empty.initialized_parameter_count(), 0);
        assert!(refused(&live_output(&bundle, root, &empty)), "{root:?}");
    }
}

#[test]
fn a_certified_root_parameter_is_read_only_by_its_own_root_translation() {
    // Rooted at the reader: its own record admits the tag read.
    let ParameterFixture { mut bundle, root, callee, .. } =
        parameter_fixture(tag_ty, FuncId::new(0));
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let issued = parameter_facts(&bundle, &authority, vec![callee]).unwrap();
    assert_eq!(issued.initialized_parameter_count(), 1);
    let output = live_output(&bundle, root, &issued);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);

    // Rooted at the forwarder: the CALLEE's record is not read (its parameter
    // takes its definedness from the actual argument), so it changes nothing.
    let ParameterFixture { mut bundle, root, callee, caller } =
        parameter_fixture(tag_ty, FuncId::new(1));
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let callee_only = parameter_facts(&bundle, &authority, vec![callee]).unwrap();
    assert!(refused(&live_output(&bundle, root, &callee_only)), "a callee record is not read");
    // The forwarder's own record makes its actual argument initialized.
    let ParameterFixture { mut bundle, root, .. } = parameter_fixture(tag_ty, FuncId::new(1));
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let own = parameter_facts(&bundle, &authority, vec![caller]).unwrap();
    let output = live_output(&bundle, root, &own);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
}

#[test]
fn initialized_parameter_record_rejects_mismatches_duplicates_and_unsupported_types() {
    let pointer = |_: &mut ModuleBuilder| Ty::Ptr;
    let float = |_: &mut ModuleBuilder| Ty::F64;
    let character = |_: &mut ModuleBuilder| Ty::Char;
    for (label, ty, mutate) in [
        ("function", tag_ty as fn(&mut ModuleBuilder) -> Ty, 0),
        ("index", tag_ty, 1),
        ("value", tag_ty, 2),
        ("duplicate", tag_ty, 3),
        ("pointer", pointer, 4),
        ("float", float, 4),
        ("char", character, 4),
    ] {
        let ParameterFixture { mut bundle, mut callee, .. } = parameter_fixture(ty, FuncId::new(0));
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
        let mut records = vec![];
        match mutate {
            0 => callee.function = FuncId::new(999),
            1 => callee.parameter_index = 1,
            2 => callee.value = ValueId::new(999),
            3 => records.push(SourceInitializedParameterFact {
                function: callee.function,
                parameter_index: callee.parameter_index,
                value: callee.value,
            }),
            _ => {}
        }
        records.push(callee);
        assert!(parameter_facts(&bundle, &authority, records).is_err(), "{label}");
    }
    // A replayed bundle is never authorized.
    let ParameterFixture { mut bundle, callee, .. } = parameter_fixture(tag_ty, FuncId::new(0));
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap();
    let replayed: NativeVerificationBundle =
        serde_json::from_slice(&serde_json::to_vec(&bundle).unwrap()).unwrap();
    assert!(parameter_facts(&replayed, &authority, vec![callee]).is_err());
}

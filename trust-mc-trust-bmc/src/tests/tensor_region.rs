// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! trust-ir's tensor region (wire v67-v70) is refused by name at every entry
//! (`crate::tensor_region`): each of the nine constructs in a VALID module, so
//! the refusal is the tensor region's and never canonical invalidity.

use super::*;
use crate::TensorConstruct;
use crate::translate::{UnsupportedSort, checked_ty_to_sort};
use std::collections::BTreeSet;
use trust_ir::Module;
use trust_ir::constant::Constant;

pub(crate) fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

/// The six tensor instructions, in [`TensorConstruct`] order.
pub(crate) const TENSOR_INSTRUCTIONS: [TensorConstruct; 6] = [
    TensorConstruct::TensorContract,
    TensorConstruct::TensorMap,
    TensorConstruct::TensorReduce,
    TensorConstruct::TensorView,
    TensorConstruct::TensorGather,
    TensorConstruct::TensorScatter,
];

/// `fn t(params) -> result { %r = <construct>; ret %r }`, the VALID shape of
/// each tensor instruction (as trust-ir's own fixtures spell it).
pub(crate) fn tensor_instruction_module(construct: TensorConstruct) -> Module {
    use trust_ir::{TensorIndexExpr as E, TensorMapNode, TensorReduceOp};
    let (params, result) = match construct {
        TensorConstruct::TensorContract => {
            (vec![tensor(Ty::I32, 2), tensor(Ty::I32, 2)], tensor(Ty::I32, 2))
        }
        TensorConstruct::TensorMap => {
            (vec![tensor(Ty::I32, 1), tensor(Ty::I32, 1)], tensor(Ty::I32, 1))
        }
        TensorConstruct::TensorReduce => (vec![tensor(Ty::I32, 2)], tensor(Ty::I32, 1)),
        TensorConstruct::TensorView => {
            (vec![tensor(Ty::I32, 2), Ty::I32, Ty::Usize], tensor(Ty::I32, 2))
        }
        TensorConstruct::TensorGather => {
            (vec![tensor(Ty::I32, 2), tensor(Ty::I64, 1), tensor(Ty::U8, 1)], tensor(Ty::I32, 1))
        }
        TensorConstruct::TensorScatter => (
            vec![tensor(Ty::I32, 2), tensor(Ty::I32, 1), tensor(Ty::I64, 1), tensor(Ty::U8, 1)],
            tensor(Ty::I32, 2),
        ),
        other => panic!("{other} is not a tensor instruction"),
    };
    let mut mb = ModuleBuilder::new(format!("tensor_region_{construct:?}"));
    let ft = mb.add_func_type(params.clone(), vec![result.clone()]);
    let mut fb = mb.function("t", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let p: Vec<_> = params.into_iter().map(|ty| fb.add_block_param(entry, ty)).collect();
    let r = match construct {
        TensorConstruct::TensorContract => {
            fb.tensor_contract(result, p[0], p[1], vec![], vec![(1, 0)])
        }
        TensorConstruct::TensorMap => fb.tensor_map(
            result,
            vec![p[0], p[1]],
            vec![TensorMapNode::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: 0, rhs: 1 }],
        ),
        TensorConstruct::TensorReduce => {
            fb.tensor_reduce(result, p[0], TensorReduceOp::SMax, vec![0])
        }
        TensorConstruct::TensorView => fb.tensor_view(
            result,
            p[0],
            vec![p[2]],
            vec![
                E::SrcExtent(1),
                E::SrcExtent(0),
                E::Coord(1),
                E::Param(0),
                E::Add(2, 3),
                E::Coord(0),
            ],
            vec![0, 1],
            vec![4, 5],
            Some(p[1]),
        ),
        TensorConstruct::TensorGather => fb.tensor_gather(result, p[0], vec![p[1], p[2]]),
        _ => fb.tensor_scatter(result, p[0], p[1], vec![p[2], p[3]]),
    };
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("tensor instruction fixture")
}

/// `fn t() -> tensor<i32, 1> { %0 = const tensor_blob<digest>[2]; ret %0 }`,
/// whose two `i32` elements are the module's one blob row.
pub(crate) fn tensor_blob_module() -> Module {
    let mut mb = ModuleBuilder::new("tensor_blob");
    let digest = mb.intern_blob(vec![1, 0, 0, 0, 2, 0, 0, 0]);
    let ft = mb.add_func_type(vec![], vec![tensor(Ty::I32, 1)]);
    let mut fb = mb.function("t", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let weights =
        fb.const_value(tensor(Ty::I32, 1), Constant::TensorBlob { digest, dims: vec![2] });
    fb.ret(vec![weights]);
    fb.build();
    mb.build().expect("tensor blob fixture")
}

/// `fn t(b: bool) { switch b [tensor_blob<digest>[1] -> bb1] default bb2;
/// bb1: ret; bb2: ret }` with an EMPTY blob table: a blob stored as a switch case, where
/// no type and no table row names the region. trust-ir checks a case's shape
/// only at an integer or `char` selector, so the module validates.
pub(crate) fn tensor_blob_switch_module() -> Module {
    let mut mb = ModuleBuilder::new("tensor_blob_switch");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("t", ft);
    let entry = fb.create_block();
    let matched = fb.create_block();
    let otherwise = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let selector = fb.add_block_param(entry, Ty::Bool);
    let blob = Constant::TensorBlob {
        digest: trust_ir::blob::BlobDigest::of(&[7, 0, 0, 0]),
        dims: vec![1],
    };
    fb.switch(
        selector,
        vec![trust_ir::SwitchCase { value: blob, target: matched, args: vec![] }],
        otherwise,
        vec![],
    );
    for exit in [matched, otherwise] {
        fb.switch_to_block(exit);
        fb.ret(vec![]);
    }
    fb.build();
    mb.build().expect("tensor blob switch fixture")
}

/// A module whose only tensor is an unused type-table row.
fn unused_tensor_row_module() -> Module {
    let mut module = ModuleBuilder::new("unused_tensor").build().unwrap();
    module.types.push(tensor(Ty::I32, 2));
    module
}

fn set(constructs: &[TensorConstruct]) -> BTreeSet<TensorConstruct> {
    constructs.iter().copied().collect()
}

fn assert_valid(module: &Module) {
    let errors = trust_ir_build::validate_module(module);
    assert!(errors.is_empty(), "the fixture must be valid trust-ir: {errors:?}");
}

/// Every public diagnostic entry refuses `module` as an UNSUPPORTED (valid)
/// module whose refusal names each of `names`, before any symbol is translated.
fn assert_module_input_refusal(module: &Module, names: &[&str]) {
    let options = TranslateOptions::default();
    let names_in = |reason: &str| {
        assert!(reason.starts_with("unsupported trust_ir module"), "{reason}");
        assert!(reason.contains("tensor region"), "{reason}");
        for name in names {
            assert!(reason.contains(name), "{name} must be named: {reason}");
        }
    };
    let bmc = trust_ir_to_bmc_vc(module, &options);
    assert_eq!(bmc.len(), 1);
    assert!(bmc[0].decls.is_empty());
    assert!(bmc[0].constraints.is_empty());
    assert_eq!(bmc[0].violations.len(), 1);
    assert_eq!(bmc[0].violations[0].kind, PropertyKind::Other);
    assert_eq!(bmc[0].violations[0].condition, Expr::true_());
    names_in(bmc[0].violations[0].message.as_deref().expect("a named refusal"));
    for outputs in [
        trust_ir_to_chc_translation_outputs(module, &options),
        trust_ir_to_chc_translation_outputs_per_block(module, &options),
    ] {
        assert_eq!(outputs.len(), 1);
        let output = &outputs[0];
        names_in(output.module_input_refusal.as_deref().expect("explicit refusal"));
        assert!(output.diagnostics.is_empty(), "no instruction site is invented");
        assert!(output.vc.decls.is_empty());
        assert_eq!(output.work.instructions_translated, 0);
        assert_eq!(output.vc.rules.len(), 1);
        assert_eq!(output.vc.rules[0].head.name, "error");
        assert!(output.vc.rules[0].body.relation.is_none());
        assert!(output.vc.rules[0].body.constraints.is_empty());
    }
    for function in &module.functions {
        let selected = crate::trust_ir_function_to_bmc_vc(module, function.id, &options).unwrap();
        assert_eq!(selected.violations.len(), 1);
        assert_eq!(selected.violations[0].condition, Expr::true_());
        names_in(selected.violations[0].message.as_deref().unwrap());
        let output =
            trust_ir_function_to_chc_translation_output(module, function.id, &options).unwrap();
        names_in(output.module_input_refusal.as_deref().unwrap());
    }
}

#[test]
fn each_tensor_instruction_module_is_valid_and_named_by_the_census() {
    for construct in TENSOR_INSTRUCTIONS {
        let module = tensor_instruction_module(construct);
        assert_valid(&module);
        let inst = &module.functions[0].blocks[0].body[0].inst;
        assert_eq!(TensorConstruct::of_inst(inst), Some(construct));
        assert!(crate::inst_spells_tensor_type(inst), "{construct}");
        assert_eq!(
            crate::tensor_region_constructs(&module),
            set(&[TensorConstruct::TensorType, construct]),
            "{construct}"
        );
    }
}

#[test]
fn the_census_names_a_blob_constant_its_table_and_an_unused_tensor_row() {
    let blob = tensor_blob_module();
    assert_valid(&blob);
    assert_eq!(
        crate::tensor_region_constructs(&blob),
        set(&[
            TensorConstruct::TensorType,
            TensorConstruct::TensorBlobConstant,
            TensorConstruct::BlobTable
        ])
    );
    assert_eq!(
        crate::tensor_construct_names(&crate::tensor_region_constructs(&blob)),
        "Ty::Tensor, Constant::TensorBlob, Module.blobs"
    );

    let row = unused_tensor_row_module();
    assert_valid(&row);
    assert_eq!(crate::tensor_region_constructs(&row), set(&[TensorConstruct::TensorType]));

    // A blob row no constant names: the table alone is named (validated or
    // not, the native boundary below refuses it before validation).
    let mut table = ModuleBuilder::new("blob_table_only").build().unwrap();
    table.intern_blob(vec![7, 7, 7, 7]);
    assert_eq!(crate::tensor_region_constructs(&table), set(&[TensorConstruct::BlobTable]));

    // A blob nested in an aggregate global initializer is found at any depth.
    let mut global = ModuleBuilder::new("blob_global").build().unwrap();
    let digest = global.intern_blob(vec![0, 0, 0, 0]);
    global.globals.push(trust_ir::Global {
        name: "weights".into(),
        ty: Ty::Tuple(vec![Ty::U64]),
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![Constant::TensorBlob {
            digest,
            dims: vec![1],
        }])),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    assert!(
        crate::tensor_region_constructs(&global).contains(&TensorConstruct::TensorBlobConstant)
    );

    // A module with no tensor construct stores none.
    let control = tensor_free_module();
    assert!(crate::tensor_region_constructs(&control).is_empty());
}

/// A blob stored as a `Switch` case (empty blob table, no tensor type
/// anywhere) is named by every entry: the census, the instruction predicate,
/// the coverage family and the shared module input.
#[test]
fn a_blob_switch_case_is_named_at_every_entry() {
    let module = tensor_blob_switch_module();
    assert_valid(&module);
    assert!(module.blobs.is_empty());
    assert_eq!(
        crate::tensor_region_constructs(&module),
        set(&[TensorConstruct::TensorBlobConstant])
    );
    let switch = &module.functions[0].blocks[0].body[0].inst;
    assert!(matches!(switch, trust_ir::Inst::Switch { .. }));
    assert!(crate::inst_carries_tensor_blob(switch));
    assert!(!crate::inst_spells_tensor_type(switch), "a case constant carries no type");
    assert_eq!(family_for_inst(switch), SemanticsFamily::Tensors);
    assert_module_input_refusal(&module, &["Constant::TensorBlob"]);
    // Control: a `bool` case at the same selector carries no blob.
    let plain = trust_ir::Inst::Switch {
        value: trust_ir::ValueId::new(0),
        default: trust_ir::BlockId::new(1),
        default_args: vec![],
        cases: vec![trust_ir::SwitchCase {
            value: Constant::Bool(true),
            target: trust_ir::BlockId::new(1),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    };
    assert!(!crate::inst_carries_tensor_blob(&plain));
}

/// The census reads a blob in every place trust-ir stores a constant, the
/// refinement tables included (trust-ir validation refuses a non-scalar member
/// there too; the census does not rely on it).
#[test]
fn the_census_reads_a_blob_in_every_constant_carrier() {
    let blob =
        || Constant::TensorBlob { digest: trust_ir::blob::BlobDigest([3; 32]), dims: vec![1] };
    let mut universe = ModuleBuilder::new("blob_universe").build().unwrap();
    universe.universes.push(trust_ir::Universe::Members(vec![blob()]));
    let mut predicate = ModuleBuilder::new("blob_predicate").build().unwrap();
    predicate.predicates.push(trust_ir::Pred::FiniteSet(vec![Constant::Int(0), blob()]));
    for module in [universe, predicate] {
        assert_eq!(
            crate::tensor_region_constructs(&module),
            set(&[TensorConstruct::TensorBlobConstant]),
            "{}",
            module.name
        );
    }
    // Control: scalar members carry none.
    let mut scalar = ModuleBuilder::new("scalar_tables").build().unwrap();
    scalar.universes.push(trust_ir::Universe::Members(vec![Constant::Int(1)]));
    scalar.predicates.push(trust_ir::Pred::FiniteSet(vec![Constant::Bool(true)]));
    scalar.predicates.push(trust_ir::Pred::Interval { lo: 0, hi: 3 });
    assert!(crate::tensor_region_constructs(&scalar).is_empty());
}

/// `fn t(u32) -> u32 { ret %0 }`: the tensor-free control.
fn tensor_free_module() -> Module {
    let mut mb = ModuleBuilder::new("tensor_free");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("t", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    fb.ret(vec![x]);
    fb.build();
    mb.build().unwrap()
}

#[test]
fn module_input_refuses_each_tensor_instruction_by_name_before_translation() {
    for construct in TENSOR_INSTRUCTIONS {
        let module = tensor_instruction_module(construct);
        assert_module_input_refusal(&module, &["Ty::Tensor", construct.name()]);
    }
}

#[test]
fn module_input_refuses_a_blob_constant_its_table_and_an_unused_tensor_row_by_name() {
    assert_module_input_refusal(
        &tensor_blob_module(),
        &["Ty::Tensor", "Constant::TensorBlob", "Module.blobs"],
    );
    assert_module_input_refusal(&unused_tensor_row_module(), &["Ty::Tensor"]);
    // The tensor-free control translates.
    let control = tensor_free_module();
    let outputs = trust_ir_to_chc_translation_outputs(&control, &TranslateOptions::default());
    assert!(outputs.iter().all(|output| output.module_input_refusal.is_none()));
}

#[test]
fn native_bmc_chc_and_pdr_refuse_the_tensor_region_with_a_typed_named_error() {
    type Mutation = fn(&mut Module);
    let mutations: [(Mutation, BTreeSet<TensorConstruct>, &str); 4] = [
        (
            |module| module.types.push(tensor(Ty::I32, 2)),
            set(&[TensorConstruct::TensorType]),
            "Ty::Tensor",
        ),
        (
            |module| {
                module.intern_blob(vec![1, 2, 3, 4]);
            },
            set(&[TensorConstruct::BlobTable]),
            "Module.blobs",
        ),
        (
            |module| {
                // An unrequested function holding a contraction.
                let fixture = tensor_instruction_module(TensorConstruct::TensorContract);
                let functy = module.add_func_type(fixture.func_types[0].clone()).unwrap();
                let mut function = fixture.functions[0].clone();
                function.id = trust_ir::FuncId::new(
                    module.functions.iter().map(|f| f.id.index()).max().unwrap_or(0) + 1,
                );
                function.name = "unrequested_contraction".into();
                function.ty = functy;
                module.functions.push(function);
            },
            set(&[TensorConstruct::TensorType, TensorConstruct::TensorContract]),
            "Inst::TensorContract",
        ),
        (
            |module| {
                // An unrequested function whose switch has a blob case.
                let fixture = tensor_blob_switch_module();
                let functy = module.add_func_type(fixture.func_types[0].clone()).unwrap();
                let mut function = fixture.functions[0].clone();
                function.id = trust_ir::FuncId::new(
                    module.functions.iter().map(|f| f.id.index()).max().unwrap_or(0) + 1,
                );
                function.name = "unrequested_blob_switch".into();
                function.ty = functy;
                module.functions.push(function);
            },
            set(&[TensorConstruct::TensorBlobConstant]),
            "Constant::TensorBlob",
        ),
    ];
    for (mutate, expected, name) in mutations {
        for mode in [
            TrustMcVerificationMode::BoundedModelCheck,
            TrustMcVerificationMode::Chc,
            TrustMcVerificationMode::Pdr,
        ] {
            let mut bundle = native_trust_mc_bundle(mode);
            mutate(&mut bundle.module);
            refresh_native_trust_mc_bundle_module_identity(&mut bundle);
            let options = TranslateOptions::default();
            let error = match mode {
                TrustMcVerificationMode::BoundedModelCheck => {
                    trust_mc_bmc_vcs_from_native_bundle(&bundle, &options).unwrap_err()
                }
                _ => {
                    trust_mc_chc_pdr_obligations_from_native_bundle(&bundle, &options).unwrap_err()
                }
            };
            assert_eq!(
                error,
                NativeTrustMcBundleError::TensorRegionNotModeled { constructs: expected.clone() },
                "{mode:?}"
            );
            assert!(error.to_string().contains(name), "{mode:?}: {error}");
        }
    }
    // The unused tensor row is a valid bundle: the refusal is the tensor
    // region's, not bundle invalidity.
    let mut bundle = native_trust_mc_bundle(TrustMcVerificationMode::Chc);
    bundle.module.types.push(tensor(Ty::I32, 2));
    refresh_native_trust_mc_bundle_module_identity(&mut bundle);
    assert_eq!(bundle.validate(), Ok(()));
}

#[test]
fn a_tensor_has_no_sort_and_no_constant_encoding() {
    assert_eq!(checked_ty_to_sort(&tensor(Ty::I32, 2)), Err(UnsupportedSort::Tensor));
    assert_eq!(checked_ty_to_sort(&tensor(Ty::Bool, 0)), Err(UnsupportedSort::Tensor));
    assert!(UnsupportedSort::Tensor.message().contains("Ty::Tensor"));
    let blob = Constant::TensorBlob { digest: trust_ir::blob::BlobDigest([0; 32]), dims: vec![1] };
    assert!(const_to_expr(&tensor(Ty::I32, 1), &blob).is_none());
    assert!(const_to_expr(&Ty::I32, &blob).is_none(), "a blob has no bits at any type");
    assert!(const_to_expr(&tensor(Ty::I32, 0), &Constant::Int(0)).is_none());
    assert!(const_to_expr(&Ty::Tuple(vec![tensor(Ty::I32, 1)]), &Constant::Int(0)).is_none());
    // Control: an ordinary scalar constant keeps its exact encoding.
    assert!(const_to_expr(&Ty::I32, &Constant::Int(7)).is_some());
}

#[test]
fn tensor_instructions_and_the_blob_constant_are_a_fail_closed_family() {
    for construct in TENSOR_INSTRUCTIONS {
        let module = tensor_instruction_module(construct);
        let inst = &module.functions[0].blocks[0].body[0].inst;
        assert_eq!(family_for_inst(inst), SemanticsFamily::Tensors, "{construct}");
    }
    let blob = tensor_blob_module();
    assert_eq!(
        family_for_inst(&blob.functions[0].blocks[0].body[0].inst),
        SemanticsFamily::Tensors
    );
    // Control: an ordinary constant stays where it was.
    assert_eq!(
        family_for_inst(&trust_ir::Inst::Const { ty: Ty::U32, value: Constant::Int(0) }),
        SemanticsFamily::IntegerArithmetic
    );
    let row = coverage_for_family(SemanticsFamily::Tensors);
    assert_eq!(row.status, SemanticsStatus::FailClosedUnsupported);
    for name in [
        "Ty::Tensor",
        "TensorContract",
        "TensorMap",
        "TensorReduce",
        "TensorView",
        "TensorGather",
        "TensorScatter",
        "Constant::TensorBlob",
        "Module.blobs",
    ] {
        assert!(row.notes.contains(name), "{name}");
    }
}

/// `f` with its tensor parameters removed and its result unreturned: a body
/// the module input would refuse, handed straight to a translator so the
/// instruction arm itself is what answers.
pub(crate) fn bypassing_body(mut module: Module) -> Module {
    let functy = module.add_func_type(FuncTy::unrecorded(vec![], vec![], false)).unwrap();
    let function = &mut module.functions[0];
    function.ty = functy;
    let block = &mut function.blocks[0];
    block.params.clear();
    let last = block.body.len() - 1;
    block.body[last].inst = trust_ir::Inst::Return { values: vec![] };
    module
}

#[test]
fn the_bmc_translator_names_each_tensor_construct_even_when_its_input_is_bypassed() {
    let options = TranslateOptions::default();
    let mut cases: Vec<(TensorConstruct, Module)> = TENSOR_INSTRUCTIONS
        .iter()
        .map(|construct| (*construct, bypassing_body(tensor_instruction_module(*construct))))
        .collect();
    cases.push((TensorConstruct::TensorBlobConstant, bypassing_body(tensor_blob_module())));
    // A non-blob constant at a tensor type is named by its type.
    let mut typed = bypassing_body(tensor_blob_module());
    typed.functions[0].blocks[0].body[0].inst =
        trust_ir::Inst::Const { ty: tensor(Ty::I32, 0), value: Constant::Int(0) };
    cases.push((TensorConstruct::TensorType, typed));
    // A blob switch case, named rather than lumped in with non-scalar cases.
    cases.push((TensorConstruct::TensorBlobConstant, tensor_blob_switch_module()));
    for (construct, module) in cases {
        let vc =
            crate::translate::translate_valid_function(&module.functions[0], &module, &options);
        let named: Vec<_> = vc
            .violations
            .iter()
            .filter_map(|violation| violation.message.as_deref())
            .filter(|message| message.contains(construct.name()))
            .collect();
        assert_eq!(named.len(), 1, "{construct}: {:?}", vc.violations);
        assert!(named[0].contains("tensor region"), "{construct}: {}", named[0]);
        let violation = vc
            .violations
            .iter()
            .find(|violation| violation.message.as_deref() == Some(named[0]))
            .unwrap();
        assert_eq!(violation.kind, PropertyKind::Other);
        assert_eq!(violation.condition, Expr::true_(), "{construct}: an always-failing violation");
    }
}

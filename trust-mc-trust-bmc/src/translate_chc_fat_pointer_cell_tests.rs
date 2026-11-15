// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::value::TyId;
use trust_ir_build::ModuleBuilder;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;

fn kinds() -> [FatPtrKind; 5] {
    [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(0)),
        FatPtrKind::TraitObject { trait_id: 0 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ]
}

fn fixture(kind: FatPtrKind, assertion: bool) -> (Module, ValueId, Ty) {
    let mut builder = ModuleBuilder::new("fat_pointer_cell");
    builder.add_type(Ty::U8);
    let ty = Ty::FatPtr(kind);
    let signature = builder.add_func_type(vec![ty.clone()], vec![]);
    let mut function = builder.function("store_and_load", signature);
    let entry = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    let input = function.add_block_param(entry, ty.clone());
    let slot = function.alloca(ty.clone());
    function.store(ty.clone(), slot, input);
    function.load(ty.clone(), slot);
    let condition = function.const_value(Ty::Bool, Constant::Bool(assertion));
    function.assert(condition);
    function.ret(vec![]);
    function.build();
    (builder.build().expect("ModuleBuilder::build: test fixture"), slot, ty)
}

fn admitted(module: &Module, slot: ValueId, ty: &Ty) -> bool {
    single_cell_alloca_is_admissible(module, &module.functions[0], slot, ty)
}

#[test]
fn fat_pointer_cell_admits_initialized_whole_slot_without_promoting_opaque_values() {
    for kind in kinds() {
        let (module, slot, ty) = fixture(kind, true);
        assert!(admitted(&module, slot, &ty), "{kind:?}");
        assert!(stack_cell_is_translator_opaque(&module, &ty));
        assert!(promoted_cell_alloca_reject(&module, &module.functions[0], slot, &ty).is_some());
        assert!(!block_local_alloca_is_admissible_reference(&module.functions[0], slot, &ty));
    }
}

#[test]
fn fat_pointer_cell_keeps_true_and_false_assertions_distinct() {
    for kind in kinds() {
        for assertion in [true, false] {
            let (module, slot, ty) = fixture(kind, assertion);
            assert!(admitted(&module, slot, &ty));
            let output =
                translate_function(&module.functions[0], &module, &TranslateOptions::default());
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            let errors: Vec<_> =
                output.vc.rules.iter().filter(|r| r.head.name == ERROR_REL).collect();
            assert_eq!(errors.len(), 1, "one assertion, no invented memory failure");
            let condition = &errors[0].body.constraints;
            let error_reachable =
                condition.iter().map(try_eval_to_bool).collect::<Option<Vec<_>>>();
            assert_eq!(
                error_reachable.map(|terms| terms.into_iter().all(|term| term)),
                Some(!assertion)
            );
        }
    }
}

#[test]
fn fat_pointer_cell_rejects_uninitialized_and_qualified_accesses() {
    for kind in kinds() {
        for mutation in 0..7 {
            let (mut module, slot, ty) = fixture(kind, true);
            let body = &mut module.functions[0].blocks[0].body;
            match mutation {
                0 => body.retain(|node| !matches!(node.inst, Inst::Store { .. })),
                1 => {
                    let store = body
                        .iter()
                        .position(|node| matches!(node.inst, Inst::Store { .. }))
                        .unwrap();
                    let load = body
                        .iter()
                        .position(|node| matches!(node.inst, Inst::Load { .. }))
                        .unwrap();
                    body.swap(store, load);
                }
                _ => {
                    for node in body {
                        match &mut node.inst {
                            Inst::Load { volatile, .. } if mutation == 2 => *volatile = true,
                            Inst::Load { align, .. } if mutation == 3 => *align = Some(8),
                            Inst::Store { volatile, .. } if mutation == 4 => *volatile = true,
                            Inst::Store { align, .. } if mutation == 5 => *align = Some(8),
                            Inst::Store { ty, .. } if mutation == 6 => *ty = Ty::U64,
                            _ => {}
                        }
                    }
                }
            }
            assert!(!admitted(&module, slot, &ty), "{kind:?}, mutation {mutation}");
        }
    }
}

#[test]
fn fat_pointer_cell_rejects_escape_but_admits_initialized_cross_block_loads() {
    for kind in kinds() {
        let (mut module, slot, ty) = fixture(kind, true);
        let body = &mut module.functions[0].blocks[0].body;
        body.insert(1, InstrNode::new(Inst::Return { values: vec![slot] }));
        assert!(!admitted(&module, slot, &ty), "escaping {kind:?}");

        let (mut module, slot, ty) = fixture(kind, true);
        let body = &mut module.functions[0].blocks[0].body;
        let index = body.iter().position(|node| matches!(node.inst, Inst::Load { .. })).unwrap();
        let load = body.remove(index);
        let mut next = Block::new(BlockId::new(1));
        next.body = vec![load, InstrNode::new(Inst::Return { values: vec![] })];
        body.pop();
        body.push(InstrNode::new(Inst::Br { target: next.id, args: vec![] }));
        module.functions[0].blocks.push(next);
        assert!(admitted(&module, slot, &ty), "initialized direct cross-block {kind:?}");
    }
}

fn diamond(kind: FatPtrKind, initialize_both: bool, assertion: bool) -> (Module, ValueId, Ty) {
    let mut builder = ModuleBuilder::new("fat_pointer_cell_diamond");
    builder.add_type(Ty::U8);
    let ty = Ty::FatPtr(kind);
    let signature = builder.add_func_type(vec![ty.clone(), Ty::Bool], vec![]);
    let mut function = builder.function("join", signature);
    let entry = function.create_block();
    let left = function.create_block();
    let right = function.create_block();
    let join = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    let input = function.add_block_param(entry, ty.clone());
    let choose_left = function.add_block_param(entry, Ty::Bool);
    let slot = function.alloca(ty.clone());
    function.condbr(choose_left, left, vec![], right, vec![]);
    function.switch_to_block(left);
    function.store(ty.clone(), slot, input);
    function.br(join, vec![]);
    function.switch_to_block(right);
    if initialize_both {
        function.store(ty.clone(), slot, input);
    }
    function.br(join, vec![]);
    function.switch_to_block(join);
    function.load(ty.clone(), slot);
    let condition = function.const_value(Ty::Bool, Constant::Bool(assertion));
    function.assert(condition);
    function.ret(vec![]);
    function.build();
    (builder.build().expect("ModuleBuilder::build: test fixture"), slot, ty)
}

#[test]
fn opaque_fat_pointer_join_requires_a_store_on_every_predecessor() {
    for kind in kinds() {
        for initialize_both in [false, true] {
            let (module, slot, ty) = diamond(kind, initialize_both, true);
            assert_eq!(admitted(&module, slot, &ty), initialize_both, "{kind:?}");
        }
    }
}

#[test]
fn opaque_fat_pointer_cross_block_havoc_preserves_assertion_errors() {
    for assertion in [false, true] {
        let (module, slot, ty) = diamond(FatPtrKind::Str, true, assertion);
        assert!(admitted(&module, slot, &ty));
        // Per block: the test folds the one error rule's own constraints.
        let output = translate_function_per_block(
            &module.functions[0],
            &module,
            &TranslateOptions::default(),
        );
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let errors: Vec<_> = output.vc.rules.iter().filter(|r| r.head.name == ERROR_REL).collect();
        assert_eq!(errors.len(), 1);
        let terms =
            errors[0].body.constraints.iter().map(try_eval_to_bool).collect::<Option<Vec<_>>>();
        assert_eq!(terms.map(|terms| terms.into_iter().all(|term| term)), Some(!assertion));
    }
}

#[test]
fn opaque_fat_pointer_loop_requires_initialization_before_the_first_iteration() {
    for initialized in [false, true] {
        let mut builder = ModuleBuilder::new("fat_pointer_cell_loop");
        let ty = Ty::FatPtr(FatPtrKind::Str);
        let signature = builder.add_func_type(vec![ty.clone(), Ty::Bool], vec![]);
        let mut function = builder.function("loop_read", signature);
        let entry = function.create_block();
        let header = function.create_block();
        let backedge = function.create_block();
        let exit = function.create_block();
        function.set_entry(entry);
        function.switch_to_block(entry);
        let input = function.add_block_param(entry, ty.clone());
        let again = function.add_block_param(entry, Ty::Bool);
        let slot = function.alloca(ty.clone());
        if initialized {
            function.store(ty.clone(), slot, input);
        }
        function.br(header, vec![]);
        function.switch_to_block(header);
        function.load(ty.clone(), slot);
        function.condbr(again, backedge, vec![], exit, vec![]);
        function.switch_to_block(backedge);
        function.store(ty.clone(), slot, input);
        function.br(header, vec![]);
        function.switch_to_block(exit);
        function.ret(vec![]);
        function.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(
            admitted(&module, slot, &ty),
            initialized,
            "a backedge store cannot initialize the first load"
        );
    }
}

// Exact function body and type tables extracted from the recorded 9178 compiler
// dump; the fixture README records the source and extraction. Its Assume needs
// live source-generation authority in the native gate. This test checks only
// the allocation predicate, never treats serialized input as that authority.
fn source_generated_unwrap_or() -> Module {
    serde_json::from_str(include_str!(
        "../tests/fixtures/option_str_unwrap_or_seal9178.module.json"
    ))
    .expect("frozen source-generated module")
}

#[test]
fn source_generated_unwrap_or_fat_pointer_cell_reaches_the_cfg_lane() {
    let module = source_generated_unwrap_or();
    assert!(trust_ir_build::validate_module_report(&module).is_ok());
    let function = &module.functions[0];
    assert_eq!(function.name, "core::option::Option::<&str>::unwrap_or");
    let slot = ValueId::new(4);
    let ty = Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)));
    assert!(block_local_alloca_reject(function, slot, &ty).is_some());
    assert!(promoted_cell_alloca_reject(&module, function, slot, &ty).is_some());
    assert!(opaque_fat_pointer_cell_is_admissible(&module, function, slot, &ty));
    assert!(single_cell_alloca_is_admissible(&module, function, slot, &ty));
}

#[test]
fn source_generated_unwrap_or_missing_arm_store_still_fails_closed() {
    for arm in [2, 3] {
        let mut module = source_generated_unwrap_or();
        let function = &mut module.functions[0];
        let block = function.blocks.iter_mut().find(|block| block.id.index() == arm).unwrap();
        block.body.retain(|node| !matches!(node.inst, Inst::Store { .. }));
        let slot = ValueId::new(4);
        let ty = Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)));
        assert!(
            !single_cell_alloca_is_admissible(&module, &module.functions[0], slot, &ty),
            "missing store in arm {arm}"
        );
    }
}

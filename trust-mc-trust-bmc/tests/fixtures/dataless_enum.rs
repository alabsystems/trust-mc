// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_ir::Module;
use trust_ir::constant::Constant;
use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant, Ty};
use trust_ir::value::{EnumId, FuncId, ValueId};
use trust_ir_build::ModuleBuilder;

pub(crate) fn fixture(make: bool, nested: bool, expected: i128) -> (Module, FuncId) {
    build(make, nested, expected, false)
}

pub(crate) fn scalar_fixture(nested: bool, expected: i128) -> (Module, FuncId) {
    build(false, nested, expected, true)
}

fn build(make: bool, nested: bool, expected: i128, scalar: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("dataless_enum_calls");
    let id = mb.add_enum(
        EnumDef::new(
            EnumId::new(0),
            "Sparse",
            ["Negative", "Positive"]
                .into_iter()
                .map(|name| EnumVariant { name: name.into(), fields: vec![], field_names: vec![] })
                .collect(),
        )
        .with_discriminants(vec![Some(-5), Some(7)])
        .with_repr(EnumTagRepr::I16),
    );
    let ty = if scalar { Ty::I16 } else { Ty::Enum(id) };
    let read_ty = mb.add_func_type(vec![ty.clone()], vec![Ty::I16]);
    let read = {
        let mut fb = mb.function("read_tag", read_ty);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let arg = fb.add_block_param(entry, ty.clone());
        let tag = if scalar { fb.copy(Ty::I16, arg) } else { fb.extract_field(Ty::I16, arg, 0) };
        fb.ret(vec![tag]);
        fb.build()
    };
    let callee = if nested {
        let mut fb = mb.function("forward", read_ty);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let arg = fb.add_block_param(entry, ty.clone());
        let tag = fb.call(read, vec![arg]);
        fb.ret(vec![tag]);
        fb.build()
    } else {
        read
    };
    let main_ty = mb.add_func_type(vec![], vec![Ty::I16]);
    let main = {
        let mut fb = mb.function("constructed_call", main_ty);
        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);
        let value = if scalar {
            fb.iconst(Ty::I16, 7)
        } else if make {
            fb.make_enum_variant(ty, 1, vec![])
        } else {
            fb.const_value(ty, Constant::Aggregate(vec![Constant::Int(7)]))
        };
        let tag = fb.call(callee, vec![value]);
        let want = fb.iconst(Ty::I16, expected);
        let equal = fb.icmp(trust_ir::inst::ICmpOp::Eq, Ty::I16, tag, want);
        fb.assert(equal);
        fb.ret(vec![tag]);
        fb.build()
    };
    (mb.build().expect("the real IR validator accepts the fixture"), main)
}

/// A symbolic scalar choice between two exact enum constructors, not a
/// symbolic enum input. Both source branches execute, including the negative tag.
pub(crate) fn symbolic_fixture(make: bool, nested: bool, bound: i128) -> (Module, FuncId) {
    let (mut module, main) = fixture(make, nested, bound);
    let function = module.functions.iter_mut().find(|f| f.id == main).unwrap();
    module.func_types[function.ty.as_usize()].params.push(Ty::Bool);
    let block = function.blocks.iter_mut().find(|b| b.id == function.entry).unwrap();
    let condition = ValueId::new(100);
    let other = ValueId::new(101);
    let selected = ValueId::new(102);
    block.params.push((condition, Ty::Bool));
    let first = block.body[0].results[0];
    block.body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::Enum(EnumId::new(0)),
            value: Constant::Aggregate(vec![Constant::Int(-5)]),
        })
        .with_result(other),
    );
    block.body.insert(
        2,
        InstrNode::new(Inst::Select {
            ty: Ty::Enum(EnumId::new(0)),
            cond: condition,
            then_val: first,
            else_val: other,
        })
        .with_result(selected),
    );
    for node in &mut block.body {
        if let Inst::Call { args, .. } = &mut node.inst {
            args[0] = selected;
        }
        if let Inst::ICmp { op, .. } = &mut node.inst {
            *op = ICmpOp::Sle;
        }
    }
    (module, main)
}

/// Enum transport through a real block-parameter join, not only an SSA select.
pub(crate) fn phi_fixture(make: bool, nested: bool, bound: i128) -> (Module, FuncId) {
    let (mut module, main) = symbolic_fixture(make, nested, bound);
    let function = module.functions.iter_mut().find(|f| f.id == main).unwrap();
    let entry = &mut function.blocks[0];
    let select = entry.body.remove(2);
    let Inst::Select { cond, then_val, else_val, ty } = select.inst else { unreachable!() };
    let join_value = select.results[0];
    let continuation = entry.body.split_off(2);
    let yes = trust_ir::BlockId::new(1);
    let no = trust_ir::BlockId::new(2);
    let join = trust_ir::BlockId::new(3);
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond,
        then_target: yes,
        then_args: vec![],
        else_target: no,
        else_args: vec![],
    }));
    let mut yes_block = trust_ir::Block::new(yes);
    yes_block.body.push(InstrNode::new(Inst::Br { target: join, args: vec![then_val] }));
    let mut no_block = trust_ir::Block::new(no);
    no_block.body.push(InstrNode::new(Inst::Br { target: join, args: vec![else_val] }));
    let mut join_block = trust_ir::Block::new(join);
    join_block.params.push((join_value, ty));
    join_block.body = continuation;
    function.blocks.extend([yes_block, no_block, join_block]);
    (module, main)
}

/// Even a discarded enum tag rewrite is canonical undefined behavior.
pub(crate) fn tag_write_fixture(inside_callee: bool) -> (Module, FuncId) {
    let (mut module, main) = fixture(false, false, 7);
    let target = if inside_callee { FuncId::new(0) } else { main };
    let function = module.functions.iter_mut().find(|f| f.id == target).unwrap();
    let block = &mut function.blocks[0];
    let (aggregate, at) =
        if inside_callee { (block.params[0].0, 0) } else { (block.body[0].results[0], 1) };
    let tag = ValueId::new(100);
    block.body.insert(
        at,
        InstrNode::new(Inst::Const { ty: Ty::I16, value: Constant::Int(-5) }).with_result(tag),
    );
    block.body.insert(
        at + 1,
        InstrNode::new(Inst::InsertField {
            ty: Ty::Enum(EnumId::new(0)),
            aggregate,
            field: 0,
            value: tag,
        })
        .with_result(ValueId::new(101)),
    );
    (module, main)
}

/// Exercise a selected enum inside the summarized callee's interpreter as well.
pub(crate) fn summarized_select_fixture(make: bool, nested: bool, bound: i128) -> (Module, FuncId) {
    let (mut module, inner) = symbolic_fixture(make, nested, bound);
    let ty = module.functions.iter().find(|f| f.id == inner).unwrap().ty;
    let id = FuncId::new(module.functions.iter().map(|f| f.id.index()).max().unwrap() + 1);
    let entry = trust_ir::BlockId::new(0);
    let mut wrapper = trust_ir::Function::new(id, "call_selector", ty, entry);
    let mut block = trust_ir::Block::new(entry);
    block.params.push((ValueId::new(0), Ty::Bool));
    block.body.push(
        InstrNode::new(Inst::Call { callee: inner, args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    wrapper.blocks.push(block);
    module.functions.push(wrapper);
    (module, id)
}

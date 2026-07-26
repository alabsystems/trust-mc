// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR transformation pass for simple `str::chars()/bytes().nth(...)` lowering.
//!
//! This pass recognizes direct constructor-plus-`nth` chains and rewrites them
//! to immutable helper calls in `kani_core`, removing the `Chars` / `Bytes`
//! iterator-state locals before CHC sees them.

use super::TransformPass;
use crate::kani_middle::attributes;
use crate::kani_middle::transform::TransformationType;
use crate::kani_middle::transform::body::MutableBody;
use crate::kani_queries::QueryDb;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BasicBlockIdx, Body, ConstOperand, Local, LocalDecl, Operand, Place, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_public::ty::{GenericArgs, MirConst, RigidTy, TyKind};
use std::collections::HashMap;
use tracing::{debug, trace};

const BYTES_HELPER_MARKER: &str = "StrBytesNthHelper";
const CHARS_HELPER_MARKER: &str = "StrCharsNthHelper";

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum StrIterKind {
    Bytes,
    Chars,
}

#[derive(Debug, Clone)]
struct StrIterConstructor {
    kind: StrIterKind,
    constructor_bb: BasicBlockIdx,
    target_bb: BasicBlockIdx,
    iter_local: Local,
    source: Operand,
    source_local: Option<Local>,
}

#[derive(Debug, Clone)]
struct SimpleStrNthChain {
    kind: StrIterKind,
    constructor_bb: BasicBlockIdx,
    constructor_target_bb: BasicBlockIdx,
    nth_bb: BasicBlockIdx,
    iter_local: Local,
    receiver_local: Local,
    source: Operand,
    source_local: Option<Local>,
    index: Operand,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct SimpleStrIterPass;

impl SimpleStrIterPass {
    pub(crate) fn new() -> Self {
        Self
    }
}

impl TransformPass for SimpleStrIterPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, _query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        true
    }

    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!("SimpleStrIterPass::transform for {:?}", instance.name());

        let chains = find_simple_nth_chains(&body);
        if chains.is_empty() {
            return (false, body);
        }

        let bytes_helper = find_helper_instance(BYTES_HELPER_MARKER);
        let chars_helper = find_helper_instance(CHARS_HELPER_MARKER);
        let mut mutable_body = MutableBody::from(body);
        let mut transformed = false;

        for chain in &chains {
            let helper = match chain.kind {
                StrIterKind::Bytes => bytes_helper,
                StrIterKind::Chars => chars_helper,
            };

            if let Some(helper) = helper {
                if transform_chain(&mut mutable_body, chain, helper) {
                    transformed = true;
                }
            } else {
                trace!(kind=?chain.kind, "simple_str_iter: helper instance missing, leaving chain unchanged");
            }
        }

        (transformed, mutable_body.into())
    }
}

fn find_simple_nth_chains(body: &Body) -> Vec<SimpleStrNthChain> {
    let mut constructors = HashMap::new();
    let locals = body.locals();

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let Some(constructor) = detect_constructor(bb_idx, &block.terminator, locals) {
            constructors.insert(constructor.iter_local, constructor);
        }
    }

    let mut chains = Vec::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let Some((receiver_local, index_operand)) = detect_nth_call(&block.terminator, locals)
        else {
            continue;
        };
        let Some(iter_local) = find_receiver_binding(&block.statements, receiver_local) else {
            continue;
        };
        let Some(constructor) = constructors.get(&iter_local) else {
            continue;
        };
        if constructor.target_bb != bb_idx {
            continue;
        }

        chains.push(SimpleStrNthChain {
            kind: constructor.kind,
            constructor_bb: constructor.constructor_bb,
            constructor_target_bb: constructor.target_bb,
            nth_bb: bb_idx,
            iter_local,
            receiver_local,
            source: constructor.source.clone(),
            source_local: constructor.source_local,
            index: index_operand,
        });
    }
    chains
}

fn transform_chain(body: &mut MutableBody, chain: &SimpleStrNthChain, helper: Instance) -> bool {
    let constructor_span = body.blocks()[chain.constructor_bb].terminator.span;
    let nth_span = body.blocks()[chain.nth_bb].terminator.span;
    let (nth_destination, nth_target, nth_unwind) =
        match &body.blocks()[chain.nth_bb].terminator.kind {
            TerminatorKind::Call { destination, target, unwind, .. } => {
                (destination.clone(), *target, *unwind)
            }
            _ => return false,
        };

    body.set_local_ty(chain.iter_local, rustc_public::ty::Ty::new_tuple(&[]));
    body.set_local_ty(chain.receiver_local, rustc_public::ty::Ty::new_tuple(&[]));

    {
        let constructor_block = body.block_mut(chain.constructor_bb);
        constructor_block.statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from(chain.iter_local),
                Rvalue::Aggregate(AggregateKind::Tuple, vec![]),
            ),
            span: constructor_span,
        });
        constructor_block.terminator = Terminator {
            kind: TerminatorKind::Goto { target: chain.constructor_target_bb },
            span: constructor_span,
        };
    }

    {
        let helper_literal = MirConst::try_new_zero_sized(helper.ty())
            .expect("helper function item should be zero-sized");
        let helper_func = Operand::Constant(ConstOperand {
            span: nth_span,
            user_ty: None,
            const_: helper_literal,
        });
        let nth_block = body.block_mut(chain.nth_bb);
        nth_block.statements.retain(|stmt| !should_remove_statement(stmt, chain));
        nth_block.terminator = Terminator {
            kind: TerminatorKind::Call {
                func: helper_func,
                args: vec![chain.source.clone(), chain.index.clone()],
                destination: nth_destination,
                target: nth_target,
                unwind: nth_unwind,
            },
            span: nth_span,
        };
    }

    true
}

fn should_remove_statement(stmt: &Statement, chain: &SimpleStrNthChain) -> bool {
    match &stmt.kind {
        StatementKind::Assign(lhs, rvalue)
            if lhs.local == chain.receiver_local
                && lhs.projection.is_empty()
                && matches!(rvalue, Rvalue::Ref(_, _, place) if place.local == chain.iter_local && place.projection.is_empty()) =>
        {
            true
        }
        StatementKind::StorageDead(local) => {
            Some(*local) == chain.source_local || *local == chain.receiver_local
        }
        _ => false,
    }
}

fn detect_constructor(
    bb_idx: BasicBlockIdx,
    terminator: &Terminator,
    locals: &[LocalDecl],
) -> Option<StrIterConstructor> {
    let TerminatorKind::Call { func, args, destination, target, .. } = &terminator.kind else {
        return None;
    };
    if args.is_empty() {
        return None;
    }

    let fn_name = call_fn_name(func, locals)?;
    let kind = match fn_name.as_str() {
        name if is_chars_constructor(name) && is_chars_local(locals[destination.local].ty) => {
            StrIterKind::Chars
        }
        name if is_bytes_constructor(name) && is_bytes_local(locals[destination.local].ty) => {
            StrIterKind::Bytes
        }
        _ => return None,
    };

    Some(StrIterConstructor {
        kind,
        constructor_bb: bb_idx,
        target_bb: (*target)?,
        iter_local: destination.local,
        source: normalize_source_operand(&args[0]),
        source_local: operand_local(&args[0]),
    })
}

fn detect_nth_call(terminator: &Terminator, locals: &[LocalDecl]) -> Option<(Local, Operand)> {
    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }

    let fn_name = call_fn_name(func, locals)?;
    if !is_nth_call(&fn_name) {
        return None;
    }

    let receiver_local = operand_local(&args[0])?;
    Some((receiver_local, args[1].clone()))
}

fn find_receiver_binding(statements: &[Statement], receiver_local: Local) -> Option<Local> {
    statements.iter().find_map(|stmt| {
        let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
            return None;
        };
        if lhs.local != receiver_local || !lhs.projection.is_empty() {
            return None;
        }
        let Rvalue::Ref(_, _, place) = rvalue else {
            return None;
        };
        place.projection.is_empty().then_some(place.local)
    })
}

fn operand_local(operand: &Operand) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

fn normalize_source_operand(operand: &Operand) -> Operand {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Operand::Copy(place.clone()),
        _ => operand.clone(),
    }
}

fn call_fn_name(func: &Operand, locals: &[LocalDecl]) -> Option<String> {
    let func_ty = func.ty(locals).ok()?;
    let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
        return None;
    };
    Some(def.name())
}

fn is_chars_constructor(fn_name: &str) -> bool {
    (fn_name == "chars" || fn_name.ends_with("::chars")) && fn_name.contains("str")
}

fn is_bytes_constructor(fn_name: &str) -> bool {
    (fn_name == "bytes" || fn_name.ends_with("::bytes")) && fn_name.contains("str")
}

fn is_nth_call(fn_name: &str) -> bool {
    fn_name == "nth" || fn_name.ends_with("::nth")
}

fn is_chars_local(ty: rustc_public::ty::Ty) -> bool {
    format!("{ty:?}").contains("str::Chars")
}

fn is_bytes_local(ty: rustc_public::ty::Ty) -> bool {
    format!("{ty:?}").contains("str::Bytes")
}

fn find_helper_instance(helper_marker: &str) -> Option<Instance> {
    rustc_public::all_local_items()
        .into_iter()
        .filter_map(|item| Instance::try_from(item).ok())
        .find(|instance| attributes::fn_marker(instance.def).as_deref() == Some(helper_marker))
        .or_else(|| {
            let mut crates = rustc_public::find_crates("kani");
            crates.extend(rustc_public::find_crates("core"));
            crates.extend(rustc_public::find_crates("std"));
            crates.into_iter().find_map(|krate| {
                krate.fn_defs().into_iter().find_map(|fn_def| {
                    (attributes::fn_marker(fn_def).as_deref() == Some(helper_marker))
                        .then(|| Instance::resolve(fn_def, &GenericArgs(vec![])).ok())
                        .flatten()
                })
            })
        })
}

#[cfg(test)]
#[path = "simple_str_iter_tests.rs"]
mod tests;

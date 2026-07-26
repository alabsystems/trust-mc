// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR remapping functions for function inlining.
//!
//! These functions remap callee MIR elements (locals, places, operands,
//! statements, terminators) to caller context during inlining. They are
//! pure functions with no dependency on the inlining pass struct.

use rustc_middle::ty::{EarlyBinder, TyCtxt, TypingEnv};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, AssertMessage, BasicBlock, BasicBlockIdx, ConstOperand, Operand, Place,
    ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnwindAction,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, GenericArgs, MirConst, Ty};
use std::collections::HashMap;

type Local = rustc_public::mir::Local;

/// Monomorphize a type using the callee instance's generic substitutions.
///
/// Falls back to the original type if monomorphization panics (e.g.,
/// unresolved generic params from a different scope).
pub(super) fn monomorphize_ty(tcx: TyCtxt<'_>, instance: Instance, ty: Ty) -> Ty {
    if instance.args().0.is_empty() {
        return ty;
    }
    let internal_instance = rustc_internal::internal(tcx, instance);
    let internal_ty = rustc_internal::internal(tcx, ty);
    rustc_internal::stable(internal_instance.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        TypingEnv::fully_monomorphized(),
        EarlyBinder::bind(internal_ty),
    ))
}

/// Remap a basic block from callee to caller context.
#[cfg(test)]
pub(super) fn remap_block(
    block: &BasicBlock,
    local_map: &HashMap<Local, Local>,
    block_map: &impl Fn(BasicBlockIdx) -> BasicBlockIdx,
    call_target: Option<BasicBlockIdx>,
) -> BasicBlock {
    remap_block_with_ty(block, local_map, block_map, call_target, &|ty| ty)
}

pub(super) fn remap_block_with_ty(
    block: &BasicBlock,
    local_map: &HashMap<Local, Local>,
    block_map: &impl Fn(BasicBlockIdx) -> BasicBlockIdx,
    call_target: Option<BasicBlockIdx>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> BasicBlock {
    let statements: Vec<Statement> =
        block.statements.iter().map(|stmt| remap_statement(stmt, local_map, remap_ty)).collect();

    let terminator =
        remap_terminator(&block.terminator, local_map, block_map, call_target, remap_ty);

    BasicBlock { statements, terminator }
}

/// Remap a statement from callee to caller context.
fn remap_statement(
    stmt: &Statement,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> Statement {
    let kind = match &stmt.kind {
        StatementKind::Assign(place, rvalue) => StatementKind::Assign(
            remap_place(place, local_map, remap_ty),
            remap_rvalue(rvalue, local_map, remap_ty),
        ),
        StatementKind::StorageLive(local) => {
            StatementKind::StorageLive(local_map.get(local).copied().unwrap_or(*local))
        }
        StatementKind::StorageDead(local) => {
            StatementKind::StorageDead(local_map.get(local).copied().unwrap_or(*local))
        }
        StatementKind::SetDiscriminant { place, variant_index } => StatementKind::SetDiscriminant {
            place: remap_place(place, local_map, remap_ty),
            variant_index: *variant_index,
        },
        StatementKind::FakeRead(kind, place) => {
            StatementKind::FakeRead(kind.clone(), remap_place(place, local_map, remap_ty))
        }
        StatementKind::Retag(kind, place) => {
            StatementKind::Retag(*kind, remap_place(place, local_map, remap_ty))
        }
        StatementKind::PlaceMention(place) => {
            StatementKind::PlaceMention(remap_place(place, local_map, remap_ty))
        }
        StatementKind::AscribeUserType { place, projections, variance } => {
            StatementKind::AscribeUserType {
                place: remap_place(place, local_map, remap_ty),
                projections: projections.clone(),
                variance: *variance,
            }
        }
        StatementKind::Intrinsic(intrinsic) => {
            StatementKind::Intrinsic(remap_intrinsic(intrinsic, local_map, remap_ty))
        }
        StatementKind::Coverage(_) | StatementKind::ConstEvalCounter | StatementKind::Nop => {
            stmt.kind.clone()
        }
    };

    Statement { kind, span: stmt.span }
}

/// Remap a place from callee to caller context.
fn remap_place(
    place: &Place,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> Place {
    let new_local = local_map.get(&place.local).copied().unwrap_or(place.local);
    let new_projection: Vec<ProjectionElem> = place
        .projection
        .iter()
        .map(|elem| remap_projection_elem(elem, local_map, remap_ty))
        .collect();

    Place { local: new_local, projection: new_projection }
}

/// Remap a projection element from callee to caller context.
fn remap_projection_elem(
    elem: &ProjectionElem,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> ProjectionElem {
    match elem {
        ProjectionElem::Index(local) => {
            ProjectionElem::Index(local_map.get(local).copied().unwrap_or(*local))
        }
        ProjectionElem::Field(field_idx, ty) => ProjectionElem::Field(*field_idx, remap_ty(*ty)),
        ProjectionElem::OpaqueCast(ty) => ProjectionElem::OpaqueCast(remap_ty(*ty)),
        _ => elem.clone(), // external enum: ProjectionElem
    }
}

/// Remap an rvalue from callee to caller context.
fn remap_rvalue(
    rvalue: &Rvalue,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> Rvalue {
    match rvalue {
        Rvalue::Use(operand) => Rvalue::Use(remap_operand(operand, local_map, remap_ty)),
        Rvalue::Repeat(operand, count) => {
            Rvalue::Repeat(remap_operand(operand, local_map, remap_ty), count.clone())
        }
        Rvalue::Ref(region, kind, place) => {
            Rvalue::Ref(region.clone(), *kind, remap_place(place, local_map, remap_ty))
        }
        Rvalue::ThreadLocalRef(def) => Rvalue::ThreadLocalRef(*def),
        Rvalue::AddressOf(kind, place) => {
            Rvalue::AddressOf(*kind, remap_place(place, local_map, remap_ty))
        }
        Rvalue::Len(place) => Rvalue::Len(remap_place(place, local_map, remap_ty)),
        Rvalue::Cast(kind, operand, ty) => {
            Rvalue::Cast(*kind, remap_operand(operand, local_map, remap_ty), remap_ty(*ty))
        }
        Rvalue::BinaryOp(op, lhs, rhs) => Rvalue::BinaryOp(
            *op,
            remap_operand(lhs, local_map, remap_ty),
            remap_operand(rhs, local_map, remap_ty),
        ),
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => Rvalue::CheckedBinaryOp(
            *op,
            remap_operand(lhs, local_map, remap_ty),
            remap_operand(rhs, local_map, remap_ty),
        ),
        Rvalue::UnaryOp(op, operand) => {
            Rvalue::UnaryOp(*op, remap_operand(operand, local_map, remap_ty))
        }
        Rvalue::Discriminant(place) => {
            Rvalue::Discriminant(remap_place(place, local_map, remap_ty))
        }
        Rvalue::Aggregate(kind, operands) => {
            let new_operands: Vec<Operand> =
                operands.iter().map(|op| remap_operand(op, local_map, remap_ty)).collect();
            Rvalue::Aggregate(remap_aggregate_kind(kind, remap_ty), new_operands)
        }
        Rvalue::ShallowInitBox(operand, ty) => {
            Rvalue::ShallowInitBox(remap_operand(operand, local_map, remap_ty), remap_ty(*ty))
        }
        Rvalue::CopyForDeref(place) => {
            Rvalue::CopyForDeref(remap_place(place, local_map, remap_ty))
        }
        Rvalue::NullaryOp(op) => Rvalue::NullaryOp(op.clone()),
    }
}

/// Remap an operand from callee to caller context.
fn remap_operand(
    operand: &Operand,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> Operand {
    match operand {
        Operand::Copy(place) => Operand::Copy(remap_place(place, local_map, remap_ty)),
        Operand::Move(place) => Operand::Move(remap_place(place, local_map, remap_ty)),
        Operand::Constant(c) => Operand::Constant(remap_const_operand(c, remap_ty)),
    }
}

/// Remap a constant operand's type from callee to caller context.
///
/// FnDef constants carry generic parameters that must be monomorphized when
/// inlining. Without this, nested calls in the inlined body retain unresolved
/// type params (e.g., `[T; LANES]`), causing panics in CHC codegen when it
/// tries to resolve these types. Part of #3675.
fn remap_const_operand(c: &ConstOperand, remap_ty: &impl Fn(Ty) -> Ty) -> ConstOperand {
    let orig_ty = c.const_.ty();
    let new_ty = remap_ty(orig_ty);
    if new_ty == orig_ty {
        return c.clone();
    }
    // For zero-sized types (FnDef, closures), reconstruct with the monomorphized type.
    if let Ok(new_const) = MirConst::try_new_zero_sized(new_ty) {
        ConstOperand { span: c.span, user_ty: c.user_ty, const_: new_const }
    } else {
        // Non-zero-sized constants (integer/float literals) should already have
        // concrete types. If remap_ty changed the type but we can't reconstruct,
        // fall back to clone — the value bits are still correct.
        c.clone()
    }
}

fn remap_aggregate_kind(kind: &AggregateKind, remap_ty: &impl Fn(Ty) -> Ty) -> AggregateKind {
    match kind {
        AggregateKind::Array(ty) => AggregateKind::Array(remap_ty(*ty)),
        AggregateKind::Tuple => AggregateKind::Tuple,
        AggregateKind::Adt(def, variant_idx, args, user_ty, field_idx) => AggregateKind::Adt(
            *def,
            *variant_idx,
            remap_generic_args(args, remap_ty),
            *user_ty,
            *field_idx,
        ),
        AggregateKind::Closure(def, args) => {
            AggregateKind::Closure(*def, remap_generic_args(args, remap_ty))
        }
        AggregateKind::Coroutine(def, args) => {
            AggregateKind::Coroutine(*def, remap_generic_args(args, remap_ty))
        }
        AggregateKind::CoroutineClosure(def, args) => {
            AggregateKind::CoroutineClosure(*def, remap_generic_args(args, remap_ty))
        }
        AggregateKind::RawPtr(ty, mutability) => AggregateKind::RawPtr(remap_ty(*ty), *mutability),
    }
}

fn remap_generic_args(args: &GenericArgs, remap_ty: &impl Fn(Ty) -> Ty) -> GenericArgs {
    GenericArgs(
        args.0
            .iter()
            .map(|arg| match arg {
                GenericArgKind::Type(ty) => GenericArgKind::Type(remap_ty(*ty)),
                _ => arg.clone(),
            })
            .collect(),
    )
}

/// Remap a non-diverging intrinsic from callee to caller context.
fn remap_intrinsic(
    intrinsic: &rustc_public::mir::NonDivergingIntrinsic,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> rustc_public::mir::NonDivergingIntrinsic {
    use rustc_public::mir::NonDivergingIntrinsic;
    match intrinsic {
        NonDivergingIntrinsic::Assume(operand) => {
            NonDivergingIntrinsic::Assume(remap_operand(operand, local_map, remap_ty))
        }
        NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
            NonDivergingIntrinsic::CopyNonOverlapping(rustc_public::mir::CopyNonOverlapping {
                src: remap_operand(&copy.src, local_map, remap_ty),
                dst: remap_operand(&copy.dst, local_map, remap_ty),
                count: remap_operand(&copy.count, local_map, remap_ty),
            })
        }
    }
}

/// Remap a terminator from callee to caller context.
fn remap_terminator(
    term: &Terminator,
    local_map: &HashMap<Local, Local>,
    block_map: &impl Fn(BasicBlockIdx) -> BasicBlockIdx,
    call_target: Option<BasicBlockIdx>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> Terminator {
    let kind = match &term.kind {
        // Return in callee becomes Goto to call's target
        TerminatorKind::Return => {
            if let Some(target) = call_target {
                TerminatorKind::Goto { target }
            } else {
                TerminatorKind::Unreachable
            }
        }

        TerminatorKind::Goto { target } => TerminatorKind::Goto { target: block_map(*target) },

        TerminatorKind::SwitchInt { discr, targets } => {
            let new_branches: Vec<(u128, BasicBlockIdx)> =
                targets.branches().map(|(val, bb)| (val, block_map(bb))).collect();
            let new_otherwise = block_map(targets.otherwise());
            TerminatorKind::SwitchInt {
                discr: remap_operand(discr, local_map, remap_ty),
                targets: rustc_public::mir::SwitchTargets::new(new_branches, new_otherwise),
            }
        }

        TerminatorKind::Call { func, args, destination, target, unwind } => TerminatorKind::Call {
            func: remap_operand(func, local_map, remap_ty),
            args: args.iter().map(|a| remap_operand(a, local_map, remap_ty)).collect(),
            destination: remap_place(destination, local_map, remap_ty),
            target: target.map(block_map),
            unwind: remap_unwind(unwind, block_map),
        },

        TerminatorKind::Assert { cond, expected, msg, target, unwind } => TerminatorKind::Assert {
            cond: remap_operand(cond, local_map, remap_ty),
            expected: *expected,
            msg: remap_assert_message(msg, local_map, remap_ty),
            target: block_map(*target),
            unwind: remap_unwind(unwind, block_map),
        },

        TerminatorKind::Drop { place, target, unwind } => TerminatorKind::Drop {
            place: remap_place(place, local_map, remap_ty),
            target: block_map(*target),
            unwind: remap_unwind(unwind, block_map),
        },

        TerminatorKind::Unreachable => TerminatorKind::Unreachable,
        TerminatorKind::Resume => TerminatorKind::Resume,
        TerminatorKind::Abort => TerminatorKind::Abort,

        TerminatorKind::InlineAsm { .. } => term.kind.clone(),
    };

    Terminator { kind, span: term.span }
}

/// Remap an unwind action from callee to caller context.
fn remap_unwind(
    unwind: &UnwindAction,
    block_map: &impl Fn(BasicBlockIdx) -> BasicBlockIdx,
) -> UnwindAction {
    match unwind {
        UnwindAction::Cleanup(bb) => UnwindAction::Cleanup(block_map(*bb)),
        other => *other,
    }
}

/// Remap an assert message from callee to caller context.
///
/// Critical for correctness: AssertMessage::Overflow contains operands that
/// reference callee locals. These must be remapped to caller locals.
/// Bug fix for #227.
fn remap_assert_message(
    msg: &AssertMessage,
    local_map: &HashMap<Local, Local>,
    remap_ty: &impl Fn(Ty) -> Ty,
) -> AssertMessage {
    match msg {
        AssertMessage::BoundsCheck { len, index } => AssertMessage::BoundsCheck {
            len: remap_operand(len, local_map, remap_ty),
            index: remap_operand(index, local_map, remap_ty),
        },
        AssertMessage::Overflow(op, lhs, rhs) => AssertMessage::Overflow(
            *op,
            remap_operand(lhs, local_map, remap_ty),
            remap_operand(rhs, local_map, remap_ty),
        ),
        AssertMessage::OverflowNeg(operand) => {
            AssertMessage::OverflowNeg(remap_operand(operand, local_map, remap_ty))
        }
        AssertMessage::DivisionByZero(operand) => {
            AssertMessage::DivisionByZero(remap_operand(operand, local_map, remap_ty))
        }
        AssertMessage::RemainderByZero(operand) => {
            AssertMessage::RemainderByZero(remap_operand(operand, local_map, remap_ty))
        }
        AssertMessage::InvalidEnumConstruction(operand) => {
            AssertMessage::InvalidEnumConstruction(remap_operand(operand, local_map, remap_ty))
        }
        // These variants don't contain operands, just clone them
        AssertMessage::ResumedAfterReturn(_)
        | AssertMessage::ResumedAfterPanic(_)
        | AssertMessage::ResumedAfterDrop(_)
        | AssertMessage::MisalignedPointerDereference { .. }
        | AssertMessage::NullPointerDereference => msg.clone(),
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};

pub(super) fn statement_allows_elided_pin_box_local(
    kind: &StatementKind,
    local_idx: usize,
) -> bool {
    match kind {
        StatementKind::Assign(place, rvalue) => {
            place.local != local_idx
                && !place_index_mentions_local(place, local_idx)
                && !rvalue_mentions_local(rvalue, local_idx)
        }
        StatementKind::SetDiscriminant { place, .. } => !place_mentions_local(place, local_idx),
        StatementKind::Intrinsic(intrinsic) => match intrinsic {
            rustc_public::mir::NonDivergingIntrinsic::Assume(op) => {
                !operand_mentions_local(op, local_idx)
            }
            rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                !operand_mentions_local(&copy.src, local_idx)
                    && !operand_mentions_local(&copy.dst, local_idx)
                    && !operand_mentions_local(&copy.count, local_idx)
            }
        },
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => true,
        StatementKind::FakeRead(_, place)
        | StatementKind::Retag(_, place)
        | StatementKind::PlaceMention(place) => !place_mentions_local(place, local_idx),
        StatementKind::AscribeUserType { place, .. } => !place_mentions_local(place, local_idx),
        StatementKind::Coverage(_) | StatementKind::ConstEvalCounter => true,
    }
}

pub(super) fn terminator_allows_ref_local_unmentioned(
    kind: &TerminatorKind,
    local_idx: usize,
) -> bool {
    match kind {
        TerminatorKind::Call { func, args, destination, .. } => {
            !operand_mentions_local(func, local_idx)
                && args.iter().all(|arg| !operand_mentions_local(arg, local_idx))
                && !place_index_mentions_local(destination, local_idx)
        }
        TerminatorKind::Drop { place, .. } => !place_mentions_local(place, local_idx),
        TerminatorKind::SwitchInt { discr, .. } => !operand_mentions_local(discr, local_idx),
        TerminatorKind::Assert { cond, msg, .. } => {
            !operand_mentions_local(cond, local_idx) && !assert_msg_mentions_local(msg, local_idx)
        }
        TerminatorKind::Return => local_idx != 0,
        TerminatorKind::Goto { .. }
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => true,
        TerminatorKind::InlineAsm { .. } => false,
    }
}

pub(super) fn rvalue_mentions_local(rvalue: &Rvalue, local_idx: usize) -> bool {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::ShallowInitBox(op, _) => operand_mentions_local(op, local_idx),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_mentions_local(lhs, local_idx) || operand_mentions_local(rhs, local_idx)
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => place_mentions_local(place, local_idx),
        Rvalue::Aggregate(_, operands) => {
            operands.iter().any(|operand| operand_mentions_local(operand, local_idx))
        }
        Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => false,
    }
}

pub(super) fn operand_mentions_local(operand: &Operand, local_idx: usize) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_mentions_local(place, local_idx),
        Operand::Constant(_) => false,
    }
}

pub(super) fn place_mentions_local(place: &rustc_public::mir::Place, local_idx: usize) -> bool {
    place.local == local_idx || place_index_mentions_local(place, local_idx)
}

pub(super) fn place_index_mentions_local(
    place: &rustc_public::mir::Place,
    local_idx: usize,
) -> bool {
    place
        .projection
        .iter()
        .any(|proj| matches!(proj, ProjectionElem::Index(index_local) if *index_local == local_idx))
}

pub(super) fn assert_msg_mentions_local(
    msg: &rustc_public::mir::AssertMessage,
    local_idx: usize,
) -> bool {
    use rustc_public::mir::AssertMessage;
    match msg {
        AssertMessage::BoundsCheck { len, index } => {
            operand_mentions_local(len, local_idx) || operand_mentions_local(index, local_idx)
        }
        AssertMessage::Overflow(_, lhs, rhs) => {
            operand_mentions_local(lhs, local_idx) || operand_mentions_local(rhs, local_idx)
        }
        AssertMessage::OverflowNeg(op)
        | AssertMessage::DivisionByZero(op)
        | AssertMessage::RemainderByZero(op) => operand_mentions_local(op, local_idx),
        AssertMessage::ResumedAfterReturn(_)
        | AssertMessage::ResumedAfterPanic(_)
        | AssertMessage::MisalignedPointerDereference { .. } => false,
        _ => false,
    }
}

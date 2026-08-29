// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR rewriting for range loop transformation.
//!
//! Contains the block-level MIR rewriting steps for transforming iterator-based
//! range loops into explicit indexed loops. Separated from detection logic in
//! `range_iter.rs` for file size.

use super::body::MutableBody;
use super::range_iter::{ElemIntType, RangeForLoop};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{
    BinOp, ConstOperand, Local, Mutability, Operand, Place, ProjectionElem, Rvalue, Statement,
    StatementKind, SwitchTargets, Terminator, TerminatorKind,
};
use rustc_public::ty::{MirConst, Ty};

/// Transform a detected range for-loop into an explicit indexed loop.
///
/// Returns `true` if the transformation succeeded.
pub(super) fn transform_range_loop(
    tcx: TyCtxt<'_>,
    body: &mut MutableBody,
    loop_info: &RangeForLoop,
) -> bool {
    let idx_local = body.new_local(loop_info.elem_ty, loop_info.span, Mutability::Mut);
    let end_local = body.new_local(loop_info.elem_ty, loop_info.span, Mutability::Not);
    let cond_local = body.new_local(Ty::bool_ty(), loop_info.span, Mutability::Not);

    let start_place = range_field_place(&loop_info.range_place, 0, loop_info.elem_ty);
    let end_place = range_field_place(&loop_info.range_place, 1, loop_info.elem_ty);

    if !replace_into_iter(body, loop_info, idx_local, end_local, start_place, end_place) {
        return false;
    }
    replace_next_call(body, loop_info, idx_local, end_local, cond_local);
    replace_option_switch(body, loop_info, cond_local);
    replace_unwrap_and_add_increment(tcx, body, loop_info, idx_local);
    true
}

/// Step 1: Replace the `into_iter` call with `_idx = start; _end = end`.
///
/// Both start and end must be copied into new locals here because the range
/// place may be killed by StorageDead in subsequent blocks (between into_iter
/// and the loop header). Reading range fields in the loop header after
/// StorageDead makes the values unconstrained in the CHC encoding, producing
/// spurious counterexamples. (#389)
fn replace_into_iter(
    body: &mut MutableBody,
    loop_info: &RangeForLoop,
    idx_local: Local,
    end_local: Local,
    start_place: Place,
    end_place: Place,
) -> bool {
    let into_iter_block = body.block_mut(loop_info.into_iter_bb);

    let original_target = match &into_iter_block.terminator.kind {
        TerminatorKind::Call { target, .. } => *target,
        _ => return false, // external enum: TerminatorKind
    };

    into_iter_block.statements.push(Statement {
        kind: StatementKind::Assign(
            Place::from(idx_local),
            Rvalue::Use(Operand::Copy(start_place)),
        ),
        span: loop_info.span,
    });
    into_iter_block.statements.push(Statement {
        kind: StatementKind::Assign(Place::from(end_local), Rvalue::Use(Operand::Copy(end_place))),
        span: loop_info.span,
    });

    if let Some(target) = original_target {
        into_iter_block.terminator =
            Terminator { kind: TerminatorKind::Goto { target }, span: loop_info.span };
    }
    true
}

/// Step 2: Replace the `Iterator::next` call with `_cond = _idx < _end`.
fn replace_next_call(
    body: &mut MutableBody,
    loop_info: &RangeForLoop,
    idx_local: Local,
    end_local: Local,
    cond_local: Local,
) {
    let next_block = body.block_mut(loop_info.next_bb);
    next_block.statements.clear();

    let idx_operand = Operand::Copy(Place::from(idx_local));
    let end_operand = Operand::Copy(Place::from(end_local));
    let lt_rvalue = Rvalue::BinaryOp(BinOp::Lt, idx_operand, end_operand);
    next_block.statements.push(Statement {
        kind: StatementKind::Assign(Place::from(cond_local), lt_rvalue),
        span: loop_info.span,
    });

    next_block.terminator = Terminator {
        kind: TerminatorKind::Goto { target: loop_info.switch_bb },
        span: loop_info.span,
    };
}

/// Step 3: Replace the Option discriminant switch with the condition switch.
fn replace_option_switch(body: &mut MutableBody, loop_info: &RangeForLoop, cond_local: Local) {
    let switch_block = body.block_mut(loop_info.switch_bb);
    let new_targets =
        SwitchTargets::new(vec![(0, loop_info.exit_bb), (1, loop_info.body_bb)], loop_info.exit_bb);

    switch_block.statements.clear();
    switch_block.terminator = Terminator {
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from(cond_local)),
            targets: new_targets,
        },
        span: loop_info.span,
    };
}

/// Step 4: Replace Option unwrap reads with idx reads and add `_idx += 1`.
fn replace_unwrap_and_add_increment(
    tcx: TyCtxt<'_>,
    body: &mut MutableBody,
    loop_info: &RangeForLoop,
    idx_local: Local,
) {
    let one_operand = match loop_info.elem_int_type {
        ElemIntType::Unsigned(uint_ty) => {
            let one_const = MirConst::try_from_uint(1u128, uint_ty)
                .expect("one should fit in unsigned range element type");
            Operand::Constant(ConstOperand {
                span: loop_info.span,
                user_ty: None,
                const_: one_const,
            })
        }
        ElemIntType::Signed(int_ty) => body.new_int_operand(tcx, 1i128, int_ty, loop_info.span),
    };

    let body_block = body.block_mut(loop_info.body_bb);

    for stmt in &mut body_block.statements {
        if let StatementKind::Assign(_lhs_place, rvalue) = &mut stmt.kind {
            let (source_place, is_copy) = match rvalue {
                Rvalue::Use(Operand::Copy(p)) => (Some(p), true),
                Rvalue::Use(Operand::Move(p)) => (Some(p), false),
                _ => (None, false), // external enum: Rvalue
            };

            if let Some(place) = source_place
                && place.local == loop_info.option_local
                && is_option_some_field_access(&place.projection)
            {
                let operand = if is_copy {
                    Operand::Copy(Place::from(idx_local))
                } else {
                    Operand::Move(Place::from(idx_local))
                };
                *rvalue = Rvalue::Use(operand);
            }
        }
    }

    let idx_operand = Operand::Copy(Place::from(idx_local));
    let add_rvalue = Rvalue::BinaryOp(BinOp::Add, idx_operand, one_operand);
    body_block.statements.push(Statement {
        kind: StatementKind::Assign(Place::from(idx_local), add_rvalue),
        span: loop_info.span,
    });
}

pub(super) fn range_field_place(range_place: &Place, field_idx: usize, field_ty: Ty) -> Place {
    let mut projection = range_place.projection.clone();
    projection.push(ProjectionElem::Field(field_idx, field_ty));
    Place { local: range_place.local, projection }
}

fn is_option_some_field_access(projection: &[ProjectionElem]) -> bool {
    let mut found_downcast = false;

    for elem in projection {
        match elem {
            ProjectionElem::Downcast(_) => {
                found_downcast = true;
            }
            ProjectionElem::Field(field_idx, _ty) => {
                if found_downcast && *field_idx == 0 {
                    return true;
                }
                return false;
            }
            _ => found_downcast = false, // external enum: ProjectionElem
        }
    }

    false
}

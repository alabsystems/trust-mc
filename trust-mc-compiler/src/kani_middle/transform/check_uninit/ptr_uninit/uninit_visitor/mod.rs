// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Visitor that collects all instructions relevant to uninitialized memory access.
//!
//! Decomposed from single 819-LOC file into:
//! - `mod.rs` — struct, TargetFinder, MirVisitor impl
//! - `assign_analysis.rs` — Assign statement analysis + helper functions
//! - `intrinsic_skip.rs` — Intrinsic classification for skip/check decisions

mod assign_analysis;
mod intrinsic_skip;

use std::mem;

use crate::kani_middle::transform::{
    body::{InsertPosition, MutableBody, SourceInstruction},
    check_uninit::{
        TargetFinder,
        relevant_instruction::{InitRelevantInstruction, MemoryInitOp},
    },
};
use rustc_public::{
    mir::{
        CastKind, LocalDecl, MirVisitor, NonDivergingIntrinsic, Operand, Place, PointerCoercion,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        alloc::GlobalAlloc,
        visit::{Location, PlaceContext},
    },
    ty::{ConstantKind, RigidTy, TyKind},
};

use crate::kani_middle::transform::check_uninit::ty_layout::tys_layout_compatible_to_size;

pub(crate) struct CheckUninitVisitor {
    pub(super) locals: Vec<LocalDecl>,
    /// All target instructions in the body.
    targets: Vec<InitRelevantInstruction>,
    /// Current analysis target, eventually needs to be added to a list of all targets.
    current_target: InitRelevantInstruction,
}

impl TargetFinder for CheckUninitVisitor {
    fn find_all(mut self, body: &MutableBody) -> Vec<InitRelevantInstruction> {
        self.locals = body.locals().to_vec();
        for (bb_idx, bb) in body.blocks().iter().enumerate() {
            // Set the first target to start iterating from.
            self.current_target = if !bb.statements.is_empty() {
                InitRelevantInstruction {
                    source: SourceInstruction::Statement { idx: 0, bb: bb_idx },
                    before_instruction: vec![],
                    after_instruction: vec![],
                }
            } else {
                InitRelevantInstruction {
                    source: SourceInstruction::Terminator { bb: bb_idx },
                    before_instruction: vec![],
                    after_instruction: vec![],
                }
            };
            if bb_idx == 0 {
                let union_args: Vec<_> = body
                    .locals()
                    .iter()
                    .enumerate()
                    .skip(1)
                    .take(body.arg_count())
                    .filter(|(_, local)| local.ty.kind().is_union())
                    .collect();
                if !union_args.is_empty() {
                    for (idx, _) in union_args {
                        self.push_target(MemoryInitOp::LoadArgument {
                            operand: Operand::Copy(Place { local: idx, projection: vec![] }),
                            argument_no: idx,
                        });
                    }
                }
            }
            self.visit_basic_block(bb);
        }
        self.targets
    }
}

impl CheckUninitVisitor {
    pub(crate) fn new() -> Self {
        Self {
            locals: vec![],
            targets: vec![],
            current_target: InitRelevantInstruction {
                source: SourceInstruction::Statement { idx: 0, bb: 0 },
                before_instruction: vec![],
                after_instruction: vec![],
            },
        }
    }

    pub(super) fn push_target(&mut self, source_op: MemoryInitOp) {
        self.current_target.push_operation(source_op);
    }
}

impl MirVisitor for CheckUninitVisitor {
    fn visit_statement(&mut self, stmt: &Statement, location: Location) {
        // Leave it as an exhaustive match to be notified when a new kind is added.
        match &stmt.kind {
            StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                self.super_statement(stmt, location);
                // The copy is untyped, so we should copy memory initialization state from `src`
                // to `dst`.
                self.push_target(MemoryInitOp::Copy {
                    from: copy.src.clone(),
                    to: copy.dst.clone(),
                    count: copy.count.clone(),
                });
            }
            StatementKind::Assign(place, rvalue) => {
                // First check rvalue.
                self.visit_rvalue(rvalue, location);
                // Delegate assign analysis to extracted module.
                self.analyze_assign(place, rvalue);
            }
            StatementKind::FakeRead(_, _)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Retag(_, _)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_))
            | StatementKind::Nop => self.super_statement(stmt, location),
        }
        // Switch to the next statement.
        if let SourceInstruction::Statement { idx, bb } = self.current_target.source {
            let next_target = InitRelevantInstruction {
                source: SourceInstruction::Statement { idx: idx + 1, bb },
                after_instruction: vec![],
                before_instruction: vec![],
            };
            self.targets.push(mem::replace(&mut self.current_target, next_target));
        } else {
            unreachable!(
                "current_target.source must be SourceInstruction::Statement during visit_statement"
            )
        }
    }

    fn visit_terminator(&mut self, term: &Terminator, location: Location) {
        if let SourceInstruction::Statement { bb, .. } = self.current_target.source {
            // We don't have to push the previous target, since it already happened in the statement
            // handling code.
            self.current_target = InitRelevantInstruction {
                source: SourceInstruction::Terminator { bb },
                after_instruction: vec![],
                before_instruction: vec![],
            };
        } else {
            // The only instruction in this basic block is the terminator, which was already set.
        }
        // Leave it as an exhaustive match to be notified when a new kind is added.
        match &term.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                self.super_terminator(term, location);
                if let Some(reason) = self.analyze_call(func, args, destination) {
                    // Preserve pre-decomposition behavior for unresolved call operands:
                    // re-traverse terminator operands and return early from visit_terminator.
                    self.super_terminator(term, location);
                    self.push_target(MemoryInitOp::Unsupported { reason });
                    return;
                }
            }
            TerminatorKind::Drop { place, .. } => {
                self.super_terminator(term, location);
                let place_ty = place.ty(&self.locals).expect("place should have valid type");

                // When drop is codegen'ed for types that could define their own dropping
                // behavior, a reference is taken to the place which is later implicitly coerced
                // to a pointer. Hence, we need to bless this pointer as initialized.
                match place
                    .ty(&self.locals)
                    .expect("place should have valid type")
                    .kind()
                    .rigid()
                    .expect("should be working with monomorphized code")
                {
                    RigidTy::Adt(..) | RigidTy::Dynamic(_, _) => {
                        self.push_target(MemoryInitOp::SetRef {
                            operand: Operand::Copy(place.clone()),
                            value: true,
                            position: InsertPosition::Before,
                        });
                    }
                    _ => {} // external enum: RigidTy
                }

                if place_ty.kind().is_raw_ptr() {
                    self.push_target(MemoryInitOp::Set {
                        operand: Operand::Copy(place.clone()),
                        value: false,
                        position: InsertPosition::After,
                    });
                }
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Assert { .. }
            | TerminatorKind::InlineAsm { .. } => self.super_terminator(term, location),
        }
        // Push the current target from the terminator onto the list.
        self.targets.push(mem::replace(
            &mut self.current_target,
            InitRelevantInstruction {
                source: SourceInstruction::Terminator { bb: 0 },
                before_instruction: vec![],
                after_instruction: vec![],
            },
        ));
    }

    fn visit_place(&mut self, place: &Place, ptx: PlaceContext, location: Location) {
        for (idx, elem) in place.projection.iter().enumerate() {
            let intermediate_place =
                Place { local: place.local, projection: place.projection[..idx].to_vec() };
            match elem {
                ProjectionElem::Deref => {
                    let ptr_ty =
                        intermediate_place.ty(&self.locals).expect("place should have valid type");
                    if ptr_ty.kind().is_raw_ptr() {
                        self.push_target(MemoryInitOp::Check {
                            operand: Operand::Copy(intermediate_place.clone()),
                        });
                    }
                }
                ProjectionElem::Field(_, _) => {
                    if intermediate_place
                        .ty(&self.locals)
                        .expect("place should have valid type")
                        .kind()
                        .is_union()
                        && !ptx.is_mutating()
                    {
                        let contains_deref_projection =
                            { place.projection.contains(&ProjectionElem::Deref) };
                        if contains_deref_projection {
                            // We do not currently support having a deref projection in the same
                            // place as union field access.
                            self.push_target(MemoryInitOp::Unsupported {
                                reason: "trust_mc does not yet support performing a dereference on a union field".to_string(),
                            });
                        }
                        // Accessing a place inside the union, need to check if it is initialized.
                        self.push_target(MemoryInitOp::CheckRef {
                            operand: Operand::Copy(place.clone()),
                        });
                    }
                }
                ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {
                    /* For a slice to be indexed, it should be valid first. */
                }
                ProjectionElem::Downcast(_) => {}
                ProjectionElem::OpaqueCast(_) => {}
            }
        }
        self.super_place(place, ptx, location);
    }

    fn visit_operand(&mut self, operand: &Operand, location: Location) {
        if let Operand::Constant(constant) = operand
            && let ConstantKind::Allocated(allocation) = constant.const_.kind()
        {
            for (_, prov) in &allocation.provenance.ptrs {
                if let GlobalAlloc::Static(_) = GlobalAlloc::from(prov.0)
                    && constant.ty().kind().is_raw_ptr()
                {
                    // If a static is a raw pointer, need to mark it as initialized.
                    self.push_target(MemoryInitOp::Set {
                        operand: Operand::Constant(constant.clone()),
                        value: true,
                        position: InsertPosition::Before,
                    });
                }
            }
        }
        self.super_operand(operand, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        if let Rvalue::Cast(cast_kind, operand, ty) = rvalue {
            match cast_kind {
                CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                    if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind()
                        && pointee_ty.kind().is_trait()
                    {
                        self.push_target(MemoryInitOp::Unsupported {
                                reason: "trust_mc does not support reasoning about memory initialization of unsized pointers.".to_string(),
                            });
                    }
                }
                CastKind::Transmute => {
                    let operand_ty =
                        operand.ty(&self.locals).expect("operand should have valid type");
                    if !tys_layout_compatible_to_size(&operand_ty, ty) {
                        // If transmuting between two types of incompatible layouts, padding
                        // bytes are exposed, which is UB.
                        self.push_target(MemoryInitOp::TriviallyUnsafe {
                            reason: "Transmuting between types of incompatible layouts."
                                .to_string(),
                        });
                    } else if let (
                        TyKind::RigidTy(RigidTy::Ref(_, from_ty, _)),
                        TyKind::RigidTy(RigidTy::Ref(_, to_ty, _)),
                    ) = (operand_ty.kind(), ty.kind())
                    {
                        if !tys_layout_compatible_to_size(&from_ty, &to_ty) {
                            // Since references are supposed to always be initialized for its type,
                            // transmuting between two references of incompatible layout is UB.
                            self.push_target(MemoryInitOp::TriviallyUnsafe {
                                reason: "Transmuting between references pointing to types of incompatible layouts."
                                    .to_string(),
                            });
                        }
                    } else if let (
                        TyKind::RigidTy(RigidTy::RawPtr(from_ty, _)),
                        TyKind::RigidTy(RigidTy::Ref(_, to_ty, _)),
                    ) = (operand_ty.kind(), ty.kind())
                    {
                        // Assert that we can only cast this way if types are the same.
                        assert!(from_ty == to_ty);
                        // When transmuting from a raw pointer to a reference, need to check that
                        // the value pointed by the raw pointer is initialized.
                        self.push_target(MemoryInitOp::Check { operand: operand.clone() });
                    }
                }
                _ => {} // external enum: Rvalue
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::useless_conversion, clippy::panic)]
mod tests;

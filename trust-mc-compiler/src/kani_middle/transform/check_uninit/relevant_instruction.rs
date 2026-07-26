// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Module containing data structures used in identifying places that need instrumentation and the
//! character of instrumentation needed.

use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use rustc_public::{
    mir::{FieldIdx, Mutability, Operand, Place, RawPtrKind, Rvalue, Statement, StatementKind},
    ty::{RigidTy, Ty},
};
use strum_macros::AsRefStr;

/// Memory initialization operations: set or get memory initialization state for a given pointer.
#[derive(AsRefStr, Clone, Debug)]
#[allow(clippy::large_enum_variant)] // Variant size difference is acceptable for this enum
pub(crate) enum MemoryInitOp {
    /// Check memory initialization of data bytes in a memory region starting from the pointer
    /// `operand` and of length `sizeof(operand)` bytes.
    Check { operand: Operand },
    /// Set memory initialization state of data bytes in a memory region starting from the pointer
    /// `operand` and of length `sizeof(operand)` bytes.
    Set { operand: Operand, value: bool, position: InsertPosition },
    /// Check memory initialization of data bytes in a memory region starting from the pointer
    /// `operand` and of length `count * sizeof(operand)` bytes.
    CheckSliceChunk { operand: Operand, count: Operand },
    /// Set memory initialization state of data bytes in a memory region starting from the pointer
    /// `operand` and of length `count * sizeof(operand)` bytes.
    SetSliceChunk { operand: Operand, count: Operand, value: bool, position: InsertPosition },
    /// Set memory initialization of data bytes in a memory region starting from the reference to
    /// `operand` and of length `sizeof(operand)` bytes.
    CheckRef { operand: Operand },
    /// Set memory initialization of data bytes in a memory region starting from the reference to
    /// `operand` and of length `sizeof(operand)` bytes.
    SetRef { operand: Operand, value: bool, position: InsertPosition },
    /// Unsupported memory initialization operation.
    Unsupported { reason: String },
    /// Operation that trivially accesses uninitialized memory, results in injecting `assert!(false)`.
    TriviallyUnsafe { reason: String },
    /// Copy memory initialization state over to another operand.
    Copy { from: Operand, to: Operand, count: Operand },
    /// Copy memory initialization state over from one union variable to another.
    AssignUnion { lvalue: Place, rvalue: Operand },
    /// Create a union from scratch with a given field index and store it in the provided operand.
    CreateUnion { operand: Operand, field: FieldIdx },
    /// Load argument containing a union from the argument buffer together if the argument number
    /// provided matches.
    LoadArgument { operand: Operand, argument_no: usize },
    /// Store argument containing a union into the argument buffer together with the argument number
    /// provided.
    StoreArgument { operand: Operand, argument_no: usize },
}

impl MemoryInitOp {
    /// Produce an operand for the relevant memory initialization related operation. This is mostly
    /// required so that the analysis can create a new local to take a reference in
    /// `MemoryInitOp::SetRef`.
    pub(crate) fn mk_operand(
        &self,
        body: &mut MutableBody,
        statements: &mut Vec<Statement>,
        source: &mut SourceInstruction,
    ) -> Operand {
        match self {
            MemoryInitOp::Check { operand, .. }
            | MemoryInitOp::Set { operand, .. }
            | MemoryInitOp::CheckSliceChunk { operand, .. }
            | MemoryInitOp::SetSliceChunk { operand, .. } => operand.clone(),
            MemoryInitOp::CheckRef { operand, .. }
            | MemoryInitOp::SetRef { operand, .. }
            | MemoryInitOp::CreateUnion { operand, .. }
            | MemoryInitOp::LoadArgument { operand, .. }
            | MemoryInitOp::StoreArgument { operand, .. } => {
                mk_ref(operand, body, statements, source)
            }
            MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. } => {
                unreachable!(
                    "mk_operand not supported for Copy/AssignUnion/Unsupported/TriviallyUnsafe"
                )
            }
        }
    }

    /// A helper to access operands of copy operation.
    pub(crate) fn expect_copy_operands(&self) -> (Operand, Operand) {
        match self {
            MemoryInitOp::Copy { from, to, .. } => (from.clone(), to.clone()),
            MemoryInitOp::Check { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::CreateUnion { .. }
            | MemoryInitOp::LoadArgument { .. }
            | MemoryInitOp::StoreArgument { .. } => {
                unreachable!("expect_copy_operands called for non-Copy operation: {self:?}")
            }
        }
    }

    /// A helper to access operands of union assign, automatically creates references to them.
    pub(crate) fn expect_assign_union_operands(
        &self,
        body: &mut MutableBody,
        statements: &mut Vec<Statement>,
        source: &mut SourceInstruction,
    ) -> (Operand, Operand) {
        match self {
            MemoryInitOp::AssignUnion { lvalue, rvalue } => {
                let lvalue_as_operand = Operand::Copy(lvalue.clone());
                (
                    mk_ref(rvalue, body, statements, source),
                    mk_ref(&lvalue_as_operand, body, statements, source),
                )
            }
            MemoryInitOp::Check { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::CreateUnion { .. }
            | MemoryInitOp::LoadArgument { .. }
            | MemoryInitOp::StoreArgument { .. } => unreachable!(
                "expect_assign_union_operands called for non-AssignUnion operation: {self:?}"
            ),
        }
    }

    pub(crate) fn operand_ty(&self, body: &MutableBody) -> Ty {
        match self {
            MemoryInitOp::Check { operand, .. }
            | MemoryInitOp::Set { operand, .. }
            | MemoryInitOp::CheckSliceChunk { operand, .. }
            | MemoryInitOp::SetSliceChunk { operand, .. } => {
                operand.ty(body.locals()).expect("operand should have type")
            }
            MemoryInitOp::SetRef { operand, .. }
            | MemoryInitOp::CheckRef { operand, .. }
            | MemoryInitOp::CreateUnion { operand, .. }
            | MemoryInitOp::LoadArgument { operand, .. }
            | MemoryInitOp::StoreArgument { operand, .. } => {
                let place = match operand {
                    Operand::Copy(place) | Operand::Move(place) => place,
                    Operand::Constant(_) => unreachable!(
                        "SetRef/CheckRef/CreateUnion/LoadArgument/StoreArgument operand must be Copy or Move, not Constant"
                    ),
                };
                let rvalue = Rvalue::AddressOf(RawPtrKind::Const, place.clone());
                rvalue.ty(body.locals()).expect("operand should have type")
            }
            MemoryInitOp::Unsupported { .. } | MemoryInitOp::TriviallyUnsafe { .. } => {
                unreachable!("operands do not exist for this operation")
            }
            MemoryInitOp::Copy { from, to, .. } => {
                // It does not matter which operand to return for layout generation, since both of
                // them have the same pointee type, so we assert that.
                let from_kind = from.ty(body.locals()).expect("operand should have type").kind();
                let to_kind = to.ty(body.locals()).expect("operand should have type").kind();

                let RigidTy::RawPtr(from_pointee_ty, _) =
                    from_kind.rigid().expect("type should be rigid").clone()
                else {
                    unreachable!("Copy operation 'from' operand must be a raw pointer")
                };
                let RigidTy::RawPtr(to_pointee_ty, _) =
                    to_kind.rigid().expect("type should be rigid").clone()
                else {
                    unreachable!("Copy operation 'to' operand must be a raw pointer")
                };
                assert!(from_pointee_ty == to_pointee_ty);
                from.ty(body.locals()).expect("operand should have type")
            }
            MemoryInitOp::AssignUnion { lvalue, .. } => {
                // It does not matter which operand to return for layout generation, since both of
                // them have the same pointee type.
                let address_of = Rvalue::AddressOf(RawPtrKind::Const, lvalue.clone());
                address_of.ty(body.locals()).expect("operand should have type")
            }
        }
    }

    pub(crate) fn expect_count(&self) -> Operand {
        match self {
            MemoryInitOp::CheckSliceChunk { count, .. }
            | MemoryInitOp::SetSliceChunk { count, .. }
            | MemoryInitOp::Copy { count, .. } => count.clone(),
            MemoryInitOp::Check { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::CreateUnion { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::StoreArgument { .. }
            | MemoryInitOp::LoadArgument { .. } => {
                unreachable!("expect_count called on variant without count field")
            }
        }
    }

    pub(crate) fn expect_value(&self) -> bool {
        match self {
            MemoryInitOp::Set { value, .. }
            | MemoryInitOp::SetSliceChunk { value, .. }
            | MemoryInitOp::SetRef { value, .. } => *value,
            MemoryInitOp::CreateUnion { .. } => true,
            MemoryInitOp::Check { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::StoreArgument { .. }
            | MemoryInitOp::LoadArgument { .. } => {
                unreachable!("expect_value called on variant without value field")
            }
        }
    }

    pub(crate) fn union_field(&self) -> Option<FieldIdx> {
        match self {
            MemoryInitOp::CreateUnion { field, .. } => Some(*field),
            MemoryInitOp::Check { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::StoreArgument { .. }
            | MemoryInitOp::LoadArgument { .. } => None,
        }
    }

    pub(crate) fn position(&self) -> InsertPosition {
        match self {
            MemoryInitOp::Set { position, .. }
            | MemoryInitOp::SetSliceChunk { position, .. }
            | MemoryInitOp::SetRef { position, .. } => *position,
            MemoryInitOp::Check { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::StoreArgument { .. }
            | MemoryInitOp::LoadArgument { .. } => InsertPosition::Before,
            MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::CreateUnion { .. } => InsertPosition::After,
        }
    }

    pub(crate) fn expect_argument_no(&self) -> usize {
        match self {
            MemoryInitOp::LoadArgument { argument_no, .. }
            | MemoryInitOp::StoreArgument { argument_no, .. } => *argument_no,
            MemoryInitOp::Check { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::CreateUnion { .. } => {
                unreachable!("expect_argument_no called for non-argument operation: {self:?}")
            }
        }
    }
}

/// Represents an instruction in the source code together with all memory initialization checks/sets
/// that are connected to the memory used in this instruction and whether they should be inserted
/// before or after the instruction.
#[derive(Clone, Debug)]
pub(crate) struct InitRelevantInstruction {
    /// The instruction that affects the state of the memory.
    pub(crate) source: SourceInstruction,
    /// All memory-related operations that should happen after the instruction.
    pub(crate) before_instruction: Vec<MemoryInitOp>,
    /// All memory-related operations that should happen after the instruction.
    pub(crate) after_instruction: Vec<MemoryInitOp>,
}

impl InitRelevantInstruction {
    pub(crate) fn push_operation(&mut self, source_op: MemoryInitOp) {
        match source_op.position() {
            InsertPosition::Before => self.before_instruction.push(source_op),
            InsertPosition::After => self.after_instruction.push(source_op),
        }
    }
}

/// A helper to generate instrumentation for taking a reference to a given operand. Returns the
/// operand which is a reference and stores all instrumentation in the statements vector passed.
fn mk_ref(
    operand: &Operand,
    body: &mut MutableBody,
    statements: &mut Vec<Statement>,
    source: &mut SourceInstruction,
) -> Operand {
    let span = source.span(body.blocks());

    let ref_local = {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => {
                unreachable!("mk_ref requires a place operand (Copy or Move), not Constant")
            }
        };
        let rvalue = Rvalue::AddressOf(RawPtrKind::Const, place.clone());
        let ret_ty = rvalue.ty(body.locals()).expect("operand should have type");
        let result = body.new_local(ret_ty, span, Mutability::Not);
        let stmt = Statement { kind: StatementKind::Assign(Place::from(result), rvalue), span };
        statements.push(stmt);
        result
    };

    Operand::Copy(Place { local: ref_local, projection: vec![] })
}

#[cfg(test)]
#[allow(clippy::useless_conversion)]
mod tests {
    use super::*;
    use crate::kani_middle::transform::body::SourceInstruction;
    use rustc_public::mir::{Local, Place};

    /// Helper: create an Operand::Copy from a local index.
    fn copy_local(idx: usize) -> Operand {
        Operand::Copy(Place::from(Local::from(idx)))
    }

    fn dummy_source() -> SourceInstruction {
        SourceInstruction::Statement { idx: 0, bb: 0usize.into() }
    }

    // =========================================================================
    // MemoryInitOp::expect_value
    // =========================================================================

    #[test]
    fn test_expect_value_set_true() {
        let op = MemoryInitOp::Set {
            operand: copy_local(0),
            value: true,
            position: InsertPosition::Before,
        };
        assert!(op.expect_value());
    }

    #[test]
    fn test_expect_value_set_false() {
        let op = MemoryInitOp::Set {
            operand: copy_local(0),
            value: false,
            position: InsertPosition::Before,
        };
        assert!(!op.expect_value());
    }

    #[test]
    fn test_expect_value_set_slice_chunk() {
        let op = MemoryInitOp::SetSliceChunk {
            operand: copy_local(0),
            count: copy_local(1),
            value: true,
            position: InsertPosition::After,
        };
        assert!(op.expect_value());
    }

    #[test]
    fn test_expect_value_set_ref() {
        let op = MemoryInitOp::SetRef {
            operand: copy_local(0),
            value: false,
            position: InsertPosition::Before,
        };
        assert!(!op.expect_value());
    }

    #[test]
    fn test_expect_value_create_union_always_true() {
        let op = MemoryInitOp::CreateUnion { operand: copy_local(0), field: 0usize.into() };
        assert!(op.expect_value());
    }

    // =========================================================================
    // MemoryInitOp::union_field
    // =========================================================================

    #[test]
    fn test_union_field_create_union() {
        let field_idx: FieldIdx = 3usize.into();
        let op = MemoryInitOp::CreateUnion { operand: copy_local(0), field: field_idx };
        assert_eq!(op.union_field(), Some(field_idx));
    }

    #[test]
    fn test_union_field_non_union_returns_none() {
        let op = MemoryInitOp::Check { operand: copy_local(0) };
        assert_eq!(op.union_field(), None);
    }

    #[test]
    fn test_union_field_copy_returns_none() {
        let op =
            MemoryInitOp::Copy { from: copy_local(0), to: copy_local(1), count: copy_local(2) };
        assert_eq!(op.union_field(), None);
    }

    // =========================================================================
    // MemoryInitOp::position
    // =========================================================================

    #[test]
    fn test_position_set_before() {
        let op = MemoryInitOp::Set {
            operand: copy_local(0),
            value: true,
            position: InsertPosition::Before,
        };
        assert_eq!(op.position(), InsertPosition::Before);
    }

    #[test]
    fn test_position_set_after() {
        let op = MemoryInitOp::Set {
            operand: copy_local(0),
            value: true,
            position: InsertPosition::After,
        };
        assert_eq!(op.position(), InsertPosition::After);
    }

    #[test]
    fn test_position_check_always_before() {
        let op = MemoryInitOp::Check { operand: copy_local(0) };
        assert_eq!(op.position(), InsertPosition::Before);
    }

    #[test]
    fn test_position_check_ref_always_before() {
        let op = MemoryInitOp::CheckRef { operand: copy_local(0) };
        assert_eq!(op.position(), InsertPosition::Before);
    }

    #[test]
    fn test_position_copy_always_after() {
        let op =
            MemoryInitOp::Copy { from: copy_local(0), to: copy_local(1), count: copy_local(2) };
        assert_eq!(op.position(), InsertPosition::After);
    }

    #[test]
    fn test_position_create_union_always_after() {
        let op = MemoryInitOp::CreateUnion { operand: copy_local(0), field: 0usize.into() };
        assert_eq!(op.position(), InsertPosition::After);
    }

    #[test]
    fn test_position_unsupported_always_before() {
        let op = MemoryInitOp::Unsupported { reason: "test".into() };
        assert_eq!(op.position(), InsertPosition::Before);
    }

    // =========================================================================
    // MemoryInitOp::expect_argument_no
    // =========================================================================

    #[test]
    fn test_expect_argument_no_load() {
        let op = MemoryInitOp::LoadArgument { operand: copy_local(0), argument_no: 42 };
        assert_eq!(op.expect_argument_no(), 42);
    }

    #[test]
    fn test_expect_argument_no_store() {
        let op = MemoryInitOp::StoreArgument { operand: copy_local(0), argument_no: 7 };
        assert_eq!(op.expect_argument_no(), 7);
    }

    // NOTE: expect_copy_operands and expect_count tests omitted — these methods
    // internally call Operand::clone() which requires the rustc compiler TLV
    // (Thread Local Variable) context, making them untestable outside a
    // compiler session.

    // =========================================================================
    // InitRelevantInstruction::push_operation
    // =========================================================================

    #[test]
    fn test_push_operation_before() {
        let mut instr = InitRelevantInstruction {
            source: dummy_source(),
            before_instruction: vec![],
            after_instruction: vec![],
        };
        let op = MemoryInitOp::Check { operand: copy_local(0) };
        instr.push_operation(op);
        assert_eq!(instr.before_instruction.len(), 1);
        assert_eq!(instr.after_instruction.len(), 0);
    }

    #[test]
    fn test_push_operation_after() {
        let mut instr = InitRelevantInstruction {
            source: dummy_source(),
            before_instruction: vec![],
            after_instruction: vec![],
        };
        let op = MemoryInitOp::CreateUnion { operand: copy_local(0), field: 0usize.into() };
        instr.push_operation(op);
        assert_eq!(instr.before_instruction.len(), 0);
        assert_eq!(instr.after_instruction.len(), 1);
    }

    #[test]
    fn test_push_operation_mixed() {
        let mut instr = InitRelevantInstruction {
            source: dummy_source(),
            before_instruction: vec![],
            after_instruction: vec![],
        };
        // Before: Check
        instr.push_operation(MemoryInitOp::Check { operand: copy_local(0) });
        // After: Copy
        instr.push_operation(MemoryInitOp::Copy {
            from: copy_local(1),
            to: copy_local(2),
            count: copy_local(3),
        });
        // Before: Unsupported
        instr.push_operation(MemoryInitOp::Unsupported { reason: "test".into() });
        assert_eq!(instr.before_instruction.len(), 2);
        assert_eq!(instr.after_instruction.len(), 1);
    }
}

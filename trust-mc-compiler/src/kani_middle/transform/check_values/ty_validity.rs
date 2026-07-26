// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Type validity helpers for the check_values transformation pass.
//!
//! This module contains:
//! - MIR instrumentation to check value validity (`build_limits`)
//! - Type layout traversal to find invalid value offsets (`ty_validity_per_offset`)
//! - Aggregate field and assignment helpers

use super::{ValidValueReq, ValidityRange};
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use rustc_public::CrateDef;
use rustc_public::abi::{FieldsShape, TagEncoding, VariantsShape, WrappingRange};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BinOp, FieldIdx, Local, LocalDecl, Mutability, Operand, Place, ProjectionElem, Rvalue,
};
use rustc_public::target::MachineInfo;
use rustc_public::ty::{AdtKind, RigidTy, Span, Ty, TyKind, UintTy};
use rustc_public_bridge::IndexedVal;
use tracing::debug;

pub(super) fn move_local(local: Local) -> Operand {
    Operand::Move(Place::from(local))
}

fn uint_ty(bytes: usize) -> UintTy {
    match bytes {
        1 => UintTy::U8,
        2 => UintTy::U16,
        4 => UintTy::U32,
        8 => UintTy::U64,
        16 => UintTy::U128,
        _ => unreachable!("Unexpected size: {bytes}"), // non-enum: usize (bytes)
    }
}

/// Gets the operand that corresponds to the assignment of the first sized field in memory.
pub(super) fn first_aggregate_operand(
    dest_ty: Ty,
    dest_shape: &FieldsShape,
    operands: &[Operand],
) -> Operand {
    let Some(first) = first_sized_field_idx(dest_ty, dest_shape) else {
        unreachable!("first_aggregate_operand called on type with no sized fields")
    };
    operands[first].clone()
}

/// Index of the first non_1zst fields in memory order.
pub(super) fn first_sized_field_idx(ty: Ty, shape: &FieldsShape) -> Option<FieldIdx> {
    if let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind()
        && adt_def.kind() == AdtKind::Struct
    {
        let offset_order = shape.fields_by_offset_order();
        let fields = adt_def.variants_iter().next().expect("at least one variant").fields();
        offset_order.into_iter().find(|idx| {
            !fields[*idx].ty_with_args(&args).layout().expect("field layout").shape().is_1zst()
        })
    } else {
        None
    }
}

/// An assignment to a field with invalid values is unsafe, and it may trigger UB if
/// the assigned value is invalid.
pub(super) fn assignment_check_points(
    machine_info: &MachineInfo,
    locals: &[LocalDecl],
    place: &Place,
    rvalue_ty: Ty,
) -> Vec<ValidValueReq> {
    let mut ty = locals[place.local].ty;
    let Some(rvalue_range) = ValidValueReq::try_from_ty(machine_info, rvalue_ty) else {
        return vec![];
    };
    let mut invalid_ranges = vec![];
    for proj in &place.projection {
        match proj {
            ProjectionElem::Field(field_idx, field_ty) => {
                let shape = ty.layout().expect("field type layout").shape();
                if first_sized_field_idx(ty, &shape.fields) == Some(*field_idx)
                    && let Some(dest_valid) = ValidValueReq::try_from_ty(machine_info, ty)
                    && !dest_valid.is_full()
                    && dest_valid.size == rvalue_range.size
                {
                    if !dest_valid.contains(&rvalue_range) {
                        invalid_ranges.push(dest_valid);
                    }
                } else {
                    invalid_ranges.clear();
                }
                ty = *field_ty;
            }
            ProjectionElem::Deref
            | ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(_)
            | ProjectionElem::OpaqueCast(_) => ty = proj.ty(ty).expect("projection type"),
        }
    }
    invalid_ranges
}

/// Retrieve the name of the intrinsic if this operand is an intrinsic.
pub(super) fn intrinsic_name(locals: &[LocalDecl], func: &Operand) -> Option<String> {
    let ty = func.ty(locals).expect("func type for intrinsic");
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return None };
    Instance::resolve(def, &args).expect("resolve intrinsic instance").intrinsic_name()
}

/// Instrument MIR to check the value pointed by `rvalue_ptr` satisfies requirement `req`.
pub(crate) fn build_limits(
    body: &mut MutableBody,
    req: &ValidValueReq,
    rvalue_ptr: Rvalue,
    source: &mut SourceInstruction,
) -> Local {
    let span = source.span(body.blocks());
    debug!(?req, ?rvalue_ptr, ?span, "build_limits");
    let primitive_ty = uint_ty(req.size.bytes());
    let orig_ptr = if req.offset != 0 {
        let start_ptr =
            move_local(body.insert_assignment(rvalue_ptr, source, InsertPosition::Before));
        let byte_ptr = move_local(body.insert_ptr_cast(
            start_ptr,
            Ty::unsigned_ty(UintTy::U8),
            Mutability::Not,
            source,
            InsertPosition::Before,
        ));
        let offset_const = body.new_uint_operand(req.offset as _, UintTy::Usize, span);
        let offset = move_local(body.insert_assignment(
            Rvalue::Use(offset_const),
            source,
            InsertPosition::Before,
        ));
        move_local(body.insert_binary_op(
            BinOp::Offset,
            byte_ptr,
            offset,
            source,
            InsertPosition::Before,
        ))
    } else {
        move_local(body.insert_assignment(rvalue_ptr, source, InsertPosition::Before))
    };
    let value_ptr = body.insert_ptr_cast(
        orig_ptr,
        Ty::unsigned_ty(primitive_ty),
        Mutability::Not,
        source,
        InsertPosition::Before,
    );
    let value = Operand::Copy(Place { local: value_ptr, projection: vec![ProjectionElem::Deref] });
    build_value_range_check(body, req, value, source)
}

/// Build the boolean validity condition comparing `value` (an operand of the
/// requirement's `uint_ty(req.size)` primitive type) against `req.valid_range`.
///
/// Shared by the byte-pointer dereference path (`build_limits`) and the precise
/// array-element path (`build_check` `DerefValidity`), so both emit identical
/// range checks — only the *source* of `value` differs (a type-punned pointer
/// deref vs. a direct `arr[idx]` element read).
pub(super) fn build_value_range_check(
    body: &mut MutableBody,
    req: &ValidValueReq,
    value: Operand,
    source: &mut SourceInstruction,
) -> Local {
    let span = source.span(body.blocks());
    let primitive_ty = uint_ty(req.size.bytes());
    match &req.valid_range {
        ValidityRange::Single(range) => {
            build_single_limit(body, range, source, span, primitive_ty, value)
        }
        ValidityRange::Multiple([range1, range2]) => {
            let cond1 = build_single_limit(body, range1, source, span, primitive_ty, value.clone());
            let cond2 = build_single_limit(body, range2, source, span, primitive_ty, value);
            body.insert_binary_op(
                BinOp::BitOr,
                move_local(cond1),
                move_local(cond2),
                source,
                InsertPosition::Before,
            )
        }
    }
}

fn build_single_limit(
    body: &mut MutableBody,
    range: &WrappingRange,
    source: &mut SourceInstruction,
    span: Span,
    primitive_ty: UintTy,
    value: Operand,
) -> Local {
    let start_const = body.new_uint_operand(range.start, primitive_ty, span);
    let end_const = body.new_uint_operand(range.end, primitive_ty, span);
    let start_result = body.insert_binary_op(
        BinOp::Ge,
        value.clone(),
        start_const,
        source,
        InsertPosition::Before,
    );
    let end_result =
        body.insert_binary_op(BinOp::Le, value, end_const, source, InsertPosition::Before);
    if range.wraps_around() {
        body.insert_binary_op(
            BinOp::BitOr,
            move_local(start_result),
            move_local(end_result),
            source,
            InsertPosition::Before,
        )
    } else {
        body.insert_binary_op(
            BinOp::BitAnd,
            move_local(start_result),
            move_local(end_result),
            source,
            InsertPosition::Before,
        )
    }
}

/// Traverse the type and find all invalid values and their location in memory.
///
/// Not all values are currently supported. For those not supported, we return Error.
pub(crate) fn ty_validity_per_offset(
    machine_info: &MachineInfo,
    ty: Ty,
    current_offset: usize,
) -> Result<Vec<ValidValueReq>, String> {
    let layout = ty.layout().expect("ty layout for validity").shape();
    let ty_req = || {
        if let Some(mut req) = ValidValueReq::try_from_ty(machine_info, ty)
            && !req.is_full()
        {
            req.offset = current_offset;
            vec![req]
        } else {
            vec![]
        }
    };
    match layout.fields {
        FieldsShape::Primitive => Ok(ty_req()),
        FieldsShape::Array { stride, count } if count > 0 => {
            let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
                unreachable!("type with FieldsShape::Array must be RigidTy::Array")
            };
            let elem_validity = ty_validity_per_offset(machine_info, elem_ty, current_offset)?;
            let mut result = vec![];
            if !elem_validity.is_empty() {
                for idx in 0..count {
                    let idx: usize = idx.try_into().expect("array index fits in usize");
                    let elem_offset = idx * stride.bytes();
                    result.extend(elem_validity.iter().cloned().map(|mut req| {
                        req.offset += elem_offset;
                        req
                    }));
                }
            }
            Ok(result)
        }
        FieldsShape::Arbitrary { ref offsets } => {
            match ty.kind().rigid().expect("rigid type expected") {
                RigidTy::Adt(def, args) => match def.kind() {
                    AdtKind::Enum => {
                        let ty_variants = def.variants();
                        match layout.variants {
                            VariantsShape::Empty => Ok(vec![]),
                            VariantsShape::Single { index } => {
                                let fields = ty_variants[index.to_index()].fields();
                                let mut fields_validity = vec![];
                                for idx in layout.fields.fields_by_offset_order() {
                                    let field_offset = offsets[idx].bytes();
                                    let field_ty = fields[idx].ty_with_args(args);
                                    fields_validity.append(&mut ty_validity_per_offset(
                                        machine_info,
                                        field_ty,
                                        field_offset + current_offset,
                                    )?);
                                }
                                Ok(fields_validity)
                            }
                            VariantsShape::Multiple {
                                tag_encoding: TagEncoding::Niche { .. },
                                ..
                            } => Err(format!("Unsupported Enum `{}` check", def.trimmed_name()))?,
                            VariantsShape::Multiple { variants, .. } => {
                                let enum_validity = ty_req();
                                let mut fields_validity = vec![];
                                for (index, variant) in variants.iter().enumerate() {
                                    let fields = ty_variants[index].fields();
                                    let FieldsShape::Arbitrary { offsets: variant_offsets } =
                                        &variant.fields
                                    else {
                                        continue;
                                    };
                                    for field_idx in variant.fields.fields_by_offset_order() {
                                        let field_offset = variant_offsets[field_idx].bytes();
                                        let field_ty = fields[field_idx].ty_with_args(args);
                                        fields_validity.append(&mut ty_validity_per_offset(
                                            machine_info,
                                            field_ty,
                                            field_offset + current_offset,
                                        )?);
                                    }
                                }
                                if fields_validity.is_empty() {
                                    Ok(enum_validity)
                                } else {
                                    Err(format!("Unsupported Enum `{}` check", def.trimmed_name()))
                                }
                            }
                        }
                    }
                    AdtKind::Union => {
                        unreachable!("Union should have FieldsShape::Union, not Arbitrary")
                    }
                    AdtKind::Struct => {
                        let mut struct_validity = ty_req();
                        let fields = def.variants_iter().next().expect("struct variant").fields();
                        for idx in layout.fields.fields_by_offset_order() {
                            let field_offset = offsets[idx].bytes();
                            let field_ty = fields[idx].ty_with_args(args);
                            struct_validity.append(&mut ty_validity_per_offset(
                                machine_info,
                                field_ty,
                                field_offset + current_offset,
                            )?);
                        }
                        Ok(struct_validity)
                    }
                },
                RigidTy::Pat(base_ty, ..) => {
                    let mut pat_validity = ty_req();
                    pat_validity.append(&mut ty_validity_per_offset(machine_info, *base_ty, 0)?);
                    Ok(pat_validity)
                }
                RigidTy::Tuple(tys) => {
                    let mut tuple_validity = vec![];
                    for idx in layout.fields.fields_by_offset_order() {
                        let field_offset = offsets[idx].bytes();
                        let field_ty = tys[idx];
                        tuple_validity.append(&mut ty_validity_per_offset(
                            machine_info,
                            field_ty,
                            field_offset + current_offset,
                        )?);
                    }
                    Ok(tuple_validity)
                }
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Never => {
                    unreachable!("Expected primitive layout for {ty:?}")
                }
                RigidTy::Str | RigidTy::Slice(_) | RigidTy::Array(_, _) => {
                    unreachable!("Expected array layout for {ty:?}")
                }
                RigidTy::RawPtr(_, _) | RigidTy::Ref(_, _, _) => Ok(ty_req()),
                RigidTy::FnDef(_, _)
                | RigidTy::FnPtr(_)
                | RigidTy::Closure(_, _)
                | RigidTy::Coroutine(_, _)
                | RigidTy::CoroutineClosure(_, _)
                | RigidTy::CoroutineWitness(_, _)
                | RigidTy::Foreign(_)
                | RigidTy::Dynamic(_, _) => Err(format!("Unsupported {ty:?}")),
            }
        }
        FieldsShape::Union(_) | FieldsShape::Array { .. } => Ok(vec![]),
    }
}

#[cfg(test)]
#[allow(clippy::useless_conversion, clippy::panic)]
mod tests {
    use super::*;

    // =========================================================================
    // uint_ty tests
    // =========================================================================

    #[test]
    fn test_uint_ty_u8() {
        assert_eq!(uint_ty(1), UintTy::U8);
    }

    #[test]
    fn test_uint_ty_u16() {
        assert_eq!(uint_ty(2), UintTy::U16);
    }

    #[test]
    fn test_uint_ty_u32() {
        assert_eq!(uint_ty(4), UintTy::U32);
    }

    #[test]
    fn test_uint_ty_u64() {
        assert_eq!(uint_ty(8), UintTy::U64);
    }

    #[test]
    fn test_uint_ty_u128() {
        assert_eq!(uint_ty(16), UintTy::U128);
    }

    #[test]
    #[should_panic(expected = "Unexpected size: 3")]
    fn test_uint_ty_invalid_size_3() {
        uint_ty(3);
    }

    #[test]
    #[should_panic(expected = "Unexpected size: 0")]
    fn test_uint_ty_invalid_size_0() {
        uint_ty(0);
    }

    #[test]
    #[should_panic(expected = "Unexpected size: 5")]
    fn test_uint_ty_invalid_size_5() {
        uint_ty(5);
    }

    // =========================================================================
    // move_local tests
    // =========================================================================

    #[test]
    fn test_move_local_creates_move_operand() {
        let local: Local = 42usize.into();
        let op = move_local(local);
        match op {
            Operand::Move(place) => {
                assert_eq!(place.local, local);
                assert!(place.projection.is_empty());
            }
            _ => panic!("Expected Operand::Move, got {op:?}"), // external enum: Operand
        }
    }

    #[test]
    fn test_move_local_zero() {
        let local: Local = 0usize.into();
        let op = move_local(local);
        match op {
            Operand::Move(place) => assert_eq!(place.local, local),
            _ => panic!("Expected Operand::Move"), // external enum: Operand
        }
    }
}

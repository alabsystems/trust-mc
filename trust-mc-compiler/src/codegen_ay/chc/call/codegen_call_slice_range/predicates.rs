// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Range-type predicates for slice indexing dispatch.
//! Part of #3981.

use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use super::super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn is_range_type_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if def.trimmed_name() == "Range" || def.trimmed_name() == "RangeInclusive"
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_inclusive_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeInclusive"
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_full_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeFull"
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_from_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeFrom"
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_to_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if def.trimmed_name() == "RangeTo"
                    || def.trimmed_name() == "RangeToInclusive"
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_to_inclusive_operand(
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeToInclusive"
        )
    }

    pub(in crate::codegen_ay::chc) fn operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Constant copy spans established by the pointer's actual definition chain.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use ay_bindings::Expr;
use rustc_public::mir::{CopyNonOverlapping, Operand};
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

impl ChcCtx<'_, '_> {
    /// A nonempty copy whose source or destination is definitely outside a
    /// tracked array is UB before any value is read or written. Emit that
    /// exact obligation without asking the value-copy lane to represent a
    /// negative index as a `usize` or invent the bytes outside the object.
    ///
    /// As with the existing punned-copy room check, an operation that always
    /// violates this obligation needs no memory update. Every defined execution
    /// stops at the violation; pre-existing approximation debt is untouched.
    pub(in crate::codegen_ay::chc) fn try_encode_invalid_array_copy_span(
        &mut self,
        copy: &CopyNonOverlapping,
    ) -> bool {
        if !self.memory_safety_checks || self.int_lift || POINTER_WIDTH != 64 {
            return false;
        }
        let Some(count) = self.body_constant_int(&copy.count).filter(|&count| count > 0) else {
            return false;
        };
        let invalid = |operand: &Operand| -> Option<bool> {
            let (Operand::Copy(pointer) | Operand::Move(pointer)) = operand else {
                return None;
            };
            if !pointer.projection.is_empty() {
                return None;
            }
            let target = self.ref_resolution.ref_targets.get(&pointer.local)?;
            if !target.projections.is_empty() {
                return None;
            }
            let target_ty = self.resolve_body_ty(self.body.locals().get(target.local)?.ty);
            let TyKind::RigidTy(RigidTy::Array(element, _)) = target_ty.kind() else {
                return None;
            };
            let pointer_ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
            let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = pointer_ty.kind() else {
                return None;
            };
            if self.resolve_body_ty(element) != self.resolve_body_ty(pointee) {
                return None;
            }
            let element_bytes = u128::try_from(self.get_type_size(element)?).ok()?;
            if element_bytes == 0 {
                return None;
            }
            let len = u128::try_from(self.get_array_length(target_ty)?).ok()?;
            let extent = len.checked_mul(element_bytes)?;
            // The split-pointer stack allocation and its exact extent fit the
            // existing 32-bit offset lane. Larger objects keep the old refusal.
            if extent > u128::from(u32::MAX) {
                return None;
            }
            let bytes = u128::try_from(count).ok()?.checked_mul(element_bytes)?;
            let displacement = self.native_array_pointer_byte_offset(pointer.local, target)?;
            // The bounded displacement is exact without reducing a far
            // wrapping step modulo the address width or the allocation lane.
            let displacement = i128::from(i32::try_from(displacement).ok()?);
            Some(
                displacement < 0 || u128::try_from(displacement).ok()?.checked_add(bytes)? > extent,
            )
        };
        if ![&copy.src, &copy.dst].into_iter().any(|pointer| invalid(pointer) == Some(true)) {
            return false;
        }
        let check = Expr::bool_const(false);
        // This new check does not enroll in the existing intrinsic-span
        // provenance discharge. Earlier approximation debt stays accounted.
        self.heap_state.pending_checks.push(check);
        true
    }
}

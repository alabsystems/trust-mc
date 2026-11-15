// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refusals where the legacy BMC representation does not carry native facts.

use super::*;
use rustc_public::mir::{BinOp, Place, ProjectionElem};

impl StatementCodegen<'_, '_, '_> {
    pub(in crate::codegen_ay::statement) fn guard_box_pointer_store(&mut self, place: &Place) {
        if self.ctx.has_native_box_allocations()
            && place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            && place.ty(self.body.locals()).ok().is_some_and(Self::ty_carries_a_pointer_value)
        {
            self.ctx.unsupported_with_fallback(
                "BoxPointerStore",
                "pointer-bearing stores need a native physical byte/provenance shadow",
            );
        }
    }
    pub(in crate::codegen_ay::statement) fn guard_box_pointer_storage(&mut self, place: &Place) {
        if self.ctx.has_native_box_allocations()
            && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            && place.ty(self.body.locals()).ok().is_some_and(Self::ty_carries_a_pointer_value)
        {
            self.ctx.unsupported_with_fallback(
                "BoxPointerStorage",
                "addressable pointer-bearing storage has no physical-byte/provenance shadow",
            );
        }
    }
    pub(in crate::codegen_ay::statement) fn guard_box_pointer_load(&mut self, operand: &Operand) {
        if !self.ctx.has_native_box_allocations() {
            return;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return };
        if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            && operand.ty(self.body.locals()).ok().is_some_and(Self::ty_carries_a_pointer_value)
        {
            self.ctx.unsupported_with_fallback("BoxPointerLoadProvenance",
                "typed pointer loads have no native provenance shadow through the byte-memory codec");
        }
    }

    pub(in crate::codegen_ay::statement) fn guard_box_pointer_comparison(
        &mut self,
        op: BinOp,
        lhs: &Operand,
        left: &Expr,
        right: &Expr,
    ) {
        if !self.ctx.has_native_box_allocations()
            || !matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Cmp
            )
            || !lhs.ty(self.body.locals()).ok().is_some_and(|ty| self.box_pointer_carrier(ty))
        {
            return;
        }
        if lhs.ty(self.body.locals()).ok().and_then(|ty| LayoutOf::new(ty).size_of()) != Some(8) {
            self.ctx.unsupported_with_fallback(
                "BoxPointerComparisonMetadata",
                "fat pointer comparison metadata is unavailable in the BMC pointer codec",
            );
            return;
        }
        let values = self.box_pointer_value(left).zip(self.box_pointer_value(right));
        let precise = values.is_some_and(|(left, right)| {
            if node(&left) == node(&right) { return true; }
            let zero = |value: &Expr| matches!(value.value(), ExprValue::BitVecConst { value, .. } if value == &0.into());
            let left_origin = self.ctx.box_pointer_origin(&left);
            let right_origin = self.ctx.box_pointer_origin(&right);
            if matches!(left_origin, Some(BoxPointerOrigin::Numeric))
                && matches!(right_origin, Some(BoxPointerOrigin::Numeric))
            { return true; }
            matches!(op, BinOp::Eq | BinOp::Ne)
                && ((zero(&left) && right_origin.is_some()) || (zero(&right) && left_origin.is_some()))
        });
        if !precise {
            self.ctx.unsupported_with_fallback(
                "BoxPointerComparison",
                "native physical address relation is not established by allocation stride IDs",
            );
        }
    }
}

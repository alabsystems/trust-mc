// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Helper routines for pointer-offset metadata propagation.

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use super::codegen_ctx::types::RefTarget;
use super::codegen_expr_constant::ExprConstant;
use crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn shift_ref_target_constant_index(
        &self,
        target_local: usize,
        projections: &mut [ProjectionElem],
        delta: i128,
    ) -> bool {
        let Some(last_idx) = projections.len().checked_sub(1) else {
            return false;
        };
        match projections[last_idx].clone() {
            ProjectionElem::ConstantIndex { offset, min_length, from_end: false } => {
                let Some(new_offset) = Self::shift_constant_index_offset(offset, delta) else {
                    return false;
                };
                projections[last_idx] = ProjectionElem::ConstantIndex {
                    offset: new_offset,
                    min_length,
                    from_end: false,
                };
                true
            }
            ProjectionElem::Index(index_local) => {
                let Some(offset) = self.constant_usize_assignment(index_local) else {
                    return false;
                };
                let Some(new_offset) = Self::shift_constant_index_offset(offset as u64, delta)
                else {
                    return false;
                };
                let Some(min_length) =
                    self.constant_index_min_length(target_local, &projections[..last_idx])
                else {
                    return false;
                };
                projections[last_idx] = ProjectionElem::ConstantIndex {
                    offset: new_offset,
                    min_length,
                    from_end: false,
                };
                true
            }
            _ => false,
        }
    }

    fn shift_constant_index_offset(offset: u64, delta: i128) -> Option<u64> {
        if delta >= 0 {
            offset.checked_add(u64::try_from(delta).ok()?)
        } else {
            offset.checked_sub(u64::try_from(delta.unsigned_abs()).ok()?)
        }
    }

    fn constant_index_min_length(
        &self,
        target_local: usize,
        prefix: &[ProjectionElem],
    ) -> Option<u64> {
        let place = Place { local: target_local, projection: prefix.to_vec() };
        let ty = place.ty(self.body.locals()).ok()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().ok(),
            _ => None,
        }
    }

    fn constant_usize_assignment(&self, local_idx: usize) -> Option<usize> {
        let mut values = Vec::new();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, Rvalue::Use(Operand::Constant(const_op))) =
                    &stmt.kind
                else {
                    continue;
                };
                if !lhs.projection.is_empty() || lhs.local != local_idx {
                    continue;
                }
                if let Some(value) = self
                    .translate_constant(const_op)
                    .and_then(|expr| Self::const_usize_from_expr(&expr))
                    && !values.contains(&value)
                {
                    values.push(value);
                }
            }
        }
        match values.as_slice() {
            [value] => Some(*value),
            _ => None,
        }
    }

    pub(in crate::codegen_ay::chc) fn const_array_element_for_ref_target(
        &mut self,
        ref_target: &RefTarget,
    ) -> Option<Expr> {
        let [ProjectionElem::ConstantIndex { offset, from_end: false, .. }] =
            ref_target.projections.as_slice()
        else {
            return None;
        };
        let index = usize::try_from(*offset).ok()?;
        let mut found_operand = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(
                    lhs,
                    Rvalue::Aggregate(AggregateKind::Array(_), operands),
                ) = &stmt.kind
                else {
                    continue;
                };
                if lhs.projection.is_empty()
                    && lhs.local == ref_target.local
                    && let Some(operand) = operands.get(index)
                {
                    found_operand = Some(operand.clone());
                    break;
                }
            }
            if found_operand.is_some() {
                break;
            }
        }
        let modified = std::collections::HashSet::new();
        self.translate_operand_with_modified(&found_operand?, &modified)
    }

    pub(in crate::codegen_ay::chc) fn apply_signed_metadata_offset(
        base_offset: usize,
        delta: i128,
    ) -> Option<usize> {
        if delta >= 0 {
            base_offset.checked_add(usize::try_from(delta).ok()?)
        } else {
            base_offset.checked_sub(usize::try_from(delta.unsigned_abs()).ok()?)
        }
    }

    pub(in crate::codegen_ay::chc) fn const_isize_from_expr(expr: &Expr) -> Option<i128> {
        match expr.value() {
            ay_bindings::ExprValue::IntConst(value) => i128::try_from(value).ok(),
            _ => {
                let (value, width) = const_bv_value(expr)?;
                let unsigned = u128::try_from(&value).ok()?;
                if width == 0 || width > 64 {
                    return None;
                }
                let sign_bit = 1u128.checked_shl(width - 1)?;
                let modulus = 1i128.checked_shl(width)?;
                let value = i128::try_from(unsigned).ok()?;
                Some(if unsigned & sign_bit == 0 { value } else { value - modulus })
            }
        }
    }

    pub(in crate::codegen_ay::chc) fn clear_ptr_offset_metadata(&mut self, dest_local: usize) {
        self.ref_resolution.ref_targets.remove(&dest_local);
        self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);
        // A stale allocation id on a reused local would feed the offset
        // alloc-bound check the WRONG allocation — clear provenance too.
        self.known_alloc_ids.remove(&dest_local);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Single-assignment scalar expression cache helpers for simple assignments.
//!
//! Part of #3905/#1739: allows cross-block propagation of symbolic scalar
//! expressions when every source operand is itself single-assignment.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn cache_single_assign_scalar_expr(
        &mut self,
        local_idx: usize,
        expr: &Expr,
        stable_sources: bool,
    ) {
        if !stable_sources || !self.encode.single_assign_locals.contains(&local_idx) {
            return;
        }
        if expr.sort().is_bool() || expr.sort().is_bitvec() || expr.sort().is_int() {
            self.encode.const_folded_call_results.insert(local_idx, expr.clone());
        }
    }

    pub(in crate::codegen_ay::chc) fn operands_have_single_assign_sources(
        &self,
        operands: &[Operand],
    ) -> bool {
        operands.iter().all(|operand| self.operand_has_single_assign_source(operand))
    }

    pub(in crate::codegen_ay::chc) fn rvalue_has_single_assign_sources(
        &self,
        rhs: &Rvalue,
    ) -> bool {
        match rhs {
            Rvalue::Use(op)
            | Rvalue::Repeat(op, _)
            | Rvalue::Cast(_, op, _)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::ShallowInitBox(op, _) => self.operand_has_single_assign_source(op),
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                self.operand_has_single_assign_source(lhs)
                    && self.operand_has_single_assign_source(rhs)
            }
            Rvalue::Aggregate(_, operands) => self.operands_have_single_assign_sources(operands),
            Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => true,
            Rvalue::Ref(_, _, _)
            | Rvalue::AddressOf(_, _)
            | Rvalue::Len(_)
            | Rvalue::Discriminant(_)
            | Rvalue::CopyForDeref(_) => false,
        }
    }

    fn operand_has_single_assign_source(&self, operand: &Operand) -> bool {
        match operand {
            Operand::Constant(_) => true,
            Operand::Copy(place) | Operand::Move(place) => {
                place.projection.is_empty()
                    && self.encode.single_assign_locals.contains(&place.local)
            }
        }
    }
}

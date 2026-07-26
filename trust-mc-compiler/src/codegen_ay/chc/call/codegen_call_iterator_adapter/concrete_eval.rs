// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Concrete BV expression evaluation and MIR string extraction utilities.
//!
//! Extracted from `helpers.rs` per #4129 (500 LOC threshold).
//!
//! Contains:
//! - `try_eval_concrete_bv_usize`: evaluate BV expressions with all-concrete operands
//! - `try_extract_concrete_strs_from_mir_array`: extract `[&str; N]` from MIR aggregates
//!
//! Part of #3189: concrete replay count extraction for filter_map chains.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue, StatementKind};

use super::super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to evaluate a BV expression with all-concrete operands to a usize.
    ///
    /// Handles patterns like `ite(bvuge(2, 0), bvsub(2, 0), 0)` that arise from
    /// `bv_saturating_sub` on concrete VecIntoIter pos/len values. AY doesn't
    /// simplify these at construction time, so we evaluate them here.
    ///
    /// Part of #3189: concrete replay count extraction for filter_map chains.
    pub(in crate::codegen_ay::chc) fn try_eval_concrete_bv_usize(expr: &Expr) -> Option<usize> {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok(),
            ExprValue::BvSub(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                l.checked_sub(r)
            }
            ExprValue::BvAdd(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                l.checked_add(r)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                let c = Self::try_eval_concrete_bv_bool(cond)?;
                if c {
                    Self::try_eval_concrete_bv_usize(then_expr)
                } else {
                    Self::try_eval_concrete_bv_usize(else_expr)
                }
            }
            _ => None,
        }
    }

    /// Try to evaluate a Bool expression with all-concrete operands.
    ///
    /// Part of #3189: helper for try_eval_concrete_bv_usize.
    fn try_eval_concrete_bv_bool(expr: &Expr) -> Option<bool> {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::BoolConst(b) => Some(*b),
            ExprValue::BvUGe(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                Some(l >= r)
            }
            ExprValue::BvULe(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                Some(l <= r)
            }
            _ => None,
        }
    }

    /// Extract concrete strings from MIR `[&str; N]` array aggregates.
    /// Part of #3189: MIR fallback when AY data array elements are BV64 pointers.
    pub(in crate::codegen_ay::chc) fn try_extract_concrete_strs_from_mir_array(
        &self,
        max_count: usize,
    ) -> Option<Vec<String>> {
        use rustc_public::mir::AggregateKind;
        use rustc_public::ty::{RigidTy, TyKind};
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind else {
                    continue;
                };
                let AggregateKind::Array(elem_ty) = kind else { continue };
                if operands.is_empty() || operands.len() > max_count {
                    continue;
                }
                let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = elem_ty.kind() else {
                    continue;
                };
                if !matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    continue;
                }
                // Part of #3189: handle both Constant and Copy/Move operands.
                // rustc may assign string literals to locals before aggregating.
                let results: Vec<Option<String>> = operands
                    .iter()
                    .map(|op| match op {
                        Operand::Constant(c) => Self::try_read_str_from_mir_const_ref(&c.const_),
                        Operand::Copy(place) | Operand::Move(place) => {
                            self.trace_local_to_str_const(place.local)
                        }
                    })
                    .collect();
                return results.into_iter().collect();
            }
        }
        None
    }

    /// Trace a MIR local back to its `&str` constant assignment.
    /// Part of #3189.
    fn trace_local_to_str_const(&self, target_local: usize) -> Option<String> {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != target_local || !lhs.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Constant(c)) = rhs {
                    return Self::try_read_str_from_mir_const_ref(&c.const_);
                }
            }
        }
        None
    }

    /// Try to constrain a FlattenNext payload to concrete chars from MIR string array.
    ///
    /// When a `flat_map(|s| s.chars())` operates on a concrete `[&str; N]` array,
    /// extract all individual char values and return a disjunction constraining the
    /// payload to be one of those chars. This turns the unconstrained symbolic into
    /// a bounded set, enabling the solver to prove concrete assertions like
    /// `assert_eq!(iter.next(), Some('H'))`.
    ///
    /// Part of #4112: flat_map(|s| s.chars()) over concrete string literals.
    pub(in crate::codegen_ay::chc) fn try_constrain_flatten_next_payload(
        &self,
        payload: &Expr,
    ) -> Option<Expr> {
        let strs = self.try_extract_concrete_strs_from_mir_array(16)?;
        if strs.is_empty() {
            return None;
        }
        let payload_width = payload.sort().bitvec_width()?;
        let mut disjuncts: Vec<Expr> = Vec::new();
        for s in &strs {
            for c in s.chars() {
                let char_bv = Expr::bitvec_const(c as u64, payload_width);
                disjuncts.push(payload.clone().eq(char_bv));
            }
        }
        if disjuncts.is_empty() {
            return None;
        }
        let mut result = disjuncts.remove(0);
        for d in disjuncts {
            result = result.or(d);
        }
        Some(result)
    }

    /// Read string bytes from a MIR `&str` constant by following provenance.
    /// Part of #3189: MIR fallback for BV64 pointer elements.
    fn try_read_str_from_mir_const_ref(mir_const: &rustc_public::ty::MirConst) -> Option<String> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::{ConstantKind, TyConstKind};
        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc.clone(),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_value_ty, alloc) => alloc.clone(),
                _ => return None,
            },
            _ => return None,
        };
        let ptr_bytes = (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
        let bytes_alloc_id = alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(bytes_alloc) = GlobalAlloc::from(bytes_alloc_id) else {
            return None;
        };
        if alloc.bytes.len() < ptr_bytes * 2 {
            return None;
        }
        let mut len_arr = [0u8; 8];
        for (i, opt_byte) in alloc.bytes[ptr_bytes..ptr_bytes * 2].iter().enumerate() {
            len_arr[i] = (*opt_byte)?;
        }
        let len = u64::from_le_bytes(len_arr) as usize;
        if len == 0 || len > 256 || bytes_alloc.bytes.len() < len {
            return None;
        }
        let bytes: Option<Vec<u8>> = (0..len).map(|i| bytes_alloc.bytes.get(i).copied()?).collect();
        String::from_utf8(bytes?).ok()
    }
}

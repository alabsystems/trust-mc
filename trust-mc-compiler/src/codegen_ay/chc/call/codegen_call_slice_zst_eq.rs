// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ZST-specific slice equality helpers.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use super::codegen_call_kani_model_dst::is_zst_ty;
use super::codegen_call_misc::CallMisc;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn try_zst_slice_eq_expr(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let lhs = args.first()?;
        let rhs = args.get(1)?;
        if !self.slice_operand_elem_is_zst(lhs) || !self.slice_operand_elem_is_zst(rhs) {
            return None;
        }

        let lhs_len = self.slice_operand_len_expr(args, 0, modified_locals)?;
        let rhs_len = self.slice_operand_len_expr(args, 1, modified_locals)?;
        Some(lhs_len.eq(rhs_len))
    }

    fn slice_operand_elem_is_zst(&self, operand: &Operand) -> bool {
        self.slice_operand_elem_ty(operand).is_some_and(|ty| is_zst_ty(self.resolve_body_ty(ty)))
    }

    fn slice_operand_elem_ty(&self, operand: &Operand) -> Option<rustc_public::ty::Ty> {
        let ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
            _ => ty,
        };

        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => {
                Some(self.resolve_body_ty(elem))
            }
            _ => None,
        }
    }

    fn slice_operand_len_expr(
        &mut self,
        args: &[Operand],
        arg_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let receiver = args.get(arg_idx)?;
        if let Some(len) = self.static_slice_len_from_operand(receiver) {
            return Some(len);
        }

        let local = match receiver {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        if let Some(local) = local
            && let Some(len) = self.ref_resolution.subslice_len.get(&local).cloned()
        {
            return Some(len);
        }

        if let Some(len) = self.translate_ptr_metadata(receiver, modified_locals) {
            return Some(len);
        }

        if let Some(expr) = self.resolve_ref_or_const_referent(receiver, modified_locals) {
            let expr_sort = expr.sort().clone();
            if let Some(dt_name) = expr_sort.datatype_name()
                && let Some(len_sort) = Self::get_dt_field_sort(&expr, "fld_len")
            {
                return Some(expr.field_select(dt_name, "fld_len", len_sort));
            }
        }

        self.resolve_slice_arg_length(args, arg_idx, modified_locals)
    }
}

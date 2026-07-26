// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BoxNew callable-payload helpers for allocation call handling.
//!
//! Part of #3980: When Box::new receives a promoted `&fn item` or closure-ref
//! payload, the standard operand translator returns None (ZST fn defs have no
//! data representation). These helpers produce a unique BV64 fn_ptr_id so the
//! heap store constrains the value correctly for later dyn dispatch read-back.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use super::super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Produce a unique BV64 fn_ptr_id for callable operands (FnDef, Closure,
    /// or references thereof). Reuses the `fn_ptr_ids` map so the same function
    /// identity yields the same pointer constant, enabling dyn dispatch matching
    /// after `Box::new(&fn_item)`.
    pub(in crate::codegen_ay::chc) fn translate_boxnew_callable_operand(
        &mut self,
        operand: &Operand,
    ) -> Option<Expr> {
        let ty = operand.ty(self.body.locals()).ok()?;
        let fn_like_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => ty,
        };
        let key = match fn_like_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                format!("{}_{:?}", def.trimmed_name(), args)
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                format!("closure_{}_{:?}", def.trimmed_name(), args)
            }
            _ => return None,
        };

        if let Some(expr) = self.fn_ptr_ids.get(&key) {
            return Some(expr.clone());
        }

        let id = self.next_fn_ptr_id;
        self.next_fn_ptr_id += 1;
        let expr = Expr::bitvec_const(id as i128, POINTER_WIDTH);
        self.fn_ptr_ids.insert(key, expr.clone());
        Some(expr)
    }

    pub(in crate::codegen_ay::chc) fn boxnew_operand_is_callable(&self, operand: &Operand) -> bool {
        let Ok(ty) = operand.ty(self.body.locals()) else {
            return false;
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(..)) | TyKind::RigidTy(RigidTy::Closure(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                matches!(inner.kind(), TyKind::RigidTy(RigidTy::FnDef(..) | RigidTy::Closure(..)))
            }
            _ => false,
        }
    }
}

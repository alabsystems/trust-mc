// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Resolution utilities and transmute intrinsic.
//!
//! Other dispatch helpers split into sibling modules per design D1
//! (file-decomposition-500loc-compliance):
//! - `ptr_arithmetic.rs` — pointer offset intrinsics
//! - `closure_call.rs` — closure invocation
//! - `precheck.rs` — abstracted fallback + btree/cow prechecks

use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;
use crate::kani_middle::abi::LayoutOf;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Resolve a call operand to its canonical def path.
    pub(in crate::codegen_ay::statement) fn resolve_callee_path(
        &self,
        func: &Operand,
    ) -> Option<String> {
        let func_ty = func.ty(self.body.locals()).into_option()?;
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };

        let instance_opt = Instance::resolve(fn_def, &fn_args).into_option();
        let def_id =
            instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
        let internal_def_id = rustc_internal::internal(self.ctx.tcx, def_id);
        let path = self.ctx.tcx.def_path_str(internal_def_id);
        Some(path)
    }

    /// Check if the callee is a foreign (FFI) function.
    ///
    /// Returns `true` if the call operand resolves to a foreign item (extern fn).
    /// Used to detect undefined FFI calls that should emit assert(false) instead
    /// of the unconstrained fallback. Part of #3175.
    ///
    /// Uses `tcx.is_foreign_item()` on the FnDef's def_id directly, bypassing
    /// Instance::resolve which can fail for extern declarations without bodies.
    /// Pattern from kani_middle/attributes/mod.rs:801.
    pub(in crate::codegen_ay::statement) fn is_foreign_call(&self, func: &Operand) -> bool {
        let func_ty = match func.ty(self.body.locals()).into_option() {
            Some(ty) => ty,
            None => return false,
        };
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return false,
        };
        let internal_def_id = rustc_internal::internal(self.ctx.tcx, fn_def.def_id());
        self.ctx.tcx.is_foreign_item(internal_def_id)
    }

    /// Extract element type size and alignment from a generic function call.
    ///
    /// Used by Layout::array<T> and Layout::new<T> to determine T's size/align.
    /// Falls back to pointer width (8, 8) if type cannot be extracted.
    pub(in crate::codegen_ay::statement) fn extract_element_type_layout(
        &self,
        func: &Operand,
    ) -> (usize, usize) {
        let func_ty = func.ty(self.body.locals()).into_option();
        func_ty
            .and_then(|ty| {
                if let TyKind::RigidTy(RigidTy::FnDef(_, args)) = ty.kind()
                    && let Some(GenericArgKind::Type(element_ty)) = args.0.first()
                {
                    let layout = LayoutOf::new(*element_ty);
                    let size = layout.size_of().unwrap_or(8);
                    let align = layout.align_of().unwrap_or(8);
                    debug!(
                        "extract_element_type_layout: T={:?} size={} align={}",
                        element_ty.kind(),
                        size,
                        align
                    );
                    Some((size, align))
                } else {
                    None
                }
            })
            .unwrap_or((8, 8)) // Fallback to pointer-width
    }

    pub(in crate::codegen_ay::statement) fn codegen_transmute_intrinsic(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let arg = args.first()?;
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        // Part of #3809: route through codegen_cast_with_kind so the
        // intrinsic path shares the same layout-sensitive transmute guard
        // as the MIR Rvalue::Cast(Transmute, ...) path.
        let expr = self.codegen_cast_with_kind(&super::super::CastKind::Transmute, arg, dest_ty)?;
        self.assign_value_to_place(destination, expr);
        target
    }
}

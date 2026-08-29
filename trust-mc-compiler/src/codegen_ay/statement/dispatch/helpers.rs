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
use rustc_span::sym;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    fn function_implements_exact_trait_method(
        &self,
        direct_def_id: rustc_hir::def_id::DefId,
        trait_def_id: rustc_hir::def_id::DefId,
        allowed_names: &[&str],
    ) -> bool {
        let direct_trait_item = self
            .ctx
            .tcx
            .opt_associated_item(direct_def_id)
            .and_then(|item| item.trait_item_def_id());
        self.ctx.tcx.associated_item_def_ids(trait_def_id).iter().copied().any(|trait_method| {
            allowed_names.contains(&self.ctx.tcx.item_name(trait_method).as_str())
                && (direct_def_id == trait_method || direct_trait_item == Some(trait_method))
        })
    }

    fn is_authenticated_index_carrier(&self, op: &Operand) -> bool {
        let Some(mut ty) = op.ty(self.body.locals()).into_option() else {
            return false;
        };
        for _ in 0..8 {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                    ty = inner;
                }
                TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Array(..) | RigidTy::Str) => {
                    return true;
                }
                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                    let def_id = rustc_internal::internal(self.ctx.tcx, def.def_id());
                    let path = self.ctx.tcx.def_path_str(def_id);
                    return self.ctx.tcx.crate_name(def_id.krate).as_str() == "alloc"
                        && matches!(path.as_str(), "alloc::vec::Vec" | "std::vec::Vec");
                }
                _ => return false,
            }
        }
        false
    }

    /// Authenticate the semantic Index/IndexMut stubs independently of the
    /// suffix-compatible registry. Returns the real `(source, index)` order.
    pub(in crate::codegen_ay::statement) fn authenticated_core_index_args<'b>(
        &self,
        func: &Operand,
        args: &'b [Operand],
    ) -> Option<(&'b Operand, &'b Operand)> {
        if args.len() != 2 {
            return None;
        }
        let func_ty = func.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            return None;
        };
        let direct_def_id = rustc_internal::internal(self.ctx.tcx, fn_def.def_id());
        if !matches!(
            self.ctx.tcx.crate_name(direct_def_id.krate).as_str(),
            "core" | "alloc" | "std"
        ) {
            return None;
        }
        let (source, index) = if self.function_implements_exact_trait_method(
            direct_def_id,
            self.ctx.tcx.lang_items().index_trait()?,
            &["index"],
        ) || self.function_implements_exact_trait_method(
            direct_def_id,
            self.ctx.tcx.lang_items().index_mut_trait()?,
            &["index_mut"],
        ) {
            (&args[0], &args[1])
        } else if let Some(slice_index_trait) = self.ctx.tcx.get_diagnostic_item(sym::SliceIndex)
            && self.function_implements_exact_trait_method(
                direct_def_id,
                slice_index_trait,
                &["index", "index_mut"],
            )
        {
            (&args[1], &args[0])
        } else {
            return None;
        };
        self.is_authenticated_index_carrier(source).then_some((source, index))
    }

    pub(in crate::codegen_ay::statement) fn is_exact_core_range_full_operand(
        &self,
        op: &Operand,
    ) -> bool {
        let Some(ty) = op.ty(self.body.locals()).into_option() else {
            return false;
        };
        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if {
            let def_id = rustc_internal::internal(self.ctx.tcx, def.def_id());
            let path = self.ctx.tcx.def_path_str(def_id);
            self.ctx.tcx.crate_name(def_id.krate).as_str() == "core"
                && matches!(path.as_str(), "core::ops::range::RangeFull" | "std::ops::RangeFull")
        })
    }

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

    /// The last path segment of a call operand's `FnDef` name, for messages.
    /// `"<unknown>"` when the operand is not a named `FnDef`. Display only —
    /// no obligation ever keys on it.
    pub(in crate::codegen_ay::statement) fn callee_display_name(&self, func: &Operand) -> String {
        let Some(func_ty) = func.ty(self.body.locals()).into_option() else {
            return "<unknown>".to_string();
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
            return "<unknown>".to_string();
        };
        let name = def.trimmed_name();
        name.rsplit("::").next().unwrap_or(&name).to_string()
    }

    /// As [`is_foreign_call`], for an already-resolved [`Instance`] — the shape
    /// a function POINTER callee arrives in. `func(x)` through an
    /// `extern "C" fn(u32) -> u32` pointer never carries a `FnDef` operand, so
    /// the operand-based test cannot see its foreignness; the resolved instance
    /// can.
    pub(in crate::codegen_ay::statement) fn is_foreign_instance(
        &self,
        instance: &rustc_public::mir::mono::Instance,
    ) -> bool {
        let internal_def_id = rustc_internal::internal(self.ctx.tcx, instance.def.def_id());
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

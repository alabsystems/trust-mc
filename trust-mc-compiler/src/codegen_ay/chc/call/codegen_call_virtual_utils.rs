// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Virtual call utility methods: local update constraints, inline field reads,
//! trait resolution, and spawn scheduler vtable model.
//!
//! Extracted from `codegen_call_virtual.rs` — Part of #4206.

use ay_bindings::{Expr, Sort};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn build_local_update_constraints(
        &mut self,
        local_idx: usize,
        value: Expr,
        context: &'static str,
    ) -> Option<Vec<Expr>> {
        if let Some(flat_constraints) =
            self.build_flattened_destination_constraints(local_idx, value.clone())
        {
            return Some(flat_constraints);
        }
        let (_, dest_var) = self.resolve_destination(local_idx)?;
        let eq =
            self.make_coerced_eq_constraint(&dest_var, value, dest_var.sort(), local_idx, context);
        Some(eq.into_iter().collect())
    }

    /// Mark type arrays that `build_self_field_map` will read during virtual
    /// inline body translation. Without this, the post-codegen pruner removes
    /// the arrays from the block's relation signature, making them universally
    /// quantified free variables in the CHC rule — the solver treats the memory
    /// read as unconstrained.
    ///
    /// Part of #3608: Fixes store-load disconnect for virtual dispatch on
    /// unsized coercion targets (basic_inner_coercion, box_coercion, etc.).
    pub(in crate::codegen_ay::chc) fn mark_inline_field_reads(
        &mut self,
        impl_body: &rustc_public::mir::Body,
        params: &[Expr],
        bb_idx: usize,
    ) {
        use super::inline_field_map::scalar_type_key;

        // Part of #4132: Only mark type arrays for param[0] (self/receiver),
        // matching build_self_field_map's self-only scope. The all-params
        // generalization from #3994 marks type arrays for non-self params
        // that have no corresponding stores, introducing unconstrained free
        // variables that cause 2-step CTREX on coroutine/async types.
        let locals = impl_body.locals();
        let Some(self_expr) = params.first() else { return };
        {
            let param_expr = self_expr;
            let has_pointer_storage = if *param_expr.sort() == Sort::bitvec(POINTER_WIDTH) {
                true
            } else {
                self.extract_pointer_storage_expr(param_expr)
                    .is_some_and(|ptr| *ptr.sort() == Sort::bitvec(POINTER_WIDTH))
            };
            if !has_pointer_storage {
                return;
            }

            let local_idx = 1;
            let Some(local_decl) = locals.get(local_idx) else { return };
            let pointee_ty = match local_decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                _ => return,
            };

            if !matches!(
                pointee_ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(..)) | TyKind::RigidTy(RigidTy::Tuple(..))
            ) {
                if let Some(type_key) = scalar_type_key(pointee_ty) {
                    if let Some((arr_name, _)) = self.heap_state.lookup_type_array(&type_key) {
                        let arr_name = arr_name.clone();
                        self.heap_state.mark_type_array_read(&arr_name, bb_idx);
                    }
                }
                return;
            }

            let field_types: Vec<rustc_public::ty::Ty> = match pointee_ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                    let variants = def.variants();
                    if variants.is_empty() {
                        return;
                    }
                    variants[0].fields().iter().map(|field| field.ty_with_args(&args)).collect()
                }
                TyKind::RigidTy(RigidTy::Tuple(elems)) => elems,
                _ => return,
            };

            for field_ty in &field_types {
                if let Some(type_key) = scalar_type_key(*field_ty) {
                    if let Some((arr_name, _)) = self.heap_state.lookup_type_array(&type_key) {
                        let arr_name = arr_name.clone();
                        self.heap_state.mark_type_array_read(&arr_name, bb_idx);
                    }
                }
            }
        }
    }

    /// Resolve the parent trait DefId from a method's FnDef.
    ///
    /// Returns `None` if the method is not a trait method, allowing the caller
    /// to bail out early.
    ///
    /// Part of #3589: extracted from find_concrete_virtual_impls for reuse.
    pub(in crate::codegen_ay::chc) fn resolve_parent_trait_def_id(
        &self,
        fn_def: rustc_public::ty::FnDef,
    ) -> Option<rustc_span::def_id::DefId> {
        use rustc_public::CrateDef;
        let method_def_id = fn_def.def_id();
        let internal_method_def_id = rustc_internal::internal(self.tcx, method_def_id);
        let parent_def_id = self.tcx.parent(internal_method_def_id);
        if !self.tcx.is_trait(parent_def_id) {
            debug!("virtual call: parent is not a trait");
            return None;
        }
        Some(parent_def_id)
    }

    /// Provide the next vtable ID from the spawn scheduler model if active.
    /// Part of #4075: provide the next vtable ID from the spawn scheduler model.
    /// Previous versions tried to scope this with `current_instance ==
    /// Scheduler::run`, but the inline walker keeps `current_instance` on the
    /// harness rather than the inlined callee. The model itself is only built
    /// for the spawn scheduler poll loop, so its presence is the scope
    /// boundary.
    pub(in crate::codegen_ay::chc) fn try_consume_spawn_scheduler_run_vtable_expr(
        &mut self,
    ) -> Option<Expr> {
        self.spawn_scheduler_vtable_model.as_mut()?.next_vtable_expr()
    }

    pub(super) fn try_consume_spawn_scheduler_future_vtable_expr(
        &mut self,
        trait_def_id: Option<rustc_span::def_id::DefId>,
    ) -> Option<Expr> {
        let trait_def_id = trait_def_id?;
        let trait_path = self.tcx.def_path_str(trait_def_id);
        if trait_path != "core::future::future::Future" && !trait_path.ends_with("::Future") {
            return None;
        }
        self.spawn_scheduler_vtable_model.as_mut()?.next_vtable_expr()
    }
}

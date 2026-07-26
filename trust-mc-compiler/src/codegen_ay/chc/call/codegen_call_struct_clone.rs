// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Struct-level Clone::clone dispatch for structs with collection fields.
//!
//! When `<SomeStruct as Clone>::clone(&self)` is called on a struct that
//! contains HashMap/BTreeMap fields, the derived Clone body has projected
//! writes (e.g., `_result.data = <BTreeMap as Clone>::clone(&self.data)`)
//! that the general fn_inline translator cannot handle (#3236 bailout).
//! This causes the entire clone result to be unconstrained.
//!
//! This dispatcher intercepts struct-level Clone before fn_inline and
//! synthesizes a CHC-level clone: copy all struct state vars (Datatype
//! identity or per-field leaf copy for flattened encoding) plus collection
//! auxiliary vars (present, len) from source to destination.
//!
//! Part of #3348: clone-return-from-method gap for struct-embedded collections.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use std::sync::Arc;

use super::ChcCtx;
use super::call_accumulator::CallAccumulator;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_decl_flatten;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{bool_sort, int_sort, ptr_sort};

/// Resolved source and destination for a struct clone operation.
struct CloneLocals {
    actual_source: usize,
    dest_local: usize,
    source_idx: usize,
    dest_idx: usize,
}

/// Extension trait for struct-level Clone dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructClone {
    fn try_dispatch_call_struct_clone(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchStructClone for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_clone(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(locals) = self.detect_struct_clone(dcx) else { return false };

        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        self.copy_struct_state_vars(&locals, &mut extra_constraints);
        self.copy_collection_aux_vars(&locals, &mut extra_constraints, &mut extra_dests);

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        debug!(
            locals.actual_source,
            locals.dest_local, "CHC: struct-level Clone with collection fields dispatched (#3348)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detect if this call is Clone::clone on a struct with collection fields.
    /// Returns resolved source/destination locals if so.
    fn detect_struct_clone(&self, dcx: &DispatchCallContext<'_>) -> Option<CloneLocals> {
        // Check callee is Clone::clone.
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return None,
        };
        // Part of #3348: trimmed_name() returns "Clone::clone" (with trait prefix)
        // for derived Clone impls, not bare "clone". Match both forms.
        let trimmed = fn_def.trimmed_name();
        if trimmed != "clone" && trimmed != "Clone::clone" {
            return None;
        }

        // Check receiver is a struct with collection fields.
        let arg0 = dcx.args.first()?;
        let arg0_ty = arg0.ty(self.body.locals()).ok()?;
        let inner_ty = match arg0_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        };
        if Self::type_is_hashmap(&inner_ty) {
            return None;
        }
        let (def, args) = match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return None,
        };
        let variants = def.variants();
        if variants.is_empty() {
            return None;
        }
        let has_collection =
            variants[0].fields().iter().any(|f| Self::type_is_hashmap(&f.ty_with_args(&args)));
        if !has_collection {
            return None;
        }

        // Resolve source and destination locals.
        let source_local = match arg0 {
            rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) => p.local,
            _ => return None,
        };
        let actual_source =
            self.ref_resolution.ref_targets.get(&source_local).map_or(source_local, |rt| rt.local);
        let source_idx = self.try_state_idx_for_local(actual_source)?;
        let dest_local: usize = dcx.destination.local;
        let dest_idx = self.try_state_idx_for_local(dest_local)?;

        Some(CloneLocals { actual_source, dest_local, source_idx, dest_idx })
    }

    /// Copy struct state vars from source to destination (Datatype or flattened).
    fn copy_struct_state_vars(&mut self, locals: &CloneLocals, constraints: &mut Vec<Expr>) {
        let (src_name, src_sort) = match self.state_var_mgr.state_vars.get(locals.source_idx) {
            Some(pair) => pair.clone(),
            None => return,
        };

        if src_sort.datatype_name().is_some() {
            if let Some((dest_out_name, _)) =
                self.state_var_mgr.output_state_vars.get(locals.dest_idx).cloned()
            {
                let src_var = Expr::var(&*src_name, src_sort.clone());
                let dest_var = Expr::var(&*dest_out_name, src_sort);
                constraints.push(dest_var.eq(src_var));
                self.mark_state_var_modified(locals.dest_idx);
            }
        } else {
            self.copy_flattened_leaf_vars(locals, constraints);
        }
    }

    /// Copy flattened leaf state vars field-by-field.
    fn copy_flattened_leaf_vars(&mut self, locals: &CloneLocals, constraints: &mut Vec<Expr>) {
        let local_ty = self.body.locals()[locals.actual_source].ty;
        let Some(struct_sort) = Self::translate_ty(local_ty) else { return };
        let Some(dt) = struct_sort.datatype_sort() else { return };
        let Some(cons) = dt.constructors.first() else { return };

        let mut offset = 0;
        for field in &cons.fields {
            let leaf_sorts = codegen_decl_flatten::collect_leaf_sorts(&field.sort, 0);
            for leaf_offset in 0..leaf_sorts.len() {
                let src_leaf_idx = locals.source_idx + offset + leaf_offset;
                let dst_leaf_idx = locals.dest_idx + offset + leaf_offset;
                if let (Some((sn, ss)), Some((dn, _))) = (
                    self.state_var_mgr.state_vars.get(src_leaf_idx).cloned(),
                    self.state_var_mgr.output_state_vars.get(dst_leaf_idx).cloned(),
                ) {
                    let sv = Expr::var(&*sn, ss.clone());
                    let dv = Expr::var(&*dn, ss);
                    constraints.push(dv.eq(sv));
                    self.mark_state_var_modified(dst_leaf_idx);
                }
            }
            offset += leaf_sorts.len();
        }
    }

    /// Copy collection auxiliary vars (present, len) from source to destination.
    ///
    /// Part of #3348: When the destination has no present/len vars registered
    /// (or shares the same name as source, making the copy tautological),
    /// create fresh independent state variables for the clone destination.
    /// This ensures clone independence: mutations to the clone's collection
    /// state do not affect the original.
    fn copy_collection_aux_vars(
        &mut self,
        locals: &CloneLocals,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // Ensure the destination has its own independent present/len vars.
        self.ensure_independent_collection_vars(locals);

        // Copy len.
        if let Some(src_len_var) =
            self.collections.len_state.get_len_var(locals.actual_source).cloned()
        {
            if let Some(dst_len_var) =
                self.collections.len_state.get_len_var(locals.dest_local).cloned()
            {
                let src_len = self.collection_current_len(&src_len_var);
                self.collection_len_set(
                    &dst_len_var,
                    src_len,
                    &mut CallAccumulator::new(constraints, extra_dests),
                );
            }
        }

        // Copy present.
        if let Some(src_present_var) =
            self.collections.len_state.get_present_var(locals.actual_source).cloned()
        {
            if let Some(dst_present_var) =
                self.collections.len_state.get_present_var(locals.dest_local).cloned()
            {
                let present_sort = self
                    .state_var_index_by_name(&src_present_var)
                    .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                    .map(|(_, s)| s.clone())
                    .unwrap_or_else(|| ay_bindings::Sort::array(int_sort(), bool_sort()));
                let src_present = Expr::var(&*src_present_var, present_sort);
                self.collection_present_set(
                    &dst_present_var,
                    src_present,
                    &mut CallAccumulator::new(constraints, extra_dests),
                );
            }
        }

        // Part of #3348 Direction 4: Copy embedded-map aux ownership from source
        // to destination on clone, preserving precise membership tracking.
        self.collections.copy_embedded_map_aux(locals.actual_source, locals.dest_local);
    }

    /// Ensure the clone destination has independent present/len state variables.
    ///
    /// Part of #3348: When cloning a struct with embedded maps, the destination
    /// needs its own present/len vars to maintain clone independence. Without
    /// this, source and clone share the same SMT variable name, making mutations
    /// to one visible to the other.
    fn ensure_independent_collection_vars(&mut self, locals: &CloneLocals) {
        let src_present = self.collections.len_state.get_present_var(locals.actual_source).cloned();
        let dst_present = self.collections.len_state.get_present_var(locals.dest_local).cloned();

        // Create fresh present var if dest has none or shares the source's name.
        if let Some(ref src_pv) = src_present {
            let needs_fresh = match &dst_present {
                None => true,
                Some(dst_pv) => dst_pv == src_pv,
            };
            if needs_fresh {
                let fresh_name: Arc<str> =
                    Arc::from(format!("hashmap_{}_present_{}", self.fn_name, locals.dest_local));
                // Only create if it differs from the source name.
                if *fresh_name != **src_pv {
                    self.collections
                        .len_state
                        .present_var_names
                        .insert(locals.dest_local, fresh_name.clone());
                    let sort = self
                        .state_var_index_by_name(src_pv)
                        .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                        .map(|(_, s)| s.clone())
                        .unwrap_or_else(|| ay_bindings::Sort::array(int_sort(), bool_sort()));
                    let out = crate::codegen_ay::names::out_name(&fresh_name);
                    self.push_late_collection_aux_var(fresh_name, &out, sort);
                }
            }
        }

        let src_len = self.collections.len_state.get_len_var(locals.actual_source).cloned();
        let dst_len = self.collections.len_state.get_len_var(locals.dest_local).cloned();

        // Create fresh len var if dest has none or shares the source's name.
        if let Some(ref src_lv) = src_len {
            let needs_fresh = match &dst_len {
                None => true,
                Some(dst_lv) => dst_lv == src_lv,
            };
            if needs_fresh {
                let fresh_name: Arc<str> =
                    Arc::from(format!("hashmap_{}_len_{}", self.fn_name, locals.dest_local));
                if *fresh_name != **src_lv {
                    self.collections
                        .len_state
                        .len_var_names
                        .insert(locals.dest_local, fresh_name.clone());
                    let out = crate::codegen_ay::names::out_name(&fresh_name);
                    self.push_late_collection_aux_var(fresh_name, &out, ptr_sort());
                }
            }
        }
    }
}

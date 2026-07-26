// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Conservative clone-based encoding for methods on structs with collection fields.
//!
//! When a method on a struct containing HashMap/BTreeMap fields cannot be inlined
//! by fn_inline (due to complex nested calls like Clone::clone + BTreeMap::insert),
//! this dispatcher treats the method as a conservative identity on all struct fields:
//! all state vars and collection auxiliaries are copied from receiver to destination.
//!
//! This is an over-approximation: mutations the method makes to collection fields
//! are lost, potentially causing false CTREX. But it is sound — it never produces
//! false PROOF. The solver has freedom to find proofs that only depend on the
//! unchanged fields (e.g., scalar field propagation through clone-mutate-return
//! patterns where assertions check keys not affected by the mutation).
//!
//! Part of #3348: scalar field propagation through method return chains.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
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

/// Extension trait for struct method passthrough dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructMethodPassthrough {
    fn try_dispatch_call_struct_method_passthrough(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool;
}

impl<'tcx, 'body> CallDispatchStructMethodPassthrough for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_method_passthrough(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = dcx.target else { return false };

        // Resolve callee — must be a concrete FnDef (not virtual, not closure).
        let func_ty = match dcx.func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return false,
        };

        // Skip Clone::clone — handled by the dedicated struct_clone dispatcher.
        let callee_name = fn_def.trimmed_name();
        if callee_name == "clone" || callee_name == "clone_from" {
            return false;
        }

        // First arg must be &self pointing to a struct with collection fields.
        let arg0 = match dcx.args.first() {
            Some(a) => a,
            None => return false,
        };
        let arg0_ty = match arg0.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let inner_ty = match arg0_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => return false,
        };
        // Skip bare collections (handled by collection stubs).
        if Self::type_is_hashmap(&inner_ty) {
            return false;
        }
        let (adt_def, adt_args) = match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return false,
        };
        let variants = adt_def.variants();
        if variants.is_empty() {
            return false;
        }
        let fields = variants[0].fields();
        let has_collection =
            fields.iter().any(|f| Self::type_is_hashmap(&f.ty_with_args(&adt_args)));
        if !has_collection {
            return false;
        }

        // Destination must have the same struct type (method returns Self).
        let dest_local: usize = dcx.destination.local;
        let dest_ty = self.body.locals()[dest_local].ty;
        match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                if def.trimmed_name() != adt_def.trimmed_name() {
                    return false;
                }
                dest_ty
            }
            _ => return false,
        };

        // Must have a body (ensures it's a real method, not an intrinsic).
        let instance = match Instance::resolve(fn_def, &fn_substs) {
            Ok(inst) => inst,
            Err(_) => return false,
        };
        if instance.body().is_none() {
            return false;
        }

        // Resolve source and destination state variable indices.
        let source_local = match arg0 {
            rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) => p.local,
            _ => return false,
        };
        let actual_source =
            self.ref_resolution.ref_targets.get(&source_local).map_or(source_local, |rt| rt.local);
        let source_idx = match self.try_state_idx_for_local(actual_source) {
            Some(idx) => idx,
            None => return false,
        };
        let Some(dest_idx) = self.try_state_idx_for_local(dest_local) else {
            return false;
        };

        // Get struct sort for field-level copy.
        let struct_sort = match Self::translate_ty(inner_ty) {
            Some(s) => s,
            None => return false,
        };

        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        // Copy all struct state vars from source to destination.
        self.passthrough_copy_state_vars(
            actual_source,
            source_idx,
            dest_local,
            dest_idx,
            &struct_sort,
            &mut extra_constraints,
        );

        // Copy collection aux vars (present, len) from source to destination.
        self.passthrough_copy_collection_aux(
            actual_source,
            dest_local,
            &mut extra_constraints,
            &mut extra_dests,
        );

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        debug!(
            actual_source,
            dest_local,
            callee = %callee_name,
            "CHC: struct method passthrough — conservative clone (#3348)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Copy struct state vars from source to destination using the struct sort.
    ///
    /// Handles both Datatype (single state var) and flattened (per-field leaf) encodings.
    fn passthrough_copy_state_vars(
        &mut self,
        _source_local: usize,
        source_idx: usize,
        _dest_local: usize,
        dest_idx: usize,
        struct_sort: &ay_bindings::Sort,
        constraints: &mut Vec<Expr>,
    ) {
        let (src_name, src_sort) = match self.state_var_mgr.state_vars.get(source_idx) {
            Some(pair) => pair.clone(),
            None => return,
        };

        // Datatype encoding: single state var for the whole struct.
        if src_sort.datatype_name().is_some() {
            if let Some((dest_out_name, _)) =
                self.state_var_mgr.output_state_vars.get(dest_idx).cloned()
            {
                let src_var = Expr::var(&*src_name, src_sort.clone());
                let dest_var = Expr::var(&*dest_out_name, src_sort);
                constraints.push(dest_var.eq(src_var));
                self.mark_state_var_modified(dest_idx);
            }
            return;
        }

        // Flattened encoding: copy each leaf state var field-by-field.
        let dt = match struct_sort.datatype_sort() {
            Some(d) => d,
            None => return,
        };
        let cons = match dt.constructors.first() {
            Some(c) => c,
            None => return,
        };

        let mut offset = 0;
        for field in &cons.fields {
            let leaf_sorts = codegen_decl_flatten::collect_leaf_sorts(&field.sort, 0);
            for leaf_offset in 0..leaf_sorts.len() {
                let src_leaf_idx = source_idx + offset + leaf_offset;
                let dst_leaf_idx = dest_idx + offset + leaf_offset;
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

    /// Copy collection aux vars (present, len) from source to destination.
    ///
    /// Part of #3348: Ensures destination has independent present/len vars
    /// before copying, preventing aliased state between original and clone.
    fn passthrough_copy_collection_aux(
        &mut self,
        source_local: usize,
        dest_local: usize,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // Ensure destination has independent present/len vars before copying.
        self.ensure_independent_passthrough_vars(source_local, dest_local);

        // Copy len.
        if let Some(src_len_var) = self.collections.len_state.get_len_var(source_local).cloned() {
            if let Some(dst_len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
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
            self.collections.len_state.get_present_var(source_local).cloned()
        {
            if let Some(dst_present_var) =
                self.collections.len_state.get_present_var(dest_local).cloned()
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

        // Part of #3348 Direction 4: Copy embedded-map aux ownership from source to
        // destination. This ensures that structs returned from passthrough methods
        // inherit the source struct's precise membership tracking state.
        self.collections.copy_embedded_map_aux(source_local, dest_local);
    }

    /// Ensure the passthrough destination has independent present/len state variables.
    ///
    /// Part of #3348: Same pattern as the clone dispatcher's independence fix.
    /// When source and dest share the same present/len var name (from alias
    /// propagation), the copy becomes tautological. Create fresh vars for the
    /// dest so mutations through the returned struct are independent.
    fn ensure_independent_passthrough_vars(&mut self, source_local: usize, dest_local: usize) {
        let src_present = self.collections.len_state.get_present_var(source_local).cloned();
        let dst_present = self.collections.len_state.get_present_var(dest_local).cloned();

        if let Some(ref src_pv) = src_present {
            let needs_fresh = match &dst_present {
                None => true,
                Some(dst_pv) => dst_pv == src_pv,
            };
            if needs_fresh {
                let fresh_name: Arc<str> =
                    Arc::from(format!("hashmap_{}_present_{}", self.fn_name, dest_local));
                if *fresh_name != **src_pv {
                    self.collections
                        .len_state
                        .present_var_names
                        .insert(dest_local, fresh_name.clone());
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

        let src_len = self.collections.len_state.get_len_var(source_local).cloned();
        let dst_len = self.collections.len_state.get_len_var(dest_local).cloned();

        if let Some(ref src_lv) = src_len {
            let needs_fresh = match &dst_len {
                None => true,
                Some(dst_lv) => dst_lv == src_lv,
            };
            if needs_fresh {
                let fresh_name: Arc<str> =
                    Arc::from(format!("hashmap_{}_len_{}", self.fn_name, dest_local));
                if *fresh_name != **src_lv {
                    self.collections.len_state.len_var_names.insert(dest_local, fresh_name.clone());
                    let out = crate::codegen_ay::names::out_name(&fresh_name);
                    self.push_late_collection_aux_var(fresh_name, &out, ptr_sort());
                }
            }
        }
    }
}

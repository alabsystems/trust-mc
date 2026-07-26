// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec accessor/mutator method dispatch for structs with Vec fields.
//!
//! When a method on a struct performs a simple Vec Index or IndexMut
//! operation (e.g., `fn get(&self, i: usize) -> bool { self.v[i] }` or
//! `fn set(&mut self, i: usize) { self.v[i] = true }`), fn_inline bails
//! because the body has projected writes and nested collection calls.
//!
//! This dispatcher intercepts such methods after fn_inline, scans the callee
//! MIR body for Vec access patterns, and emits the corresponding select/store
//! constraints on the caller's Vec state variable.
//!
//! Part of #3348: method-based Vec accessor/mutator encoding gap.

mod codegen_call_struct_vec_accessor_scan;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{ConstOperand, Operand, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::call_accumulator::CallAccumulator;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_decl_flatten;
use super::codegen_expr_constant::ExprConstant;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use trust_mc_codegen_types::names::vec_layout;

use codegen_call_struct_vec_accessor_scan::{
    resolve_callee_body, scan_vec_access_pattern, scan_vec_as_slice_pattern,
    scan_vec_is_empty_pattern, scan_vec_len_pattern, type_is_vec,
};

/// Extension trait for Vec accessor/mutator method dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructVecAccessor {
    fn try_dispatch_call_struct_vec_accessor(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

/// Detected Vec access pattern from MIR body scan.
pub(in crate::codegen_ay::chc) enum VecAccessKind {
    /// Read: method returns `self.vec_field[index]`.
    Read { index_local: usize },
    /// Write: method stores a value into `self.vec_field[index]`.
    Write { index_local: usize, stored_value: StoredValue },
    /// Len: method returns `self.vec_field.len()`.
    Len,
    /// IsEmpty: method returns `self.vec_field.is_empty()` (bool). Part of #3348.
    IsEmpty,
    /// AsSlice: method returns `&self.vec_field` / `&self.0` as `&[T]`.
    AsSlice,
}

/// Value being stored in a Vec write pattern.
pub(in crate::codegen_ay::chc) enum StoredValue {
    /// A compile-time constant from the callee body.
    ConstantOp(Box<ConstOperand>),
    /// A method parameter (callee local index — local 1 = self, local 2 = first param).
    Parameter(usize),
}

/// Result of MIR body scan for Vec access patterns.
pub(in crate::codegen_ay::chc) struct VecAccessPattern {
    pub(in crate::codegen_ay::chc) vec_field_idx: usize,
    pub(in crate::codegen_ay::chc) kind: VecAccessKind,
}

/// Validated receiver info for struct Vec accessor dispatch.
struct ReceiverInfo {
    struct_local: usize,
    inner_ty: rustc_public::ty::Ty, // inner type behind the reference
}

/// Resolved Vec data state variable info (name, sort, flat state index).
struct VecDataInfo {
    name: std::sync::Arc<str>,
    sort: ay_bindings::Sort,
    state_idx: usize,
}

impl<'tcx, 'body> CallDispatchStructVecAccessor for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_vec_accessor(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        // Resolve callee — must be a concrete FnDef.
        let func_ty = match dcx.func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return false,
        };

        // Skip Clone — handled by dedicated dispatcher.
        let callee_name = fn_def.trimmed_name();
        if callee_name == "clone" || callee_name == "clone_from" {
            return false;
        }

        let receiver = match self.validate_struct_vec_receiver(dcx, &callee_name) {
            Some(r) => r,
            None => return false,
        };

        let callee_body = match resolve_callee_body(fn_def, &fn_substs) {
            Some(b) => b,
            None => return false,
        };

        let access_pattern = scan_vec_access_pattern(&callee_body);
        let len_pattern = scan_vec_len_pattern(&callee_body);
        let is_empty_pattern = scan_vec_is_empty_pattern(&callee_body);
        let slice_pattern = scan_vec_as_slice_pattern(&callee_body);

        let Some(pattern) = access_pattern.or(len_pattern).or(is_empty_pattern).or(slice_pattern)
        else {
            return false;
        };

        self.emit_vec_access(dcx, target, &receiver, &pattern)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Validate that the call's first arg is `&self` or `&mut self` on a struct
    /// that contains at least one Vec field. Returns receiver info on success.
    fn validate_struct_vec_receiver(
        &self,
        dcx: &DispatchCallContext<'_>,
        callee_name: &str,
    ) -> Option<ReceiverInfo> {
        let arg0 = dcx.args.first()?;
        let arg0_ty = arg0.ty(self.body.locals()).ok()?;
        let inner_ty = match arg0_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => {
                debug!(callee = %callee_name, "struct_vec_accessor: arg0 not a ref");
                return None;
            }
        };
        if Self::type_is_hashmap(&inner_ty) {
            return None;
        }
        let (adt_def, adt_args) = match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => {
                debug!(callee = %callee_name, "struct_vec_accessor: inner not ADT");
                return None;
            }
        };
        let variants = adt_def.variants();
        if variants.is_empty() {
            return None;
        }
        let fields = variants[0].fields();
        if !fields.iter().any(|f| type_is_vec(&f.ty_with_args(&adt_args))) {
            debug!(callee = %callee_name, adt = %adt_def.trimmed_name(), "struct_vec_accessor: no Vec field");
            return None;
        }

        debug!(callee = %callee_name, adt = %adt_def.trimmed_name(), "struct_vec_accessor: struct has Vec field");

        let ref_local = match arg0 {
            Operand::Copy(p) | Operand::Move(p) => p.local,
            _ => return None,
        };
        let struct_local =
            self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);

        Some(ReceiverInfo { struct_local, inner_ty })
    }

    /// Emit constraints for a validated Vec access pattern.
    fn emit_vec_access(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        receiver: &ReceiverInfo,
        pattern: &VecAccessPattern,
    ) -> bool {
        // Resolve fields from the stored inner type.
        let (adt_def, adt_args) = match receiver.inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return false,
        };
        let variants = adt_def.variants();
        if variants.is_empty() {
            return false;
        }
        let fields = variants[0].fields();
        if pattern.vec_field_idx >= fields.len() {
            return false;
        }
        let field_ty = fields[pattern.vec_field_idx].ty_with_args(&adt_args);
        if !type_is_vec(&field_ty) {
            return false;
        }

        // Len/IsEmpty patterns use the len state var, not data array.
        if matches!(pattern.kind, VecAccessKind::Len) {
            return self.emit_vec_len_expr(dcx, target, receiver, pattern.vec_field_idx, false);
        }
        if matches!(pattern.kind, VecAccessKind::IsEmpty) {
            return self.emit_vec_len_expr(dcx, target, receiver, pattern.vec_field_idx, true);
        }
        if matches!(pattern.kind, VecAccessKind::AsSlice) {
            return self.emit_vec_as_slice(dcx, target, receiver, pattern.vec_field_idx);
        }

        let state_idx =
            match self.compute_vec_data_flat_offset(receiver.struct_local, pattern.vec_field_idx) {
                Some(idx) => idx,
                None => return false,
            };
        let (name, sort) = match self.state_var_mgr.state_vars.get(state_idx) {
            Some(pair) => pair.clone(),
            None => return false,
        };
        if sort.array_sort().is_none() {
            return false;
        }
        let vec_data = VecDataInfo { name, sort, state_idx };

        match &pattern.kind {
            VecAccessKind::Read { index_local } => {
                self.emit_vec_read(dcx, target, *index_local, &vec_data)
            }
            VecAccessKind::Write { index_local, stored_value } => {
                self.emit_vec_write(dcx, target, *index_local, stored_value, &vec_data)
            }
            VecAccessKind::Len | VecAccessKind::IsEmpty => unreachable!("handled above"),
            VecAccessKind::AsSlice => unreachable!("handled above"),
        }
    }

    /// Emit a Vec read: `dest = select(vec_data, index_arg)`.
    fn emit_vec_read(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        index_local: usize,
        vec_data: &VecDataInfo,
    ) -> bool {
        let index_expr = match self.resolve_callee_arg(dcx, index_local) {
            Some(e) => e,
            None => return false,
        };

        let data_expr = Expr::var(&*vec_data.name, vec_data.sort.clone());
        let result = data_expr.select(index_expr);

        let dest_local: usize = dcx.destination.local;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                "struct_vec_accessor_read",
            );
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );

            debug!(
                callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
                "CHC: struct Vec accessor read dispatched (#3348)"
            );
            true
        } else {
            false
        }
    }

    /// Emit a Vec write: `vec_data_out = store(vec_data, index_arg, value)`.
    fn emit_vec_write(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        index_local: usize,
        stored_value: &StoredValue,
        vec_data: &VecDataInfo,
    ) -> bool {
        let index_expr = match self.resolve_callee_arg(dcx, index_local) {
            Some(e) => e,
            None => return false,
        };

        let value_expr = match &stored_value {
            StoredValue::ConstantOp(const_op) => match self.translate_constant(const_op) {
                Some(e) => e,
                None => return false,
            },
            StoredValue::Parameter(param_local) => {
                match self.resolve_callee_arg(dcx, *param_local) {
                    Some(e) => e,
                    None => return false,
                }
            }
        };

        let data_expr = Expr::var(&*vec_data.name, vec_data.sort.clone());
        let value_expr =
            ChcCtx::coerce_store_value(data_expr.sort(), value_expr, false, &self.diagnostics);
        let stored = data_expr.store(index_expr, value_expr);

        let (data_out_name, _) = match self.state_var_mgr.output_state_vars.get(vec_data.state_idx)
        {
            Some(pair) => pair.clone(),
            None => return false,
        };
        let data_out = Expr::var(&*data_out_name, vec_data.sort.clone());
        let store_eq = data_out.eq(stored);
        self.mark_state_var_modified(vec_data.state_idx);

        let dest_local: usize = dcx.destination.local;
        let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            [store_eq],
        );

        debug!(
            callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
            "CHC: struct Vec accessor write dispatched (#3348)"
        );
        true
    }

    /// Emit Vec len/is_empty on struct-embedded Vec. Part of #3348.
    fn emit_vec_len_expr(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        receiver: &ReceiverInfo,
        vec_field_idx: usize,
        as_is_empty: bool,
    ) -> bool {
        let state_idx = match self.compute_vec_field_flat_offset(
            receiver.struct_local,
            vec_field_idx,
            vec_layout::IDX_LEN,
        ) {
            Some(idx) => idx,
            None => return false,
        };
        let (name, sort) = match self.state_var_mgr.state_vars.get(state_idx) {
            Some(pair) => pair.clone(),
            None => return false,
        };
        let len_expr = Expr::var(&*name, sort.clone());
        let result = if as_is_empty {
            let zero = Expr::bitvec_const(0u64, sort.bitvec_width().unwrap_or(64));
            len_expr.eq(zero)
        } else {
            len_expr
        };
        let site = if as_is_empty { "struct_vec_is_empty" } else { "struct_vec_len" };
        let dest_local: usize = dcx.destination.local;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                site,
            );
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
            debug!("CHC: struct Vec accessor {} dispatched (#3348)", site);
            true
        } else {
            false
        }
    }

    /// Emit a slice accessor by reusing the existing VecAsSlice bridge.
    fn emit_vec_as_slice(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        receiver: &ReceiverInfo,
        vec_field_idx: usize,
    ) -> bool {
        let (adt_def, adt_args) = match receiver.inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return false,
        };
        let variants = adt_def.variants();
        if variants.is_empty() || vec_field_idx >= variants[0].fields().len() {
            return false;
        }
        let field_ty = variants[0].fields()[vec_field_idx].ty_with_args(&adt_args);
        if !type_is_vec(&field_ty) {
            return false;
        }

        let field_projections = vec![ProjectionElem::Field(vec_field_idx, field_ty)];
        let dest_local = dcx.destination.local;
        let mut extra_constraints = Vec::new();
        let mut extra_dests = Vec::new();
        self.vec_op_as_slice(
            dcx.modified_locals,
            Some(receiver.struct_local),
            dest_local,
            &field_projections,
            &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
        );
        self.ref_resolution.slice_to_vec_field_projections.insert(dest_local, field_projections);

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        debug!(
            callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
            "CHC: struct Vec accessor as_slice dispatched (#3348)"
        );
        true
    }

    /// Map a callee local index to a translated caller operand expression.
    fn resolve_callee_arg(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_local: usize,
    ) -> Option<Expr> {
        let caller_arg_idx = callee_local.checked_sub(1)?;
        let arg = dcx.args.get(caller_arg_idx)?;
        self.translate_operand_with_modified(arg, dcx.modified_locals)
    }

    /// Compute the flat state var index for a Vec's data array within a struct.
    ///
    /// The Vec Datatype has 4 fields: fld_ptr, fld_len, fld_cap, fld_data.
    /// In the flattened struct encoding, the data array is at offset IDX_DATA (3)
    /// from the Vec field's base.
    pub(in crate::codegen_ay::chc) fn compute_vec_data_flat_offset(
        &self,
        struct_local: usize,
        vec_field_idx: usize,
    ) -> Option<usize> {
        self.compute_vec_field_flat_offset(struct_local, vec_field_idx, vec_layout::IDX_DATA)
    }

    /// Compute the flat state var index for any Vec sub-field within a struct.
    ///
    /// `vec_sub_field` is one of `vec_layout::IDX_PTR/IDX_LEN/IDX_CAP/IDX_DATA`.
    fn compute_vec_field_flat_offset(
        &self,
        struct_local: usize,
        vec_field_idx: usize,
        vec_sub_field: usize,
    ) -> Option<usize> {
        let local_ty = self.body.locals().get(struct_local).map(|l| l.ty)?;
        let struct_sort = Self::translate_ty(local_ty)?;
        let dt = struct_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if vec_field_idx >= cons.fields.len() {
            return None;
        }

        let struct_base = self.try_state_idx_for_local(struct_local)?;
        let mut flat_offset = 0;
        for f in &cons.fields[..vec_field_idx] {
            flat_offset += codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len();
        }
        Some(struct_base + flat_offset + vec_sub_field)
    }
}

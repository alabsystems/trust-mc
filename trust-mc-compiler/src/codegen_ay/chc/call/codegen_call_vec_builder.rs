// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec-building function call dispatcher for CHC codegen.
//!
//! Detects function calls whose body constructs a Vec via for-loop-push
//! patterns (e.g., `for i in 0..n { vec.push(f(i)) }`) and emits
//! length-constrained Vec results instead of falling through to
//! unconstrained over-approximation.
//!
//! Part of #3348: Vec iteration encoding for for-loop push patterns.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_vec_builder_pattern::{
    detect_from_u64_value_param_idx, extract_operand_local, has_back_edge, is_vec_method,
    local_is_known_zero, make_vec_builder_data_expr, resolve_callee_name, trace_local_to_param,
};
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::CtorFieldExt;
use crate::codegen_ay::types::ptr_sort;

/// Extension trait for Vec-building function call dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchVecBuilder {
    fn try_dispatch_call_vec_builder(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchVecBuilder for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_vec_builder(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        // Resolve callee and detect the for-range-push pattern.
        let (pattern, len_bv) = match self.resolve_vec_builder_candidate(dcx) {
            Some(result) => result,
            None => return false,
        };
        let builder_data_expr =
            pattern.from_u64_value_param_idx.filter(|&idx| idx < dcx.args.len()).and_then(|idx| {
                self.translate_operand_with_modified(&dcx.args[idx], dcx.modified_locals)
            });

        // Emit Vec result with constrained length.
        let dest_local: usize = dcx.destination.local;
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_vec_builder_dest");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                *target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
            return true;
        };
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        // Set sidecar ghost vars (len, cap) if available.
        if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var_name,
                len_bv.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(
                &cap_var_name,
                len_bv.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
            extra_constraints.push(len_bv.clone().bvuge(len_bv.clone()));
        }

        let handled = self.emit_vec_builder_result(
            dest_local,
            dest_vec_idx,
            &len_bv,
            builder_data_expr.as_ref(),
            &mut extra_constraints,
            &mut extra_dests,
        );
        if !handled {
            return false;
        }

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        self.diagnostics.vec_builder_pattern.inc();
        debug!(
            fn_name = %self.fn_name,
            dest_local,
            len_param_idx = pattern.len_param_idx,
            from_u64_data = pattern.from_u64_value_param_idx.is_some(),
            "vec_builder: for-range-push pattern detected -- len constrained (#3348)"
        );
        true
    }
}

/// Detected for-range-push pattern info.
struct ForRangePushPattern {
    len_param_idx: usize,
    from_u64_value_param_idx: Option<usize>,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve callee, check dest type, detect pattern, translate len argument.
    /// Returns the pattern and translated length expression, or None.
    fn resolve_vec_builder_candidate(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(ForRangePushPattern, Expr)> {
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_body = instance.body()?;

        // Check destination type: must be a struct (ADT) or Vec directly.
        let dest_local: usize = dcx.destination.local;
        let dest_ty = self.body.locals()[dest_local].ty;
        if !dest_has_vec_field(dest_ty) {
            return None;
        }

        let pattern = detect_for_range_push(&callee_body)?;
        if pattern.len_param_idx >= dcx.args.len() {
            return None;
        }

        let len_expr = self.translate_operand_with_modified(
            &dcx.args[pattern.len_param_idx],
            dcx.modified_locals,
        )?;
        if !len_expr.sort().is_bitvec() {
            return None;
        }
        Some((pattern, len_expr))
    }

    /// Emit Vec result constraints for the destination local.
    fn emit_vec_builder_result(
        &mut self,
        dest_local: usize,
        dest_vec_idx: usize,
        len_bv: &Expr,
        vec_data_expr: Option<&Expr>,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        use super::codegen_ctx::types::CollectionProjectionKind;

        // Case 1: Flattened/projected Vec destination.
        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr =
                super::declare_pending_var(format!("vec_builder_ptr_{dest_local}"), ptr_sort());
            let data_sort = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .map(|(_, s)| s.clone())
                .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));
            let data = make_vec_builder_data_expr(dest_local, &data_sort, vec_data_expr);
            Self::emit_cap_ge_len(len_bv.clone(), len_bv.clone(), constraints);
            let handled = self.constrain_projected_vec_fields_for_call(
                dest_local,
                super::codegen_call_vec_ops::ProjectedVecState {
                    ptr,
                    len: len_bv.clone(),
                    cap: len_bv.clone(),
                    data,
                },
                constraints,
                extra_dests,
            );
            return handled;
        }

        // Case 1b: Flattened struct-wrapped Vec destination.
        // Part of #3903: `compute_vec_data_flat_offset` returns an absolute
        // state-variable index, but `field_values` is indexed by the local's
        // relative field offset. Convert by subtracting `dest_vec_idx`
        // (the local's base state-variable index).
        let dest_ty = self.body.locals()[dest_local].ty;
        if self.flatten.flattened_tuple_locals.contains(&dest_local)
            && let Some(vec_field_idx) = find_vec_field_idx(dest_ty)
            && let Some(data_idx) = self.compute_vec_data_flat_offset(dest_local, vec_field_idx)
            && let Some(vec_base_abs) = data_idx.checked_sub(vec_layout::IDX_DATA)
        {
            // Convert absolute state-variable index to relative field offset.
            let vec_base = vec_base_abs.checked_sub(dest_vec_idx).unwrap_or(vec_base_abs);
            let field_count = self.flattened_field_count(dest_local);
            let data_sort = self
                .state_var_mgr
                .output_state_vars
                .get(vec_base_abs + vec_layout::IDX_DATA)
                .map(|(_, s)| s.clone())
                .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));
            let ptr =
                super::declare_pending_var(format!("vec_builder_ptr_{dest_local}"), ptr_sort());
            let data = make_vec_builder_data_expr(dest_local, &data_sort, vec_data_expr);
            let mut field_values = vec![None; field_count];
            for (slot, value) in [Some(ptr), Some(len_bv.clone()), Some(len_bv.clone()), Some(data)]
                .into_iter()
                .enumerate()
            {
                if vec_base + slot >= field_count {
                    return false;
                }
                field_values[vec_base + slot] = value;
            }
            Self::emit_cap_ge_len(len_bv.clone(), len_bv.clone(), constraints);
            let handled =
                self.constrain_flattened_fields_for_call(dest_local, &field_values, constraints);
            if handled {
                extra_dests.push(dest_local);
                return true;
            }
            return false;
        }

        // Case 2/3: Datatype Vec or struct-wrapping-Vec destination.
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
        else {
            return false;
        };
        let Some(dt) = out_sort.datatype_sort() else {
            return false;
        };

        // Case 2: Direct Vec Datatype.
        if dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_LEN)) {
            return self.emit_direct_vec_dt(
                dest_local,
                len_bv,
                vec_data_expr,
                &dt,
                &out_name,
                &out_sort,
                constraints,
                extra_dests,
            );
        }

        // Case 3: Struct wrapping a Vec (e.g., Bits(Vec<bool>)).
        self.emit_struct_wrapping_vec(
            dest_local,
            len_bv,
            vec_data_expr,
            &dt,
            &out_name,
            &out_sort,
            constraints,
            extra_dests,
        )
    }

    fn emit_direct_vec_dt(
        &self,
        dest_local: usize,
        len_bv: &Expr,
        vec_data_expr: Option<&Expr>,
        dt: &ay_bindings::DatatypeSort,
        out_name: &str,
        out_sort: &ay_bindings::Sort,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        let dt_name = out_sort.datatype_name().expect("has datatype_sort");
        let ptr = super::declare_pending_var(format!("vec_builder_ptr_{dest_local}"), ptr_sort());
        let data_sort = dt
            .constructors
            .first()
            .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
            .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));
        let data = make_vec_builder_data_expr(dest_local, &data_sort, vec_data_expr);
        Self::emit_cap_ge_len(len_bv.clone(), len_bv.clone(), constraints);
        constraints.push(Self::build_vec_datatype_eq(
            dt_name,
            vec![ptr, len_bv.clone(), len_bv.clone(), data],
            out_name,
            out_sort,
        ));
        extra_dests.push(dest_local);
        true
    }

    fn emit_struct_wrapping_vec(
        &self,
        dest_local: usize,
        len_bv: &Expr,
        vec_data_expr: Option<&Expr>,
        dt: &ay_bindings::DatatypeSort,
        out_name: &str,
        out_sort: &ay_bindings::Sort,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        let Some(ctor) = dt.constructors.first() else {
            return false;
        };
        for field in &ctor.fields {
            let inner_dt = match field.sort.datatype_sort() {
                Some(d) => d,
                None => continue,
            };
            if !inner_dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_LEN)) {
                continue;
            }
            let inner_dt_name = field.sort.datatype_name().expect("has datatype_sort");
            let vec_ptr =
                super::declare_pending_var(format!("vec_builder_ptr_{dest_local}"), ptr_sort());
            let vec_data_sort = inner_dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
                .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));
            let vec_data = make_vec_builder_data_expr(dest_local, &vec_data_sort, vec_data_expr);

            Self::emit_cap_ge_len(len_bv.clone(), len_bv.clone(), constraints);
            let vec_expr = Expr::datatype_constructor(
                inner_dt_name,
                names::cons_name(inner_dt_name),
                vec![vec_ptr, len_bv.clone(), len_bv.clone(), vec_data],
                field.sort.clone(),
            );

            let outer_dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let outer_ctor_name = names::resolve_ctor_name(out_sort, outer_dt_name);
            let vec_field_idx = ctor.fields.iter().position(|ff| ff.name == field.name);
            let outer_fields: Vec<Expr> = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(fi, f)| {
                    if Some(fi) == vec_field_idx {
                        vec_expr.clone()
                    } else {
                        super::declare_pending_var(
                            format!("vec_builder_fld{fi}_{dest_local}"),
                            f.sort.clone(),
                        )
                    }
                })
                .collect();

            let outer_expr = Expr::datatype_constructor(
                outer_dt_name,
                outer_ctor_name,
                outer_fields,
                out_sort.clone(),
            );
            constraints.push(Expr::var(out_name, out_sort.clone()).eq(outer_expr));
            extra_dests.push(dest_local);
            return true;
        }
        false
    }
}

/// Check if a type is or contains a Vec field.
fn dest_has_vec_field(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            def.trimmed_name() == "Vec"
                || def.variants().first().is_some_and(|v| {
                    v.fields().iter().any(|f| {
                        matches!(f.ty_with_args(&args).kind(),
                            TyKind::RigidTy(RigidTy::Adt(inner_def, _))
                            if inner_def.trimmed_name() == "Vec"
                        )
                    })
                })
        }
        _ => false,
    }
}

fn find_vec_field_idx(ty: rustc_public::ty::Ty) -> Option<usize> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            if def.trimmed_name() == "Vec" {
                return Some(0);
            }
            def.variants().first()?.fields().iter().position(|f| {
                matches!(
                    f.ty_with_args(&args).kind(),
                    TyKind::RigidTy(RigidTy::Adt(inner_def, _))
                        if inner_def.trimmed_name() == "Vec"
                )
            })
        }
        _ => None,
    }
}

/// Detect the for-range-push pattern in a callee's MIR body.
fn detect_for_range_push(body: &Body) -> Option<ForRangePushPattern> {
    let mut vec_local: Option<usize> = None;
    let mut cap_param_local: Option<usize> = None;
    let mut has_push_in_loop = false;
    let mut range_end_local: Option<usize> = None;
    // Part of #3610: track whether we saw a Range with nonzero start.
    // If so, the capacity fallback is unsound (capacity != actual len).
    let mut saw_nonzero_range = false;

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let TerminatorKind::Call { func, args, destination, target, .. } = &block.terminator.kind
        {
            if let Some(callee_name) = resolve_callee_name(func, body) {
                if callee_name.contains("with_capacity") && is_vec_method(&callee_name) {
                    vec_local = Some(destination.local);
                    if let Some(arg0) = args.first() {
                        cap_param_local = extract_operand_local(arg0);
                    }
                } else if callee_name.ends_with("::new") && is_vec_method(&callee_name) {
                    vec_local = Some(destination.local);
                }
                if callee_name.ends_with("::push") && is_vec_method(&callee_name) {
                    if let Some(target_bb) = target {
                        if has_back_edge(body, *target_bb, bb_idx) {
                            has_push_in_loop = true;
                        }
                    }
                }
            }
        }
        // Find Range construction: Range { start, end } as Aggregate Adt.
        // Part of #3610: only accept ranges where start is provably zero.
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Aggregate(rustc_public::mir::AggregateKind::Adt(def, _, _, _, _), fields),
            ) = &stmt.kind
            {
                if def.trimmed_name() == "Range" && fields.len() >= 2 {
                    let start_is_zero = {
                        use super::codegen_call_vec_builder_pattern::extract_operand_const_uint;
                        if extract_operand_const_uint(&fields[0]) == Some(0) {
                            true
                        } else if let Some(start_local) = extract_operand_local(&fields[0]) {
                            local_is_known_zero(body, start_local)
                        } else {
                            false
                        }
                    };
                    if start_is_zero {
                        range_end_local = extract_operand_local(&fields[1]);
                    } else {
                        saw_nonzero_range = true;
                    }
                }
            }
        }
    }

    if vec_local.is_none() || !has_push_in_loop {
        return None;
    }
    // Part of #3610: if we saw a Range with nonzero start and did not find
    // a valid zero-start range, reject the pattern entirely. The capacity
    // fallback would emit len = capacity, which overstates the actual Vec
    // length for k..n loops.
    if saw_nonzero_range && range_end_local.is_none() {
        return None;
    }
    let len_local = range_end_local.or(cap_param_local)?;
    let param_idx = trace_local_to_param(body, len_local)?;
    Some(ForRangePushPattern {
        len_param_idx: param_idx,
        from_u64_value_param_idx: detect_from_u64_value_param_idx(body),
    })
}

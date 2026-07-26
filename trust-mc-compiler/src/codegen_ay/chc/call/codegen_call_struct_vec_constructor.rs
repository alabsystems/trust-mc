// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constructor bridge for structs with embedded Vec fields.
//!
//! When `CnfClause::unit(lit)` creates a struct via `Self(vec![lit])`,
//! this dispatcher intercepts the call, constrains the flattened Vec state
//! (ptr, len, cap, data), and registers Vec sidecar ownership. Without this,
//! fn_inline bails on the nested `Box::new`/`exchange_malloc` call inside
//! `vec![]`, causing the constructor to fall through to `P_inf_*` (inferable
//! summary), which leaves the Vec sidecar unconstrained.
//!
//! Part of #3348: struct-Vec constructor bridge for CnfClause-style patterns.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;
use trust_mc_codegen_types::names::vec_layout;

use super::ChcCtx;
use super::call_accumulator::CallAccumulator;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::codegen_ctx::globals::declare_pending_var;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

/// Extension trait for struct-Vec constructor dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructVecConstructor {
    fn try_dispatch_call_struct_vec_constructor(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

/// Detected Vec construction pattern inside a constructor body.
enum VecFieldSource {
    /// Vec constructed from `vec![args]` (via `<[T]>::into_vec`).
    IntoVec { element_count: usize, element_arg_indices: Vec<Option<usize>> },
    /// Vec constructed from `Vec::new()` — empty Vec.
    VecNew,
}

/// Resolved constructor candidate.
struct VecConstructorCandidate {
    callee_name: String,
    dest_local: usize,
    vec_field_idx: usize,
    vec_source: VecFieldSource,
    /// For non-Vec fields: caller argument index (0-based).
    non_vec_field_sources: Vec<Option<usize>>,
}

impl<'tcx, 'body> CallDispatchStructVecConstructor for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_vec_constructor(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(candidate) = self.resolve_vec_constructor_candidate(dcx) else {
            return false;
        };

        let dest_local = candidate.dest_local;

        // CnfClause-style newtypes are flattened: 4 state vars (ptr, len, cap, data).
        if !self.flatten.flattened_tuple_locals.contains(&dest_local) {
            return false;
        }

        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        if !self.emit_vec_constructor_constraints(
            dcx,
            &candidate,
            &mut extra_constraints,
            &mut extra_dests,
        ) {
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

        debug!(
            dest_local,
            vec_field_idx = candidate.vec_field_idx,
            callee = %candidate.callee_name,
            "CHC: struct-Vec constructor bridge dispatched (#3348)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn resolve_vec_constructor_candidate(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<VecConstructorCandidate> {
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };

        let callee_name = fn_def.trimmed_name();
        if matches!(&*callee_name, "clone" | "clone_from" | "Clone::clone") {
            return None;
        }

        let dest_local: usize = dcx.destination.local;
        let dest_ty = self.body.locals()[dest_local].ty;
        let (adt_def, adt_args) = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return None,
        };
        if is_vec_type(&dest_ty) || Self::type_is_hashmap(&dest_ty) {
            return None;
        }

        let variants = adt_def.variants();
        if variants.is_empty() {
            return None;
        }
        let fields = variants[0].fields();
        let field_is_vec: Vec<bool> =
            fields.iter().map(|field| is_vec_type(&field.ty_with_args(&adt_args))).collect();
        let vec_count = field_is_vec.iter().filter(|v| **v).count();
        if vec_count != 1 {
            return None;
        }
        let vec_field_idx = field_is_vec.iter().position(|v| *v)?;

        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_body = instance.body()?;
        let (vec_source, non_vec_field_sources) =
            scan_vec_constructor_pattern(&callee_body, &field_is_vec)?;

        debug!(
            callee = %callee_name,
            dest_local,
            vec_field_idx,
            "struct_vec_constructor: pattern detected (#3348)"
        );

        Some(VecConstructorCandidate {
            callee_name,
            dest_local,
            vec_field_idx,
            vec_source,
            non_vec_field_sources,
        })
    }
    fn emit_vec_constructor_constraints(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        candidate: &VecConstructorCandidate,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        let dest_local = candidate.dest_local;
        let Some(base_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_vec_constructor_dest");
            return false;
        };
        // Vec leaves start at base_idx + vec_field_idx because each preceding
        // non-Vec scalar field occupies exactly 1 flattened leaf slot.
        let vec_leaf_base = base_idx + candidate.vec_field_idx;

        let (len_val, data_expr) = match &candidate.vec_source {
            VecFieldSource::IntoVec { element_count, element_arg_indices } => {
                let data = self.build_vec_data_array(dcx, element_arg_indices, vec_leaf_base);
                (*element_count, data)
            }
            VecFieldSource::VecNew => (0usize, None),
        };

        let len_expr = Expr::bitvec_const(len_val as u64, POINTER_WIDTH);
        let cap_expr = len_expr.clone();

        // Resolve the data array sort from the state var.
        let data_sort_idx = vec_leaf_base + vec_layout::IDX_DATA;
        let data_sort = self
            .state_var_mgr
            .output_state_vars
            .get(data_sort_idx)
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));

        let data = data_expr.unwrap_or_else(|| {
            let fresh_name = format!("vec_ctor_data_{}_{}", self.fn_name, dest_local);
            declare_pending_var(fresh_name, data_sort.clone())
        });

        // Fresh symbolic pointer.
        let ptr_sort_idx = vec_leaf_base + vec_layout::IDX_PTR;
        let ptr_s = self
            .state_var_mgr
            .output_state_vars
            .get(ptr_sort_idx)
            .map(|(_, s)| s.clone())
            .unwrap_or_else(ptr_sort);
        let ptr =
            declare_pending_var(format!("vec_ctor_ptr_{}_{}", self.fn_name, dest_local), ptr_s);

        let field_count =
            self.flatten.flattened_local_field_count.get(&dest_local).copied().unwrap_or(0);
        if field_count == 0 {
            return false;
        }

        // For a newtype CnfClause(Vec<i32>), field_count = 4 and all leaves
        // are Vec fields: [ptr, len, cap, data].
        let mut values: Vec<Option<Expr>> = Vec::with_capacity(field_count);

        // Build values for each struct field in order.
        let total_fields = candidate.non_vec_field_sources.len() + 1;
        let mut non_vec_source_idx = 0;
        for field_idx in 0..total_fields {
            if field_idx == candidate.vec_field_idx {
                // Vec field: 4 flattened leaves.
                values.push(Some(ptr.clone()));
                values.push(Some(len_expr.clone()));
                values.push(Some(cap_expr.clone()));
                values.push(Some(data.clone()));
            } else {
                // Non-Vec field: translate from caller arg.
                if let Some(Some(caller_arg_idx)) =
                    candidate.non_vec_field_sources.get(non_vec_source_idx)
                {
                    if let Some(arg) = dcx.args.get(*caller_arg_idx) {
                        values.push(self.translate_operand_with_modified(arg, dcx.modified_locals));
                    } else {
                        values.push(None);
                    }
                } else {
                    values.push(None);
                }
                non_vec_source_idx += 1;
            }
        }

        // Pad/truncate to match expected field_count.
        while values.len() < field_count {
            values.push(None);
        }
        values.truncate(field_count);

        let emitted =
            self.constrain_flattened_fields_for_call(dest_local, &values, extra_constraints);
        if emitted {
            extra_dests.push(dest_local);
            for offset in 0..field_count {
                self.mark_state_var_modified(base_idx + offset);
            }
        }

        // Set Vec sidecar len/cap if they exist.
        if let Some(len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
            let mut acc = CallAccumulator::new(extra_constraints, extra_dests);
            self.collection_len_set(&len_var, len_expr.clone(), &mut acc);
        }
        if let Some(cap_var) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            let mut acc = CallAccumulator::new(extra_constraints, extra_dests);
            self.collection_cap_set(&cap_var, cap_expr.clone(), &mut acc);
        }

        Self::emit_cap_ge_len(cap_expr, len_expr, extra_constraints);
        emitted
    }

    /// Build a data array from the constructor's element arguments.
    fn build_vec_data_array(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        element_arg_indices: &[Option<usize>],
        base_idx: usize,
    ) -> Option<Expr> {
        if element_arg_indices.is_empty() {
            return None;
        }

        let mut elem_exprs: Vec<Expr> = Vec::new();
        for arg_idx in element_arg_indices {
            let caller_arg_idx = (*arg_idx)?;
            let arg = dcx.args.get(caller_arg_idx)?;
            let expr = self.translate_operand_with_modified(arg, dcx.modified_locals)?;
            elem_exprs.push(expr);
        }

        if elem_exprs.is_empty() {
            return None;
        }

        // Determine element sort from the data state var's array sort.
        let data_sort_idx = base_idx + vec_layout::IDX_DATA;
        let elem_sort = self
            .state_var_mgr
            .output_state_vars
            .get(data_sort_idx)
            .and_then(|(_, s)| s.array_sort())
            .map(|a| a.element_sort.clone())
            .unwrap_or_else(|| elem_exprs[0].sort().clone());

        let base_name = format!("vec_ctor_base_{}", self.fn_name);
        let mut arr = declare_pending_var(base_name, Sort::array(ptr_sort(), elem_sort));
        for (i, elem) in elem_exprs.into_iter().enumerate() {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let elem = Self::coerce_store_value(arr.sort(), elem, false, &self.diagnostics);
            arr = arr.store(idx, elem);
        }
        Some(arr)
    }
}

/// Check if a type is `Vec<T>` (by ADT trimmed name).
fn is_vec_type(ty: &rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => def.trimmed_name() == "Vec",
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => is_vec_type(&inner),
        _ => false,
    }
}

/// Scan a callee body for a struct constructor pattern with Vec fields.
fn scan_vec_constructor_pattern(
    body: &Body,
    field_is_vec: &[bool],
) -> Option<(VecFieldSource, Vec<Option<usize>>)> {
    let num_fields = field_is_vec.len();
    let arg_count = body.arg_locals().len();

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest_place, rvalue) = &stmt.kind else { continue };
            if dest_place.local != 0 || !dest_place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(AggregateKind::Adt(_, _, _, _, _), operands) = rvalue else {
                continue;
            };
            if operands.len() != num_fields {
                continue;
            }

            let mut vec_source = None;
            let mut non_vec_field_sources: Vec<Option<usize>> = Vec::new();

            for (field_idx, op) in operands.iter().enumerate() {
                let src_local = match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
                    _ => return None,
                };

                if field_is_vec.get(field_idx).copied().unwrap_or(false) {
                    vec_source = detect_vec_construction(body, src_local, arg_count);
                } else if src_local >= 1 && src_local <= arg_count {
                    non_vec_field_sources.push(Some(src_local - 1));
                } else if let Some(param_local) = trace_to_parameter(body, src_local, arg_count) {
                    non_vec_field_sources.push(Some(param_local - 1));
                } else {
                    non_vec_field_sources.push(None);
                }
            }

            if let Some(vs) = vec_source {
                return Some((vs, non_vec_field_sources));
            }
        }
    }
    None
}

/// Detect how a Vec local is constructed in the body.
///
/// Returns `None` for unknown construction patterns — the caller should bail
/// so the call falls through to fn_inline or P_inf_* rather than producing
/// unsound len=0 constraints for non-empty Vecs.
fn detect_vec_construction(
    body: &Body,
    vec_local: usize,
    arg_count: usize,
) -> Option<VecFieldSource> {
    for block in &body.blocks {
        if let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind {
            if destination.local != vec_local {
                continue;
            }
            let Ok(func_ty) = func.ty(body.locals()) else { continue };
            let fn_def = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
                _ => continue,
            };
            let name = fn_def.trimmed_name();

            if name == "into_vec" || name.ends_with("::into_vec") {
                let element_count = find_array_literal_count(body);
                let element_arg_indices = find_array_element_args(body, arg_count);
                return Some(VecFieldSource::IntoVec { element_count, element_arg_indices });
            }

            if name == "new" || name.ends_with("::new") {
                return Some(VecFieldSource::VecNew);
            }
        }
    }

    // Unknown construction: bail rather than emitting unsound len=0 constraints.
    None
}

/// Find the count of elements in an array literal in the body.
fn find_array_literal_count(body: &Body) -> usize {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
            match rvalue {
                Rvalue::Aggregate(AggregateKind::Array(_), elements) => {
                    return elements.len();
                }
                Rvalue::Repeat(_, count) => {
                    if let Ok(val) = count.eval_target_usize() {
                        return val as usize;
                    }
                }
                _ => {}
            }
        }
    }
    0
}

/// Find which caller arguments map to the array elements.
fn find_array_element_args(body: &Body, arg_count: usize) -> Vec<Option<usize>> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
            if let Rvalue::Aggregate(AggregateKind::Array(_), elements) = rvalue {
                return elements
                    .iter()
                    .map(|op| {
                        let src_local = match op {
                            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                                p.local
                            }
                            _ => return None,
                        };
                        if src_local >= 1 && src_local <= arg_count {
                            Some(src_local - 1)
                        } else {
                            trace_to_parameter(body, src_local, arg_count).map(|l| l - 1)
                        }
                    })
                    .collect();
            }
        }
    }
    Vec::new()
}

/// Trace a local back through simple assignments to find a source parameter.
fn trace_to_parameter(body: &Body, mut local: usize, arg_count: usize) -> Option<usize> {
    for _ in 0..10 {
        if local >= 1 && local <= arg_count {
            return Some(local);
        }
        let mut found = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        local = src.local;
                        found = true;
                        break;
                    }
                    _ => {}
                }
            }
            if found {
                break;
            }
        }
        if !found {
            return None;
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Test-only helpers
// ---------------------------------------------------------------------------

/// Test-only: check if a callee body matches the struct-Vec constructor pattern.
///
/// Mirrors the `constructor_pattern_detected` hook in `codegen_call_struct_map_constructor.rs`.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn vec_constructor_pattern_detected(
    body: &Body,
    field_is_vec: &[bool],
) -> bool {
    if field_is_vec.iter().filter(|v| **v).count() != 1 {
        return false;
    }
    scan_vec_constructor_pattern(body, field_is_vec).is_some()
}

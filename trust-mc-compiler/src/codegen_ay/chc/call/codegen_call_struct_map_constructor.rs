// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constructor bridge for structs with embedded BTreeMap/HashMap fields.
//!
//! When `MyStruct::new(default)` creates a struct with an embedded map field,
//! this dispatcher intercepts the call, emits the struct construction, and
//! registers embedded-map aux ownership for the destination local. Without this,
//! the `present` array association is lost because the aggregate statement lives
//! in the callee body (not the caller body), so the legacy MIR aggregate scan
//! in `get_struct_embedded_hashmap_present_var()` cannot find it.
//!
//! Part of #3348 Direction 2: populate embedded-map aux bridge at constructor
//! boundaries.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::sync::Arc;
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::types::EmbeddedMapAuxState;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{bool_sort, int_sort, ptr_sort};

/// Extension trait for struct-map constructor dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructMapConstructor {
    fn try_dispatch_call_struct_map_constructor(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

/// Detected constructor pattern from a callee body scan.
struct ConstructorPattern {
    /// Field index of the BTreeMap/HashMap in the struct.
    map_field_idx: usize,
    /// Mapping from struct field index to caller argument index (0-based in callee args,
    /// where 0 is the first non-self parameter). `None` for the map field (initialized
    /// with `new()` instead of passed from caller).
    field_sources: Vec<Option<usize>>,
}

/// Resolved candidate for struct-map constructor dispatch.
struct ConstructorCandidate {
    callee_name: String,
    dest_local: usize,
    dest_ty: rustc_public::ty::Ty,
    pattern: ConstructorPattern,
}

impl<'tcx, 'body> CallDispatchStructMapConstructor for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_map_constructor(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(candidate) = self.resolve_constructor_candidate(dcx) else {
            return false;
        };

        let struct_sort = match Self::translate_ty(candidate.dest_ty) {
            Some(s) => s,
            None => return false,
        };
        let Some(dest_idx) = self.try_state_idx_for_local(candidate.dest_local) else {
            debug!(
                candidate.dest_local,
                "CHC: map_constructor dest not in state map — sound over-approx"
            );
            self.record_sound_fallback_reason("state_idx_missing_map_constructor_dest");
            return false;
        };
        let mut extra_constraints: Vec<Expr> = Vec::new();

        if !self.build_datatype_constructor_expr(
            dcx,
            &candidate,
            &struct_sort,
            dest_idx,
            &mut extra_constraints,
        ) {
            return false;
        }

        // Extract key sort from the map field's type for present array sort.
        let map_key_sort =
            Self::map_field_key_sort(candidate.dest_ty, candidate.pattern.map_field_idx);

        self.register_constructor_aux_state(
            candidate.dest_local,
            candidate.pattern.map_field_idx,
            map_key_sort.as_ref(),
            &mut extra_constraints,
        );

        let new_output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        debug!(
            dest_local = candidate.dest_local,
            map_field_idx = candidate.pattern.map_field_idx,
            callee = %candidate.callee_name,
            "CHC: struct-map constructor bridge dispatched (#3348)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Validate and resolve a struct-map constructor candidate from a call.
    fn resolve_constructor_candidate(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<ConstructorCandidate> {
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
        if Self::type_is_hashmap(&dest_ty) {
            return None;
        }
        let variants = adt_def.variants();
        if variants.is_empty() {
            return None;
        }
        let fields = variants[0].fields();
        let field_is_map: Vec<bool> = fields
            .iter()
            .map(|field| Self::type_is_hashmap(&field.ty_with_args(&adt_args)))
            .collect();
        if !field_is_map.iter().any(|is_map| *is_map) {
            return None;
        }
        // Part of #3348: the bridge only stores aux ownership for one embedded map field.
        // Reject multi-map structs rather than attaching aux state to an arbitrary field.
        if field_is_map.iter().filter(|is_map| **is_map).count() != 1 {
            return None;
        }

        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_body = instance.body()?;
        let pattern = scan_constructor_pattern(&callee_body, &field_is_map)?;

        debug!(
            callee = %callee_name,
            dest_local,
            map_field_idx = pattern.map_field_idx,
            "struct_map_constructor: constructor pattern detected (#3348)"
        );

        Some(ConstructorCandidate { callee_name, dest_local, dest_ty, pattern })
    }

    /// Build the Datatype constructor expression and emit constraints.
    fn build_datatype_constructor_expr(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        candidate: &ConstructorCandidate,
        struct_sort: &ay_bindings::Sort,
        dest_idx: usize,
        extra_constraints: &mut Vec<Expr>,
    ) -> bool {
        let Some(dt) = struct_sort.datatype_sort() else { return false };
        let Some(cons) = dt.constructors.first() else { return false };
        let mut field_exprs: Vec<Expr> = Vec::new();

        for (field_idx, source) in candidate.pattern.field_sources.iter().enumerate() {
            if field_idx == candidate.pattern.map_field_idx {
                let field_sort = &cons.fields[field_idx].sort;
                let default_name = format!("hashmap_default_{}", candidate.dest_local);
                if let Some(arr) = field_sort.array_sort() {
                    let default_val = Expr::var(&default_name, arr.element_sort.clone());
                    field_exprs.push(Expr::const_array(arr.index_sort.clone(), default_val));
                } else {
                    field_exprs.push(Expr::var(&default_name, field_sort.clone()));
                }
            } else if let Some(caller_arg_idx) = source {
                let Some(arg) = dcx.args.get(*caller_arg_idx) else { return false };
                let Some(expr) = self.translate_operand_with_modified(arg, dcx.modified_locals)
                else {
                    return false;
                };
                field_exprs.push(expr);
            } else {
                return false;
            }
        }

        if field_exprs.len() != cons.fields.len() {
            return false;
        }

        let struct_expr =
            Expr::datatype_constructor(&dt.name, &cons.name, field_exprs, struct_sort.clone());

        if let Some((dest_out_name, _)) =
            self.state_var_mgr.output_state_vars.get(dest_idx).cloned()
        {
            let dest_var = Expr::var(&*dest_out_name, struct_sort.clone());
            extra_constraints.push(dest_var.eq(struct_expr));
            self.mark_state_var_modified(dest_idx);
        }
        true
    }

    /// Register embedded-map aux ownership and initialize present/len.
    fn register_constructor_aux_state(
        &mut self,
        dest_local: usize,
        map_field_idx: usize,
        map_key_sort: Option<&ay_bindings::Sort>,
        extra_constraints: &mut Vec<Expr>,
    ) {
        let fn_name = &*self.fn_name;
        let present_var_name: Arc<str> =
            Arc::from(format!("hashmap_{}_present_{}", fn_name, dest_local));
        let len_var_name: Arc<str> = Arc::from(format!("hashmap_{}_len_{}", fn_name, dest_local));

        if self.collections.len_state.get_present_var(dest_local).is_none() {
            self.collections.len_state.present_var_names.insert(dest_local, present_var_name);
        }
        if self.collections.len_state.get_len_var(dest_local).is_none() {
            self.collections.len_state.len_var_names.insert(dest_local, len_var_name);
        }

        // Part of #3348: Late-declare present/len as CHC state variables if the
        // declaration phase did not pre-allocate them. The declaration phase only
        // creates present/len state vars for bare collection locals (direct
        // BTreeMap/HashMap). For struct-embedded maps constructed via methods
        // (e.g., MyStruct::new()), the constructor bridge runs during codegen —
        // after declaration. Without late-declaring, the present/len are free
        // variables in Z3 that don't propagate between basic blocks, causing
        // false CTREX on dual-struct queries.
        if let Some(present_name) = self.collections.len_state.get_present_var(dest_local).cloned()
        {
            let key_s = map_key_sort.cloned().unwrap_or_else(int_sort);
            let present_sort = ay_bindings::Sort::array(key_s, bool_sort());
            let out_name_str = crate::codegen_ay::names::out_name(&present_name);
            self.push_late_collection_aux_var(present_name, &out_name_str, present_sort);
        }
        if let Some(len_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            let out_name_str = crate::codegen_ay::names::out_name(&len_name);
            self.push_late_collection_aux_var(len_name, &out_name_str, ptr_sort());
        }

        if let Some(present_name) = self.collections.len_state.get_present_var(dest_local).cloned()
        {
            let present_sort = self
                .state_var_index_by_name(&present_name)
                .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                .map(|(_, s)| s.clone())
                .unwrap_or_else(|| ay_bindings::Sort::array(int_sort(), bool_sort()));
            let fresh_present = Expr::const_array(
                present_sort.array_sort().map_or_else(int_sort, |a| a.index_sort.clone()),
                Expr::bool_const(false),
            );
            let out_name = crate::codegen_ay::names::out_name(&present_name);
            let out_var = Expr::var(&out_name, present_sort);
            extra_constraints.push(out_var.eq(fresh_present));
            self.collections.len_state.mark_present_modified(&present_name);
            if let Some(idx) = self.state_var_index_by_name(&present_name) {
                self.mark_state_var_modified(idx);
            }
        }

        self.collections.register_embedded_map_aux(
            dest_local,
            map_field_idx,
            EmbeddedMapAuxState {
                len_var: self.collections.len_state.get_len_var(dest_local).cloned(),
                present_var: self.collections.len_state.get_present_var(dest_local).cloned(),
            },
        );
    }

    /// Extract key sort from struct's map field for present array sort.
    fn map_field_key_sort(
        struct_ty: rustc_public::ty::Ty,
        map_field_idx: usize,
    ) -> Option<ay_bindings::Sort> {
        let (adt_def, adt_args) = match struct_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
            _ => return None,
        };
        let field = adt_def.variants().first()?.fields().get(map_field_idx)?.clone();
        let field_ty = field.ty_with_args(&adt_args);
        Self::extract_hashmap_sorts(field_ty).map(|(key_sort, _)| key_sort)
    }
}

/// Scan a callee body for a struct constructor pattern:
/// `fn new(...) -> Self { Self { data: BTreeMap::new(), field1: arg1, ... } }`
///
/// Returns the pattern if exactly one map field is found that's initialized via
/// `new()`, and all other fields come from parameters.
fn scan_constructor_pattern(body: &Body, field_is_map: &[bool]) -> Option<ConstructorPattern> {
    let num_fields = field_is_map.len();
    let arg_count = body.arg_locals().len();

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest_place, rvalue) = &stmt.kind else { continue };
            if !dest_place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(AggregateKind::Adt(_, _, _, _, _), operands) = rvalue else {
                continue;
            };
            if operands.len() != num_fields {
                continue;
            }

            if let Some(pattern) = match_aggregate_operands(body, operands, arg_count, field_is_map)
            {
                return Some(pattern);
            }
        }
    }
    None
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn constructor_pattern_detected(
    body: &Body,
    field_is_map: &[bool],
) -> bool {
    if field_is_map.iter().filter(|is_map| **is_map).count() != 1 {
        return false;
    }
    scan_constructor_pattern(body, field_is_map).is_some()
}

/// Match aggregate operands to determine if they form a constructor pattern.
fn match_aggregate_operands(
    body: &Body,
    operands: &[Operand],
    arg_count: usize,
    field_is_map: &[bool],
) -> Option<ConstructorPattern> {
    let mut map_field_idx = None;
    let mut field_sources: Vec<Option<usize>> = Vec::with_capacity(field_is_map.len());

    for (field_idx, op) in operands.iter().enumerate() {
        let src_local = match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };

        if field_is_map.get(field_idx).copied().unwrap_or(false)
            && is_map_new_result(body, src_local)
        {
            if map_field_idx.is_some() {
                return None;
            }
            map_field_idx = Some(field_idx);
            field_sources.push(None);
        } else if src_local >= 1 && src_local <= arg_count {
            field_sources.push(Some(src_local - 1));
        } else if let Some(param_local) = trace_to_parameter(body, src_local, arg_count) {
            field_sources.push(Some(param_local - 1));
        } else {
            return None;
        }
    }

    let map_field_idx = map_field_idx?;
    if field_sources.len() != field_is_map.len() {
        return None;
    }
    Some(ConstructorPattern { map_field_idx, field_sources })
}

/// Check if a local is the result of a `BTreeMap::new()` or `HashMap::new()` call.
fn is_map_new_result(body: &Body, local: usize) -> bool {
    for block in &body.blocks {
        if let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind {
            if destination.local != local {
                continue;
            }
            let Ok(func_ty) = func.ty(body.locals()) else { continue };
            let fn_def = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
                _ => continue,
            };
            let name = fn_def.trimmed_name();
            if name == "new" || name.ends_with("::new") {
                return true;
            }
        }
    }
    false
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

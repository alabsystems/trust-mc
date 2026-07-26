// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iter-map-collect method dispatcher for CHC codegen.
//!
//! Detects methods on structs with Vec fields whose body follows the pattern:
//!   `self.field.iter().[zip(other.field.iter())].map(closure).collect()`
//! and emits result Vec with:
//!   - Length preservation: result.len = source.len
//!   - Element-wise forall: `idx < len → select(data, idx) = closure_body(...)`
//!
//! Handles `Bits::and`, `Bits::or`, `Bits::xor`, `Bits::not` and similar
//! iter-map-collect patterns on struct Vec fields.
//!
//! Part of #3348: iter-map-collect encoding for bv_bitblast operations.

mod emit;

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Operand, TerminatorKind};
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_decl_flatten;
use super::codegen_types::CodegenTypes;
use super::inline_body::translate_closure_inline_body;
use crate::codegen_ay::names::struct_sort;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::ptr_sort;

/// Extension trait for iter-map-collect method dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchIterCollectMethod {
    fn try_dispatch_call_iter_collect_method(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

/// Detected iter-map-collect pattern from a callee body scan.
pub(in crate::codegen_ay::chc) struct IterMapCollectPattern {
    /// Number of source iterators (1 for map-only, 2 for zip+map).
    pub(in crate::codegen_ay::chc) source_count: usize,
}

/// Resolved source Vec info from caller's CHC state.
pub(in crate::codegen_ay::chc) struct SourceVecInfo {
    pub(in crate::codegen_ay::chc) data_expr: Expr,
    pub(in crate::codegen_ay::chc) data_sort: Sort,
    pub(in crate::codegen_ay::chc) len_expr: Expr,
}

/// Translated closure result: an index variable and body expression.
pub(in crate::codegen_ay::chc) struct ClosureResult {
    pub(in crate::codegen_ay::chc) idx_var_name: String,
    pub(in crate::codegen_ay::chc) body_expr: Expr,
}

impl<'tcx, 'body> CallDispatchIterCollectMethod for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_iter_collect_method(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        let Some((callee_name, callee_body, pattern)) = self.validate_iter_collect_candidate(dcx)
        else {
            return false;
        };

        // Resolve source Vec data and len from caller's state variables.
        let sources: Vec<SourceVecInfo> = (0..pattern.source_count)
            .filter_map(|param_idx| self.resolve_source_vec(dcx, param_idx))
            .collect();
        if sources.len() != pattern.source_count {
            return false;
        }

        // Translate closure body with symbolic index and source element selects.
        let closure_result = match self.translate_callee_closure(&callee_body, &pattern, &sources) {
            Some(cr) => cr,
            None => return false,
        };

        // Emit result Vec with length + forall constraints.
        let dest_local: usize = dcx.destination.local;
        let handled =
            self.emit_iter_collect_result(dcx, *target, dest_local, &sources[0], &closure_result);
        if !handled {
            return false;
        }

        debug!(
            fn_name = %self.fn_name,
            callee = %callee_name,
            sources = pattern.source_count,
            "iter_collect_method: detected and constrained (#3348)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Validate that this call is a candidate for iter-collect-method dispatch.
    /// Returns the callee name, body, and detected pattern on success.
    fn validate_iter_collect_candidate(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(String, Body, IterMapCollectPattern)> {
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };

        // Skip known non-patterns.
        let callee_name = fn_def.trimmed_name();
        if matches!(callee_name.as_str(), "clone" | "clone_from" | "drop" | "fmt") {
            return None;
        }

        // Destination must contain a Vec field.
        let dest_ty = self.body.locals()[dcx.destination.local].ty;
        if !type_contains_vec(&dest_ty) {
            return None;
        }

        if dcx.args.is_empty() {
            return None;
        }

        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_body = instance.body()?;
        let pattern = detect_iter_map_collect(&callee_body)?;

        if pattern.source_count > dcx.args.len() {
            return None;
        }

        Some((callee_name, callee_body, pattern))
    }

    /// Resolve source Vec data and len from the caller's CHC state for a given
    /// call argument index. Handles `&StructWithVec` references.
    fn resolve_source_vec(
        &self,
        dcx: &DispatchCallContext<'_>,
        param_idx: usize,
    ) -> Option<SourceVecInfo> {
        let arg = dcx.args.get(param_idx)?;

        // Resolve reference to get the struct local.
        let ref_local = match arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let struct_local =
            self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);

        // Find the Vec field index in the struct.
        let local_ty = self.body.locals().get(struct_local).map(|l| l.ty)?;
        let vec_field_idx = find_vec_field_idx(&local_ty)?;

        // Compute flat state variable offsets for data and len.
        let struct_sort_ay = Self::translate_ty(local_ty)?;
        let dt = struct_sort_ay.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if vec_field_idx >= cons.fields.len() {
            return None;
        }
        let struct_base = self.try_state_idx_for_local(struct_local)?;
        let mut flat_offset = 0;
        for f in &cons.fields[..vec_field_idx] {
            flat_offset += codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len();
        }

        let data_idx = struct_base + flat_offset + vec_layout::IDX_DATA;
        let len_idx = struct_base + flat_offset + vec_layout::IDX_LEN;

        let (data_name, data_sort) = self.state_var_mgr.state_vars.get(data_idx)?.clone();
        let (len_name, len_sort) = self.state_var_mgr.state_vars.get(len_idx)?.clone();

        data_sort.array_sort()?;

        Some(SourceVecInfo {
            data_expr: Expr::var(&*data_name, data_sort.clone()),
            data_sort,
            len_expr: Expr::var(&*len_name, len_sort),
        })
    }

    /// Find the `map` closure in the callee body, resolve it, and translate
    /// its body using symbolic `select(source_data, idx)` element expressions.
    fn translate_callee_closure(
        &mut self,
        callee_body: &Body,
        pattern: &IterMapCollectPattern,
        sources: &[SourceVecInfo],
    ) -> Option<ClosureResult> {
        let (closure_def, closure_args) = find_map_closure(callee_body)?;

        // Resolve the closure Instance and get its MIR body.
        let mut resolved_body = None;
        for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
            if let Ok(instance) = Instance::resolve_closure(closure_def, &closure_args, kind) {
                if let Some(body) = instance.body() {
                    resolved_body = Some(body);
                    break;
                }
            }
        }
        let closure_body = resolved_body?;

        // Create a shared index variable for array select operations.
        let idx_var_name = super::chc_fresh_name("icm_idx");
        let idx = Expr::var(idx_var_name.clone(), ptr_sort());

        // Build element expressions: select(source_data[i], idx) for each source.
        let elem_sorts: Vec<Sort> = sources
            .iter()
            .filter_map(|s| s.data_sort.array_sort().map(|a| a.element_sort.clone()))
            .collect();
        if elem_sorts.len() != sources.len() {
            return None;
        }

        let element_selects: Vec<Expr> =
            sources.iter().map(|s| s.data_expr.clone().select(idx.clone())).collect();

        // Build the closure parameter expression.
        let param = if element_selects.len() == 1 {
            element_selects[0].clone()
        } else {
            // Build a tuple Datatype for multi-source (zip) pattern.
            let fields: Vec<(String, Sort)> = elem_sorts
                .iter()
                .enumerate()
                .map(|(i, s)| (format!("fld_{i}"), s.clone()))
                .collect();
            let tuple_name = format!(
                "IcmTuple_{}",
                elem_sorts.iter().map(sort_short_label).collect::<Vec<_>>().join("_")
            );
            let tuple_sort = struct_sort(tuple_name.clone(), fields);
            let ctor_name = format!("mk_{tuple_name}");
            Expr::datatype_constructor(&tuple_name, &ctor_name, element_selects, tuple_sort)
        };

        // Translate the closure body with the parameterized element(s).
        let captures: Vec<Expr> = Vec::new();
        let body_expr = translate_closure_inline_body(
            self,
            &closure_body,
            &[param],
            &captures,
            0, // bb_idx placeholder
            0, // inline_depth: top-level dispatch
        )?;

        debug!(
            idx_var = %idx_var_name,
            sources = pattern.source_count,
            body_sort = %body_expr.sort(),
            "iter_collect_method: translated closure body (#3348)"
        );

        Some(ClosureResult { idx_var_name, body_expr })
    }
}

// === Pattern detection ===

/// Scan a callee's MIR body for the iter-map-collect pattern.
/// Returns `Some(pattern)` if the body contains:
///   - At least one call to a function named "iter"
///   - A call to "map" (with a closure argument)
///   - A call to "collect"
///   - Optionally, a call to "zip" (indicating dual source)
fn detect_iter_map_collect(body: &Body) -> Option<IterMapCollectPattern> {
    let mut has_collect = false;
    let mut has_map = false;
    let mut has_zip = false;
    let mut iter_count = 0usize;

    for block in &body.blocks {
        if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
            if let Some(name) = callee_name_of(func, body) {
                if name == "collect" || name.ends_with("::collect") {
                    has_collect = true;
                } else if name == "map" || name.ends_with("::map") {
                    has_map = true;
                } else if name == "zip" || name.ends_with("::zip") {
                    has_zip = true;
                } else if name == "iter" || name.ends_with("::iter") {
                    iter_count += 1;
                }
            }
        }
    }

    if !has_collect || !has_map || iter_count == 0 {
        return None;
    }

    let source_count = if has_zip && iter_count >= 2 { 2 } else { 1 };

    Some(IterMapCollectPattern { source_count })
}

/// Find the map call's closure argument type in the callee body.
/// Returns the ClosureDef and GenericArgs from `RigidTy::Closure`.
fn find_map_closure(
    body: &Body,
) -> Option<(rustc_public::ty::ClosureDef, rustc_public::ty::GenericArgs)> {
    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
            let name = callee_name_of(func, body)?;
            if name == "map" || name.ends_with("::map") {
                // The closure is typically args[1] (after self/iter).
                let closure_arg = args.get(1)?;
                let closure_ty = closure_arg.ty(body.locals()).ok()?;
                match closure_ty.kind() {
                    TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                        return Some((def, args));
                    }
                    _ => continue,
                }
            }
        }
    }
    None
}

// === Helpers ===

/// Resolve the trimmed callee name from a call's func operand.
fn callee_name_of(func: &Operand, body: &Body) -> Option<String> {
    let func_ty = func.ty(body.locals()).ok()?;
    match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.trimmed_name()),
        _ => None,
    }
}

/// Check if a type is or contains a Vec field.
fn type_contains_vec(ty: &rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            def.trimmed_name() == "Vec"
                || def.variants().first().is_some_and(|v| {
                    v.fields().iter().any(|f| {
                        matches!(
                            f.ty_with_args(&args).kind(),
                            TyKind::RigidTy(RigidTy::Adt(inner_def, _))
                            if inner_def.trimmed_name() == "Vec"
                        )
                    })
                })
        }
        _ => false,
    }
}

/// Find the first Vec field index in a struct type.
fn find_vec_field_idx(ty: &rustc_public::ty::Ty) -> Option<usize> {
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

/// Short label for a AY Sort, used for unique Datatype name generation.
fn sort_short_label(sort: &Sort) -> &'static str {
    if sort.is_bool() {
        "Bool"
    } else if sort.is_bitvec() {
        "BV"
    } else if sort.is_int() {
        "Int"
    } else {
        "X"
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Call-result equality constraint coercion and output argument builders.
//!
//! Contains:
//! - `COERCE_EQ_DROPPED_CONSTRAINT_COUNT`: counter for dropped constraints (#2235)
//! - `coerce_eq_constraint`: sort-safe dest=result equality builder (free function)
//! - `CallCoerce` extension trait: `build_output_args`, `push_coerced_eq_constraint`
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

mod constructor_wrap;
mod raw_memory_reconstruct;

use ay_bindings::{Expr, Sort};
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use tracing::{debug, warn};

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{
    CtorFieldExt, POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe,
    coerce_datatype_structural, flatten_datatype_to_bitvec, flattenable_datatype_sort_width,
    unflatten_bitvec_to_datatype, unwrap_single_field_datatype_to_sort,
};

use self::constructor_wrap::wrap_value_into_matching_constructor;
use self::raw_memory_reconstruct::reconstruct_datatype_from_raw_memory_bits;
use super::ChcCtx;
use super::codegen_ctx::diagnostics::{CellCounter, GLOBAL_COUNTERS};
use super::codegen_ctx::globals::declare_pending_var;

// All counter storage consolidated into GLOBAL_COUNTERS (Part of #2906).
// Functions below delegate to GLOBAL_COUNTERS fields/methods.

/// Drain the global dropped-constraint counter, returning its value and resetting to zero.
pub(in crate::codegen_ay) fn take_chc_coerce_eq_dropped_constraint_count() -> usize {
    GLOBAL_COUNTERS.coerce_eq_dropped_constraint.swap(0, Ordering::Relaxed)
}

/// Returns and clears per-function dropped call-result equality constraint counts.
pub(in crate::codegen_ay) fn take_chc_coerce_eq_dropped_constraint_counts_by_fn()
-> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.take_coerce_eq_dropped_by_fn()
}

/// Returns a snapshot of per-function dropped call-result equality constraint counts.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay) fn get_chc_coerce_eq_dropped_constraint_counts_by_fn()
-> BTreeMap<String, usize> {
    GLOBAL_COUNTERS.get_coerce_eq_dropped_by_fn()
}

#[cfg(test)]
pub(in crate::codegen_ay) fn clear_chc_coerce_eq_dropped_constraint_counts_by_fn() {
    GLOBAL_COUNTERS.clear_coerce_eq_dropped_by_fn();
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_chc_coerce_eq_dropped_constraint_count_for_test(
    fn_name: &str,
    dropped_count: usize,
) {
    GLOBAL_COUNTERS.set_coerce_eq_dropped_for_test(fn_name, dropped_count);
}

/// Build a `dest_var = result_expr` constraint with sort coercion (Part of #2194).
///
/// AY's `.eq()` requires both sides to have the same sort. When stub results
/// have a different sort than the destination state variable (e.g., BV64 inner
/// value from Option::unwrap vs BV32 dest for i32), this helper coerces the
/// result to match the destination sort before building the equality.
///
/// Returns `Some(constraint)` on success, `None` if sorts are incompatible.
///
/// Part of #2976: `signed` controls whether BV widening uses sign-extend
/// (true) or zero-extend (false). Callers should derive signedness from
/// the destination MIR type via `ty_signedness_shallow`.
pub(in crate::codegen_ay::chc) fn coerce_eq_constraint(
    dest_var: &Expr,
    result_expr: Expr,
    out_sort: &Sort,
    signed: bool,
) -> Option<Expr> {
    let result_sort = result_expr.sort().clone();
    if result_sort == *out_sort {
        // Same sort — direct equality
        Some(dest_var.clone().eq(result_expr))
    } else if result_sort.is_bitvec() && out_sort.is_bitvec() {
        // BV↔BV width mismatch — coerce result to destination width
        let target_width = out_sort.bitvec_width()?;
        let coerced = coerce_bitvec_width_safe(result_expr, target_width, signed.into());
        Some(dest_var.clone().eq(coerced))
    } else if result_sort.is_bool() && out_sort.is_bitvec() {
        // Bool→BV (predicate stubs returning Bool, dest is BV8/BV32 for Rust bool)
        let bits = out_sort.bitvec_width()?;
        let coerced =
            Expr::ite(result_expr, Expr::bitvec_const(1u64, bits), Expr::bitvec_const(0u64, bits));
        Some(dest_var.clone().eq(coerced))
    } else if result_sort.is_bitvec() && out_sort.is_bool() {
        // BV→Bool (e.g., BV1 result assigned to Bool-sorted state var)
        let coerced = result_expr.ne(Expr::bitvec_const(0u64, result_sort.bitvec_width()?));
        Some(dest_var.clone().eq(coerced))
    } else if let Some(unwrapped) = unwrap_single_field_datatype_to_sort(&result_expr, out_sort) {
        // Datatype(single-field)→X: unwrap tuple-like wrappers before equality.
        Some(dest_var.clone().eq(unwrapped))
    } else if result_sort.is_datatype() && out_sort.is_bitvec() {
        // Dyn_Trait DT → BV: flattened single-field wrapper locals still store the
        // data pointer in their only slot, with vtable metadata tracked separately.
        let dt = result_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        let target_width = out_sort.bitvec_width()?;
        if cons.fields.iter().any(|field| field.name == "fld_ptr") {
            // Part of #4050: full flatten when DT width matches target (e.g., Dyn_Trait→BV128).
            if let Some(dt_width) = flattenable_datatype_sort_width(&result_sort)
                && dt_width == target_width
                && dt_width > POINTER_WIDTH
                && let Some(flattened) = flatten_datatype_to_bitvec(&result_expr, dt_width)
            {
                Some(dest_var.clone().eq(flattened))
            } else {
                let ptr_expr =
                    result_expr.field_select(&dt.name, "fld_ptr", Sort::bitvec(POINTER_WIDTH));
                let coerced =
                    coerce_bitvec_width_safe(ptr_expr, target_width, SignExtension::ZeroExtend);
                Some(dest_var.clone().eq(coerced))
            }
        } else if let Some(dt_width) = flattenable_datatype_sort_width(&result_sort)
            && let Some(flattened) = flatten_datatype_to_bitvec(&result_expr, dt_width)
        {
            // Part of #4099: DT → BV via flatten + width coerce. Handles both
            // single-field (e.g., DummySubscriber{bv32} → bv64) and multi-field cases.
            let coerced =
                coerce_bitvec_width_safe(flattened, target_width, SignExtension::ZeroExtend);
            Some(dest_var.clone().eq(coerced))
        } else {
            None
        }
    } else if result_sort.is_datatype()
        && out_sort.is_bitvec()
        && let Some(dt_width) = flattenable_datatype_sort_width(&result_sort)
        && Some(dt_width) == out_sort.bitvec_width()
        && let Some(flattened) = flatten_datatype_to_bitvec(&result_expr, dt_width)
    {
        // Part of #3814: flattened scalar slots may receive a fixed-layout
        // Datatype value (for example `Rational`) from an inline helper call.
        // Pack the Datatype fields into the destination BV width instead of
        // dropping the flattened-field constraint.
        Some(dest_var.clone().eq(flattened))
    } else if result_sort.is_bitvec()
        && out_sort.is_datatype()
        && let Some(dt_width) = flattenable_datatype_sort_width(out_sort)
        && Some(dt_width) == result_sort.bitvec_width()
        && let Some(reconstructed) = unflatten_bitvec_to_datatype(&result_expr, out_sort)
    {
        // Part of #3984: BV→DT reconstruction for flattened array elements.
        // When an array stores flattened BV elements (via flatten_dt_array_element)
        // but the destination local has Datatype sort, reconstruct the Datatype
        // from the BV. Reverse of the DT→BV flatten path above.
        Some(dest_var.clone().eq(reconstructed))
    } else if result_sort.is_bitvec()
        && out_sort.is_datatype()
        && let Some(reconstructed) =
            reconstruct_datatype_from_raw_memory_bits(&result_expr, out_sort)
    {
        // Part of #4191: ptr::read can load Rust-layout raw memory for aggregates
        // whose AY datatype encoding carries explicit enum/marker bits that are
        // absent from memory, e.g. Foo { Option<NonNull-backed Root>, usize }.
        // Rebuild the destination datatype using tag-free option payloads and
        // zero-width marker fields instead of dropping the call-result equality.
        debug!(
            result_sort = ?result_sort,
            dest_sort = ?out_sort,
            "coerce_eq_constraint: raw memory BV→DT reconstruction"
        );
        Some(dest_var.clone().eq(reconstructed))
    } else if result_sort.is_datatype()
        && out_sort.is_datatype()
        && let Some(src_dt) = result_sort.datatype_sort()
        && let Some(tgt_dt) = out_sort.datatype_sort()
        && let Some(coerced) = coerce_datatype_structural(
            result_expr.clone(),
            src_dt,
            tgt_dt,
            out_sort.clone(),
            signed.into(),
        )
    {
        // Part of #3198: DT→DT structural coercion for multi-field single-constructor
        // datatypes (e.g., Box<T>→Box<dyn Trait>) via shared utility.
        Some(dest_var.clone().eq(coerced))
    } else if result_sort.is_bitvec() && out_sort.is_int() {
        // BV→Int: lift bitvector to integer using signedness from MIR type.
        // Signed types use bv2int_signed so negative values (e.g., -2i32) are
        // preserved. Unsigned types use bv2int so large values with MSB set
        // remain positive. Part of #2875, #3055.
        let int_val = if signed { result_expr.bv2int_signed() } else { result_expr.bv2int() };
        Some(dest_var.clone().eq(int_val))
    } else if result_sort.is_int() && out_sort.is_bitvec() {
        // Int→BV: truncate integer to bitvector when an Int-domain value
        // is assigned to a BV-sorted destination. Part of #2875.
        let target_width = out_sort.bitvec_width()?;
        Some(dest_var.clone().eq(result_expr.int2bv(target_width)))
    } else if out_sort.is_array() && result_sort.is_datatype() {
        // Part of #1632: Datatype(Slice/Vec)→Array via fld_data extraction.
        // CHC translate_ty maps [T] to Array(BV, T) but VecAsSlice and other
        // paths may produce Datatype(Slice_bvN) with (fld_ptr, fld_len, fld_data).
        // Extract fld_data if it matches the destination Array sort.
        let dt = result_sort.datatype_sort()?;
        let dt_name = &dt.name;
        let data_field = dt.constructors.first()?.field("fld_data")?;
        if data_field.sort == *out_sort {
            let extracted =
                result_expr.field_select(dt_name.as_str(), "fld_data", data_field.sort.clone());
            Some(dest_var.clone().eq(extracted))
        } else {
            None
        }
    } else if let Some(coerced) = ChcCtx::reinterpret_fixed_layout_expr(&result_expr, out_sort) {
        // BV↔Array / Datatype(Array) reinterpretation: handles transmute-like
        // sort mismatches where the source and target have compatible fixed layouts
        // (e.g., repr(simd) BV128 → [i64; 2] Array, or Datatype unwrap → BV).
        // Part of #3675: fixes check_ge SIMD PartialOrd via transmute.
        Some(dest_var.clone().eq(coerced))
    } else if out_sort.is_array()
        && let Some(arr) = out_sort.array_sort()
        && arr.element_sort == result_sort
    {
        // Part of #3783: Element→Array wrapping for compound Vec element types.
        // When the destination is Array<K, V> and the value is V (the element sort),
        // the value is a single element being assigned to an array-sorted slot.
        // This arises for Vec<[T; N]> where the data field is Array<BV64, Array<BV64, T>>
        // but the value is a single [T; N] element with sort Array<BV64, T>.
        //
        // Sound over-approximation: wrap the value in a fresh array with store(0, value).
        // Index 0 is constrained to the value; all other indices are nondeterministic.
        // This is strictly more precise than dropping the constraint entirely (which
        // leaves the entire array nondeterministic via sound_fallback).
        let fresh =
            declare_pending_var(format!("coerce_elem_to_arr_{}", dest_var), out_sort.clone());
        let idx = Expr::bitvec_const(0u64, arr.index_sort.bitvec_width().unwrap_or(POINTER_WIDTH));
        let wrapped = fresh.store(idx, result_expr);
        debug!(
            val_sort = ?result_sort,
            out_sort = ?out_sort,
            "coerce_eq_constraint: element→array wrapping (#3783)"
        );
        Some(dest_var.clone().eq(wrapped))
    } else if result_sort.is_array()
        && out_sort.is_array()
        && let Some(src_arr) = result_sort.array_sort()
        && let Some(tgt_arr) = out_sort.array_sort()
        && src_arr.index_sort == tgt_arr.index_sort
        && src_arr.element_sort.is_datatype()
        && tgt_arr.element_sort.is_bitvec()
        && let Some(dt_width) = flattenable_datatype_sort_width(&src_arr.element_sort)
        && Some(dt_width) == tgt_arr.element_sort.bitvec_width()
    {
        // Part of #3814: Array(K, Datatype) → Array(K, BV) element packing.
        // When translate_ty applies flatten_dt_array_element to produce Array(K, BV)
        // for state vars, but the expression pipeline produces Array(K, DT) values,
        // coerce by packing each element's DT fields into a BV via concat.
        //
        // Build a store chain for indices 0..BOUND that packs each DT element.
        // This is exact for fixed-size arrays ≤ BOUND and a sound over-approximation
        // for larger arrays (indices beyond BOUND retain their base value).
        const COERCE_ARRAY_ELEM_BOUND: u64 = 8;
        let idx_width = src_arr.index_sort.bitvec_width().unwrap_or(POINTER_WIDTH);
        let zero_elem = Expr::bitvec_const(0u64, dt_width);
        let mut arr = Expr::const_array(Sort::bitvec(idx_width), zero_elem);
        for i in 0..COERCE_ARRAY_ELEM_BOUND {
            let idx = Expr::bitvec_const(i, idx_width);
            let dt_elem = result_expr.clone().select(idx.clone());
            if let Some(packed) = flatten_datatype_to_bitvec(&dt_elem, dt_width) {
                arr = arr.store(idx, packed);
            } else {
                break;
            }
        }
        debug!(
            src_elem = ?src_arr.element_sort,
            tgt_elem = ?tgt_arr.element_sort,
            dt_width,
            "coerce_eq_constraint: Array(K,DT)→Array(K,BV) element packing (#3814)"
        );
        Some(dest_var.clone().eq(arr))
    } else if out_sort.is_datatype()
        && let Some(tgt_dt) = out_sort.datatype_sort()
        && let Some(wrapped) = wrap_value_into_matching_constructor(&result_expr, &tgt_dt, out_sort)
    {
        // Part of #3979: X→DT constructor wrapping for Result/Option-like types.
        // When an inlined function returns the payload type directly (e.g., [u8; 8])
        // but the destination local has a multi-constructor Datatype sort
        // (e.g., Result<[u8; 8], TryFromSliceError>), wrap the value into the
        // matching constructor (Ok/Some). This is the dual of
        // unwrap_single_field_datatype_to_sort.
        debug!(
            result_sort = ?result_sort,
            dest_sort = ?out_sort,
            "coerce_eq_constraint: value→DT constructor wrapping (#3979)"
        );
        Some(dest_var.clone().eq(wrapped))
    } else {
        // Incompatible sorts (e.g., Datatype vs BV) — cannot coerce
        debug!("coerce_eq_constraint sort mismatch: result={:?} dest={:?}", result_sort, out_sort);
        None
    }
}

/// Extension trait for call-result coercion methods on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallCoerce {
    /// Build output args vector with specified locals using output variables.
    ///
    /// This is the shared helper that replaces the repeated `new_output_args`
    /// closure pattern across all call family handlers. Locals in `modified_locals`
    /// or matching any entry in `extra_dests` use their output-state variable;
    /// others pass through the input-state variable.
    ///
    /// `extra_dests` accepts additional MIR local indices that should use output
    /// variables without cloning the entire `modified_locals` set. Callers that
    /// update raw state-vector slots directly must use `mark_state_var_modified`
    /// instead of passing vec indices here.
    fn build_output_args(
        &self,
        modified_locals: &HashSet<usize>,
        extra_dests: &[usize],
    ) -> Vec<Expr>;

    /// Push `dest_var = result_expr` with coercion, logging dropped constraints.
    ///
    /// Returns true when a constraint was pushed. On coercion failure, emits a
    /// warning with call-site context and increments
    /// `COERCE_EQ_DROPPED_CONSTRAINT_COUNT`.
    fn push_coerced_eq_constraint(
        &mut self,
        constraints: &mut Vec<Expr>,
        dest_var: &Expr,
        result_expr: Expr,
        out_sort: &Sort,
        dest_local: usize,
        site: &'static str,
    ) -> bool;

    /// Like `push_coerced_eq_constraint`, but returns the constraint instead
    /// of pushing it. Used with `emit_goto_rule_extra` to avoid caller-side
    /// `.to_vec()` allocation. Part of #2486.
    fn make_coerced_eq_constraint(
        &mut self,
        dest_var: &Expr,
        result_expr: Expr,
        out_sort: &Sort,
        dest_local: usize,
        site: &'static str,
    ) -> Option<Expr>;
}

impl<'tcx, 'body> CallCoerce for ChcCtx<'tcx, 'body> {
    fn build_output_args(
        &self,
        modified_locals: &HashSet<usize>,
        extra_dests: &[usize],
    ) -> Vec<Expr> {
        // Part of #2244: Expand MIR local indices to vec_idx space.
        // `modified_locals` contains MIR local indices but flattened locals
        // occupy N consecutive state_var slots. Same expansion as
        // `build_block_output_args`.
        let mut modified_vec_indices: HashSet<usize> = HashSet::new();
        for &local_idx in modified_locals {
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                continue;
            };
            modified_vec_indices.insert(vec_idx);

            if self.flatten.flattened_tuple_locals.contains(&local_idx) {
                let n = self.flattened_field_count(local_idx);
                for i in 0..n {
                    modified_vec_indices.insert(vec_idx + i);
                }
            }
        }
        // Also expand extra_dests from MIR locals to vec_idx space (Part of #2267).
        // Replaces the old `Option<usize>` single extra_dest with a slice, allowing
        // callers to pass multiple local indices without cloning the entire HashSet.
        for &extra in extra_dests {
            let Some(vec_idx) = self.try_state_idx_for_local(extra) else {
                continue;
            };
            modified_vec_indices.insert(vec_idx);

            if self.flatten.flattened_tuple_locals.contains(&extra) {
                let n = self.flattened_field_count(extra);
                for i in 0..n {
                    modified_vec_indices.insert(vec_idx + i);
                }
            }
        }
        self.state_var_mgr
            .state_vars
            .iter()
            .enumerate()
            .map(|(idx, (in_name, in_sort))| {
                if modified_vec_indices.contains(&idx) {
                    let (out_name, out_sort) = &self.state_var_mgr.output_state_vars[idx];
                    return Expr::var(&**out_name, out_sort.clone());
                }

                // Part of #2552: Check centralized modified state index set.
                // This catches region arrays, type-indexed arrays, metadata arrays,
                // and any other state variable recorded via mark_state_var_modified.
                if self.encode.modified_state_indices.contains(&idx) {
                    let (out_name, out_sort) = &self.state_var_mgr.output_state_vars[idx];
                    return Expr::var(&**out_name, out_sort.clone());
                }

                Expr::var(&**in_name, in_sort.clone())
            })
            .collect()
    }

    fn push_coerced_eq_constraint(
        &mut self,
        constraints: &mut Vec<Expr>,
        dest_var: &Expr,
        result_expr: Expr,
        out_sort: &Sort,
        dest_local: usize,
        site: &'static str,
    ) -> bool {
        if let Some(eq) =
            self.make_coerced_eq_constraint(dest_var, result_expr, out_sort, dest_local, site)
        {
            constraints.push(eq);
            true
        } else {
            false
        }
    }

    fn make_coerced_eq_constraint(
        &mut self,
        dest_var: &Expr,
        result_expr: Expr,
        out_sort: &Sort,
        dest_local: usize,
        site: &'static str,
    ) -> Option<Expr> {
        let result_sort = result_expr.sort().clone();
        // fc-interior-mut: refuse to widen a sub-pointer-width bitvec into a
        // raw-pointer-typed destination. A narrow result reaching a `*T` dest
        // is a dematerialized referent VALUE (e.g. the flattened u32 payload
        // of a Cell routed through contract instrumentation), not an address;
        // zero/sign-extending it fabricates obj_id=0 provenance whose deref,
        // alignment, and frame checks are then decided by the cell's
        // arbitrary payload (spurious Genuine CTREX) — or worse, silently
        // checked against the wrong object (a fail-open surface). Route to
        // the existing dropped-constraint lane: the destination stays havoced
        // (sound over-approximation) and the drop is surfaced through the
        // coerce-eq-dropped diagnostics. Scoped to RawPtr dests: `&T` dests
        // keep the legacy value-forwarding paths (promoted refs).
        let refused_ptr_widening = out_sort.bitvec_width() == Some(POINTER_WIDTH)
            && result_sort.bitvec_width().is_some_and(|w| w < POINTER_WIDTH)
            && self.body.locals().get(dest_local).is_some_and(|decl| {
                matches!(
                    decl.ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(..))
                )
            });
        // Part of #2976: determine signedness from destination local's MIR type
        // so BV-to-BV widening uses sign-extend for signed integers.
        let signed = self
            .body
            .locals()
            .get(dest_local)
            .map(|decl| decl.ty)
            .and_then(ty_signedness_shallow)
            .unwrap_or(false);
        if !refused_ptr_widening
            && let Some(eq) = coerce_eq_constraint(dest_var, result_expr, out_sort, signed)
        {
            Some(eq)
        } else {
            let dropped = self.diagnostics.coerce_eq_dropped_constraint.inc_get();
            let dropped_for_fn = {
                let entry = self
                    .diagnostics
                    .coerce_dropped_by_fn
                    .entry(Arc::clone(&self.fn_name))
                    .or_insert(0);
                *entry += 1;
                *entry
            };
            GLOBAL_COUNTERS.record_coerce_eq_dropped_for_fn(&self.fn_name, 1);
            warn!(
                fn_name = %self.fn_name,
                dest_local,
                site,
                result_sort = ?result_sort,
                dest_sort = ?out_sort,
                refused_ptr_widening,
                dropped_constraints = dropped,
                dropped_constraints_for_fn = dropped_for_fn,
                "CHC: dropped call-result equality constraint after sort coercion failure; destination may be unconstrained"
            );
            None
        }
    }
}

// Sound-fallback transition helpers extracted to codegen_call_fallback_emit.rs.
// Re-exported here for backward compatibility with existing imports.
pub(in crate::codegen_ay::chc) use super::codegen_call_fallback_emit::{
    emit_sound_fallback_goto, emit_sound_fallback_goto_extra, emit_sound_fallback_goto_prebuilt,
    try_emit_precise_call_result,
};

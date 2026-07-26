// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comparison operand resolution and deref helpers (Part of #2306).
//!
//! Extracted from `codegen_call_cmp.rs`:
//! - `resolve_double_ref_raw_ptr_cmp`: double-ref `&&*const T` resolution
//! - `deref_cmp_operands_if_needed`: pointer-to-pointee deref for `&T` cmp
//! - `recover_fixed_array_cmp_operands`: `&&[T; N]` array recovery
//! - `resolve_cmp_deref_operand`: single operand deref via local addr / memory
//! - `try_resolve_local_value_from_addr`: stack-local value bypass
//! - Free functions: raw-ptr detection, ref-pointee extraction, slice data

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::codegen_call_kani_model_dst::is_zst_ty;
use tracing::debug;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #4030: Resolve double-ref raw pointer operands (`&&*const T`).
    /// Blanket impls wrap args in an extra `&`; follow ref_targets two levels.
    pub(super) fn resolve_double_ref_raw_ptr_cmp(
        &self,
        lhs: &mut Expr,
        rhs: &mut Expr,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) {
        if is_raw_ptr_cmp_arg(&args[0], self.body.locals())
            || !is_raw_ptr_cmp_arg_any_depth(&args[0], self.body.locals())
            || lhs.sort().bitvec_width() != Some(64)
        {
            return;
        }
        let resolve_inner = |arg: &Operand| -> Option<Expr> {
            let place = match arg {
                Operand::Copy(p) | Operand::Move(p) => p,
                _ => return None,
            };
            let outer = self.ref_resolution.ref_targets.get(&place.local)?;
            let inner = self.ref_resolution.ref_targets.get(&outer.local)?;
            let inner_place = rustc_public::mir::Place {
                local: inner.local,
                projection: inner.projections.clone(),
            };
            self.translate_place_with_modified(&inner_place, modified_locals)
        };
        if let (Some(inner_lhs), Some(inner_rhs)) =
            (resolve_inner(&args[0]), resolve_inner(&args[1]))
        {
            *lhs = inner_lhs;
            *rhs = inner_rhs;
        }
    }

    /// Part of #3270: Dereference pointer operands for reference-type comparisons.
    ///
    /// When comparing `<&T as PartialEq>::eq`, `resolve_ref_or_const_referent` peels
    /// one `&` level, leaving BV64 pointer values. Rust semantics require comparing
    /// pointee values (`*self == *other`), not addresses. This method resolves pointers
    /// to their pointee values via local-address lookup or typed memory loads.
    ///
    /// Part of #3305: Selectively retains heap safety checks for non-stack addresses.
    /// Stack-local addresses have redundant checks (always valid within function scope).
    /// Real heap addresses need their checks preserved for use-after-free/bounds detection.
    pub(super) fn deref_cmp_operands_if_needed(
        &mut self,
        lhs: &mut Expr,
        rhs: &mut Expr,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) {
        if self.track_level < ChcTrackLevel::Mem
            || *lhs.sort() != ptr_sort()
            || *rhs.sort() != ptr_sort()
        {
            return;
        }
        // Part of #3994: Try double-ref `&&T` first (#3270), then single-ref `&T`.
        // MIR-inlined derived PartialEq for BV-flattened enums generates
        // field-level `<T as PartialEq>::eq(&field1, &field2)` where args are
        // `&T` (single ref). Without this fallback, the deref never fires and
        // raw BV64 pointer addresses are compared instead of pointee values.
        let Some(pointee_ty) = extract_ref_pointee_from_cmp_arg(&args[0], self.body.locals())
            .or_else(|| extract_single_ref_pointee(&args[0], self.body.locals()))
        else {
            return;
        };
        // Part of #4030: Raw pointer comparisons (`<*const T as Ord>::cmp`)
        // pass `&*const T` args. Do NOT dereference through the raw pointer —
        // Rust's Ord for raw pointers compares addresses (+ metadata for fat
        // pointers), not the pointed-to content.
        // Note: double-ref `&&*const T` (blanket impls) handled by
        // resolve_double_ref_raw_ptr_cmp in codegen_call_primitive_cmp_stub.
        if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..))) {
            return;
        }
        // Resolve each operand, selectively retaining heap safety checks.
        if let Some(lhs_val) = self.resolve_cmp_deref_operand(lhs, pointee_ty, modified_locals) {
            debug!("[#3270] cmp deref lhs: ptr -> {:?}", lhs_val.sort());
            *lhs = lhs_val;
        }
        if let Some(rhs_val) = self.resolve_cmp_deref_operand(rhs, pointee_ty, modified_locals) {
            debug!("[#3270] cmp deref rhs: ptr -> {:?}", rhs_val.sort());
            *rhs = rhs_val;
        }
    }

    /// Part of #3792/#3806: recover fixed-array operands from `&&[T; N]` and
    /// unsized-slice intermediates before the primitive cmp stub decides
    /// between array and scalar comparison paths.
    pub(super) fn recover_fixed_array_cmp_operands(
        &mut self,
        lhs: &mut Expr,
        rhs: &mut Expr,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) {
        self.recover_fixed_array_cmp_operand(lhs, &args[0], modified_locals);
        self.recover_fixed_array_cmp_operand(rhs, &args[1], modified_locals);
    }

    fn recover_fixed_array_cmp_operand(
        &mut self,
        expr: &mut Expr,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) {
        // Part of #4030: Do NOT resolve through raw pointers to their backing
        // array data. For `<&A as PartialOrd<&B>>::lt` where A = *const [u8],
        // the arg is `&&*const [u8]`. Without this guard, resolve_ref_chain_to_array
        // chases through the raw pointer to the [u8] backing Array(BV64→BV8),
        // which produces Array-sort operands that compute_partial_ord cannot handle.
        // Raw pointer comparisons should stay on the pointer-address level (BV64).
        if is_raw_ptr_cmp_arg_any_depth(arg, self.body.locals()) {
            return;
        }
        if expr.sort().bitvec_width() == Some(64)
            && let Some(arr) = self.resolve_ref_chain_to_array(arg, modified_locals)
        {
            *expr = arr;
        }
        if let Some(arr) = extract_slice_array_data(expr) {
            *expr = arr;
        }
        if let Some(arr) = extract_single_field_array_wrapper(expr) {
            *expr = arr;
        }
    }

    /// Part of #3305: Resolve a single comparison operand from pointer to pointee value.
    ///
    /// Stack-local addresses (obj_id in `local_addresses`) have their safety checks
    /// discarded — stack locals are valid for the entire function scope.
    /// Non-stack addresses (heap allocations, collection stubs) retain their safety
    /// checks for soundness (use-after-free, bounds, alignment).
    fn resolve_cmp_deref_operand(
        &mut self,
        addr: &Expr,
        pointee_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if is_zst_ty(pointee_ty) {
            debug!(?pointee_ty, "[#3807] cmp deref: canonical ZST pointee");
            return Some(Expr::bool_const(true));
        }

        // Try local-address resolution first — no heap checks generated.
        if let Some(val) = self.try_resolve_local_value_from_addr(addr, modified_locals) {
            return Some(val);
        }

        // Determine if address is a stack local (checks would be redundant).
        let is_stack_local = Self::try_extract_obj_id(addr)
            .map(|id| self.heap_state.local_idx_for_obj_id(id).is_some())
            .unwrap_or(false);

        let prev_checks = self.heap_state.pending_checks.len();
        let result = self.load_from_memory(addr.clone(), pointee_ty);

        if is_stack_local {
            // Stack local with non-scalar type (Datatype/Array): checks are
            // redundant since stack locals are always valid within function scope.
            self.heap_state.pending_checks.truncate(prev_checks);
            debug!("[#3305] cmp deref: discarded checks for stack-local address");
        }
        // Non-stack addresses (heap, collection stubs): retain checks for soundness.

        result
    }

    /// Part of #3270: Resolve a pointer to a local's value without going through
    /// typed memory. When a pointer has a constant obj_id that maps to a stack
    /// local (via local_addresses), return the local's state variable directly.
    ///
    /// This bypasses typed memory loads that may be unconstrained when the
    /// assignment path fails to emit a store. Applies only to base-address
    /// pointers (offset = 0). Part of #3901: multi-field flattened locals
    /// are reconstructed from state vars instead of typed memory.
    pub(in crate::codegen_ay::chc) fn try_resolve_local_value_from_addr(
        &self,
        addr: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let obj_id = Self::try_extract_obj_id(addr)?;
        let local_idx = self.heap_state.local_idx_for_obj_id(obj_id)?;
        if self.flatten.flattened_tuple_locals.contains(&local_idx)
            && self.flattened_field_count(local_idx) > 1
        {
            let expr = self.reconstruct_flattened_bare_read(local_idx, modified_locals)?;
            debug!(
                obj_id,
                local_idx,
                sort = ?expr.sort(),
                "[#3901] resolved flattened local value from addr via reconstruction"
            );
            return Some(expr);
        }
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        let (name, sort) = if modified_locals.contains(&local_idx) {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        debug!(
            obj_id,
            local_idx,
            name = &**name,
            sort = ?sort,
            "[#3270] resolved local value from addr — bypassing typed memory"
        );
        Some(Expr::var(&**name, sort.clone()))
    }
}

/// Part of #4030: Detect raw-pointer comparison arguments.
///
/// For `<*const T as Ord>::cmp(&self, &other)`, the MIR arg type is `&*const T`.
/// This function returns `true` when the arg is a reference whose pointee is a
/// raw pointer — indicating the comparison should operate on pointer addresses,
/// not on the content the raw pointer points to.
pub(super) fn is_raw_ptr_cmp_arg(arg: &Operand, locals: &[rustc_public::mir::LocalDecl]) -> bool {
    let pointee = extract_single_ref_pointee(arg, locals);
    matches!(pointee.map(|ty| ty.kind()), Some(TyKind::RigidTy(RigidTy::RawPtr(..))))
}

/// Part of #4030: Detect raw-pointer comparison arguments at any ref depth.
///
/// Returns `true` for both `&*const T` (direct) and `&&*const T` (blanket
/// `<&A as PartialOrd<&B>>::lt` where `A = *const T`). Used by
/// `recover_fixed_array_cmp_operand` to prevent resolving through the raw
/// pointer to slice/array backing data.
pub(super) fn is_raw_ptr_cmp_arg_any_depth(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    if is_raw_ptr_cmp_arg(arg, locals) {
        return true;
    }
    // Double-ref: `&&*const T` → peel two refs to find `*const T`.
    let double_pointee = extract_ref_pointee_from_cmp_arg(arg, locals);
    matches!(double_pointee.map(|ty| ty.kind()), Some(TyKind::RigidTy(RigidTy::RawPtr(..))))
}

/// Extract pointee type T from a single-reference `&T` comparison argument.
///
/// For `<T as PartialEq>::eq(&self, &other)`, the MIR arg type is `&T`.
/// This function peels one level to return `T`. Used by #3994 for ZST detection
/// and single-ref deref when `extract_ref_pointee_from_cmp_arg` returns None
/// because it expects `&&T`.
pub(super) fn extract_single_ref_pointee(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<rustc_public::ty::Ty> {
    let local_idx = match arg {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    let arg_ty = locals.get(local_idx)?.ty;
    match arg_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    }
}

/// For `<&T as PartialEq>::eq(&self, &other)`, the MIR arg type is `&&T`.
/// After resolve_ref_or_const_referent peels the outer `&`, we have `&T`.
/// This function peels both levels to return `T`, the actual value type to compare.
///
/// Returns `None` if the arg type is not a double-reference (meaning the resolved
/// values are already the comparison values and no dereference is needed).
///
/// Part of #3270.
pub(super) fn extract_ref_pointee_from_cmp_arg(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<rustc_public::ty::Ty> {
    let local_idx = match arg {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    let arg_ty = locals.get(local_idx)?.ty;
    // arg_ty is &&T — peel the outer &
    let inner_ref = match arg_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
        _ => return None,
    };
    // inner_ref is &T — peel the inner & to get T
    match inner_ref.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    }
}

pub(super) fn extract_slice_array_data(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return None;
    }
    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    let data_field = cons.fields.iter().find(|f| &*f.name == "fld_data")?;
    if !data_field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&*dt.name, "fld_data", data_field.sort.clone()))
}

/// Extract the inner Array from a single-field Datatype wrapper.
///
/// Repr-SIMD operands can arrive at the primitive cmp stub wrapped as a
/// one-field Datatype even when the underlying field is the real fixed-array
/// payload. Unwrapping here preserves the array compare lane used by
/// `compute_array_cmp_result` instead of dropping to scalar/datatype fallback.
pub(super) fn extract_single_field_array_wrapper(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return None;
    }
    let dt = expr.sort().datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    if cons.fields.len() != 1 {
        return None;
    }
    let field = &cons.fields[0];
    if !field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone()))
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Helper methods for CHC slice stub codegen.
//!
//! Extracted from codegen_call_slice.rs per #3348 (file size limit).
//! Contains type inspection, operand splitting, and IndexMut tracking.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};

use super::codegen_call_misc::CallMisc;
use super::codegen_ctx::globals::declare_pending_var;
use super::stubs_option_helpers::OptionHelpers;
use super::{ChcCtx, chc_fresh_name};

/// A slice resolved down to storage the encoder can index.
///
/// # All three fields are VALUES, and that is the point
///
/// `resolve_slice_backing` is the encoder's answer to "what does this slice
/// operand actually hold?", and the answer is never an address: `data` is the
/// element storage itself (an `Array`-sorted term, or the `fld_data` field of a
/// `Vec`/`String` datatype), `len` is an element count and `offset` is an
/// element index into `data`. When resolution has to go *through* a pointer it
/// performs the load first — see the `PtrRepr` lane in
/// [`ChcCtx::resolve_slice_backing`] — so the `Loc -> Val` crossing happens
/// inside the resolver, exactly once, at a real load.
///
/// Typing the fields [`Val`] states that, so consumers stop re-deriving it. It
/// also pins down the one place a caller *can* still be handed an address for a
/// slice operand (the `resolve_ref_or_const_referent` fallback in
/// `codegen_call_slice_index`), instead of leaving four producers merged into
/// one anonymous `Option<Expr>` that has to be width-tested afterwards.
pub(in crate::codegen_ay::chc) struct ResolvedSliceBacking {
    pub(in crate::codegen_ay::chc) data: Val,
    pub(in crate::codegen_ay::chc) len: Val,
    pub(in crate::codegen_ay::chc) offset: Val,
}

pub(in crate::codegen_ay::chc) const SLICE_BACKING_REBASE_MAX_ELEMS: usize = 32;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Identify (slice, index) from call args.
    ///
    /// SliceIndex::index takes (self: &[T], index: usize).
    /// Index::index takes (&self, index) where self may be Vec or array.
    /// We use type information to identify which arg is the slice/array.
    pub(in crate::codegen_ay::chc) fn split_chc_slice_index_args<'a>(
        &self,
        args: &'a [Operand],
    ) -> (&'a Operand, Option<&'a Operand>) {
        // Parity with statement/slice.rs:is_slice_or_array_ref_ty — also matches &Vec<T>.
        let is_slice_like = |op: &Operand| -> bool {
            let Ok(ty) = op.ty(self.body.locals()) else { return false };
            let ty = self.resolve_body_ty(ty);
            let inner = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
                _ => return false,
            };
            // Part of #3979: Peel through double references for subslice-of-slice
            // patterns like `&slice1[1..2]` where the argument type is `&&[T]`.
            // The Index trait takes `&self`, so indexing a `&[T]` yields `&&[T]`.
            let inner = match inner.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner2, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner2, _)) => self.resolve_body_ty(inner2),
                _ => inner,
            };
            match inner.kind() {
                TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Array(..)) => true,
                TyKind::RigidTy(RigidTy::Adt(def, _)) => def.trimmed_name() == "Vec",
                _ => false,
            }
        };

        match (args.first(), args.get(1)) {
            (Some(lhs), Some(rhs)) if is_slice_like(lhs) => (lhs, Some(rhs)),
            (Some(lhs), Some(rhs)) if is_slice_like(rhs) => (rhs, Some(lhs)),
            // Fallback: assume first arg is slice, second is index.
            (Some(lhs), idx) => (lhs, idx),
            _ => (&args[0], None), // non-enum: (Option, Option) tuple exhaustion
        }
    }

    /// Extract element type from a slice/array reference operand.
    pub(in crate::codegen_ay::chc) fn chc_slice_elem_ty(
        &self,
        operand: &Operand,
    ) -> Option<rustc_public::ty::Ty> {
        let ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
            _ => ty, // external enum: TyKind — non-pointer type used as-is
        };
        // Part of #3979: Peel through double references (same as is_slice_like).
        let inner_ty = match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner2, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner2, _)) => self.resolve_body_ty(inner2),
            _ => inner_ty,
        };
        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => Some(self.resolve_body_ty(elem)),
            TyKind::RigidTy(RigidTy::Array(elem, _)) => Some(self.resolve_body_ty(elem)),
            // Part of #2991: Vec<T, A> element type extraction (parity with statement/slice.rs:252).
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
                args.0.first().and_then(|arg| {
                    if let rustc_public::ty::GenericArgKind::Type(elem_ty) = arg {
                        Some(self.resolve_body_ty(*elem_ty))
                    } else {
                        None
                    }
                })
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Check if a type is zero-sized for slice indexing purposes.
    pub(in crate::codegen_ay::chc) fn is_zst_type_for_slice(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => true,
            TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
                if len.eval_target_usize().ok() == Some(0) {
                    return true;
                }
                Self::is_zst_type_for_slice(elem_ty)
            }
            TyKind::RigidTy(RigidTy::Never) => true,
            _ => false, // external enum: TyKind
        }
    }

    /// Coerce an expression to POINTER_WIDTH bitvector, or return None.
    pub(in crate::codegen_ay::chc) fn coerce_to_pointer_width(&self, expr: Expr) -> Option<Expr> {
        match expr.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => Some(expr),
            Some(w) if w < POINTER_WIDTH => Some(expr.zero_extend(POINTER_WIDTH - w)),
            Some(_) => Some(expr.extract(POINTER_WIDTH - 1, 0)),
            None => None,
        }
    }

    /// Extract length from a CHC-resolved array/datatype value.
    pub(in crate::codegen_ay::chc) fn chc_array_length(value: &Expr) -> Option<Expr> {
        if let Some(dt_name) = value.sort().datatype_name() {
            let dt = value.sort().datatype_sort()?;
            let ctor = dt.constructors.first()?;
            if ctor.has_field("fld_len") {
                return Some(value.clone().field_select(dt_name, "fld_len", ptr_sort()));
            }
        }
        None
    }

    /// Get the sort of a specific field in a datatype expression.
    pub(in crate::codegen_ay::chc) fn get_dt_field_sort(
        expr: &Expr,
        field_name: &str,
    ) -> Option<Sort> {
        let dt = expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;
        ctor.field_sort(field_name)
    }

    pub(in crate::codegen_ay::chc) fn resolve_slice_backing(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<ResolvedSliceBacking> {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
        {
            let resolved = self.resolve_provenance_local(place.local);
            if let Some(backing) =
                self.resolve_slice_backing_local(place.local, modified_locals, arg)
            {
                return Some(backing);
            }
            if resolved != place.local {
                if let Some(backing) = self.resolve_slice_backing_with_metadata_local(
                    resolved,
                    place.local,
                    modified_locals,
                    arg,
                ) {
                    return Some(backing);
                }
                if let Some(backing) =
                    self.resolve_slice_backing_local(resolved, modified_locals, arg)
                {
                    return Some(backing);
                }
            }
        }

        // Part of #4179: After unsized coercion, static_slice_len_from_operand
        // returns None for `&[T]`. trace_static_array_len_through_casts recovers
        // the length by walking backward through MIR to find `&[T; N]` or `Box<[T; N]>`.
        let len_hint = self.static_slice_len_from_operand(arg).or_else(|| {
            if let Operand::Copy(p) | Operand::Move(p) = arg {
                self.trace_static_array_len_through_casts(p.local)
            } else {
                None
            }
        });
        let value = self.resolve_ref_or_const_referent(arg, modified_locals)?;
        if let Some(backing) =
            self.slice_backing_from_expr(value.clone(), len_hint.clone(), zero.clone())
        {
            return Some(backing);
        }

        // Part of #4179: When the resolved value is a pointer, load the actual
        // array data from the memory model. This handles `&(*box_ptr)[start..end]`
        // where `box_ptr` is a heap-allocated array: the resolution chain stops at
        // the raw pointer because Box stores its data in the heap, so we
        // dereference through `load_from_memory` to get the Array-sorted expression.
        //
        // This used to be TWO copies of the same block, partitioned by width — one
        // for a BV64 thin pointer, one for a BV128 fat pointer that extracted the
        // low half first. The only thing the width test decided was *where the data
        // address lives inside the expression*, which is exactly what `PtrRepr`
        // answers: `data()` is total, so both shapes take one path. (After Unsize
        // coercion a `Box<[u16; 2]>` reference resolves to `(zero_extend 64 ptr)` —
        // a widened thin pointer whose data half is still perfectly good; only its
        // metadata half is fabricated, and this block never reads that.)
        if let Some(data_ptr) = PtrRepr::classify(&value).map(|repr| repr.into_data().into_expr()) {
            let pointee_ty = arg.ty(self.body.locals()).ok().and_then(|ty| {
                let ty = self.resolve_body_ty(ty);
                match ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                        Some(self.resolve_body_ty(inner))
                    }
                    _ => None,
                }
            });
            if let Some(pointee_ty) = pointee_ty {
                // Part of #4179 (fix): When pointee is unsized slice [T],
                // load_from_memory cannot reconstruct the array because
                // get_array_length([T]) returns None. Trace backward through
                // MIR to find the sized array type [T; N] from the Box<[T; N]>
                // source. Use that for the load so the multi-element array
                // reconstruction path fires (memory_impl.rs:116-147).
                let effective_ty =
                    if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Slice(_))) {
                        self.trace_box_inner_sized_array_ty(arg).unwrap_or(pointee_ty)
                    } else {
                        pointee_ty
                    };
                if let Some(loaded) = self.load_from_memory_untyped(data_ptr, effective_ty) {
                    if let Some(backing) = self.slice_backing_from_expr(loaded, len_hint, zero) {
                        tracing::debug!(
                            fn_name = %self.fn_name,
                            "resolve_slice_backing: resolved pointer-backed array via memory load (#4179)"
                        );
                        return Some(backing);
                    }
                }
            }
        }

        None
    }

    /// The `slice::as_ptr` data address for `arg`.
    ///
    /// Wave 11: every lane below is an address by construction — a promoted
    /// constant's `concat(obj_id, 0)` allocation base, `translate_ref_to_address`
    /// (address-of a place), the decoded data half of a wide pointer, or
    /// `extract_pointer_expr` — and the tail is byte-offset arithmetic on that
    /// address. So the function is a derived address producer and says so.
    pub(in crate::codegen_ay::chc) fn slice_as_ptr_data_expr(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Loc> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }

        let base = if let Some(promoted_obj_id) =
            self.ref_resolution.const_ref_promoted_obj_ids.get(&place.local).copied()
        {
            // ALLOCATION: `promoted_const_address_for` is literally
            // `concat(obj_id const, 0)` — the split-pointer base of a promoted
            // constant object, an address by construction.
            Loc::of_address(self.heap_state.promoted_const_address_for(promoted_obj_id))
        } else if let Some(ref_target) = self.ref_resolution.ref_targets.get(&place.local).cloned()
        {
            let target_place = rustc_public::mir::Place {
                local: ref_target.local,
                projection: ref_target.projections,
            };
            self.translate_ref_to_address(&target_place, modified_locals)?
        } else {
            let value = self.translate_operand_with_modified(arg, modified_locals)?;
            // Wide pointer -> its data half, decoded rather than measured. A thin
            // pointer (and anything not pointer-shaped) still goes to
            // `extract_pointer_expr`, which is Wave 11's address producer and owns
            // that case; the partition is exactly the one the width test made.
            match PtrRepr::classify(&value) {
                Some(repr @ (PtrRepr::Fat { .. } | PtrRepr::WidenedThin(_))) => repr.into_data(),
                _ => return super::super::dyn_coercion::extract_pointer_expr(&value),
            }
        };

        let Some(offset) = self.ref_resolution.subslice_offset.get(&place.local).cloned() else {
            return Some(base);
        };
        if Self::is_zero_pointer_width_bitvec(&offset) {
            return Some(base);
        }
        let elem_size = self.slice_elem_byte_size_from_operand(arg).unwrap_or(1);
        let byte_offset = if elem_size == 1 {
            offset
        } else {
            offset.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
        };
        // ADDRESS ARITHMETIC on a `Loc` stays a `Loc`.
        Some(Loc::of_address(base.into_expr().bvadd(byte_offset)))
    }

    pub(in crate::codegen_ay::chc) fn propagate_slice_as_ptr_metadata(
        &mut self,
        dest_local: usize,
        arg: &Operand,
    ) {
        let Some(src_local) = Self::unprojected_operand_local(arg) else {
            self.clear_slice_as_ptr_metadata(dest_local);
            return;
        };

        self.clear_slice_as_ptr_metadata(dest_local);
        let has_nonzero_offset = self
            .ref_resolution
            .subslice_offset
            .get(&src_local)
            .is_some_and(|offset| !Self::is_zero_pointer_width_bitvec(offset));

        if !has_nonzero_offset
            && let Some(obj_id) = self
                .ref_resolution
                .const_ref_promoted_obj_ids
                .get(&src_local)
                .copied()
                .or_else(|| self.known_alloc_ids.get(&src_local).copied())
        {
            self.known_alloc_ids.insert(dest_local, obj_id);
            self.ref_resolution.alloc_result_locals.insert(dest_local);
        }

        if !has_nonzero_offset
            && let Some(ref_target) = self.ref_resolution.ref_targets.get(&src_local).cloned()
        {
            self.ref_resolution.ref_targets.insert(dest_local, ref_target);
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
        }

        if let Some(backing) = self.const_byte_backing_for_slice_as_ptr(src_local) {
            self.ref_resolution.const_ref_values.insert(dest_local, backing);
            let offset = self
                .ref_resolution
                .subslice_offset
                .get(&src_local)
                .cloned()
                .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        }

        // Carry the receiver's element count so the deref-site `idx < len`
        // memory-safety obligation (try_resolve_const_ref_deref) keeps firing
        // on the as_ptr result and every const-offset derived from it — the
        // check that catches one-past-end derefs of str/slice-const pointers.
        // clear_slice_as_ptr_metadata above wiped it; restore from the source.
        if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
        }
    }

    fn clear_slice_as_ptr_metadata(&mut self, dest_local: usize) {
        self.known_alloc_ids.remove(&dest_local);
        self.ref_resolution.alloc_result_locals.remove(&dest_local);
        self.ref_resolution.ref_targets.remove(&dest_local);
        self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.const_ref_slice_views.remove(&dest_local);
        self.ref_resolution.const_ref_promoted_obj_ids.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
    }

    fn unprojected_operand_local(arg: &Operand) -> Option<usize> {
        match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }

    fn const_byte_backing_for_slice_as_ptr(&self, src_local: usize) -> Option<Expr> {
        let value = self
            .ref_resolution
            .const_ref_values
            .get(&src_local)
            .or_else(|| self.ref_resolution.const_ref_slice_views.get(&src_local))?
            .clone();
        if value.sort().array_sort().is_some() {
            return Some(value);
        }

        let dt_name = value.sort().datatype_name()?.to_owned();
        let data_sort = Self::get_dt_field_sort(&value, "fld_data")?;
        Some(value.field_select(&dt_name, "fld_data", data_sort))
    }

    fn resolve_slice_backing_local(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
        arg: &Operand,
    ) -> Option<ResolvedSliceBacking> {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        // Part of #4179: After unsized coercion (`&[T; N]` -> `&[T]`), the operand
        // type is `&[T]` so static_slice_len_from_operand returns None.
        // trace_static_array_len_through_casts recovers N by tracing backward
        // through Cast/Copy/Move/Ref MIR chains to the pre-coercion source type.
        let len_hint = self
            .ref_resolution
            .subslice_len
            .get(&local)
            .cloned()
            .or_else(|| self.static_slice_len_from_operand(arg))
            .or_else(|| self.trace_static_array_len_through_casts(local));
        let offset = self
            .ref_resolution
            .subslice_offset
            .get(&local)
            .cloned()
            .unwrap_or_else(|| zero.clone());

        let value = self.slice_backing_value_for_local(local, modified_locals)?;
        self.slice_backing_from_expr(value, len_hint, offset)
    }

    fn resolve_slice_backing_with_metadata_local(
        &mut self,
        data_local: usize,
        metadata_local: usize,
        modified_locals: &HashSet<usize>,
        arg: &Operand,
    ) -> Option<ResolvedSliceBacking> {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let len_hint = self
            .ref_resolution
            .subslice_len
            .get(&metadata_local)
            .cloned()
            .or_else(|| self.static_slice_len_from_operand(arg));
        // `slice_from_raw_parts_mut(ptr.add(k), len)` can leave the offset on the
        // data local while the metadata local carries a zero/default offset.
        let offset = self
            .ref_resolution
            .subslice_offset
            .get(&metadata_local)
            .filter(|offset| !Self::is_zero_pointer_width_bitvec(offset))
            .or_else(|| self.ref_resolution.subslice_offset.get(&data_local))
            .cloned()
            .unwrap_or(zero);
        let value = self.slice_backing_value_for_local(data_local, modified_locals)?;
        self.slice_backing_from_expr(value, len_hint, offset)
    }

    fn slice_backing_value_for_local(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let mut visited = HashSet::new();
        self.slice_backing_value_for_local_inner(local, modified_locals, &mut visited)
    }

    fn slice_backing_value_for_local_inner(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
        visited: &mut HashSet<usize>,
    ) -> Option<Expr> {
        if !visited.insert(local) {
            return None;
        }
        if let Some(slice_view) = self.ref_resolution.const_ref_slice_views.get(&local).cloned() {
            return Some(slice_view);
        }
        if let Some(value) = self.ref_resolution.const_ref_values.get(&local).cloned() {
            return Some(value);
        }
        if let Some(value) =
            self.resolve_slice_backing_value_from_ref_assignment(local, modified_locals)
        {
            return Some(value);
        }
        if let Some(source_local) = self.resolve_slice_backing_source_local(local)
            && let Some(value) =
                self.slice_backing_value_for_local_inner(source_local, modified_locals, visited)
        {
            return Some(value);
        }
        self.try_resolve_local_expr(local, modified_locals)
    }

    fn resolve_slice_backing_value_from_ref_assignment(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Box-backed range receivers often appear as `_slice = &(*_raw_ptr)`.
        // When ref_targets metadata is unavailable on the reference local, recover
        // the backing by translating the borrowed place directly.
        let places: Vec<_> = self
            .body
            .blocks
            .iter()
            .flat_map(|bb_data| {
                bb_data.statements.iter().filter_map(|stmt| {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    if lhs.local != local || !lhs.projection.is_empty() {
                        return None;
                    }
                    match rhs {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            Some(place.clone())
                        }
                        _ => None,
                    }
                })
            })
            .collect();

        places
            .into_iter()
            .find_map(|place| self.translate_slice_backing_borrowed_place(&place, modified_locals))
    }

    fn translate_slice_backing_borrowed_place(
        &mut self,
        place: &rustc_public::mir::Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            if matches!(
                self.body.locals()[place.local].ty.kind(),
                TyKind::RigidTy(RigidTy::RawPtr(_, _))
            ) && !self.known_alloc_ids.contains_key(&place.local)
                && let Some(obj_id) = self.trace_deref_store_alloc_id(place.local)
            {
                self.known_alloc_ids.insert(place.local, obj_id);
            }
            return self.translate_place_with_deref(place, modified_locals);
        }

        self.translate_place_with_modified(place, modified_locals)
    }

    fn resolve_slice_backing_source_local(&self, dest_local: usize) -> Option<usize> {
        self.body.blocks.iter().flat_map(|bb_data| bb_data.statements.iter()).find_map(|stmt| {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                return None;
            };
            if lhs.local != dest_local || !lhs.projection.is_empty() {
                return None;
            }
            match rhs {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() =>
                {
                    Some(src.local)
                }
                _ => None,
            }
        })
    }

    fn slice_backing_from_expr(
        &self,
        expr: Expr,
        len_hint: Option<Expr>,
        offset: Expr,
    ) -> Option<ResolvedSliceBacking> {
        let len_hint = len_hint.and_then(|len| self.coerce_to_pointer_width(len));
        let offset = Val::of_value(self.coerce_to_pointer_width(offset)?);

        // `expr` is element storage by the time it reaches here: an array-sorted
        // term, or a collection datatype whose `fld_data` is one. Both halves
        // below select a datum out of it, never an address.
        if expr.sort().array_sort().is_some() {
            return Some(ResolvedSliceBacking {
                data: Val::of_value(expr),
                len: Val::of_value(len_hint?),
                offset,
            });
        }

        let dt_name = expr.sort().datatype_name()?.to_owned();
        let data_sort = Self::get_dt_field_sort(&expr, "fld_data")?;
        let len = Self::chc_array_length(&expr)
            .and_then(|len| self.coerce_to_pointer_width(len))
            .or(len_hint)?;
        let data = expr.field_select(&dt_name, "fld_data", data_sort);
        Some(ResolvedSliceBacking { data: Val::of_value(data), len: Val::of_value(len), offset })
    }

    pub(in crate::codegen_ay::chc) fn is_zero_pointer_width_bitvec(expr: &Expr) -> bool {
        matches!(expr.value(), ExprValue::BitVecConst { value, .. } if *value == 0u64.into())
    }

    pub(in crate::codegen_ay::chc) fn rebase_slice_backing_to_zero_based_array(
        &mut self,
        backing: &ResolvedSliceBacking,
        target_sort: &Sort,
        fresh_prefix: &str,
        max_elems: usize,
    ) -> Option<Expr> {
        let target_arr = target_sort.array_sort()?;
        let data = backing.data.as_expr();
        let offset = backing.offset.as_expr();
        let _source_arr = data.sort().array_sort()?;

        if data.sort() == target_sort && Self::is_zero_pointer_width_bitvec(offset) {
            return Some(data.clone());
        }

        let mut rebased = declare_pending_var(chc_fresh_name(fresh_prefix), target_sort.clone());
        for i in 0..max_elems {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let src_idx = Self::slice_rebase_source_index(offset, idx.clone(), i);
            let elem = data.clone().select(src_idx);
            let elem = self.coerce_value_to_sort(elem, &target_arr.element_sort, false)?;
            rebased = rebased.store(idx, elem);
        }
        Some(rebased)
    }

    pub(in crate::codegen_ay::chc) fn slice_rebase_source_index(
        offset: &Expr,
        idx: Expr,
        logical_index: usize,
    ) -> Expr {
        if logical_index == 0 { offset.clone() } else { offset.clone().bvadd(idx) }
    }

    pub(in crate::codegen_ay::chc) fn static_slice_len_from_operand(
        &self,
        arg: &Operand,
    ) -> Option<Expr> {
        // Guard: Operand::ty() panics on out-of-bounds local index.
        // Check bounds before calling to avoid ICE on synthetic or malformed MIR.
        if let Operand::Copy(p) | Operand::Move(p) = arg {
            if p.local >= self.body.locals().len() {
                return None;
            }
        }
        let ty = self.resolve_body_ty(arg.ty(self.body.locals()).ok()?);
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
            _ => ty,
        };

        if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner_ty.kind()
            && let Ok(len) = const_len.eval_target_usize()
        {
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }

        None
    }

    fn slice_elem_byte_size_from_operand(&self, arg: &Operand) -> Option<usize> {
        let ty = self.resolve_body_ty(arg.ty(self.body.locals()).ok()?);
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
            _ => ty,
        };
        let elem_ty = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem_ty) | RigidTy::Array(elem_ty, _)) => elem_ty,
            _ => return None,
        };
        self.get_type_size(elem_ty)
    }

    pub(in crate::codegen_ay::chc) fn build_precise_slice_eq(
        &self,
        lhs: &ResolvedSliceBacking,
        rhs: &ResolvedSliceBacking,
    ) -> Option<Expr> {
        if *lhs.data.as_expr().sort() != *rhs.data.as_expr().sort() {
            return None;
        }

        let idx_name = chc_fresh_name("slice_eq_idx");
        let idx_sort = ptr_sort();
        let idx = Expr::var(&idx_name, idx_sort.clone());
        let lhs_idx = lhs.offset.as_expr().clone().bvadd(idx.clone());
        let rhs_idx = rhs.offset.as_expr().clone().bvadd(idx.clone());
        let elems_eq = lhs.data.as_expr().clone().select(lhs_idx).eq(rhs
            .data
            .as_expr()
            .clone()
            .select(rhs_idx));
        let in_bounds = idx.bvult(lhs.len.as_expr().clone());
        let content_eq = Expr::forall(vec![(idx_name, idx_sort)], in_bounds.implies(elems_eq));
        Some(lhs.len.as_expr().clone().eq(rhs.len.as_expr().clone()).and(content_eq))
    }

    /// Part of #4179 (fix): Trace backward through MIR to find a sized array
    /// type `[T; N]` from a `Box<[T; N]>` or `&[T; N]` source.
    ///
    /// When `Box::new([0u16, 10])` is indexed as `&obj[1..2]`, the receiver
    /// type after unsized coercion is `&[u16]` (no length info). This walks
    /// backward from the coerced local to find the original `[T; N]` type so
    /// that `load_from_memory` can use the multi-element array reconstruction
    /// path (which requires `get_array_length` to return `Some(N)`).
    fn trace_box_inner_sized_array_ty(&self, arg: &Operand) -> Option<rustc_public::ty::Ty> {
        let local = match arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let mut current = local;
        let mut seen = HashSet::new();
        for _ in 0..8 {
            if !seen.insert(current) {
                break;
            }
            if current < self.body.locals().len() {
                let ty = self.resolve_body_ty(self.body.locals()[current].ty);
                let inner_ty = match ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                        Some(self.resolve_body_ty(inner))
                    }
                    TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Box" => {
                        use rustc_public::ty::GenericArgKind;
                        args.0.iter().find_map(|a| match a {
                            GenericArgKind::Type(inner) => Some(self.resolve_body_ty(*inner)),
                            _ => None,
                        })
                    }
                    _ => None,
                };
                if let Some(inner) = inner_ty {
                    if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                        return Some(inner);
                    }
                }
            }
            let next =
                self.body.blocks.iter().flat_map(|bb| bb.statements.iter()).find_map(|stmt| {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    if lhs.local != current || !lhs.projection.is_empty() {
                        return None;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => {
                            if src.projection.is_empty() { Some(src.local) } else { None }
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            if place.projection.is_empty()
                                || (place.projection.len() == 1
                                    && matches!(place.projection[0], ProjectionElem::Deref))
                            {
                                Some(place.local)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                });
            match next {
                Some(n) => current = n,
                None => break,
            }
        }
        None
    }

    /// Part of #4179: Trace backward through MIR Cast/Copy/Move/Ref chains to
    /// recover a static array length from the pre-coercion source type.
    ///
    /// When `Box::new([0u16, 10])` is indexed via `&obj[1..2]`, the receiver type
    /// after unsized coercion is `&[u16]` (no length info). This method walks
    /// backward from the coerced local to find the original `&[T; N]` or
    /// `Box<[T; N]>` type and extract N.
    fn trace_static_array_len_through_casts(&self, local: usize) -> Option<Expr> {
        let mut current = local;
        let mut seen = HashSet::new();
        for _ in 0..8 {
            if !seen.insert(current) {
                break;
            }
            // Check the type of the current local for a static array length.
            if current < self.body.locals().len() {
                let ty = self.resolve_body_ty(self.body.locals()[current].ty);
                // Peel through Ref/RawPtr/Box to find the inner type.
                let inner_ty = match ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                        Some(self.resolve_body_ty(inner))
                    }
                    TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Box" => {
                        use rustc_public::ty::GenericArgKind;
                        args.0.iter().find_map(|a| match a {
                            GenericArgKind::Type(inner) => Some(self.resolve_body_ty(*inner)),
                            _ => None,
                        })
                    }
                    _ => None,
                };
                if let Some(inner) = inner_ty {
                    if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner.kind() {
                        if let Ok(len) = const_len.eval_target_usize() {
                            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
                        }
                    }
                }
            }
            // Follow Cast/Copy/Move/Ref chains backward to find the source local.
            let next =
                self.body.blocks.iter().flat_map(|bb| bb.statements.iter()).find_map(|stmt| {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    if lhs.local != current || !lhs.projection.is_empty() {
                        return None;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => {
                            if src.projection.is_empty() { Some(src.local) } else { None }
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            if place.projection.is_empty()
                                || (place.projection.len() == 1
                                    && matches!(place.projection[0], ProjectionElem::Deref))
                            {
                                Some(place.local)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                });
            match next {
                Some(n) => current = n,
                None => break,
            }
        }
        None
    }
}

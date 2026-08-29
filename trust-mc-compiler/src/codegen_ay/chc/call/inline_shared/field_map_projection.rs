// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Field-map place resolution helpers for inline translation.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{LocalDecl, Place, ProjectionElem};
use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, TyKind};
use std::collections::HashMap;

use super::super::{ChcCtx, constant_index_offset};
use crate::codegen_ay::chc::call::inline_field_map::DIRECT_DEREF_FIELD;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::dyn_coercion;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Resolve a projected place (e.g., `(*_1).field[idx]`) against the inline
/// receiver field-map, rebuilding flattened array elements when MIR type
/// information says the selected element should be a Datatype.
pub(in crate::codegen_ay::chc) fn resolve_projected_place(
    ctx: &mut ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    self_field_map: &HashMap<(usize, usize), Expr>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let base = local_exprs.get(&place.local)?;
    let mut current = base.clone();
    let mut current_ty = ctx.resolve_body_ty(locals.get(place.local)?.ty);
    let mut had_deref = false;
    let mut direct_deref_hint_eligible = true;
    let mut last_deref_was_raw_ptr = false;
    // Part of #3889: Track Downcast variant index for subsequent Field extraction.
    // MIR pattern `(_tmp as Some).0` → [Downcast(_, 1), Field(0, _)].
    // The Field must use the constructor at the downcasted variant index.
    let mut downcast_variant: Option<usize> = None;
    // Part of #4050: Track flattened DT field chain traversal.
    // When projecting through intermediate structs (RawVec, RawVecInner, Unique)
    // within a flattened DT (Vec, String), accumulate byte offsets until we
    // reach a leaf field, then resolve to the correct DT field by offset.
    let mut flattened_dt_ctx: Option<(Expr, u64)> = None;

    for proj in &place.projection {
        match proj {
            ProjectionElem::Deref => {
                last_deref_was_raw_ptr =
                    matches!(current_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)));
                // Part of #4050: resolve pending flattened DT before Deref.
                if let Some((dt_expr, offset)) = flattened_dt_ctx.take() {
                    if let Some(resolved) = resolve_dt_field_by_byte_offset(&dt_expr, offset) {
                        current = resolved;
                    }
                }
                // Captured-ref walk gap: when the local was seeded BY VALUE
                // with the pointee's Datatype (closure env passed by reference
                // into contract ensures/requires closures), Deref is identity.
                // extract_pointer_expr would otherwise peel the env DT's cap_0
                // — a capture the closure sort may legitimately declare to be
                // an address (wave 18) — and use it as the base, destroying the
                // env and failing every subsequent capture Field read.
                let identity_value_deref = !last_deref_was_raw_ptr
                    && match current_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                            super::place::deref_is_identity_on_value_dt(
                                &current,
                                ctx.resolve_body_ty(pointee),
                            )
                        }
                        _ => false,
                    };
                if !identity_value_deref {
                    if let Some(ptr_expr) = dyn_coercion::extract_pointer_expr(&current) {
                        // `current` is the walker's running term and is a VALUE
                        // on the identity lane above, so the slot cannot be
                        // typed; the tag ends at this crossing.
                        current = ptr_expr.into_expr();
                    }
                }
                current_ty = match current_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ctx.resolve_body_ty(inner),
                    TyKind::RigidTy(RigidTy::Adt(def, args))
                        if is_pointer_wrapper_adt(&def.trimmed_name()) =>
                    {
                        args.0
                            .iter()
                            .find_map(|arg| match arg {
                                GenericArgKind::Type(pointee) => {
                                    Some(ctx.resolve_body_ty(*pointee))
                                }
                                _ => None,
                            })
                            .unwrap_or(current_ty)
                    }
                    _ => current_ty,
                };
                had_deref = true;
                downcast_variant = None;
            }
            ProjectionElem::Field(idx, field_ty) => {
                direct_deref_hint_eligible = false;
                if let Some(loaded) = self_field_map.get(&(place.local, *idx))
                    && had_deref
                {
                    current = loaded.clone();
                    current_ty = ctx.resolve_body_ty(*field_ty);
                    if !current.sort().is_array() {
                        if let Some(arr) = try_rebuild_bv_as_array(&current, current_ty) {
                            current = arr;
                        }
                    }
                    had_deref = false;
                    continue;
                }
                // Part of #4132: Do NOT overwrite `current` from DIRECT_DEREF_FIELD
                // mid-field. This whole-object substitution did not exist at last-good
                // c4d6ff3fdf. Field projection prefers (local, field_idx) cache or
                // datatype_field_select. DIRECT_DEREF_FIELD is only valid for the
                // end-of-chain bare-deref fallback at the bottom of this function.
                //
                // Part of #4050: If we're in flattened DT accumulation mode,
                // continue accumulating byte offsets through intermediate structs.
                if let Some((_, ref mut offset)) = flattened_dt_ctx {
                    if let Some(field_off) = ctx.get_field_offset(current_ty, *idx) {
                        *offset += field_off;
                        current_ty = ctx.resolve_body_ty(*field_ty);
                        had_deref = false;
                        continue;
                    }
                }
                current = ctx.try_unflatten_bv_to_datatype(current, current_ty);
                let cons_idx = downcast_variant.take();
                // `current` is the running term for the place's value as the
                // projection chain is walked; every producer feeding it above is
                // a local expression or a loaded pointee, so it is a value.
                if let Some(selected) = ChcCtx::datatype_field_select(
                    &crate::codegen_ay::provenance::Val::of_value(current.clone()),
                    *idx,
                    cons_idx,
                )
                .map(crate::codegen_ay::provenance::Val::into_expr)
                {
                    // Part of #4050: Detect flattened DT field chain mismatch.
                    // When the DT is flattened (e.g., Vec_bv64 has {fld_ptr, fld_len,
                    // fld_cap, fld_data}) but MIR projects into an intermediate struct
                    // (e.g., Field(0) → RawVec, not a scalar), the DT field at the MIR
                    // index doesn't match the MIR semantics. Enter accumulated offset
                    // mode: track byte offsets through the type hierarchy until we reach
                    // the actual leaf field, then resolve by offset.
                    let resolved_field_ty = ctx.resolve_body_ty(*field_ty);
                    let mir_field_is_intermediate = matches!(
                        resolved_field_ty.kind(),
                        TyKind::RigidTy(RigidTy::Adt(ref def, _))
                        if def.kind() == AdtKind::Struct
                    ) && !selected.sort().is_datatype();
                    if mir_field_is_intermediate {
                        if let Some(field_off) = ctx.get_field_offset(current_ty, *idx) {
                            flattened_dt_ctx = Some((current.clone(), field_off));
                            current_ty = resolved_field_ty;
                            had_deref = false;
                            continue;
                        }
                    }
                    current = selected;
                    current_ty = resolved_field_ty;
                    had_deref = false;
                    continue;
                }
                if let ay_bindings::SortInner::Datatype(dt) = current.sort().inner() {
                    // Part of #3889: Use downcasted variant's constructor when available,
                    // fall back to first constructor for non-downcasted access.
                    let cons = if let Some(vi) = cons_idx {
                        dt.constructors.get(vi)
                    } else {
                        dt.constructors.first()
                    };
                    if let Some(cons) = cons {
                        if let Some(field) = cons.fields.get(*idx) {
                            // Part of #3901: Z3 PDR treats DT accessors as
                            // uninterpreted ("Uninterpreted 'value' in <null>").
                            // Avoid emitting DT accessor calls by extracting
                            // fields directly from known expression shapes:
                            // 1. ite-reconstructed Option: ite(c, Some(p), None) → p
                            // 2. bare DT constructor: Some(p) → p
                            if let Some(payload) =
                                try_extract_dt_field_without_accessor(&current, *idx)
                            {
                                current = payload;
                                current_ty = ctx.resolve_body_ty(*field_ty);
                                had_deref = false;
                                continue;
                            }
                            let dt_name = dt.name.clone();
                            let field_name = field.name.clone();
                            let field_sort = field.sort.clone();
                            current = current.field_select(&dt_name, &field_name, field_sort);
                            current_ty = ctx.resolve_body_ty(*field_ty);
                            had_deref = false;
                            continue;
                        }
                    }
                }
                // Part of #4050: transparent wrapper fallback for non-DT
                // expressions. Vec internals project through NonNull → Unique →
                // *const T chains where each wrapper has a single non-ZST field.
                // When the expr is BV, Field(0) is identity.
                if let Some(passthrough) = super::place::try_transparent_field_passthrough(
                    ctx,
                    &current,
                    *idx,
                    Some(current_ty),
                ) {
                    current = passthrough;
                    current_ty = ctx.resolve_body_ty(*field_ty);
                    had_deref = false;
                    continue;
                }
                return None;
            }
            ProjectionElem::Index(local) => {
                direct_deref_hint_eligible = false;
                if !current.sort().is_array() {
                    return None;
                }
                let idx_expr = local_exprs.get(local)?;
                current = current.select(idx_expr.clone());
                current_ty = ctx.resolve_body_ty(ctx.get_array_element_ty(current_ty)?);
                current = ctx.try_unflatten_bv_to_datatype(current, current_ty);
                had_deref = false;
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                direct_deref_hint_eligible = false;
                if !current.sort().is_array() {
                    return None;
                }
                // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                let Some(actual_offset) = constant_index_offset(*offset, *min_length, *from_end)
                else {
                    return None;
                };
                current = current.select(Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH));
                current_ty = ctx.resolve_body_ty(ctx.get_array_element_ty(current_ty)?);
                current = ctx.try_unflatten_bv_to_datatype(current, current_ty);
                had_deref = false;
            }
            // Part of #3889: Downcast is a MIR type-narrowing annotation
            // (e.g., `(_tmp as Some).0`). Record the variant index so the
            // subsequent Field projection uses the correct constructor.
            ProjectionElem::Downcast(variant_idx) => {
                use crate::rustc_public_bridge::IndexedVal;
                downcast_variant = Some(variant_idx.to_index());
            }
            // Part of #3188: OpaqueCast is transparent in CHC encoding.
            ProjectionElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }

    // Part of #4050: resolve pending flattened DT at end of projection chain.
    if let Some((dt_expr, offset)) = flattened_dt_ctx.take() {
        if let Some(resolved) = resolve_dt_field_by_byte_offset(&dt_expr, offset) {
            current = resolved;
        }
    }

    if had_deref {
        // Part of #4151: only use the whole-object deref hint for a bare
        // receiver deref like `*_1`. For `(_1.field)`-then-deref chains
        // (notably `Pin<&mut Coroutine>` entry reads), overwriting `current`
        // with the entry-time whole-object hint drops updated receiver state.
        if direct_deref_hint_eligible
            && let Some(loaded) = self_field_map.get(&(place.local, DIRECT_DEREF_FIELD))
        {
            current = loaded.clone();
        }
        // Part of #3848: When dereferencing a raw pointer to a static (e.g.,
        // `_old = (*_ptr)` where `_ptr = &raw mut CELL`), the field_map has
        // no entry because the pointer isn't the `self` parameter. Without
        // this load, we return the raw address instead of the value at that
        // address, causing `CELL += 1` to compute `address + 1`.
        //
        // `last_deref_was_raw_ptr` is read off the MIR type and is what makes
        // the term an address: references ARE transparent in the CHC encoding
        // (deref is identity), raw pointers never are. That type test now
        // leads — it used to sit inside a width test that had already decided
        // the term was an address — and `PtrRepr::thin_address` supplies only
        // the pointer's shape.
        else if last_deref_was_raw_ptr
            && let Some(addr) = PtrRepr::thin_address(&current)
            && let Some(loaded) = ctx.load_from_memory(addr, current_ty)
        {
            current = loaded.into_expr();
        }
    }

    Some(ctx.try_unflatten_bv_to_datatype(current, current_ty))
}

/// Part of #3889: Rebuild a flat BV as a AY Array when the Rust type is
/// `[T; N]`. Memory loads for fixed-size arrays return flat BVs (e.g., BV128
/// for `[u32; 4]`), but the inline walker's `Index` projection requires an
/// Array-sorted expression for `select` to work.
///
/// Builds: `store(store(const_array(0), 0, extract[31:0]), 1, extract[63:32]) ...`
fn try_rebuild_bv_as_array(bv_expr: &Expr, array_ty: rustc_public::ty::Ty) -> Option<Expr> {
    let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = array_ty.kind() else {
        return None;
    };
    let bv_width = bv_expr.sort().bitvec_width()?;
    let elem_sort = ChcCtx::translate_ty(elem_ty)?;
    let elem_bits = elem_sort.bitvec_width()?;
    if elem_bits == 0 {
        return None;
    }
    let len = len_const.eval_target_usize().ok()? as usize;
    if len == 0 || len.checked_mul(elem_bits as usize)? > bv_width as usize {
        return None;
    }

    let idx_sort = Sort::bitvec(POINTER_WIDTH);
    let mut arr = Expr::const_array(idx_sort, Expr::bitvec_const(0u128, elem_bits));
    for i in 0..len {
        let low = (i as u32) * elem_bits;
        let high = low + elem_bits - 1;
        let elem = bv_expr.clone().extract(high, low);
        arr = arr.store(Expr::bitvec_const(i as u128, POINTER_WIDTH), elem);
    }
    Some(arr)
}

/// Part of #3901: Extract a DT field value without emitting a DT accessor.
///
/// Z3 PDR treats DT accessors (`(value expr)`, `(Ok_field_0 expr)`) as
/// uninterpreted, producing "Uninterpreted '<name>' in <null>" errors.
/// This function handles three cases:
///
/// 1. **Bare DT constructor**: `Ctor(arg0, arg1, ...)` → `args[field_idx]`
/// 2. **ite-reconstructed enum**: `ite(cond, CtorA(a), CtorB(b))` →
///    `ite(cond, extract(CtorA(a), idx), extract(CtorB(b), idx))`
///    This recurses into both branches, handling Option (Some/None) and
///    Result (Ok/Err) uniformly.
/// 3. **Nullary constructor**: `None` / `Err()` with no args → `None`
///
/// Returns `None` for symbolic DT expressions where the field can only be
/// extracted via the DT accessor (which remains as a fallback).
pub(in crate::codegen_ay::chc) fn try_extract_dt_field_without_accessor(
    container: &Expr,
    field_idx: usize,
) -> Option<Expr> {
    use ay_bindings::ExprValue;

    match container.value() {
        // Case 1: bare DT constructor — Ctor(arg0, arg1, ...) → args[field_idx]
        ExprValue::DatatypeConstructor { args, .. } => args.get(field_idx).cloned(),

        // Case 2: ite-reconstructed enum — recurse into both branches
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_val = try_extract_dt_field_without_accessor(then_expr, field_idx);
            let else_val = try_extract_dt_field_without_accessor(else_expr, field_idx);
            match (then_val, else_val) {
                (Some(t), Some(e)) => Some(Expr::ite(cond.clone(), t, e)),
                // One branch is nullary (e.g., None has no field 0). The field
                // is only meaningful when the other branch is active, so return
                // that branch's value directly — the guard condition from the
                // discriminant check ensures the nullary branch is unreachable.
                (Some(t), None) => Some(t),
                (None, Some(e)) => Some(e),
                (None, None) => None,
            }
        }

        _ => None,
    }
}

/// Part of #4050: Resolve a DT field by accumulated byte offset within the
/// flattened struct hierarchy.
///
/// Vec is encoded as a flat DT `Vec_bv64 { fld_ptr, fld_len, fld_cap, fld_data }`
/// but its MIR layout has nested structs: `Vec.buf(RawVec).inner(RawVecInner).cap`.
/// When the inline walker accumulates byte offsets through the MIR hierarchy,
/// this function maps the total byte offset to the correct DT field.
///
/// Byte-to-DT-field mapping for Vec-family DTs (64-bit):
///   - byte 0  → fld_ptr (pointer, at beginning of RawVec.inner.ptr chain)
///   - byte 8  → fld_cap (capacity, at RawVecInner.cap)
///   - byte 16 → fld_len (length, at Vec.len after RawVec)
fn resolve_dt_field_by_byte_offset(dt_expr: &Expr, byte_offset: u64) -> Option<Expr> {
    let ay_bindings::SortInner::Datatype(dt) = dt_expr.sort().inner() else {
        return None;
    };
    let cons = dt.constructors.first()?;

    // Map known byte offsets to DT field names for Vec/String layout.
    // Vec memory layout: [ptr @ 0, cap @ 8, len @ 16]
    // DT field order:    [fld_ptr @ 0, fld_len @ 1, fld_cap @ 2, fld_data @ 3]
    let ptr_bytes = (POINTER_WIDTH / 8) as u64;
    let target_name = match byte_offset {
        0 => "fld_ptr",
        off if off == ptr_bytes => "fld_cap",
        off if off == 2 * ptr_bytes => "fld_len",
        _ => return None,
    };

    // Find the DT field by name and extract it.
    for field in &cons.fields {
        if field.name == target_name {
            let dt_name = dt.name.clone();
            let field_name = field.name.clone();
            let field_sort = field.sort.clone();
            // Try accessor-free extraction first (bare constructor / ite).
            if let Some(payload) = try_extract_dt_field_by_name(dt_expr, &field_name, &cons.fields)
            {
                return Some(payload);
            }
            return Some(dt_expr.clone().field_select(&dt_name, &field_name, field_sort));
        }
    }
    None
}

/// Extract a named DT field without emitting a DT accessor, by finding the
/// field's positional index within the constructor and using positional extraction.
fn try_extract_dt_field_by_name(
    container: &Expr,
    field_name: &str,
    fields: &[ay_bindings::DatatypeField],
) -> Option<Expr> {
    let field_idx = fields.iter().position(|f| f.name == field_name)?;
    try_extract_dt_field_without_accessor(container, field_idx)
}

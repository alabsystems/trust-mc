// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Place and operand resolution for inline body translators.
//!
//! Extracted from `inline_shared/mod.rs` per #3913 Step 6.
//! Provides `resolve_place`, `inline_operand_to_expr`, `inline_ref_place_to_expr`,
//! and closure-capture / local-projection resolution helpers.

use rustc_public::mir::{LocalDecl, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

use ay_bindings::Expr;

use super::super::ChcCtx;
use super::super::codegen_expr_constant::ExprConstant;
use super::super::codegen_types::CodegenTypes;
use super::PlaceResolver;
use super::field_map_projection;
use super::subslice::{apply_inline_subslice, array_element_ty};
use crate::codegen_ay::chc::dyn_coercion;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Captured-ref walk gap: true when `expr` already IS the pointee VALUE for a
/// `Deref` step — the walker seeded the local (a closure env passed by
/// reference into contract ensures/requires closures) with the pointee's
/// translated Datatype value rather than an address. Deref must then be
/// identity. Without this gate, `extract_pointer_expr` fabricates a "pointer"
/// from the env DT's first BV64 field (`cap_0`), destroying the env and
/// failing every subsequent capture Field read
/// (`rvalue_gap_Use_root_projected` → walk failure → dropped side-channel
/// checks).
///
/// Scope is deliberately CLOSURE-ENV ONLY (`Closure_{id}` sorts from
/// `closure_sort_name`, deterministic per ClosureDef): pointer-representation
/// DTs (`Dyn_Trait{fld_ptr, fld_vtable}`, `Vec{fld_ptr, ...}`) must keep the
/// `extract_pointer_expr` lane, and every other shape stays on the existing
/// fail-closed path (walk failure → demoting fallback), never a fabricated
/// value.
pub(in crate::codegen_ay) fn deref_is_identity_on_value_dt(
    expr: &Expr,
    pointee_ty: rustc_public::ty::Ty,
) -> bool {
    let ay_bindings::SortInner::Datatype(dt) = expr.sort().inner() else {
        return false;
    };
    if !dt.name.starts_with("Closure_") {
        return false;
    }
    let Some(pointee_sort) = <ChcCtx<'_, '_> as CodegenTypes>::translate_ty(pointee_ty) else {
        return false;
    };
    match pointee_sort.inner() {
        ay_bindings::SortInner::Datatype(p) => p.name == dt.name,
        _ => false,
    }
}

pub(in crate::codegen_ay) fn inline_ref_place_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    // Part of #4003: Use `if let Some` instead of `?` so that when local 1
    // (closure env) is not in local_exprs, we fall through to resolve_place
    // which routes through PlaceResolver::Captures. The previous `?` caused
    // an early return from the entire function, skipping capture resolution
    // for Ref rvalues like `&(*_1).0` in closure bodies.
    if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        if let Some(root) = local_exprs.get(&place.local) {
            let current_ty_opt = locals.get(place.local).and_then(|decl| {
                match ctx.resolve_body_ty(decl.ty).kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                        Some(ctx.resolve_body_ty(pointee))
                    }
                    _ => None,
                }
            });
            // Captured-ref walk gap: when the root local was seeded BY VALUE
            // with the pointee's Datatype (closure env), the address-arithmetic
            // path below would fabricate `cap_0 + offset` addresses out of the
            // env's first field. Skip straight to resolve_place, which resolves
            // the projection transparently on the value (references are
            // transparent in the CHC encoding).
            if current_ty_opt.is_some_and(|p| deref_is_identity_on_value_dt(root, p)) {
                return resolve_place(ctx, local_exprs, place, resolver, locals);
            }
            // Part of #4030: `&raw const (*wide_ptr)` inside inline bodies must
            // preserve the full fat-pointer value. Pulling out only `fld_ptr`
            // erases `fld_len`/metadata and breaks wide-pointer ordering.
            // Also covers BV128 fat pointers (slice/str/custom DST) where the
            // metadata lives in the high 64 bits. extract_pointer_expr would
            // strip those bits, losing the length for downstream PtrMetadata.
            let is_unsized_pointee = current_ty_opt
                .map(|ty| ty.layout().ok().is_some_and(|layout| layout.shape().is_unsized()))
                .unwrap_or(false);
            let is_fat_sort =
                root.sort().is_datatype() || root.sort().bitvec_width() == Some(2 * POINTER_WIDTH);
            let preserve_fat_pointer =
                place.projection.len() == 1 && is_fat_sort && is_unsized_pointee;
            if preserve_fat_pointer {
                return Some(root.clone());
            }
            let base_addr =
                dyn_coercion::extract_pointer_expr(root).unwrap_or_else(|| root.clone());
            if base_addr.sort().bitvec_width() == Some(POINTER_WIDTH) {
                let mut addr = base_addr;
                if let Some(mut current_ty) = current_ty_opt {
                    let mut resolved_all = true;
                    for proj in &place.projection.as_slice()[1..] {
                        match proj {
                            ProjectionElem::Field(idx, field_ty) => {
                                if let Some(offset) = ctx.get_field_offset(current_ty, *idx) {
                                    if offset > 0 {
                                        addr = addr.bvadd(Expr::bitvec_const(
                                            offset as i64,
                                            POINTER_WIDTH,
                                        ));
                                    }
                                    current_ty = ctx.resolve_body_ty(*field_ty);
                                } else {
                                    resolved_all = false;
                                    break;
                                }
                            }
                            // Part of #3188: OpaqueCast is transparent — skip it.
                            ProjectionElem::OpaqueCast(_) => {}
                            _ => {
                                resolved_all = false;
                                break;
                            }
                        }
                    }
                    if resolved_all {
                        return Some(addr);
                    }
                }
            }
        }
    }
    resolve_place(ctx, local_exprs, place, resolver, locals)
}

/// Translate a MIR Operand to a AY Expr within an inline body context.
///
/// Part of #3241: replaces `closure_operand_to_expr_inline`, `virtual_operand_to_expr`,
/// and `closure_operand_to_expr` (quantifier encoding).
pub(in crate::codegen_ay) fn inline_operand_to_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &Operand,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            resolve_place(ctx, local_exprs, place, resolver, locals)
        }
        Operand::Constant(const_op) => {
            ctx.translate_constant_referent(const_op).or_else(|| ctx.translate_constant(const_op))
        }
    }
}

/// Resolve a place reference to a AY expression using the provided resolver strategy.
pub(in crate::codegen_ay) fn resolve_place(
    ctx: &mut ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    if place.projection.is_empty() {
        return local_exprs.get(&place.local).cloned();
    }
    match resolver {
        PlaceResolver::Captures(captures) => resolve_capture_field(place, captures, local_exprs)
            .or_else(|| resolve_local_projections(ctx, local_exprs, place, locals)),
        PlaceResolver::FieldMap(self_field_map) => field_map_projection::resolve_projected_place(
            ctx,
            local_exprs,
            place,
            self_field_map,
            locals,
        ),
    }
}

/// Resolve Field/Deref projections on non-capture locals using Datatype extraction.
///
/// Part of #3348: Enables closure body translation for closures with tuple
/// parameters (e.g., `|(&a, &b)| a ^ b` from `iter().zip().map().collect()`).
/// The tuple parameter (local 2) has Field projections that extract elements.
/// Previously, these fell through to returning the base expression without
/// applying projections, silently producing wrong results.
fn resolve_local_projections(
    ctx: &mut ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let base = local_exprs.get(&place.local)?;
    let mut current = base.clone();
    // Part of #3901: Track Downcast variant index for subsequent Field extraction.
    // MIR pattern `(_tmp as Some).0` → [Downcast(_, 1), Field(0, _)].
    // The Field must use the constructor at the downcasted variant index.
    let mut downcast_variant: Option<usize> = None;
    // Part of #3188: Track current MIR type through projections for Subslice
    // length recovery. When the array length is compile-time-known (e.g., [T; N]),
    // from_end=true Subslice can compute the effective range without runtime info.
    let mut current_ty: Option<rustc_public::ty::Ty> =
        locals.get(place.local).map(|decl| ctx.resolve_body_ty(decl.ty));

    for proj in &place.projection {
        #[allow(unreachable_patterns)] // forward compat for new ProjectionElem variants
        match proj {
            ProjectionElem::Deref => {
                // Part of #4101: Detect raw pointer dereference BEFORE updating
                // current_ty. Raw pointer derefs need a typed memory load; references
                // are transparent in CHC encoding (deref is identity).
                let is_raw_ptr_deref = current_ty.is_some_and(|ty| {
                    matches!(ctx.resolve_body_ty(ty).kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
                });

                // Resolve pointee type for subsequent projections.
                let pointee_ty = current_ty.and_then(|ty| match ctx.resolve_body_ty(ty).kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                        Some(ctx.resolve_body_ty(pointee))
                    }
                    _ => None,
                });

                // Captured-ref walk gap: a by-value-seeded pointee Datatype
                // (closure env) must NOT be routed through extract_pointer_expr,
                // which would fabricate a "pointer" from its first BV64 field.
                // Deref is identity on the value.
                let identity_value_deref = !is_raw_ptr_deref
                    && pointee_ty.is_some_and(|p| deref_is_identity_on_value_dt(&current, p));

                // Identity in BV model — references are transparent in CHC encoding.
                if !identity_value_deref {
                    if let Some(ptr_expr) = dyn_coercion::extract_pointer_expr(&current) {
                        current = ptr_expr;
                    }
                }

                // Part of #4101: For raw pointer derefs at Mem track level, load
                // the value from the typed memory array. The value was stored via
                // mirror_local_assignment_to_memory and lives in mem_<type>[addr].
                // Without this load, the inline walker returns the BV64 address
                // instead of the value, causing CTREX in pointer-wrapper harnesses
                // (e.g., Container<T> wrapping NonNull<T>).
                if is_raw_ptr_deref {
                    if let Some(pty) = pointee_ty {
                        if current.sort().bitvec_width() == Some(POINTER_WIDTH) {
                            if let Some(loaded) = ctx.load_from_memory(current.clone(), pty) {
                                current = loaded;
                            }
                        }
                    }
                }

                // Part of #4207: For reference derefs where the expression is
                // still a BV64 pointer (memory address) and the pointee is an
                // ADT/tuple, load from typed memory. This happens when a struct
                // was stored to heap (e.g., via Rc/Arc) and the drop shim
                // passes a &mut ref — the ref is transparent in CHC encoding
                // but the value lives in the typed memory array, not a DT expr.
                // Without this load, subsequent Field projections fail because
                // resolve_dt_field requires a Datatype expression.
                if !is_raw_ptr_deref
                    && current.sort().bitvec_width() == Some(POINTER_WIDTH)
                    && let Some(pty) = pointee_ty
                    && matches!(
                        ctx.resolve_body_ty(pty).kind(),
                        TyKind::RigidTy(RigidTy::Adt(..)) | TyKind::RigidTy(RigidTy::Tuple(_))
                    )
                {
                    if let Some(loaded) = ctx.load_from_memory(current.clone(), pty) {
                        if loaded.sort().is_datatype() || !loaded.sort().is_bitvec() {
                            current = loaded;
                        }
                    }
                }

                current_ty = pointee_ty;
                downcast_variant = None;
            }
            ProjectionElem::Field(idx, field_ty) => {
                if let Some(dt_result) = resolve_dt_field(&current, *idx, &mut downcast_variant) {
                    current = dt_result;
                } else if let Some(passthrough) =
                    try_transparent_field_passthrough(ctx, &current, *idx, current_ty)
                {
                    // Part of #4050: transparent wrapper types (NonNull, Unique,
                    // single-field newtypes) are identity at BV level. When the
                    // expr is BV (not DT), Field(0) passes through unchanged.
                    current = passthrough;
                } else {
                    return None;
                }
                current_ty = Some(ctx.resolve_body_ty(*field_ty));
            }
            // Part of #3901: Downcast is a MIR type-narrowing annotation
            // (e.g., `(_tmp as Some).0`). Record the variant index so the
            // subsequent Field projection uses the correct constructor.
            ProjectionElem::Downcast(variant_idx) => {
                use crate::rustc_public_bridge::IndexedVal;
                downcast_variant = Some(variant_idx.to_index());
            }
            ProjectionElem::Index(local) => {
                // Array select: base[index_local]
                // Part of #3454: enables closure body translation for array
                // indexing patterns like `(*_5)[_2]` where _5 is a local
                // resolved to Array sort.
                if current.sort().is_array() {
                    let idx_expr = local_exprs.get(local)?;
                    current = current.select(idx_expr.clone());
                } else {
                    return None;
                }
                current_ty = current_ty.and_then(|ty| array_element_ty(ctx, ty));
                downcast_variant = None;
            }
            // Part of #3188: ConstantIndex is the compile-time-known variant
            // of Index (e.g., `arr[0]`). The write path in projected_assign.rs
            // already handles this; this adds the symmetric read path.
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                if current.sort().is_array() {
                    let idx = super::super::constant_index_offset(*offset, *min_length, *from_end);
                    let idx_expr = Expr::bitvec_const(idx as u128, POINTER_WIDTH);
                    current = current.select(idx_expr);
                } else {
                    return None;
                }
                current_ty = current_ty.and_then(|ty| array_element_ty(ctx, ty));
                downcast_variant = None;
            }
            // Part of #3188: OpaqueCast is a transparent MIR annotation for
            // coroutine/async types. Identity in CHC encoding (same as Deref on
            // value types). Without this, inline bodies with coroutine locals bail.
            ProjectionElem::OpaqueCast(_) => {}
            // Part of #3188: Subslice projects a contiguous sub-range of an array.
            ProjectionElem::Subslice { from, to, from_end } => {
                let known_len = current_ty.and_then(|ty| match ctx.resolve_body_ty(ty).kind() {
                    TyKind::RigidTy(RigidTy::Array(_, len_const)) => {
                        len_const.eval_target_usize().ok()
                    }
                    _ => None,
                });
                current = apply_inline_subslice(&current, *from, *to, *from_end, known_len)?;
                downcast_variant = None;
            }
            _ => return None,
        }
    }

    Some(current)
}

/// Extract a DT field, using the downcasted variant's constructor when available.
/// Part of #3901: avoids DT accessor calls that PDR treats as uninterpreted.
fn resolve_dt_field(
    current: &Expr,
    idx: usize,
    downcast_variant: &mut Option<usize>,
) -> Option<Expr> {
    let cons_idx = downcast_variant.take();
    if let Some(selected) = ChcCtx::datatype_field_select(current, idx, cons_idx) {
        return Some(selected);
    }

    if let ay_bindings::SortInner::Datatype(dt) = current.sort().inner() {
        let cons =
            if let Some(vi) = cons_idx { dt.constructors.get(vi) } else { dt.constructors.first() };
        if let Some(cons) = cons {
            if let Some(field) = cons.fields.get(idx) {
                if let Some(payload) =
                    field_map_projection::try_extract_dt_field_without_accessor(current, idx)
                {
                    return Some(payload);
                }
                let dt_name = dt.name.clone();
                let field_name = field.name.clone();
                let field_sort = field.sort.clone();
                return Some(current.clone().field_select(&dt_name, &field_name, field_sort));
            }
        }
    }
    // Part of #2440: bail closed for non-DT field access
    None
}

/// Part of #4050: Handle Field projections on non-Datatype expressions for
/// transparent wrapper types (NonNull, Unique, single-field newtypes).
///
/// In Vec internals, MIR projects through chains like:
///   `_ptr = Move(_rawvec.0.0.0)` — RawVec → Unique → NonNull → *const T
///
/// These wrapper types have a single non-ZST field. When the expression is
/// BV (pointer-width), Field(0) is an identity — the BV IS the inner value.
/// Without this, 12+ root gaps cascade into 48+ downstream gaps.
pub(super) fn try_transparent_field_passthrough(
    ctx: &ChcCtx<'_, '_>,
    current: &Expr,
    field_idx: usize,
    current_ty: Option<rustc_public::ty::Ty>,
) -> Option<Expr> {
    // Only handle BV expressions (pointer-width values in the inline walker).
    if !current.sort().is_bitvec() {
        return None;
    }
    let ty = current_ty?;
    let resolved = ctx.resolve_body_ty(ty);

    // Part of #4166: Fat pointer (BV128) Field decomposition.
    // BV128 = concat(metadata:BV64, data:BV64). Field(0) = data (low 64),
    // Field(1) = metadata (high 64). Must check before the field_idx != 0 bail.
    if let TyKind::RigidTy(RigidTy::RawPtr(..)) | TyKind::RigidTy(RigidTy::Ref(..)) =
        resolved.kind()
    {
        let bv_width = current.sort().bitvec_width().unwrap_or(0);
        if bv_width == 2 * POINTER_WIDTH {
            // Fat pointer: BV128.
            return match field_idx {
                0 => Some(current.clone().extract(POINTER_WIDTH - 1, 0)),
                1 => Some(current.clone().extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH)),
                _ => None,
            };
        }
        // Thin pointer: BV64 — Field(0) is identity.
        if field_idx == 0 {
            return Some(current.clone());
        }
        return None;
    }

    // Only handle Field(0) for non-pointer types — multi-field structs need DT encoding.
    if field_idx != 0 {
        return None;
    }

    // Check: is this a struct/newtype with exactly one non-ZST field at index 0?
    // That covers NonNull<T>, Unique<T>, and other #[repr(transparent)] wrappers.
    match resolved.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            use rustc_public::ty::AdtKind;
            if def.kind() != AdtKind::Struct {
                return None;
            }
            let variants = def.variants();
            let variant = variants.first()?;
            let fields = variant.fields();
            // Single-field struct: Field(0) is identity on BV.
            if fields.len() == 1 {
                return Some(current.clone());
            }
            // Multi-field struct where all fields except index 0 are ZST:
            // e.g., PhantomData-carrying wrappers. Check via layout.
            if let Ok(layout) = resolved.layout() {
                if let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields
                {
                    // If field 0 starts at offset 0 and the total size equals
                    // the BV width, the non-phantom field occupies the full value.
                    if offsets.first().is_some_and(|off| off.bytes() == 0) {
                        let total_bytes = layout.shape().size.bytes() as u32;
                        if let Some(bv_width) = current.sort().bitvec_width() {
                            if total_bytes * 8 == bv_width {
                                return Some(current.clone());
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

pub(in crate::codegen_ay) fn inline_coroutine_discriminant_expr(current: Expr) -> Option<Expr> {
    let discr = crate::codegen_ay::types::coroutine_discriminant_select(current)?;
    Some(match discr.sort().bitvec_width() {
        Some(width) if width < POINTER_WIDTH => discr.zero_extend(POINTER_WIDTH - width),
        Some(width) if width > POINTER_WIDTH => discr.extract(POINTER_WIDTH - 1, 0),
        _ => discr,
    })
}

/// Resolve a closure-struct field projection to a captured variable.
///
/// Part of #2943: the closure struct is always local 1; field projections
/// on it index into the `captures` array.
///
/// Part of #3454: handles compound projections on captures. For closures
/// like `|j| a[j] < 10`, the MIR accesses `(*_1).0[_2]` which is
/// `Place { local: 1, projection: [Deref, Field(0), Deref, Index(2)] }`.
/// After extracting the capture (Array sort), applies remaining projections:
/// - `Deref` → identity (references are transparent in CHC)
/// - `Index(local)` → `capture.select(local_exprs[local])`
fn resolve_capture_field(
    place: &Place,
    captures: &[Expr],
    local_exprs: &HashMap<usize, Expr>,
) -> Option<Expr> {
    if place.local != 1 || place.projection.is_empty() {
        return None;
    }
    // Find the Field projection that selects the capture.
    let mut capture_expr: Option<Expr> = None;
    let mut remaining_start = 0;
    for (i, proj) in place.projection.iter().enumerate() {
        match proj {
            ProjectionElem::Field(idx, _) => {
                capture_expr = captures.get(*idx).cloned();
                remaining_start = i + 1;
                break;
            }
            ProjectionElem::Deref => continue, // skip leading Deref
            _ => return None,
        }
    }
    let mut current = capture_expr?;
    // Apply remaining projections after the capture field extraction.
    for proj in &place.projection[remaining_start..] {
        match proj {
            ProjectionElem::Deref => {
                // Identity in CHC model — references are transparent.
            }
            ProjectionElem::Index(local) => {
                // Array select: capture[index_local]
                if current.sort().is_array() {
                    let idx_expr = local_exprs.get(local)?;
                    current = current.select(idx_expr.clone());
                } else {
                    return None;
                }
            }
            // Part of #3188: ConstantIndex on captures (e.g., tuple destructuring).
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                if current.sort().is_array() {
                    let idx = super::super::constant_index_offset(*offset, *min_length, *from_end);
                    let idx_expr = Expr::bitvec_const(idx as u128, POINTER_WIDTH);
                    current = current.select(idx_expr);
                } else {
                    return None;
                }
            }
            ProjectionElem::Field(idx, _) => {
                // Datatype field extraction on the capture
                if let ay_bindings::SortInner::Datatype(dt) = current.sort().inner() {
                    if let Some(cons) = dt.constructors.first() {
                        if let Some(field) = cons.fields.get(*idx) {
                            let dt_name = dt.name.clone();
                            let field_name = field.name.clone();
                            let field_sort = field.sort.clone();
                            current = current.field_select(&dt_name, &field_name, field_sort);
                            continue;
                        }
                    }
                }
                return None;
            }
            // Part of #3188: OpaqueCast is transparent in CHC encoding.
            ProjectionElem::OpaqueCast(_) => {}
            // Part of #3188: Subslice on captures. No type context available,
            // so from_end=true with nonzero from/to still bails (known_len=None).
            ProjectionElem::Subslice { from, to, from_end } => {
                current = apply_inline_subslice(&current, *from, *to, *from_end, None)?;
            }
            _ => return None,
        }
    }
    Some(current)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use ay_bindings::Sort;

    const PASSTHROUGH_SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(transparent)]
        pub struct TransparentPtr(*const u8);

        pub struct NonTransparent(*const u8, u8);

        pub fn probe_thin_ptr(p: *const u8) -> *const u8 { p }

        pub fn probe_wide_ptr(p: *const [u8]) -> *const [u8] { p }

        pub fn probe_transparent_wrapper(w: TransparentPtr) -> TransparentPtr { w }

        pub fn probe_nontransparent_wrapper(w: NonTransparent) -> NonTransparent { w }
    "#;

    fn with_arg_ty(
        fn_name: &str,
        arg_local: usize,
        f: impl FnOnce(&ChcCtx<'_, '_>, Option<rustc_public::ty::Ty>) + Send,
    ) {
        with_test_ay_ctx_for_source(PASSTHROUGH_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            f(&chc_ctx, Some(chc_ctx.resolve_body_ty(body.locals()[arg_local].ty)));
        });
    }

    #[test]
    fn test_try_transparent_field_passthrough_thin_pointer_identity() {
        with_arg_ty("probe_thin_ptr", 1, |chc_ctx, current_ty| {
            let expr = Expr::var("thin_ptr", Sort::bitvec(POINTER_WIDTH));
            let passthrough = try_transparent_field_passthrough(chc_ctx, &expr, 0, current_ty)
                .expect("thin pointer Field(0) should pass through");
            assert_eq!(
                passthrough.to_string(),
                expr.to_string(),
                "thin pointer Field(0) should stay as the original BV expression"
            );
            assert!(
                try_transparent_field_passthrough(chc_ctx, &expr, 1, current_ty).is_none(),
                "thin pointer Field(1) should be rejected"
            );
        });
    }

    #[test]
    fn test_try_transparent_field_passthrough_wide_pointer_extracts_halves() {
        with_arg_ty("probe_wide_ptr", 1, |chc_ctx, current_ty| {
            let expr = Expr::var("wide_ptr", Sort::bitvec(2 * POINTER_WIDTH));
            let data = try_transparent_field_passthrough(chc_ctx, &expr, 0, current_ty)
                .expect("wide pointer Field(0) should extract the data pointer");
            let metadata = try_transparent_field_passthrough(chc_ctx, &expr, 1, current_ty)
                .expect("wide pointer Field(1) should extract metadata");

            assert_eq!(
                data.to_string(),
                expr.clone().extract(POINTER_WIDTH - 1, 0).to_string(),
                "wide pointer Field(0) should select the low pointer-width half"
            );
            assert_eq!(
                metadata.to_string(),
                expr.clone().extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH).to_string(),
                "wide pointer Field(1) should select the high pointer-width half"
            );
            assert!(
                try_transparent_field_passthrough(chc_ctx, &expr, 2, current_ty).is_none(),
                "wide pointer Field(2) should be out of bounds"
            );
        });
    }

    #[test]
    fn test_try_transparent_field_passthrough_transparent_wrapper_identity() {
        with_arg_ty("probe_transparent_wrapper", 1, |chc_ctx, current_ty| {
            let expr = Expr::var("transparent_wrapper", Sort::bitvec(POINTER_WIDTH));
            let passthrough = try_transparent_field_passthrough(chc_ctx, &expr, 0, current_ty)
                .expect("transparent single-field wrapper should pass through");
            assert_eq!(
                passthrough.to_string(),
                expr.to_string(),
                "transparent wrapper Field(0) should keep the BV payload unchanged"
            );
        });
    }

    const CLOSURE_ENV_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_closure_env(x: u32, y: u32) -> u32 {
            let f = move || x + y;
            f()
        }

        pub fn probe_vec_ref(v: &Vec<u8>) -> usize { v.len() }
    "#;

    #[test]
    fn test_deref_identity_fires_only_for_matching_closure_env_dt() {
        use crate::codegen_ay::chc::codegen_types::CodegenTypes;
        with_test_ay_ctx_for_source(CLOSURE_ENV_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_closure_env");
            let body = instance.body().expect("function body");
            let closure_ty = body
                .locals()
                .iter()
                .map(|decl| decl.ty)
                .find(|ty| {
                    matches!(
                        ty.kind(),
                        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Closure(..))
                    )
                })
                .expect("closure local in probe body");
            let env_sort = <ChcCtx<'_, '_> as CodegenTypes>::translate_ty(closure_ty)
                .expect("closure env sort");
            assert!(env_sort.is_datatype(), "capturing closure env should be a DT");

            // Positive: env expr whose sort IS the pointee's translated DT.
            let env_expr = Expr::var("env", env_sort);
            assert!(
                deref_is_identity_on_value_dt(&env_expr, closure_ty),
                "by-value closure env deref must be identity"
            );

            // Negative: BV expr (address) never triggers identity.
            let addr = Expr::var("addr", Sort::bitvec(POINTER_WIDTH));
            assert!(
                !deref_is_identity_on_value_dt(&addr, closure_ty),
                "BV64 address must keep the pointer lane"
            );

            // Negative: non-Closure DT (e.g. a manufactured fld_ptr carrier)
            // must keep the extract_pointer_expr lane even if shapes align.
            let fat = Expr::var(
                "fat",
                crate::codegen_ay::names::struct_sort(
                    "Dyn_Trait_test",
                    [("fld_ptr", Sort::bitvec(POINTER_WIDTH))],
                ),
            );
            assert!(
                !deref_is_identity_on_value_dt(&fat, closure_ty),
                "non-Closure DT must not claim identity deref"
            );
        });
    }

    #[test]
    fn test_try_transparent_field_passthrough_nontransparent_wrapper_rejects() {
        with_arg_ty("probe_nontransparent_wrapper", 1, |chc_ctx, current_ty| {
            let expr = Expr::var("nontransparent_wrapper", Sort::bitvec(POINTER_WIDTH));
            assert!(
                try_transparent_field_passthrough(chc_ctx, &expr, 0, current_ty).is_none(),
                "multi-field wrapper should not pass through as transparent"
            );
            assert!(
                try_transparent_field_passthrough(chc_ctx, &expr, 1, current_ty).is_none(),
                "nontransparent wrapper Field(1) should also be rejected"
            );
        });
    }
}

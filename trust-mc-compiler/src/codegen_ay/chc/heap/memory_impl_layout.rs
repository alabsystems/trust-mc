// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! CHC type layout helpers: size, alignment, field offsets, array queries.
//! Converted from include!() to proper module per #2595.
//! Extracted from memory_impl.rs per #2246 (500 LOC threshold).
use super::ChcCtx;
use crate::kani_middle::abi::LayoutOf;
use rustc_middle::ty::TypingEnv;
use rustc_public::CrateDef;
use rustc_public::abi::VariantsShape;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyConstKind, TyKind};
use tracing::{debug, warn};

pub(in crate::codegen_ay::chc) fn unwrap_heap_transparent_ty(
    mut ty: rustc_public::ty::Ty,
) -> rustc_public::ty::Ty {
    loop {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return ty;
        };
        let is_wrapper = matches!(
            def.trimmed_name().as_str(),
            "UnsafeCell"
                | "Cell"
                | "RefCell"
                | "MaybeUninit"
                | "ManuallyDrop"
                | "Mutex"
                | "RwLock"
                | "MutexGuard"
                | "RwLockReadGuard"
                | "RwLockWriteGuard"
                | "PoisonError"
        );
        let Some(GenericArgKind::Type(inner_ty)) = args.0.first() else {
            return ty;
        };
        if !is_wrapper {
            return ty;
        }
        ty = *inner_ty;
    }
}

pub(super) fn ty_has_unresolved_non_region_params(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::Param(_) => true,
        TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
            ty_has_unresolved_non_region_params(elem_ty)
                || matches!(len.kind(), TyConstKind::Param(_))
        }
        TyKind::RigidTy(RigidTy::Slice(elem_ty)) => ty_has_unresolved_non_region_params(elem_ty),
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
            ty_has_unresolved_non_region_params(pointee)
        }
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
            ty_has_unresolved_non_region_params(pointee)
        }
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field_ty| ty_has_unresolved_non_region_params(*field_ty))
        }
        TyKind::RigidTy(RigidTy::Adt(_, ref args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(arg_ty) => ty_has_unresolved_non_region_params(*arg_ty),
            GenericArgKind::Const(c) => matches!(c.kind(), TyConstKind::Param(_)),
            _ => false,
        }),
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // ============================================================================
    // Type Layout Helpers
    // ============================================================================
    /// Resolve a dyn-trait tail layout from the metadata gathered by the CHC
    /// vtable passes.
    ///
    /// Returns constant layout information only when the tail alignment or size
    /// is unambiguous across the currently-known concrete implementations. This
    /// keeps `get_type_size` / `get_type_align` conservative for mixed-layout
    /// trait objects while still recovering the single-layout unsized-coercion
    /// cases from #3589.
    pub(super) fn resolve_trait_tail_layout(
        &self,
        ty: rustc_public::ty::Ty,
        layout: &LayoutOf,
    ) -> Option<(Option<usize>, Option<u64>)> {
        if !layout.has_trait_tail() {
            return None;
        }
        let tail_layouts: Vec<(u64, u64)> = if self.vtable_type_metadata.is_empty() {
            self.predeclared_concrete_layouts.clone()
        } else {
            self.vtable_type_metadata.values().copied().collect()
        };
        let &(_, first_align) = tail_layouts.first()?;
        let align_is_constant = tail_layouts.iter().all(|&(_, align)| align == first_align);
        let align = if align_is_constant {
            Some(first_align.max(layout.align_of_head() as u64))
        } else {
            None
        };
        let &(first_size, _) = tail_layouts.first()?;
        let size = if tail_layouts.iter().all(|&(size, _)| size == first_size) {
            let align = align?;
            let head_size = layout.size_of_head();
            let tail_size = usize::try_from(first_size).ok()?;
            let align = usize::try_from(align).ok()?;
            let unaligned = head_size.checked_add(tail_size)?;
            let rounded = if align <= 1 {
                unaligned
            } else {
                unaligned.checked_add(align - 1)?.checked_div(align)?.checked_mul(align)?
            };
            Some(rounded)
        } else {
            None
        };

        debug!(
            ?ty,
            ?size,
            ?align,
            candidate_count = tail_layouts.len(),
            "resolved dyn-tail layout from vtable metadata"
        );
        Some((size, align))
    }
    /// Recover exact layout for repr-SIMD ADTs via rustc's internal layout query.
    ///
    /// Stable `ty.layout()` can fail for concrete repr-SIMD newtypes even though
    /// rustc still has a precise vector layout for codegen. Falling back to the
    /// inner array field is unsound because repr-SIMD rounds size/alignment up
    /// to the target vector ABI (for example `[u8; 10]` becomes size/alignment
    /// 16 on arm64). Use the internal query only for repr-SIMD ADTs when the
    /// stable layout path above could not resolve them.
    pub(super) fn resolve_repr_simd_layout(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<(usize, u64)> {
        let TyKind::RigidTy(RigidTy::Adt(_, _)) = ty.kind() else {
            return None;
        };
        let internal_ty = rustc_internal::internal(self.tcx, ty);
        if !internal_ty.is_simd() {
            return None;
        }
        // Part of #3942: Bail out only for unresolved type/const params.
        // Lifetime-only params do not affect repr-simd layout and should still
        // be allowed through rustc layout queries.
        if ty_has_unresolved_non_region_params(ty) {
            return None;
        }

        let layout = self
            .tcx
            .layout_of(TypingEnv::fully_monomorphized().as_query_input(internal_ty))
            .ok()?;
        let size = usize::try_from(layout.size.bytes()).ok()?;
        let align = layout.align.abi.bytes();
        debug!(?ty, size, align, "resolved repr-simd layout from internal rustc query");
        Some((size, align))
    }

    /// Gets the byte offset of a field within a type.
    ///
    /// Uses Rust's type layout information to determine field positions.
    /// Returns `None` if layout is unavailable — callers must handle
    /// the missing offset rather than guessing (#2315).
    pub(in crate::codegen_ay::chc) fn get_field_offset(
        &mut self,
        ty: rustc_public::ty::Ty,
        field_idx: usize,
    ) -> Option<u64> {
        // Part of #3942: Bail out only for unresolved type/const params.
        // Lifetime-only params are layout-transparent.
        if ty_has_unresolved_non_region_params(ty) {
            return None;
        }
        // Use proper layout from rustc when available (#901 done)
        if let Ok(layout) = ty.layout() {
            // Layout exists - use FieldsShape::Arbitrary offsets if available
            if let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields
                && let Some(off) = offsets.get(field_idx)
            {
                return Some(off.bytes() as u64);
            }
        }

        // A field projection on a THIN reference/raw pointer can only mean a
        // field of its pointee: thin pointers have no fields of their own
        // (FieldsShape::Primitive), so the direct-layout branch above never
        // resolves them and they previously fell to the demoting unknown-type
        // fallback (the fc-interior-mut `old()`-snapshot shape: a contract
        // closure's captured `&Struct` queried with the STRUCT's field index).
        // Peel and recurse for the pointee's precise layout offset. Guarded to
        // sized-ADT pointees whose ref layout resolved as field-less: WIDE
        // pointers keep their own (data, meta) Arbitrary layout and resolve in
        // the direct branch above; unresolvable layouts keep the fail-closed
        // None.
        if let TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) =
            ty.kind()
            && matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Adt(..)))
            && let Ok(layout) = ty.layout()
            && !matches!(layout.shape().fields, rustc_public::abi::FieldsShape::Arbitrary { .. })
        {
            debug!(?ty, field_idx, "thin-pointer field offset: peeling to pointee layout");
            return self.get_field_offset(pointee, field_idx);
        }

        // Part of #3589/#3975: For unsized ADTs with a dyn-trait tail,
        // normalize to the concrete tail type to recover field offsets.
        let concrete_ty = self.normalize_unique_dyn_tail_ty(ty);
        if concrete_ty != ty {
            if let Ok(concrete_layout) = concrete_ty.layout() {
                if let rustc_public::abi::FieldsShape::Arbitrary { offsets } =
                    concrete_layout.shape().fields
                    && let Some(off) = offsets.get(field_idx)
                {
                    debug!(
                        ?ty,
                        ?concrete_ty,
                        field_idx,
                        offset = off.bytes(),
                        "resolved dyn-tail field offset from MIR coercion (#3589/#3975)"
                    );
                    return Some(off.bytes() as u64);
                }
            }
        }

        if let Some(offset) = self.resolve_unsized_slice_tail_field_offset(ty, field_idx) {
            return Some(offset);
        }

        // Fallback: heuristic-based offset computation for types without layout
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _args))
                if def.kind() == rustc_public::ty::AdtKind::Union =>
            {
                // Union fields all start at offset 0. Common case: MaybeUninit<T>
                // where ty.layout() fails but offset is always 0 for all fields.
                // Part of #3464: eliminate spurious record_fallback() for union ADTs.
                debug!(?ty, field_idx, "Union ADT: all fields at offset 0");
                Some(0)
            }
            TyKind::RigidTy(RigidTy::Adt(_def, _args)) => {
                // ADT without layout: return None instead of guessing field_idx * 8.
                // Callers must handle the missing offset (#2315).
                warn!(?ty, field_idx, "No layout available for ADT field offset");
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                // Returning None causes callers to skip stores → memory identity.
                self.record_fallback();
                None
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => {
                // Layout-less tuple offset computation (sum of prior field sizes)
                // is unsound because tuple layout may include alignment padding.
                // Fail closed instead of guessing (#2315).
                warn!(?ty, field_idx, "No layout available for tuple field offset");
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                self.record_fallback();
                None
            }
            _ => {
                // external enum: TyKind
                // Unknown type: return None instead of guessing.
                // Heuristic offset (field_idx * 8) was unsound for packed structs,
                // repr(C) with alignment, and fields smaller than 8 bytes (#2315).
                warn!(?ty, field_idx, "No layout available for field offset (unknown type)");
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                self.record_fallback();
                None
            }
        }
    }

    /// Gets the byte offset of a field within an enum variant's layout.
    ///
    /// For multi-variant enums, field offsets differ per variant. The `variant_idx`
    /// selects which variant's `FieldsShape` to query.
    /// Part of #3041: Category B fix — variant-aware field offsets for enum address calculation.
    /// Constant byte offset added by a place's projections AFTER a leading
    /// `Deref`, or `None` when it cannot be proved constant.
    ///
    /// `known_alloc_ids` records an object id with an implicit offset of ZERO,
    /// so a caller may only inherit provenance across `&(*base).f` when `f`
    /// genuinely sits at offset 0. Everything this walk cannot fold — an
    /// `Index`, a `Subslice`, an unknown layout — returns `None` so the caller
    /// fails closed rather than recording a pointer the map cannot express.
    pub(in crate::codegen_ay::chc) fn constant_projection_byte_offset(
        &mut self,
        place: &rustc_public::mir::Place,
    ) -> Option<u64> {
        use rustc_public::mir::ProjectionElem;

        let mut current_ty = self.body.locals().get(place.local)?.ty;
        let mut offset: u64 = 0;
        let mut variant: Option<usize> = None;

        for (idx, elem) in place.projection.iter().enumerate() {
            match elem {
                ProjectionElem::Deref => {
                    if idx != 0 {
                        // A second dereference reads through a POINTER whose
                        // value this walk does not have. Nothing after it can
                        // be folded into a byte offset from the original base.
                        return None;
                    }
                    current_ty = crate::codegen_ay::chc::ChcCtx::deref_pointee_ty(current_ty)?;
                    variant = None;
                }
                ProjectionElem::Field(field_idx, field_ty) => {
                    let this = match variant.take() {
                        Some(v) => self.get_variant_field_offset(current_ty, v, *field_idx)?,
                        None => self.get_field_offset(current_ty, *field_idx)?,
                    };
                    offset = offset.checked_add(this)?;
                    current_ty = *field_ty;
                }
                ProjectionElem::Downcast(v) => {
                    variant = Some(crate::rustc_public_bridge::IndexedVal::to_index(v));
                }
                // Layout-transparent.
                ProjectionElem::OpaqueCast(ty) => current_ty = *ty,
                // Data-dependent or unsupported: not a constant offset.
                _ => return None,
            }
        }
        Some(offset)
    }

    pub(in crate::codegen_ay::chc) fn get_variant_field_offset(
        &mut self,
        ty: rustc_public::ty::Ty,
        variant_idx: usize,
        field_idx: usize,
    ) -> Option<u64> {
        // Part of #3942: Bail out only for unresolved type/const params.
        if ty_has_unresolved_non_region_params(ty) {
            return None;
        }
        let Ok(layout) = ty.layout() else {
            warn!(?ty, variant_idx, field_idx, "No layout for variant field offset");
            // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
            self.record_fallback();
            return None;
        };
        let shape = layout.shape();
        match &shape.variants {
            VariantsShape::Multiple { variants, .. } => {
                if let Some(variant_layout) = variants.get(variant_idx) {
                    if let rustc_public::abi::FieldsShape::Arbitrary { offsets } =
                        &variant_layout.fields
                    {
                        if let Some(off) = offsets.get(field_idx) {
                            debug!(
                                variant_idx,
                                field_idx,
                                offset = off.bytes(),
                                "CHC: variant field offset from layout"
                            );
                            return Some(off.bytes() as u64);
                        }
                    }
                    warn!(
                        ?ty,
                        variant_idx,
                        field_idx,
                        "Variant layout fields not Arbitrary or field index out of bounds"
                    );
                } else {
                    warn!(?ty, variant_idx, "Variant index out of range");
                }
            }
            VariantsShape::Single { .. } => {
                // Single-variant ADT (struct-like): fall through to regular field offset
                return self.get_field_offset(ty, field_idx);
            }
            VariantsShape::Empty => {
                warn!(?ty, "Empty variants shape — uninhabited type");
            }
        }
        // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
        self.record_fallback();
        None
    }

    // get_type_size, get_type_align, get_array_element_ty, get_array_length
    // moved to memory_impl_layout_query.rs per #4206.
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref-resolution cascade for MIR place translation.
//!
//! Extracted from `codegen_expr_deref.rs` per #4125 (500 LOC threshold).
//! Contains the resolution strategies that attempt to resolve `*ptr` dereferences
//! before the main projection loop runs:
//! - ref-target resolution (concrete value flow for `&`-backed derefs)
//! - coroutine deref resolution (coroutine state payloads)
//! - const-ref resolution (promoted constant references)
//! - argument-ref resolution (function parameter references)
//! - static-ref resolution (static pointer locals)
//! - known-alloc heap-backed derefs below Mem level
//! - track-level guards (Reg/Ptr bail-out)
//!
//! The projection loop that processes Field/Index/Deref/Downcast elements
//! remains in `codegen_expr_deref.rs`.

mod codegen_expr_deref_resolve_const_array;

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, unflatten_bitvec_to_datatype,
};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_stmt_projection::FieldProjection;
use super::codegen_types::CodegenTypes;

/// Result of the deref-resolution cascade.
///
/// The cascade attempts multiple strategies to resolve a `*ptr` dereference.
/// If one succeeds with a final answer, the caller should return that expression
/// directly. If the cascade exhausts its strategies without resolving, the
/// caller should fall through to the projection loop.
pub(in crate::codegen_ay::chc) enum DerefCascadeResult {
    /// Cascade fully resolved the deref — return this expression immediately.
    Resolved(Expr),
    /// Cascade did not resolve — proceed to the projection loop.
    Unresolved,
    /// Cascade determined translation should bail (return None to the caller).
    Bail,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve `*_ref` reads of coroutine state through the pre-registered
    /// coroutine root expression instead of falling back to a generic memory load.
    ///
    /// This mirrors the coroutine-specific `Discriminant(*_ref)` bridge:
    /// `ref_targets` handles direct referent locals, while `coroutine_root_map`
    /// and arg-pointee state handle wrapper-propagated and `Pin<&mut _>` cases.
    pub(in crate::codegen_ay::chc) fn resolve_coroutine_deref_place(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return None;
        }

        let pointee_ty = Self::deref_pointee_ty(self.body.locals()[local_idx].ty)?;
        if !matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            return None;
        }

        let root_expr = if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx)
            && ref_target.projections.is_empty()
            && ref_target.local != local_idx
            && let Some(root_expr) =
                self.resolve_coroutine_root_expr(ref_target.local, modified_locals)
        {
            debug!(
                ref_local = local_idx,
                target_local = ref_target.local,
                "CHC: resolved coroutine deref via referent local"
            );
            root_expr
        } else if let Some(root_expr) = self.resolve_coroutine_root_expr(local_idx, modified_locals)
        {
            debug!(
                ref_local = local_idx,
                "CHC: resolved coroutine deref via coroutine_root_map/arg-pointee"
            );
            root_expr
        } else {
            return None;
        };

        if place.projection.len() == 1 {
            return Some(root_expr);
        }

        let result = self.translate_projection_chain_from_root(
            &place.projection[1..],
            root_expr,
            pointee_ty,
            modified_locals,
        );
        if result.is_some() {
            debug!(
                ref_local = local_idx,
                projection = ?place.projection,
                "CHC: translated coroutine deref payload via coroutine root bridge"
            );
        }
        result
    }

    /// Run the deref-resolution cascade for a place that contains Deref projections.
    ///
    /// Tries, in order:
    /// 1. Ref-target resolution (`try_resolve_deref_via_ref_targets`)
    /// 2. Coroutine deref resolution (`resolve_coroutine_deref_place`)
    /// 3. Const-ref values (`const_ref_values` / `const_ref_discriminants`)
    /// 4. Argument-ref resolution (`resolve_arg_ref_deref`)
    /// 5. Static-ref resolution (`resolve_static_ref_deref`)
    /// 6. Known-alloc heap-backed deref below Mem level
    /// 7. Track-level guard (bail at Reg/Ptr if no resolution found)
    ///
    /// Returns `Resolved(expr)` if the entire place was resolved,
    /// `Unresolved` to continue to the projection loop, or `Bail` to return None.
    pub(in crate::codegen_ay::chc) fn try_resolve_deref_cascade(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> DerefCascadeResult {
        // Soundness: every raw-pointer deref read carries a `ptr != 0`
        // obligation, emitted BEFORE any resolution strategy runs so it fires
        // for Resolved/Unresolved/Bail outcomes alike. A null raw deref must
        // produce a violated obligation (CTREX), not a silent PROOF via an
        // unconstrained memory load or a sound fallback.
        // See expr/codegen_expr_deref_null_check.rs.
        self.emit_raw_ptr_null_deref_check(place, modified_locals);

        // Prefer ref-target resolution for reference-backed derefs so reads like
        // `*ref` keep concrete value flow. Raw pointers at Mem level stay on the
        // explicit memory path (guarded inside try_resolve_deref_via_ref_targets).
        if let Some(resolved) =
            self.try_resolve_deref_via_ref_targets(place, local_idx, modified_locals)
        {
            return DerefCascadeResult::Resolved(resolved);
        }

        if let Some(result) = self.resolve_coroutine_deref_place(place, local_idx, modified_locals)
        {
            return DerefCascadeResult::Resolved(result);
        }

        // Part of #1739: Prefer declaration-pass constant-reference facts for
        // direct `*_ref_local` reads at all track levels (including Mem).
        // This avoids routing promoted constants through unconstrained pointer
        // addresses when `_ref_local = const &...` assignment fallback marks the
        // local modified.
        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            if let Some(result) =
                self.try_resolve_const_ref_deref(place, local_idx, modified_locals)
            {
                return result;
            }
            if place.projection.len() == 1 {
                if let Some(discr) = self.ref_resolution.const_ref_discriminants.get(&local_idx) {
                    debug!(local_idx, discr, "CHC: resolved deref via const_ref_discriminants");
                    return DerefCascadeResult::Resolved(Expr::bitvec_const(*discr as u128, 32));
                }
            }
        }

        // Part of #2844: Resolve deref through argument reference locals.
        // Helpers in codegen_expr_deref_field.rs (Part of #2884).
        if let Some(result) = self.resolve_arg_ref_deref(place, local_idx, modified_locals) {
            return DerefCascadeResult::Resolved(result);
        }

        // Part of #428: Resolve deref through static pointer locals.
        // Helpers in codegen_expr_deref_static.rs (Part of #2884).
        if let Some(result) = self.resolve_static_ref_deref(place, local_idx, modified_locals) {
            return DerefCascadeResult::Resolved(result);
        }

        // Part of #3871: Heap-backed derefs with a concrete alloc_id can safely
        // reuse the existing memory-load path even below Mem tracking. This
        // preserves Box/Rc wrapper payload loads such as `copy (*_23)` after
        // the pointer local has already been tied to a specific allocation.
        let allow_known_alloc_deref_below_mem = self.track_level < ChcTrackLevel::Mem
            && matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && self.known_alloc_ids.contains_key(&local_idx);

        // At Reg/Ptr, unresolved derefs cannot be modeled without the memory path.
        // Index-only paths remain supported below.
        if self.track_level < ChcTrackLevel::Mem && !allow_known_alloc_deref_below_mem {
            // Part of #2310: At Ptr level, emit obj_valid check for raw pointer
            // dereferences even though the load value is unconstrained.
            if self.track_level >= ChcTrackLevel::Ptr {
                self.emit_ptr_obj_valid_check(local_idx, modified_locals);
            }
            // Part of #3447: Record that the deref load is unconstrained due to
            // track level below Mem. The self-loop handler also calls
            // record_sound_fallback(), but this counter distinguishes
            // "deref below mem level" from other deref-load failures.
            self.diagnostics.place_translation_drop.inc();
            record_translation_drop_site_reason_for_fn(&self.fn_name, "deref_below_mem_level");
            debug!(
                ?place,
                "CHC: Deref projection at {:?} level - returning None", self.track_level
            );
            return DerefCascadeResult::Bail;
        }
        if allow_known_alloc_deref_below_mem {
            debug!(
                local_idx,
                obj_id = ?self.known_alloc_ids.get(&local_idx),
                "CHC: using known-alloc deref memory path below Mem level (#3871)"
            );
        }

        DerefCascadeResult::Unresolved
    }

    /// Try to resolve a deref place via `const_ref_values`.
    ///
    /// Handles direct `*_ref` reads and `(*_ref).field(+index)` chains through
    /// const-ref values from promoted constants and byte string literals.
    ///
    /// Returns `Some(DerefCascadeResult)` if the const-ref path matched
    /// (either resolving or falling through), `None` if const-ref is not applicable.
    fn try_resolve_const_ref_deref(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<DerefCascadeResult> {
        let val = self.ref_resolution.const_ref_values.get(&local_idx)?.clone();

        if place.projection.len() == 1 {
            // Part of #4022 D3: When the const_ref_values entry is
            // Array-sorted (e.g., `*ptr` where ptr points to a const
            // array literal), apply subslice_offset selection if the
            // pointer was offset via ptr.add/offset. Without this,
            // `*offset(ptr, N)` returns the whole Array -> sort mismatch.
            if val.sort().is_array() {
                let offset_expr =
                    self.ref_resolution.subslice_offset.get(&local_idx).cloned().or_else(|| {
                        let local_ty = self.body.locals().get(local_idx)?.ty;
                        let pointee_ty = Self::deref_pointee_ty(local_ty)?;
                        if matches!(
                            pointee_ty.kind(),
                            TyKind::RigidTy(RigidTy::Array(..) | RigidTy::Slice(_))
                        ) {
                            None
                        } else {
                            Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
                        }
                    });
                if let Some(offset_expr) = offset_expr {
                    let idx = coerce_bitvec_width_safe(
                        offset_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    // Soundness: `val.select(idx)` reads directly from the
                    // promoted-constant element array. The array is a logical
                    // `const_array` with a default element beyond the seeded
                    // `[0, len)` range, so an out-of-object read (e.g.
                    // `*offset(str_ptr, len)`) silently returns the default and
                    // proves SAFE. When the subslice length is known, emit an
                    // `idx < len` memory-safety obligation so a one-past-end
                    // deref of a str/slice-constant pointer produces a CTREX. A
                    // valid in-bounds read (idx < len) still resolves to the
                    // real element, so correctly-bounded slice/str reads keep
                    // verifying. (offset-u8-fail false proof.)
                    if let Some(len_expr) =
                        self.ref_resolution.subslice_len.get(&local_idx).cloned()
                    {
                        let len_expr = coerce_bitvec_width_safe(
                            len_expr,
                            POINTER_WIDTH,
                            SignExtension::ZeroExtend,
                        );
                        self.heap_state.pending_checks.push(idx.clone().bvult(len_expr));
                    }
                    debug!(
                        local_idx,
                        "CHC: applying subslice_offset to const_ref_values Array (#4022)"
                    );
                    return Some(DerefCascadeResult::Resolved(val.select(idx)));
                }
                // No subslice_offset -- reject so memory load path
                // can resolve via typed memory array select.
                debug!(
                    local_idx,
                    "CHC: rejecting Array const_ref_values without subslice_offset (#4022)"
                );
                // Fall through (don't return) -- let memory load handle it.
            } else {
                debug!(local_idx, "CHC: resolved deref via const_ref_values");
                return Some(DerefCascadeResult::Resolved(val));
            }
        }

        // Part of #3698: Handle Deref+Field(+Index) chains through const_ref_values.
        // Pattern: (*_ref).field or (*_ref).field[idx] where _ref has known
        // const data from a byte string literal or transmute propagation.
        // Apply remaining field selections (and optional trailing Index) to
        // the const value.
        let remaining = &place.projection[1..];
        if let Some(result) =
            self.try_resolve_const_array_deref_index(local_idx, &val, remaining, modified_locals)
        {
            return Some(DerefCascadeResult::Resolved(result));
        }
        // Split remaining into leading Field projections and optional trailing Index.
        let field_count =
            remaining.iter().take_while(|p| matches!(p, ProjectionElem::Field(..))).count();
        let trailing = &remaining[field_count..];
        let trailing_index = match trailing {
            [ProjectionElem::Index(idx_local)] => Some(*idx_local),
            [] => None,
            _ => None, // Unsupported trailing projections -- skip
        };
        // Handle Deref+Index+Field(s) pattern: (*_ref)[idx].field
        // This is the dual of the Deref+Field+Index pattern below.
        // Occurs when indexing a const slice of tuples: point[i].0
        // where _ref points to a const `&[(u8, u32)]`.
        if field_count == 0 {
            if let [ProjectionElem::Index(idx_local), rest @ ..] = remaining {
                let trailing_field_count =
                    rest.iter().take_while(|p| matches!(p, ProjectionElem::Field(..))).count();
                if trailing_field_count > 0 && trailing_field_count == rest.len() {
                    if val.sort().is_array() {
                        if let Some(idx_expr) = self.resolve_local_expr(*idx_local, modified_locals)
                        {
                            let idx_expr = coerce_bitvec_width_safe(
                                idx_expr,
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            );
                            let element = val.clone().select(idx_expr);
                            let field_selections: Vec<FieldProjection> = rest
                                .iter()
                                .filter_map(|p| {
                                    if let ProjectionElem::Field(idx, ty) = p {
                                        Some(FieldProjection {
                                            field_idx: *idx,
                                            cons_idx: None,
                                            field_ty: Some(*ty),
                                        })
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            if let Some(result) =
                                Self::apply_field_selections(element.clone(), &field_selections)
                            {
                                debug!(
                                    local_idx,
                                    n_fields = field_selections.len(),
                                    "CHC: resolved deref+index+field via const_ref_values (DT path)"
                                );
                                return Some(DerefCascadeResult::Resolved(result));
                            }
                            // Fallback: Array elements may be BV-encoded tuples
                            // (flattened by flatten_dt_array_element during type
                            // translation). Reconstruct the Datatype from the flat
                            // BV so apply_field_selections can project fields.
                            if element.sort().is_bitvec() {
                                if let Some(dt_sort) = self.derive_slice_element_dt_sort(local_idx)
                                {
                                    if let Some(unflat) =
                                        unflatten_bitvec_to_datatype(&element, &dt_sort)
                                    {
                                        if let Some(result) =
                                            Self::apply_field_selections(unflat, &field_selections)
                                        {
                                            debug!(
                                                local_idx,
                                                n_fields = field_selections.len(),
                                                "CHC: resolved deref+index+field via const_ref_values (BV unflatten)"
                                            );
                                            return Some(DerefCascadeResult::Resolved(result));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        let all_recognized = field_count > 0 && (trailing.is_empty() || trailing_index.is_some());
        if all_recognized {
            let field_projs = &remaining[..field_count];
            let field_selections: Vec<FieldProjection> = field_projs
                .iter()
                .filter_map(|p| {
                    if let ProjectionElem::Field(idx, ty) = p {
                        Some(FieldProjection {
                            field_idx: *idx,
                            cons_idx: None,
                            field_ty: Some(*ty),
                        })
                    } else {
                        None
                    }
                })
                .collect();
            let mut resolved = Self::apply_field_selections(val.clone(), &field_selections);
            // Field selection failed for custom DST identity case (Part of #3698).
            if resolved.is_none() && field_count == 1 {
                if let ProjectionElem::Field(0, field_ty) = &field_projs[0] {
                    let field_sort_matches =
                        Self::translate_ty(*field_ty).map_or(false, |fs| fs == *val.sort());
                    if field_sort_matches {
                        resolved = Some(val.clone());
                    }
                }
            }
            if let Some(mut result) = resolved {
                // Part of #3698: Apply trailing Index projection if present.
                // Pattern: (*_ref).inner[idx] where inner: [u8] and the
                // const value is an Array-sorted expression from a byte literal.
                if let Some(idx_local) = trailing_index {
                    if result.sort().is_array() {
                        if let Some(idx_expr) = self.resolve_local_expr(idx_local, modified_locals)
                        {
                            let idx_expr = coerce_bitvec_width_safe(
                                idx_expr,
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            );
                            result = result.select(idx_expr);
                            debug!(
                                local_idx,
                                ?idx_local,
                                "CHC: resolved deref+field+index via const_ref_values (Part of #3698)"
                            );
                        } else {
                            debug!(
                                local_idx,
                                ?idx_local,
                                "CHC: const_ref_values index local unresolved, falling through"
                            );
                            // Fall through to main projection loop
                        }
                    } else {
                        debug!(
                            local_idx,
                            sort = ?result.sort(),
                            "CHC: const_ref_values result not array-sorted for Index, falling through"
                        );
                        // Fall through -- non-array can't be indexed here
                    }
                }
                if trailing_index.is_none() || result.sort() != val.sort() {
                    // Return if no trailing index, or if we successfully applied it
                    // (sort changed from Array to element type).
                    debug!(
                        local_idx,
                        n_fields = field_selections.len(),
                        has_index = trailing_index.is_some(),
                        "CHC: resolved deref+field(+index) via const_ref_values (Part of #3698)"
                    );
                    return Some(DerefCascadeResult::Resolved(result));
                }
            }
        }

        None
    }

    /// Derive the Datatype sort for the element type of a slice/array that
    /// a local points to.
    ///
    /// For a local of type `&[(u8, u32)]`, this returns the Datatype sort for
    /// `(u8, u32)`. Used when array elements are BV-encoded (via
    /// `flatten_dt_array_element`) and need to be unflattened for field projection.
    fn derive_slice_element_dt_sort(&self, local_idx: usize) -> Option<ay_bindings::Sort> {
        let local_ty = self.body.locals()[local_idx].ty;
        let pointee_ty = Self::deref_pointee_ty(local_ty)?;
        let elem_ty = match pointee_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => elem_ty,
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => elem_ty,
            _ => return None,
        };
        // translate_ty for tuples returns a Datatype sort (not flattened).
        // This is the sort that unflatten_bitvec_to_datatype needs.
        let sort = Self::translate_ty(elem_ty)?;
        if sort.is_datatype() { Some(sort) } else { None }
    }
}

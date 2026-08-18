// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Projection-chain walkers for MIR place translation.
//!
//! `translate_projection_chain_from_root` walks a sequence of Field, Index,
//! ConstantIndex, Downcast, and Subslice projections starting from a known
//! root expression. Unlike `translate_place_with_deref`, this does NOT handle
//! Deref projections or memory loads — it operates purely on expression trees.
//!
//! `walk_deref_projection_loop` owns the Deref-aware projection loop extracted
//! from `codegen_expr_deref.rs`, including Array post-check handling after
//! Deref chains.
//!
//! Used by `codegen_expr_deref_resolve.rs` for ref-target resolution paths
//! where the base has already been resolved to a concrete AY expression.
//!
//! Extracted from `codegen_expr_deref.rs` per #4125 (500 LOC threshold).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use crate::codegen_ay::chc::dyn_coercion;
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_expr_deref_field_offset::DerefFieldOffsetResult;
use super::codegen_stmt_projection::FieldProjection;
use super::constant_index_offset;

#[derive(Clone, Copy)]
pub(in crate::codegen_ay::chc) enum ArrayProjectionKind {
    Index { local_idx: usize, index_local: usize },
    ConstantIndex { local_idx: usize, actual_offset: u64, from_end: bool },
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn translate_projection_chain_from_root(
        &mut self,
        projections: &[ProjectionElem],
        root: Expr,
        root_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let mut current = root;
        let mut current_ty = Some(root_ty);
        let mut active_variant: Option<usize> = None;

        for proj in projections {
            match proj {
                ProjectionElem::Downcast(variant_idx) => {
                    active_variant = Some(variant_idx.to_index());
                }
                ProjectionElem::Field(field_idx, field_ty) => {
                    let selections = vec![FieldProjection {
                        field_idx: *field_idx,
                        cons_idx: active_variant.take(),
                        field_ty: Some(*field_ty),
                    }];
                    current = Self::apply_field_selections(current, &selections)?;
                    current_ty = Some(*field_ty);
                }
                ProjectionElem::Index(index_local) => {
                    let index_expr = self.resolve_local_expr(*index_local, modified_locals)?;
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    let actual_offset = constant_index_offset(*offset, *min_length, *from_end);
                    let index_expr = Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    let source_ty = current_ty?;
                    current =
                        self.build_subslice_expr(&current, source_ty, *from, *to, *from_end)?;
                    active_variant = None;
                }
                _ => return None,
            }
        }

        Some(current)
    }

    pub(in crate::codegen_ay::chc) fn array_select_with_bounds_check(
        &mut self,
        current_expr: Expr,
        current_ty: rustc_public::ty::Ty,
        index_expr: Expr,
        projection_kind: ArrayProjectionKind,
    ) -> Option<(Expr, rustc_public::ty::Ty)> {
        // Part of #1888: Emit bounds check for array indexing.
        if let Some(array_len) = self.get_array_length(current_ty) {
            let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
            let bounds_check = index_expr.clone().bvult(len_expr);
            self.heap_state.pending_checks.push(bounds_check);
            match projection_kind {
                ArrayProjectionKind::Index { .. } => {
                    debug!(
                        array_len,
                        "CHC: translate_place_with_deref - emitted bounds check (Part of #1888)"
                    );
                }
                ArrayProjectionKind::ConstantIndex { actual_offset, from_end, .. } => {
                    debug!(
                        actual_offset,
                        array_len,
                        from_end,
                        "CHC: translate_place_with_deref - emitted ConstantIndex bounds check"
                    );
                }
            }
        }

        if !current_expr.sort().is_array() {
            // BV-rooted scalar array — e.g. a union field `FOO.a` coerced from
            // the union's BV root by the deref chain's union-field arm. Element
            // extract instead of dropping (mirrors translate_place_field_index's
            // bv_array_index_select wiring); the #1888 bounds check above was
            // already emitted from `current_ty`, so OOB stays caught.
            if let Some((val, Some(elem_ty))) =
                self.bv_array_index_select(&current_expr, Some(current_ty), &index_expr)
            {
                let val = self.try_unflatten_bv_to_datatype(val, elem_ty);
                return Some((val, elem_ty));
            }
            // Part of #3447: Non-array sort at Index/ConstantIndex projection.
            self.diagnostics.place_translation_drop.inc();
            match projection_kind {
                ArrayProjectionKind::Index { local_idx, index_local } => {
                    record_translation_drop_site_reason_for_fn(
                        &self.fn_name,
                        "deref_index_non_array",
                    );
                    warn!(
                        sort = ?current_expr.sort(),
                        ?current_ty,
                        local_idx,
                        ?index_local,
                        "CHC: Index projection on non-array expression in deref chain"
                    );
                }
                ArrayProjectionKind::ConstantIndex { local_idx, actual_offset, .. } => {
                    record_translation_drop_site_reason_for_fn(
                        &self.fn_name,
                        "deref_const_index_non_array",
                    );
                    warn!(
                        sort = ?current_expr.sort(),
                        ?current_ty,
                        local_idx,
                        actual_offset,
                        "CHC: ConstantIndex projection on non-array expression in deref chain"
                    );
                }
            }
            return None;
        }

        let current_expr = self
            .finite_fixed_array_select(&current_expr, &index_expr, current_ty)
            .unwrap_or_else(|| current_expr.select(index_expr));
        let current_ty = match self.get_array_element_ty(current_ty) {
            Some(ty) => ty,
            None => {
                // Part of #3447: Array element type unknown at Index/ConstantIndex.
                match projection_kind {
                    ArrayProjectionKind::Index { .. } => {
                        self.record_aggregate_gap("deref_array_element_ty_unknown_index");
                        debug!(?current_ty, "CHC: get_array_element_ty returned None at Index");
                    }
                    ArrayProjectionKind::ConstantIndex { .. } => {
                        self.record_aggregate_gap("deref_array_element_ty_unknown_const_index");
                        debug!(
                            ?current_ty,
                            "CHC: get_array_element_ty returned None at ConstantIndex"
                        );
                    }
                }
                return None;
            }
        };

        // Part of #3296: Unflatten BV->DT after array select if element was flattened.
        let current_expr = self.try_unflatten_bv_to_datatype(current_expr, current_ty);
        Some((current_expr, current_ty))
    }

    pub(in crate::codegen_ay::chc) fn walk_deref_projection_loop(
        &mut self,
        place: &Place,
        local_idx: usize,
        current_expr: Expr,
        current_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
        has_deref: bool,
    ) -> Option<Expr> {
        let mut current_expr = current_expr;
        let mut current_ty = current_ty;

        // Track Downcast variant index for subsequent Field projections.
        // Pattern: Downcast(variant_idx) sets this, Field consumes it as cons_idx.
        // Without this, enum field access after Deref uses cons_idx: None, which
        // fails for multi-constructor datatypes like Option/Result. (Part of #1739)
        let mut active_variant: Option<usize> = None;

        // Process projections with special handling for Deref+Field pattern
        let mut proj_idx = 0;
        while proj_idx < place.projection.len() {
            let proj = &place.projection[proj_idx];
            match proj {
                ProjectionElem::Deref => {
                    // Some lowered paths use marker projections like `(*x).0` where
                    // `x` is already scalar (non-pointer). Treat this Deref as no-op
                    // so the following Field(0, T) marker selection can proceed.
                    if matches!(
                        place.projection.get(proj_idx + 1),
                        Some(ProjectionElem::Field(0, field_ty)) if *field_ty == current_ty
                    ) {
                        debug!(
                            local_idx,
                            ?current_ty,
                            "CHC: treating scalar marker Deref as no-op in place translation"
                        );
                        proj_idx += 1;
                        continue;
                    }

                    // Part of #3608/#4179: prefer concrete stack/heap provenance
                    // for store-to-load forwarding before falling back to state vars.
                    if proj_idx == 0
                        && let Some(addr) = self.known_deref_base_addr_expr(local_idx)
                    {
                        current_expr = addr;
                    }

                    if let Some(ptr_expr) = dyn_coercion::extract_pointer_expr(&current_expr) {
                        // `current_expr` is the projection walker's running term
                        // and holds VALUES on other iterations, so the slot
                        // cannot be typed; the tag ends at this crossing.
                        current_expr = ptr_expr.into_expr();
                    }

                    // current_expr is a pointer, check for following Field projections
                    let pointee_ty = match Self::deref_pointee_ty(current_ty) {
                        Some(ty) => ty,
                        None => {
                            // Part of #3447: Deref on unrecognized pointer type.
                            self.record_aggregate_gap("deref_pointee_ty_none");
                            debug!(?current_ty, "CHC: deref_pointee_ty returned None");
                            return None;
                        }
                    };

                    // THE address-of for this whole arm, minted once.
                    //
                    // Evidence, and it is not a width test: `deref_pointee_ty`
                    // just succeeded, so `current_ty` is a `&T`/`&mut T`/`*const
                    // T`/`*mut T`/`Box<T>` — the MIR type says this term is a
                    // pointer, and we are standing on the `Deref` that consumes
                    // it. Everything below this line already treated it as an
                    // address (the provenance bound checks, the field-offset
                    // byte arithmetic, the whole-struct load); the tag states
                    // that shared premise once instead of leaving each consumer
                    // to re-derive it from `bitvec_width()`.
                    //
                    // The running `current_expr` slot itself stays untyped: it
                    // carries VALUES on the Field/Index/Downcast iterations, and
                    // the reassignment at the end of this arm puts a loaded
                    // datum back into it. The `Loc` lives exactly as long as the
                    // fact does.
                    let deref_loc = Loc::of_address(current_expr.clone());

                    // Offset-deref stack-provenance keystone: for a RAW-pointer
                    // base local whose allocation resolves via the fail-closed
                    // single-assignment walk, emit the strict access bound that
                    // `heap_access_checks` fail-opens on (opaque obj_id lane).
                    // Catches one-past-end derefs of offset-derived stack
                    // pointers (`*arr.as_ptr().add(len)`).
                    if proj_idx == 0
                        && matches!(
                            current_ty.kind(),
                            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(
                                ..
                            ))
                        )
                    {
                        let checks = self.provenance_deref_bound_checks(
                            deref_loc.as_expr(),
                            pointee_ty,
                            local_idx,
                        );
                        self.heap_state.pending_checks.extend(checks);
                    }

                    // Part of #1161: Look ahead for Field projections after Deref.
                    // Delegated to try_deref_field_offset_load (codegen_expr_deref_field_offset.rs).
                    let remaining_projs = &place.projection[proj_idx + 1..];
                    match self.try_deref_field_offset_load(
                        deref_loc.clone(),
                        pointee_ty,
                        remaining_projs,
                    ) {
                        DerefFieldOffsetResult::Loaded(expr) => {
                            current_expr = expr;
                            break;
                        }
                        DerefFieldOffsetResult::Bail => return None,
                        DerefFieldOffsetResult::NotApplicable => {}
                    }

                    // Part of #4099: Slice Deref+Index look-ahead (unsized [T]).
                    if let super::codegen_expr_deref_slice_index::SliceDerefIndexResult::Resolved {
                        elem_expr, elem_ty,
                    } = self.try_slice_deref_index(
                        place, proj_idx, &current_expr, pointee_ty,
                        modified_locals, local_idx,
                    ) {
                        current_expr = elem_expr;
                        proj_idx += 2;
                        current_ty = elem_ty;
                        active_variant = None;
                        continue;
                    }

                    // Fallback: Load whole struct and extract fields.
                    // Dyn-tail normalization is handled inside load_from_memory (#3974).
                    current_expr = match self.load_from_memory(deref_loc, pointee_ty) {
                        Some(val) => val.into_expr(),
                        None => {
                            // Part of #3447: Fallback whole-struct load failed.
                            self.record_aggregate_gap("deref_whole_struct_load_failed");
                            debug!(?pointee_ty, "CHC: fallback load_from_memory returned None");
                            return None;
                        }
                    };
                    // Unflatten BV back to DT so subsequent Field projections
                    // use datatype_field_select instead of raw BV extraction.
                    // Without this, padded structs (e.g. (u8, u32) stored as BV64)
                    // fail field_idx > 0 extraction.
                    current_expr = self.try_unflatten_bv_to_datatype(current_expr, pointee_ty);
                    current_ty = pointee_ty;
                    active_variant = None; // Reset: Deref breaks Downcast-Field pairing
                }
                ProjectionElem::Field(field_idx, field_ty) => {
                    // Apply field selection with constructor index from preceding Downcast.
                    // For enums (Option, Result), cons_idx selects the variant constructor
                    // before extracting the field. Without this, multi-constructor datatypes
                    // produce wrong values. (Part of #1739, Gap 1)
                    let field_idx_usize: usize = *field_idx;

                    // Part of #4181: Coroutine Datatype field mapping.
                    // MIR Field(N) on a Coroutine means "Nth captured field",
                    // but AY Datatype field 0 is `direct_fields`. Use
                    // coroutine_root_select to navigate correctly.
                    if crate::codegen_ay::types::is_coroutine_root_sort(current_expr.sort()) {
                        current_expr = match crate::codegen_ay::types::coroutine_root_select(
                            current_expr,
                            active_variant.take(),
                            field_idx_usize,
                        ) {
                            Some(expr) => expr,
                            None => {
                                self.record_aggregate_gap("coroutine_root_select_failed");
                                debug!(
                                    field_idx_usize,
                                    "CHC: coroutine_root_select returned None in deref chain"
                                );
                                return None;
                            }
                        };
                        current_ty = *field_ty;
                        active_variant = None;
                        proj_idx += 1;
                        continue;
                    }

                    let selections = vec![FieldProjection {
                        field_idx: field_idx_usize,
                        cons_idx: active_variant,
                        field_ty: Some(*field_ty),
                    }];
                    let field_root = current_expr.clone();
                    current_expr = match Self::apply_field_selections(current_expr, &selections) {
                        Some(expr) => expr,
                        None => {
                            // Union field on a BV root (unions translate to
                            // Sort::bitvec(size*8)): coerce to the field width
                            // instead of bailing — mirrors apply_field_projection's
                            // union arm, so `(*static_ref).field` reads work for
                            // union statics pinned by the zero-fill lane.
                            if let Some(coerced) =
                                Self::union_bv_field_coerce(&field_root, current_ty, *field_ty)
                            {
                                coerced
                            } else {
                                // Part of #3447: Field selection failed in deref chain.
                                self.record_aggregate_gap("deref_field_selection_failed");
                                debug!(
                                    field_idx_usize,
                                    ?field_ty,
                                    "CHC: apply_field_selections returned None in deref chain"
                                );
                                return None;
                            }
                        }
                    };
                    current_ty = *field_ty;
                    active_variant = None;
                }
                ProjectionElem::Index(index_local) => {
                    // Array indexing - get index value and select
                    let index_expr = match self.resolve_local_expr(*index_local, modified_locals) {
                        Some(expr) => expr,
                        None => {
                            // Part of #3447: Index local resolution failed.
                            self.record_aggregate_gap("deref_index_local_resolution_failed");
                            debug!(?index_local, "CHC: resolve_local_expr for index returned None");
                            return None;
                        }
                    };
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    if index_expr.sort().bitvec_width().is_none() {
                        // Part of #3447: Non-BV index expression in deref chain.
                        self.diagnostics.place_translation_drop.inc();
                        record_translation_drop_site_reason_for_fn(
                            &self.fn_name,
                            "deref_non_bv_index",
                        );
                        warn!(?index_expr, "CHC: non-bitvec index expression in deref chain");
                        return None;
                    }

                    let projection_kind =
                        ArrayProjectionKind::Index { local_idx, index_local: *index_local };
                    let (next_expr, next_ty) = match self.array_select_with_bounds_check(
                        current_expr,
                        current_ty,
                        index_expr,
                        projection_kind,
                    ) {
                        Some(result) => result,
                        None => return None,
                    };
                    current_expr = next_expr;
                    current_ty = next_ty;
                    active_variant = None; // Reset: Index breaks Downcast-Field pairing
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    let actual_offset = constant_index_offset(*offset, *min_length, *from_end);
                    let index_expr = Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                    let projection_kind = ArrayProjectionKind::ConstantIndex {
                        local_idx,
                        actual_offset,
                        from_end: *from_end,
                    };
                    let (next_expr, next_ty) = match self.array_select_with_bounds_check(
                        current_expr,
                        current_ty,
                        index_expr,
                        projection_kind,
                    ) {
                        Some(result) => result,
                        None => return None,
                    };
                    current_expr = next_expr;
                    current_ty = next_ty;
                    active_variant = None; // Reset: ConstantIndex breaks Downcast-Field pairing
                }
                ProjectionElem::Downcast(variant_idx) => {
                    // Downcast selects an enum variant for subsequent Field access.
                    // Track the variant index so the next Field projection uses the
                    // correct constructor index. (Part of #1739, Gap 1)
                    active_variant = Some(variant_idx.to_index());
                    proj_idx += 1;
                    continue;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    // Part of #3306: SubSlice extracts a contiguous sub-range.
                    if let Some(result) =
                        self.build_subslice_expr(&current_expr, current_ty, *from, *to, *from_end)
                    {
                        current_expr = result;
                    } else {
                        debug!("CHC: Subslice failed, returning None");
                        self.diagnostics.place_translation_drop.inc();
                        record_translation_drop_site_reason_for_fn(
                            &self.fn_name,
                            "deref_subslice_failed",
                        );
                        return None;
                    }
                    active_variant = None;
                }
                ProjectionElem::OpaqueCast(_) => {
                    // Part of #1351: OpaqueCast is a transparent type annotation
                    // for coroutine/async state machines. Skip it — no runtime effect.
                    // Matches inline path behavior (projected_assign.rs:370).
                    proj_idx += 1;
                    continue;
                }
            }
            proj_idx += 1;
        }
        // Part of #4022 D3: Post-check — if the result is Array-sorted after a Deref
        // chain, the pipeline returned the whole memory array instead of selecting an
        // element at the pointer address. This happens when ref_target resolution or
        // const_ref_values resolves through a pointer to a stack array without applying
        // the element index. Apply subslice_offset if available; otherwise the Array
        // propagates to the assignment site as a sort mismatch.
        if has_deref && current_expr.sort().is_array() {
            if let Some(offset_expr) = self.ref_resolution.subslice_offset.get(&local_idx).cloned()
            {
                let idx =
                    coerce_bitvec_width_safe(offset_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!(
                    local_idx,
                    "CHC: applying subslice_offset select for Array deref result (#4022)"
                );
                current_expr = current_expr.select(idx);
            }
        }
        debug!(?place, "CHC: translate_place_with_deref succeeded at Mem level");
        Some(current_expr)
    }
}

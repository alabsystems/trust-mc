// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rvalue::Len translation and length resolution helpers for CHC encoding.
//!
//! Extracted from `codegen_stmt_rvalue.rs` per #3920 to reduce merge-conflict
//! contention. Contains the Len arm body and three length resolution strategies:
//! - `try_resolve_len_from_unsize`: recover N from Unsize casts of [T; N]
//! - `try_resolve_len_from_subslice_ref`: recover subslice length from Subslice projections
//! - `try_resolve_len_from_datatype`: extract fld_len from Vec/Slice Datatypes

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{CastKind, Place, PointerCoercion, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_stmt_projection::{UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate `Rvalue::Len(place)` to a CHC expression.
    ///
    /// Tries four strategies in order:
    /// 1. Compile-time array length for `[T; N]`
    /// 2. Recover N from Unsize cast origin (`&[T; N]` → `&[T]`)
    /// 3. Recover subslice length from Subslice ref chain
    /// 4. Extract `fld_len` from Vec/Slice Datatype state variable
    /// 5. Fallback: fresh unconstrained symbolic usize (sound over-approximation)
    ///
    /// Part of #3920: extracted from `translate_rvalue_with_modified`.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_len(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #1888: Rvalue::Len returns usize.
        // For fixed-size arrays [T; N], use the compile-time constant length.
        // For slices, we would need fat pointer metadata (not yet supported).
        let ty = place.ty(self.body.locals()).ok();

        if let Some(ty) = &ty
            && let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind()
            && let Some(len) = const_len.eval_target_usize().ok()
        {
            debug!(?place, len, "CHC: Rvalue::Len on array - compile-time length");
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }

        // Part of #3099: Try to recover array length from unsize origin.
        // When MIR has `Len(*_x)` where `_x` was assigned via an Unsize
        // cast from `&[T; N]` → `&[T]`, we can use N directly.
        if let Some(len) = self.try_resolve_len_from_unsize(place) {
            debug!(?place, len, "CHC: Rvalue::Len on slice - recovered length from array unsize");
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }

        // Part of #3495: Try to recover length from Subslice ref chain.
        // When MIR has `_s = &(*_x)[Subslice(from, to, from_end)]` and
        // `Len(*_s)`, trace through the Ref to resolve the source length.
        if let Some(len) = self.try_resolve_len_from_subslice_ref(place) {
            debug!(?place, len, "CHC: Rvalue::Len on slice - recovered length from subslice ref");
            return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
        }

        // Try to recover length from call-registered subslice_len side table.
        // When MIR has `Len(*_x)` and `_x` was the destination of a Range-based
        // slice index call (`codegen_call_slice_range`), the subslice length
        // was registered in `ref_resolution.subslice_len[_x]`.
        // This handles the slice-of-slice pattern: `&array[2..5]` then `&slice1[1..2]`
        // where `_x` is the result of the Range index call, not a MIR Subslice projection.
        if let Some(len_expr) = self.try_resolve_len_from_call_subslice(place) {
            debug!(
                ?place,
                "CHC: Rvalue::Len on slice - recovered length from call-registered subslice_len"
            );
            return Some(len_expr);
        }

        // Part of #3084: Try to extract fld_len from Vec/Slice Datatype.
        if let Some(len_expr) = self.try_resolve_len_from_datatype(place, modified_locals) {
            debug!(?place, "CHC: Rvalue::Len on Vec/Slice - extracted fld_len from Datatype");
            return Some(len_expr);
        }

        // Part of #3099: Fallback for slices and other dynamic-length
        // types. Return a fresh unconstrained symbolic bitvec of
        // POINTER_WIDTH (usize). This is a SOUND over-approximation:
        // the symbolic length is universally quantified over all
        // possible usize values, so any PROOF that holds under this
        // model also holds for the actual length. Reclassified from
        // chc_fallback (DEMOTED) to place_translation_drop
        // (SOUND_APPROXIMATION) — avoids false demotion and
        // eliminates the double-counting that occurred when returning
        // None triggered the self-loop handler's record_fallback().
        warn!(?place, "CHC Rvalue::Len fallback: fresh symbolic usize (sound over-approximation)");
        self.record_sound_fallback_reason("rvalue_len_fallback");
        let len_name = chc_fresh_name("__len_nondet");
        Some(declare_pending_var(len_name, ptr_sort()))
    }

    /// Trace backward through MIR to find the array length for a `Len(*_x)` place.
    ///
    /// When MIR has:
    ///   `_2 = &_1`            where `_1: [T; N]`
    ///   `_3 = _2 as &[T]`    (PointerCoercion::Unsize)
    ///   `_4 = Len(*_3)`
    ///
    /// This method recovers N by scanning for the Unsize cast assignment to _3's
    /// base local and extracting the source array type.
    ///
    /// Part of #3099: prevents false fallback for `.len()` on slices from arrays.
    pub(in crate::codegen_ay::chc) fn try_resolve_len_from_unsize(
        &self,
        place: &Place,
    ) -> Option<u64> {
        // Only handle deref places: Len(*_x).
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return None;
        }
        let local = place.local;

        // Scan MIR for a Cast(Unsize) assignment to this local.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.local != local {
                    continue;
                }
                if let Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize),
                    src_operand,
                    _,
                ) = rhs
                {
                    // Get the source operand's type.
                    let src_ty = src_operand.ty(self.body.locals()).ok()?;
                    // Extract inner type from &[T; N], *const [T; N], etc.
                    let inner = match src_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                        TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                        _ => return None,
                    };
                    if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner.kind() {
                        return const_len.eval_target_usize().ok();
                    }
                }
            }
        }
        None
    }

    /// Trace backward through MIR to find the slice length for `Len(*_s)` where
    /// `_s` was assigned via `Rvalue::Ref` with a `Subslice` projection.
    ///
    /// Pattern:
    ///   `_x = Cast(Unsize, &_arr, &[T])` where `_arr: [T; N]`
    ///   `_s = &(*_x)[Subslice(from, to, from_end)]`
    ///   `_len = Len(*_s)`
    ///
    /// Recovers `N - from - to` by following the Ref chain back to the Unsize source.
    ///
    /// Part of #3495: prevents false fallback for `Len` on pattern-match subslices.
    pub(in crate::codegen_ay::chc) fn try_resolve_len_from_subslice_ref(
        &self,
        place: &Place,
    ) -> Option<u64> {
        // Only handle deref places: Len(*_s).
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return None;
        }
        let local = place.local;

        // Scan MIR for a Ref/AddressOf assignment to this local with a Subslice projection.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.local != local {
                    continue;
                }
                if let Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place) = rhs {
                    // Look for [Deref, ..., Subslice(from, to, from_end)] pattern.
                    let subslice = ref_place.projection.iter().rev().find_map(|p| {
                        if let ProjectionElem::Subslice { from, to, from_end } = p {
                            Some((*from, *to, *from_end))
                        } else {
                            None
                        }
                    });
                    let Some((from, to, _from_end)) = subslice else {
                        continue;
                    };
                    // The base local (before Deref) holds the source slice reference.
                    let source_local = ref_place.local;
                    let source_place =
                        Place { local: source_local, projection: vec![ProjectionElem::Deref] };
                    // Try to resolve the source slice's length.
                    // First: check if source is a fixed-size array type.
                    if let Ok(src_ty) = source_place.ty(self.body.locals()) {
                        if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = src_ty.kind() {
                            if let Ok(n) = const_len.eval_target_usize() {
                                let subslice_len = n - from - to;
                                debug!(
                                    local,
                                    source_local,
                                    n,
                                    from,
                                    to,
                                    subslice_len,
                                    "CHC: Len resolved via Subslice ref from array"
                                );
                                return Some(subslice_len);
                            }
                        }
                    }
                    // Second: try Unsize origin for the source local.
                    if let Some(n) = self.try_resolve_len_from_unsize(&source_place) {
                        let subslice_len = n - from - to;
                        debug!(
                            local,
                            source_local,
                            n,
                            from,
                            to,
                            subslice_len,
                            "CHC: Len resolved via Subslice ref from Unsize source"
                        );
                        return Some(subslice_len);
                    }
                }
            }
        }
        None
    }

    /// Recover subslice length from call-registered side table.
    ///
    /// When `codegen_call_slice_range` processes `&slice[start..end]`, it registers
    /// `subslice_len[dest_local] = end - start` in `ref_resolution.subslice_len`.
    /// When MIR has `Len(*_x)` and `_x` has a registered subslice_len, return it.
    /// Also follows ref_targets and Move/Copy chains.
    fn try_resolve_len_from_call_subslice(&self, place: &Place) -> Option<Expr> {
        // Only handle Len(*_x) — one Deref projection.
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return None;
        }
        let local = place.local;

        // Direct lookup.
        if let Some(len) = self.ref_resolution.subslice_len.get(&local) {
            return Some(len.clone());
        }

        // Follow ref_targets: if `_y = &(*_x)`, look up _x's subslice_len.
        if let Some(referent) = self.ref_resolution.ref_targets.get(&local) {
            if referent.projections.is_empty() {
                if let Some(len) = self.ref_resolution.subslice_len.get(&referent.local) {
                    return Some(len.clone());
                }
            }
        }

        // Follow Move/Copy chain: if `_local = Move/Copy(_src)`, check _src.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(
                    rustc_public::mir::Operand::Copy(src) | rustc_public::mir::Operand::Move(src),
                ) = rhs
                {
                    if src.projection.is_empty() {
                        if let Some(len) = self.ref_resolution.subslice_len.get(&src.local) {
                            return Some(len.clone());
                        }
                    }
                }
            }
        }
        None
    }

    /// Extract `fld_len` from a Vec/Slice Datatype state variable for `Rvalue::Len`.
    ///
    /// Part of #3084: eliminates false fallback for `.len()` on Vec/Slice locals.
    ///
    /// Handles three patterns:
    /// 1. `Len(_x)` where `_x` is a direct Vec/Slice local
    /// 2. `Len(*_x)` where `_x` has a ref_target pointing to a Vec/Slice local
    /// 3. `Len(*_x)` where `_x` has a ref_target with field projections navigating
    ///    through a struct to reach a Vec/Slice field (e.g., `struct.items: Vec<T>`)
    fn try_resolve_len_from_datatype(
        &self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::CtorFieldExt;

        // Resolve the target local and any field projections from ref_targets.
        let (target_local, ref_projections) = if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
        {
            let ref_target = self.ref_resolution.ref_targets.get(&place.local)?;
            (ref_target.local, ref_target.projections.as_slice())
        } else if place.projection.is_empty() {
            (place.local, [].as_slice())
        } else {
            return None;
        };

        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            return None;
        }

        let vec_idx = self.try_state_idx_for_local(target_local)?;
        let expr = if modified_locals.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                let (name, sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
                Expr::var(&**name, sort.clone())
            }
        } else {
            let (name, sort) = self.state_var_mgr.state_vars.get(vec_idx)?;
            Expr::var(&**name, sort.clone())
        };

        // Part of #3084: If ref_target had field projections (e.g., struct.field → Vec),
        // navigate through the struct Datatype to reach the Vec/Slice field.
        let field_expr = if !ref_projections.is_empty() {
            let field_projs =
                collect_field_projections(ref_projections, UnknownProjectionPolicy::Skip);
            if field_projs.is_empty() {
                return None;
            }
            Self::apply_field_selections(expr, &field_projs)?
        } else {
            expr
        };

        let sort = field_expr.sort();
        let dt_name = sort.datatype_name()?.to_owned();
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        if ctor.has_field("fld_len") {
            debug!(
                target_local,
                %dt_name,
                ref_proj_count = ref_projections.len(),
                "CHC: Rvalue::Len resolved fld_len from Datatype state variable"
            );
            Some(field_expr.field_select(&dt_name, "fld_len", ptr_sort()))
        } else {
            None
        }
    }
}

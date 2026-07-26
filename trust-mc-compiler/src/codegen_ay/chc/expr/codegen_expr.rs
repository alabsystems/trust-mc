// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Core operand/place translation.
//!
//! Signedness analysis extracted to codegen_expr_signedness.rs per #2129.
//! Assertion/assume handling extracted to codegen_expr_assert.rs per #2129.
//! Heap safety checks extracted to codegen_expr_heap.rs per #2129.
//! Constant translation extracted to codegen_expr_constant.rs per #2246.
//! Loop invariant + env translation extracted to codegen_expr_env.rs per #2246.
//! Deref resolution extracted to codegen_expr_deref.rs per #2246.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use ay_bindings::{Expr, ExprValue};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_expr_constant::ExprConstant;
use super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use super::codegen_types::CodegenTypes;
use super::constant_index_offset;
use super::{UnknownProjectionPolicy, collect_field_projections};

/// Returns and resets the flattened-place drop counter for metadata emission.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn take_place_translation_drop_count() -> usize {
    GLOBAL_COUNTERS.place_translation_drop.swap(0, Ordering::Relaxed)
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_place_translation_drop_count_for_test(count: usize) {
    GLOBAL_COUNTERS.place_translation_drop.store(count, Ordering::Relaxed);
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn omitted_flattened_field_expr(
        field_ty: Option<rustc_public::ty::Ty>,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(field_ty?)?;
        if sort.is_bool() {
            return Some(Expr::bool_const(true));
        }
        Self::sort_default_expr(&sort)
    }

    fn resolve_static_ref_deref_place(
        &self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;
        if !matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
            || !self.ref_resolution.static_ref_to_state_idx.contains_key(&local_idx)
        {
            return None;
        }

        let root = self.resolve_static_ref_root_expr(local_idx, modified_locals)?;
        if place.projection.len() == 1 {
            return Some(root);
        }

        let (pointee_ty, _) = Self::deref_ref_ty(self.body.locals()[local_idx].ty);
        self.translate_place_field_index(
            &place.projection[1..],
            root,
            Some(pointee_ty),
            modified_locals,
        )
    }

    fn resolve_ref_target_redirect(&self, place: &Place) -> Option<Place> {
        let local_idx: usize = place.local;
        if !matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref)) {
            return None;
        }

        let ref_target = self.ref_resolution.ref_targets.get(&local_idx)?;
        let target_place =
            Place { local: ref_target.local, projection: ref_target.projections.clone() };
        let target_ty_is_ptr = target_place.ty(self.body.locals()).ok().is_some_and(|ty| {
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        });
        let is_double_ref = matches!(
            self.body.locals()[local_idx].ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _))
                if matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        );

        let mut redirected_projection = target_place.projection;
        if target_ty_is_ptr && !is_double_ref {
            redirected_projection.push(rustc_public::mir::ProjectionElem::Deref);
        }
        redirected_projection.extend(place.projection.iter().skip(1).cloned());

        let redirected_place =
            Place { local: target_place.local, projection: redirected_projection };
        (redirected_place.local != place.local || redirected_place.projection != place.projection)
            .then_some(redirected_place)
    }

    fn resolve_root_expr(
        &self,
        local_idx: usize,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        if modified_locals.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                return Some(env_expr.clone());
            }
            if let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(vec_idx) {
                return Some(Expr::var(&**name, sort.clone()));
            }
            warn!(
                local_idx,
                vec_idx,
                output_state_vars_len = self.state_var_mgr.output_state_vars.len(),
                "local index out of bounds in output_state_vars"
            );
            return None;
        }

        if place.projection.is_empty()
            && let Some(const_expr) = self.encode.const_folded_call_results.get(&local_idx)
            && self.cached_expr_dependencies_live_at_current_block(const_expr)
        {
            return Some(const_expr.clone());
        }

        if place.projection.is_empty()
            && let Some(discr_expr) = self.single_variant_unit_enum_discriminant(local_idx)
        {
            return Some(discr_expr);
        }

        if let Some((name, sort)) = self.state_var_mgr.state_vars.get(vec_idx) {
            return Some(Expr::var(&**name, sort.clone()));
        }

        warn!(
            local_idx,
            vec_idx,
            state_vars_len = self.state_var_mgr.state_vars.len(),
            "local index out of bounds in CHC translate_place_with_modified"
        );
        None
    }

    fn cached_expr_dependencies_live_at_current_block(&self, expr: &Expr) -> bool {
        let Some(live_indices) = self.state_var_mgr.live_state_indices.get(self.current_encode_bb)
        else {
            return false;
        };

        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            if let ExprValue::Var { name } = node.value() {
                let Some(state_idx) = self.state_var_index_by_name(name) else {
                    return false;
                };
                if !live_indices.contains(&state_idx) {
                    debug!(
                        local_var = %name,
                        bb = self.current_encode_bb,
                        "CHC: skipping cached scalar expression with non-live dependency"
                    );
                    return false;
                }
            }
            stack.extend(node.children());
        }

        true
    }

    fn single_variant_unit_enum_discriminant(&self, local_idx: usize) -> Option<Expr> {
        let local_ty = self.body.locals().get(local_idx)?.ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() else {
            return None;
        };
        if def.kind() != rustc_public::ty::AdtKind::Enum {
            return None;
        }
        let variants = def.variants();
        if variants.len() != 1 || !variants[0].fields().is_empty() {
            return None;
        }
        let sort = Self::translate_ty(local_ty)?;
        let width = sort.bitvec_width()?;
        let internal_def = rustc_internal::internal(self.tcx, def);
        let discr =
            internal_def.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(0));
        let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, self.tcx, width);
        Some(Expr::bitvec_const(discriminant_val, width))
    }

    fn translate_union_field_read_fallback(
        &self,
        local_idx: usize,
        root_expr: Expr,
        field_projections: &[super::FieldProjection],
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
        use rustc_public::ty::{RigidTy, TyKind};

        let local_ty = self.body.locals()[local_idx].ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() else {
            return None;
        };
        if def.kind() != rustc_public::ty::AdtKind::Union || !root_expr.sort().is_bitvec() {
            return None;
        }

        let field_ty = field_projections.last().and_then(|fp| fp.field_ty);
        let field_width = field_ty
            .and_then(|ty| ty.layout().ok())
            .map(|l| byte_size_to_bv_width(l.shape().size.bytes()))
            .unwrap_or(0);
        if field_width == 0 {
            debug!(local_idx, "translate_place: union ZST field read -> Bool true");
            return Some(Expr::bool_const(true));
        }

        debug!(local_idx, field_width, "translate_place: union field read -> coerced BV");
        Some(coerce_bitvec_width_safe(root_expr, field_width, SignExtension::ZeroExtend))
    }

    /// Translates a MIR Operand using OUTPUT variables for modified locals.
    ///
    /// For locals in `modified_locals`, uses the OUTPUT state variable instead of INPUT.
    /// This is needed when translating terminator operands that reference values
    /// computed in statements within the same basic block (#656).
    ///
    /// At Mem track level, this also handles Deref projections via memory loads.
    /// Part of #892: Phase 3 - Memory load/store integration (#905).
    pub(in crate::codegen_ay::chc) fn translate_operand_with_modified(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // At Mem track level, use translate_place_with_deref which handles
                // memory loads for Deref projections. It delegates to
                // translate_place_with_modified when there's no Deref.
                self.translate_place_with_deref(place, modified_locals)
            }
            Operand::Constant(const_op) => self.translate_constant(const_op),
        }
    }

    /// Translates a MIR Place using OUTPUT variables for modified locals.
    ///
    /// For locals in `modified_locals`, uses the OUTPUT state variable instead of INPUT.
    /// This handles projections (field access) correctly by selecting from the appropriate
    /// root variable based on whether the local was modified in the current block (#656).
    pub(in crate::codegen_ay::chc) fn translate_place_with_modified(
        &self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;

        // Part of #2214 / #3908 Step 5: Flattened locals dispatch to dedicated method.
        if self.flatten.flattened_tuple_locals.contains(&local_idx) {
            return self.translate_flattened_place(place, local_idx, modified_locals);
        }

        if matches!(place.projection.first(), Some(rustc_public::mir::ProjectionElem::Deref))
            && self.ref_resolution.static_ref_to_state_idx.contains_key(&local_idx)
        {
            return self.resolve_static_ref_deref_place(place, modified_locals);
        }

        if let Some(redirected_place) = self.resolve_ref_target_redirect(place) {
            return self.translate_place_with_modified(&redirected_place, modified_locals);
        }

        // Fix #2055: For modified locals, first check the block-local expression
        // environment. This ensures reads get the expression value at the point of
        // assignment, not the __out variable which may be re-bound by later assignments.
        // For no-projection reads, the env expression is the exact value.
        // For projection reads, use the env expression as the root for field selection.
        // Fix #2238: Use local_to_state_idx mapping to handle non-sequential
        // state variable indices caused by flattened locals consuming multiple slots.
        let root_expr = self.resolve_root_expr(local_idx, place, modified_locals)?;

        // If no projections, return the root directly
        if place.projection.is_empty() {
            return Some(root_expr);
        }

        if let Some(redirected_place) = self.redirect_leading_deref_through_unique_ref_source(place)
        {
            debug!(
                orig_local = local_idx,
                redirected_local = redirected_place.local,
                redirected_projection = ?redirected_place.projection,
                "CHC: redirected leading deref through unique MIR ref source"
            );
            return self.translate_place_with_modified(&redirected_place, modified_locals);
        }

        // Handle any index-bearing projection chain on non-flattened locals.
        if Self::has_index_like_projection(&place.projection) {
            debug!(
                local_idx,
                "CHC: index-bearing projection on non-flattened local, using translate_place_field_index"
            );
            return self.translate_place_field_index(
                &place.projection,
                root_expr,
                Some(self.body.locals()[local_idx].ty),
                modified_locals,
            );
        }

        self.translate_place_field_projection_tail(place, local_idx, root_expr)
    }

    /// Collect field projections, apply Datatype field selections, and fall back
    /// to union BV coercion if needed.
    fn translate_place_field_projection_tail(
        &self,
        place: &Place,
        local_idx: usize,
        root_expr: Expr,
    ) -> Option<Expr> {
        let field_projections = collect_field_projections(
            &place.projection,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );

        if field_projections.is_empty() {
            debug!(?place, "place has projections but no Field projections found");
            return None;
        }

        if let Some(result) = Self::apply_field_selections(root_expr.clone(), &field_projections) {
            return Some(result);
        }

        self.translate_union_field_read_fallback(local_idx, root_expr, &field_projections)
    }

    fn has_index_like_projection(projection: &[rustc_public::mir::ProjectionElem]) -> bool {
        use rustc_public::mir::ProjectionElem;
        projection.iter().any(|p| {
            matches!(
                p,
                ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        })
    }

    fn redirect_leading_deref_through_unique_ref_source(&self, place: &Place) -> Option<Place> {
        use rustc_public::mir::ProjectionElem;

        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return None;
        }
        let remaining = &place.projection[1..];
        if remaining.is_empty()
            || !remaining.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
            || !remaining.iter().all(|proj| {
                matches!(proj, ProjectionElem::Downcast(_) | ProjectionElem::Field(_, _))
            })
        {
            return None;
        }

        let local_idx: usize = place.local;
        let mut unique_source: Option<Place> = None;

        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.local != local_idx || !lhs.projection.is_empty() {
                    continue;
                }

                let candidate = match rhs {
                    Rvalue::Ref(_, _, source_place) | Rvalue::AddressOf(_, source_place) => {
                        source_place.clone()
                    }
                    _ => continue,
                };

                if let Some(existing) = &unique_source {
                    if existing.local != candidate.local
                        || existing.projection != candidate.projection
                    {
                        debug!(
                            local_idx,
                            existing = ?existing,
                            candidate = ?candidate,
                            "CHC: ambiguous MIR ref source for leading-deref place; skipping redirect"
                        );
                        return None;
                    }
                } else {
                    unique_source = Some(candidate);
                }
            }
        }

        let source_place = unique_source?;
        let mut redirected_projection = source_place.projection.clone();
        redirected_projection.extend(place.projection.iter().skip(1).cloned());
        let redirected_place =
            Place { local: source_place.local, projection: redirected_projection };
        (redirected_place.local != place.local || redirected_place.projection != place.projection)
            .then_some(redirected_place)
    }
    // Datatype reconstruction extracted to codegen_expr_reconstruct.rs per #3199.

    fn apply_field_projection(
        &self,
        current: Expr,
        current_ty: Option<rustc_public::ty::Ty>,
        cons_idx: Option<usize>,
        field_idx: usize,
        field_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use super::FieldProjection;
        use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
        use rustc_public::ty::{RigidTy, TyKind};

        if crate::codegen_ay::types::is_coroutine_root_sort(current.sort()) {
            return crate::codegen_ay::types::coroutine_root_select(current, cons_idx, field_idx);
        }

        let selections = vec![FieldProjection { field_idx, cons_idx, field_ty: Some(field_ty) }];
        if let Some(expr) = Self::apply_field_selections(current.clone(), &selections) {
            return Some(expr);
        }
        if let Some(ty) = current_ty
            && current.sort().is_bitvec()
        {
            if let Some(selected) = Self::bv_field_select(&current, ty, &selections) {
                return Some(selected);
            }
            if let Some(coerced) = Self::union_bv_field_coerce(&current, ty, field_ty) {
                return Some(coerced);
            }
        }
        None
    }

    /// Union field select on a BV root: unions translate to
    /// `Sort::bitvec(size*8)`, so a field read is a zero-extend/truncate to the
    /// field's width (LE layout, all union fields at offset 0). `None` when the
    /// root isn't a BV-sorted union. Shared by `apply_field_projection` and the
    /// deref-chain Field arm.
    pub(in crate::codegen_ay::chc) fn union_bv_field_coerce(
        current: &Expr,
        current_ty: rustc_public::ty::Ty,
        field_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
        use rustc_public::ty::{RigidTy, TyKind};
        if !current.sort().is_bitvec() {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = current_ty.kind() else {
            return None;
        };
        if def.kind() != rustc_public::ty::AdtKind::Union {
            return None;
        }
        let field_width = field_ty
            .layout()
            .ok()
            .map(|l| byte_size_to_bv_width(l.shape().size.bytes()))
            .unwrap_or(0);
        Some(if field_width == 0 {
            Expr::bool_const(true)
        } else {
            coerce_bitvec_width_safe(current.clone(), field_width, SignExtension::ZeroExtend)
        })
    }

    /// Element select from a fixed-size scalar array `[T; N]` that reached this
    /// projection as a plain BITVEC — e.g. a union field coerced from the
    /// union's BV root (`apply_field_projection`'s union arm), where the Index
    /// arms would otherwise bail on the non-Array sort. LE layout puts element
    /// `i` at bit offset `i * elem_bits`, so `extract(lshr(cur, i*eb), eb)`
    /// reads the exact stored element for both constant and symbolic indices.
    pub(in crate::codegen_ay::chc) fn bv_array_index_select(
        &self,
        current: &Expr,
        current_ty: Option<rustc_public::ty::Ty>,
        index_expr: &Expr,
    ) -> Option<(Expr, Option<rustc_public::ty::Ty>)> {
        use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
        let ty = current_ty?;
        let elem_ty = self.get_array_element_ty(ty)?;
        let cur_width = current.sort().bitvec_width()?;
        let elem_sort = Self::translate_ty(elem_ty)?;
        // Scalar (bitvec) elements only; Bool/datatype elements keep the old bail.
        let elem_width = elem_sort.bitvec_width()?;
        if elem_width == 0 || elem_width > cur_width {
            return None;
        }
        let idx =
            coerce_bitvec_width_safe(index_expr.clone(), cur_width, SignExtension::ZeroExtend);
        let shift = idx.bvmul(Expr::bitvec_const(elem_width as u128, cur_width));
        let value = current.clone().bvlshr(shift).extract(elem_width - 1, 0);
        Some((value, Some(elem_ty)))
    }

    fn apply_array_index_select(
        &self,
        mut current: Expr,
        current_ty: Option<rustc_public::ty::Ty>,
        index_expr: Expr,
    ) -> (Expr, Option<rustc_public::ty::Ty>) {
        current = if let Some(array_ty) = current_ty {
            self.finite_fixed_array_select(&current, &index_expr, array_ty)
                .unwrap_or_else(|| current.select(index_expr))
        } else {
            current.select(index_expr)
        };
        let next_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
        if let Some(elem_ty) = next_ty {
            if current.sort().is_bitvec()
                && let Some(elem_sort) = Self::translate_ty(elem_ty)
                && elem_sort.is_datatype()
                && let Some(unflat) =
                    crate::codegen_ay::types::unflatten_bitvec_to_datatype(&current, &elem_sort)
            {
                current = unflat;
            }
            (current, Some(elem_ty))
        } else {
            (current, None)
        }
    }

    /// Translate a place with Field/Index/Subslice projections from a concrete root.
    ///
    /// Iterates through projections applying:
    /// - Field: Datatype field selection via `apply_field_selections`
    /// - Downcast: Sets active variant for next Field's `cons_idx`
    /// - Index/ConstantIndex: Z3 array `select` operation
    /// - Subslice: array slicing via `build_subslice_expr`
    pub(crate) fn translate_place_field_index(
        &self,
        projections: &[rustc_public::mir::ProjectionElem],
        root: Expr,
        root_ty: Option<rustc_public::ty::Ty>,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
        use crate::rustc_public_bridge::IndexedVal;
        use rustc_public::mir::ProjectionElem;

        let mut current = root;
        let mut current_ty = root_ty;
        let mut active_variant: Option<usize> = None;

        for proj in projections {
            match proj {
                ProjectionElem::Downcast(variant_idx) => {
                    active_variant = Some(variant_idx.to_index());
                }
                ProjectionElem::Field(field_idx, field_ty) => {
                    current = self.apply_field_projection(
                        current,
                        current_ty,
                        active_variant.take(),
                        *field_idx,
                        *field_ty,
                    )?;
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
                        // BV-rooted scalar array (union field coerced from the
                        // union's BV root): element extract instead of bailing.
                        let (next_current, next_ty) =
                            self.bv_array_index_select(&current, current_ty, &index_expr)?;
                        current = next_current;
                        current_ty = next_ty;
                        active_variant = None;
                        continue;
                    }
                    let (next_current, next_ty) =
                        self.apply_array_index_select(current, current_ty, index_expr);
                    current = next_current;
                    current_ty = next_ty;
                    active_variant = None;
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    let actual_offset = constant_index_offset(*offset, *min_length, *from_end);
                    let index_expr = Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                    if !current.sort().is_array() {
                        // Same BV-rooted scalar-array element extract as Index.
                        let (next_current, next_ty) =
                            self.bv_array_index_select(&current, current_ty, &index_expr)?;
                        current = next_current;
                        current_ty = next_ty;
                        active_variant = None;
                        continue;
                    }
                    let (next_current, next_ty) =
                        self.apply_array_index_select(current, current_ty, index_expr);
                    current = next_current;
                    current_ty = next_ty;
                    active_variant = None;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    let source_ty = current_ty?;
                    current =
                        self.build_subslice_expr(&current, source_ty, *from, *to, *from_end)?;
                    active_variant = None;
                }
                _ => {
                    debug!(
                        "CHC: unsupported projection in translate_place_field_index: {:?}",
                        proj
                    );
                    return None;
                }
            }
        }
        Some(current)
    }

    // Flattened place translation methods extracted to codegen_expr_flattened.rs:
    //   reconstruct_flattened_root, translate_flattened_place,
    //   translate_flattened_downcast_nested, translate_flattened_single_field,
    //   translate_flattened_mixed_field_index
}

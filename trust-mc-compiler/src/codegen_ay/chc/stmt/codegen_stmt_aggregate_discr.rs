// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Discriminant extraction for CHC encoding (#2246, #2306).

use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;

/// Rule E: the unresolved-referent discriminant symbol ranges over every
/// variant's discriminant value, a sound value havoc (audited in
/// `codegen_ctx::fallback_soundness`).
pub(in crate::codegen_ay::chc) const DISCR_UNRESOLVED_REFERENT: &str = "discr_unresolved_referent";

/// Rule E: the unresolved-referent discriminant reached on a place with NO
/// deref, where the place itself should have translated: fail-closed.
pub(in crate::codegen_ay::chc) const DISCR_UNRESOLVED_DIRECT_PLACE: &str =
    "discr_unresolved_direct_place";

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Infer discriminant (true_val, false_val) for a flattened enum local.
    /// Checks the flattened_enum_discr map first; if missing, falls back to
    /// type-based inference: Option → (1,0), Result → (0,1), general 2-variant
    /// ADTs → inferred from variant structure (#3136).
    /// Calls record_fallback() only for 3+ variant or non-ADT types.
    pub(in crate::codegen_ay::chc) fn infer_flattened_discr(
        &mut self,
        local_idx: usize,
    ) -> (u64, u64) {
        if let Some(&discr) = self.flatten.flattened_enum_discr.get(&local_idx) {
            return discr;
        }
        // Type-based inference: check the ADT variant structure.
        if let Some(local_decl) = self.body.locals().get(local_idx)
            && let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_decl.ty.kind()
        {
            let name = def.trimmed_name();
            if name == "Option" {
                warn!(
                    local_idx,
                    "flattened_enum_discr missing for Option local; inferred (1,0) from type"
                );
                return (1, 0);
            }
            if name == "Result" {
                warn!(
                    local_idx,
                    "flattened_enum_discr missing for Result local; inferred (0,1) from type"
                );
                return (0, 1);
            }
            // Part of #3136: General 2-variant ADT — infer from variant structure.
            // Bool fld0 convention: option-like → true = payload variant;
            // both-payload or both-empty → true = variant 0.
            let variants = def.variants();
            if variants.len() == 2 {
                let idef = rustc_internal::internal(self.tcx, def);
                let discr0 =
                    idef.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(0));
                let d0 =
                    sign_extend_discr_val(discr0.val, discr0.ty, self.tcx, POINTER_WIDTH) as u64;
                let discr1 =
                    idef.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(1));
                let d1 =
                    sign_extend_discr_val(discr1.val, discr1.ty, self.tcx, POINTER_WIDTH) as u64;
                let swap = variants[0].fields().is_empty() && !variants[1].fields().is_empty();
                let (true_val, false_val) = if swap { (d1, d0) } else { (d0, d1) };
                warn!(
                    local_idx,
                    true_val,
                    false_val,
                    "flattened_enum_discr missing for 2-variant ADT; \
                     inferred from variant structure"
                );
                return (true_val, false_val);
            }
        }
        // 3+ variant ADTs: infer from variant structure.
        // Bool fld0 encoding is inherently lossy for 3+ variants but this path
        // should only be reached for 2-variant enums with Bool fld0. If a 3+
        // variant enum reaches here, use the first two discriminant values
        // from the ADT definition and record a sound fallback.
        if let Some(local_decl) = self.body.locals().get(local_idx)
            && let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_decl.ty.kind()
        {
            let variants = def.variants();
            if variants.len() >= 2 {
                let idef = rustc_internal::internal(self.tcx, def);
                let discr0 =
                    idef.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(0));
                let d0 =
                    sign_extend_discr_val(discr0.val, discr0.ty, self.tcx, POINTER_WIDTH) as u64;
                let discr1 =
                    idef.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(1));
                let d1 =
                    sign_extend_discr_val(discr1.val, discr1.ty, self.tcx, POINTER_WIDTH) as u64;
                let swap = variants[0].fields().is_empty() && !variants[1].fields().is_empty();
                let (true_val, false_val) = if swap { (d1, d0) } else { (d0, d1) };
                self.record_sound_fallback_reason("infer_flattened_discr_3plus_variant");
                warn!(
                    local_idx,
                    true_val,
                    false_val,
                    num_variants = variants.len(),
                    "flattened_enum_discr missing for {}-variant ADT; \
                     inferred first two discriminants (sound over-approx)",
                    variants.len()
                );
                return (true_val, false_val);
            }
        }
        // Non-ADT or single-variant: record fallback and use Option-like default.
        self.record_sound_fallback_reason("infer_flattened_discr_unknown_type");
        warn!(
            local_idx,
            "flattened_enum_discr missing and type not recognized; \
             defaulting to Option-like (1,0) with sound fallback recorded"
        );
        (1, 0)
    }

    /// The discriminant VALUE of a flattened enum local, read from its tag
    /// slot `fld0` by the local's own flattening: an `EnumBvLayout` tag (a
    /// Bool for two constructors, else a constructor index) mapped through
    /// the layout's discriminants, or a flattened Bool tag mapped through
    /// [`Self::infer_flattened_discr`]. `None` when the local is neither, or
    /// its tag slot does not translate. `translate_discriminant` reads a
    /// bare flattened local through it, and the flattened enum memory mirror
    /// (`try_decompose_flattened_enum_field_stores`) writes the tag bytes from
    /// it.
    pub(in crate::codegen_ay::chc) fn flattened_local_discriminant(
        &mut self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // #3215: BV-flattened multi-ctor enum — tag at fld0 (Bool or BV(n)).
        if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx) {
            if let Some(tag) = self.flattened_local_field_expr(local_idx, 0, modified_locals) {
                let d = |v: u64| Expr::bitvec_const(v, POINTER_WIDTH);
                let discr = if layout.num_constructors == 2 && tag.sort().is_bool() {
                    Expr::ite(tag, d(layout.discriminants[1]), d(layout.discriminants[0]))
                } else {
                    let last = *layout
                        .discriminants
                        .last()
                        .expect("invariant: enum_bv_layouts has ≥2 discriminants");
                    layout.discriminants.iter().enumerate().rev().skip(1).fold(
                        d(last),
                        |acc, (i, &dv)| {
                            let cond =
                                tag.clone().eq(Expr::bitvec_const(i as u64, layout.tag_bits));
                            Expr::ite(cond, d(dv), acc)
                        },
                    )
                };
                return Some(discr);
            }
        }

        // Part of #2214: For flattened enum locals (Option, Result), the
        // discriminant proxy is the Bool at state_vars[vec_idx + 0].
        // General scalar tuples (e.g., (usize, u32)) also live in
        // flattened_tuple_locals but fld0 is NOT Bool — guard on sort.
        if self.flatten.flattened_tuple_locals.contains(&local_idx) {
            if let Some(discr_bool) = self.flattened_local_field_expr(local_idx, 0, modified_locals)
            {
                if discr_bool.sort().is_bool() {
                    let (true_val, false_val) = self.infer_flattened_discr(local_idx);
                    debug!(
                        local_idx,
                        true_val, false_val, "CHC: translate_discriminant for flattened enum"
                    );
                    return Some(Expr::ite(
                        discr_bool,
                        Expr::bitvec_const(true_val, POINTER_WIDTH),
                        Expr::bitvec_const(false_val, POINTER_WIDTH),
                    ));
                }
                // Non-Bool fld0: this is a general tuple, not an enum.
                // Tuples don't have discriminants in MIR.
                debug!(
                    local_idx,
                    "CHC: translate_discriminant on non-enum flattened tuple — skipping"
                );
            }
        }
        None
    }

    /// Translates a Discriminant rvalue to a AY expression.
    /// Handles: BV-flattened enums (#3215), Option/Result, unit enums, general ADT enums.
    pub(in crate::codegen_ay::chc) fn translate_discriminant(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;
        if place.projection.is_empty()
            && let Some(discr) = self.flattened_local_discriminant(local_idx, modified_locals)
        {
            return Some(discr);
        }

        // #2876: Resolve place type, falling back to manual deref peeling if needed.
        let ty = if let Ok(ty) = place.ty(self.body.locals()) {
            ty
        } else {
            // Fallback: resolve through local type + manual deref peeling
            let local_ty = self.body.locals().get(local_idx).map(|decl| decl.ty);
            let peeled = local_ty.and_then(|base_ty| {
                let mut current = base_ty;
                for proj in &place.projection {
                    match proj {
                        ProjectionElem::Deref => {
                            current = match current.kind() {
                                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                                _ => return None, // external enum: TyKind
                            };
                        }
                        _ => return None, // non-Deref projection: bail
                    }
                }
                Some(current)
            });
            if let Some(ty) = peeled {
                debug!(
                    local_idx,
                    "CHC translate_discriminant: place.ty() failed, resolved via manual deref peeling"
                );
                ty
            } else {
                warn!(
                    local_idx,
                    "CHC translate_discriminant: place.ty() and manual deref both failed"
                );
                return None;
            }
        };

        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            if place.projection.is_empty() {
                let root_expr = self.resolve_coroutine_root_expr(local_idx, modified_locals);
                warn!(
                    local_idx,
                    root_sort = ?root_expr.as_ref().map(|e| e.sort().clone()),
                    "translate_discriminant: coroutine root_expr attempt"
                );
                if let Some(result) =
                    root_expr.as_ref().and_then(Self::try_coroutine_discriminant_expr)
                {
                    return Some(result);
                }
            } else if place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref)
            {
                if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx)
                    && ref_target.projections.is_empty()
                {
                    let target_local = ref_target.local;
                    if let Some(result) = self
                        .resolve_coroutine_root_expr(target_local, modified_locals)
                        .as_ref()
                        .and_then(Self::try_coroutine_discriminant_expr)
                    {
                        debug!(
                            ref_local = local_idx,
                            target_local, "translate_discriminant coroutine deref-to-target"
                        );
                        return Some(result);
                    }
                }

                if let Some((pointee_vec_idx, _, pointee_expr)) =
                    self.resolve_arg_ref_pointee_expr(local_idx)
                    && let Some(result) = Self::try_coroutine_discriminant_expr(&pointee_expr)
                {
                    debug!(
                        ref_local = local_idx,
                        pointee_vec_idx, "translate_discriminant coroutine deref-to-arg-pointee"
                    );
                    return Some(result);
                }

                // Part of #3807: mirror SetDiscriminant's coroutine_root_map fallback
                // for deref reads. Locals bridged via wrapper-arg propagation or
                // coroutine_root_map may not have ref_targets entries but still
                // resolve to a coroutine root expression.
                if let Some((_, _, root_expr)) = self.resolve_coroutine_root_state_expr(local_idx) {
                    if let Some(result) = Self::try_coroutine_discriminant_expr(&root_expr) {
                        debug!(
                            ref_local = local_idx,
                            "translate_discriminant coroutine deref-to-root-map"
                        );
                        return Some(result);
                    }
                    debug!(
                        ref_local = local_idx,
                        root_sort = ?root_expr.sort(),
                        "translate_discriminant: root_state_expr found but discriminant extract failed"
                    );
                } else {
                    debug!(
                        ref_local = local_idx,
                        in_root_map =
                            self.ref_resolution.coroutine_root_map.contains_key(&local_idx),
                        "translate_discriminant: coroutine deref resolve_coroutine_root_state_expr returned None"
                    );
                }
            }
            let deref_expr = self.translate_place_with_deref(place, modified_locals);
            warn!(
                local_idx,
                deref_sort = ?deref_expr.as_ref().map(|e| e.sort().clone()),
                "translate_discriminant: coroutine deref_expr fallback"
            );
            if let Some(result) =
                deref_expr.as_ref().and_then(Self::try_coroutine_discriminant_expr)
            {
                return Some(result);
            }
            warn!(
                local_idx,
                "translate_discriminant: coroutine ALL extraction paths failed, falling through to general"
            );
        }

        // #2618/#2242/#2267: Allocation ControlFlow/Result get symbolic discriminants
        // so both variant paths are explored. Check ADT name first, then format args.
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            let adt_name = def.0.name();
            let is_control_flow = adt_name.contains("ControlFlow");
            let is_result = adt_name.contains("Result");
            if is_control_flow || is_result {
                // Only format args when the container type matches
                let type_name = format!("{:?}", ty);
                if type_name.contains("AllocError") || type_name.contains("LayoutError") {
                    let label = if is_control_flow {
                        "allocation ControlFlow"
                    } else {
                        "allocation Result"
                    };
                    let discr_name = crate::codegen_ay::names::alloc_discr_name(
                        place.local,
                        place.projection.len(),
                    );
                    debug!(
                        discr_name,
                        label, "CHC translate_discriminant: symbolic discriminant (#2618)"
                    );
                    self.record_aggregate_gap("discr_symbolic_discriminant_2618");
                    let discr = Havoc::mint(
                        self,
                        sound_havoc::UNTRACKED_DISCRIMINANT,
                        discr_name,
                        ptr_sort(),
                    );
                    // Constrain to valid range [0, 2): both types have exactly 2 variants.
                    let upper = Expr::bitvec_const(2u64, POINTER_WIDTH);
                    self.heap_state.pending_updates.push(discr.clone().bvult(upper));
                    return Some(discr);
                }
            }
        }

        // Part of #3041: Single-variant enums always have a deterministic discriminant.
        // Return the constant value directly, avoiding the complex deref-based path
        // that can fail for enums in pre-inlined method bodies (e.g., derived PartialEq).
        // This generalizes the unit-enum check at line ~300 to include single-variant
        // enums WITH fields (e.g., `enum EnumSingle { MySingle(u32) }`).
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
            let variants = def.variants();
            if variants.len() == 1 {
                let internal_def = rustc_internal::internal(self.tcx, def);
                let variant_idx = InternalVariantIdx::from_usize(0);
                let discr = internal_def.discriminant_for_variant(self.tcx, variant_idx);
                let discr_val = sign_extend_discr_val(discr.val, discr.ty, self.tcx, POINTER_WIDTH);
                debug!(
                    local = place.local,
                    discriminant_val = discr_val,
                    "CHC translate_discriminant: single-variant enum — returning constant"
                );
                return Some(Expr::bitvec_const(discr_val, POINTER_WIDTH));
            }
        }

        // Rule E, exact arm (design trust-mc-reds-final §4.4): an enum whose
        // layout is `VariantsShape::Single { index }` — every other variant
        // uninhabited, e.g. `enum E { A(Infallible), B }` — has exactly one
        // possible discriminant, the VALUE of that variant
        // (`discriminant_for_variant`, the encoder's value convention), whatever
        // the place. Before, an unresolved place fell to a symbol confined to
        // the INDEX range `[0, n)`, which excludes the value whenever it is not
        // the index, and a counterexample through it was certified Genuine
        // (`zst_enum_variant_index_dual.rs::safe_iflet_b_direct`).
        if let Some(discr) = self.single_layout_enum_discriminant(ty) {
            return Some(discr);
        }

        // Part of #3798: Discriminant(*_ref) on ordinary `&_local` references
        // should reuse the target local's direct discriminant logic. This keeps
        // deref reads aligned with the precise enum-tag encodings already
        // available for direct locals (flattened Bool tags, enum_bv_layouts,
        // and zero-for-non-enum semantics).
        if place.projection.len() == 1 && matches!(place.projection[0], ProjectionElem::Deref) {
            let ref_local: usize = place.local;
            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&ref_local).cloned()
                && ref_target.projections.is_empty()
            {
                let ref_ty = self.body.locals().get(ref_local).map(|decl| decl.ty);
                if matches!(ref_ty.map(|ty| ty.kind()), Some(TyKind::RigidTy(RigidTy::Ref(..)))) {
                    let target_place =
                        rustc_public::mir::Place { local: ref_target.local, projection: vec![] };
                    if let Some(result) =
                        self.translate_discriminant(&target_place, modified_locals)
                    {
                        let target_local = ref_target.local;
                        debug!(
                            "translate_discriminant deref-to-target: *_{ref_local} -> local {target_local}"
                        );
                        return Some(result);
                    }
                }
            }
        }

        // Fix #1919: Use translate_place_with_deref to handle places with Deref projections
        // (e.g., `(*_11)` where _11 is a reference to the enum). This resolves the deref chain
        // via ref_targets tracking or memory loads at Mem level.
        let enum_expr = if let Some(expr) = self.translate_place_with_deref(place, modified_locals)
        {
            expr
        } else {
            // Part of #1905: Fallback for constant reference discriminants.
            // Pattern: Discriminant(*_N) where _N is assigned from a constant reference.
            // If we tracked the discriminant value during collection, return it directly.
            if place.projection.len() == 1 && matches!(place.projection[0], ProjectionElem::Deref) {
                let ref_local: usize = place.local;
                if let Some(&discr) = self.ref_resolution.const_ref_discriminants.get(&ref_local) {
                    debug!(ref_local, discr, "translate_discriminant: const ref → discriminant");
                    return Some(Expr::bitvec_const(discr as u128, POINTER_WIDTH));
                }
            }
            // #2876 and Rule E (design trust-mc-reds-final §4.4): the
            // unresolved-referent discriminant. The place's value is unknown, so
            // its discriminant is a symbol ranging over the discriminant VALUES
            // of the enum's variants (`discriminant_for_variant`, the encoder's
            // convention), never the index range `[0, n)`, which excludes a real
            // value whenever explicit discriminants exist. It is a sound value
            // havoc, booked as one (`DISCR_UNRESOLVED_REFERENT`, an audited
            // SoundHavoc reason) with its identity, so a counterexample that
            // reads it is OverApproximation unless recertified. Only a place
            // with a Deref reaches it legitimately; any other is booked
            // fail-closed as well.
            if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                && def.kind() == rustc_public::ty::AdtKind::Enum
                && !def.variants().is_empty()
            {
                let discr_name =
                    crate::codegen_ay::names::discr_sym_name(place.local, place.projection.len());
                warn!(
                    local = place.local,
                    "CHC translate_discriminant: unresolved referent — symbolic discriminant \
                     over the variants' discriminant values"
                );
                self.record_aggregate_gap("discr_pointer_deref_fallback");
                let booked = self.record_sound_fallback_reason_identified(
                    DISCR_UNRESOLVED_REFERENT,
                    Some(&discr_name),
                );
                if !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                    self.record_sound_fallback_reason(DISCR_UNRESOLVED_DIRECT_PLACE);
                }
                let discr = Havoc::booked(booked, discr_name, ptr_sort());
                let range = self.enum_discriminant_value_set(def, &discr);
                self.heap_state.pending_updates.push(range);
                return Some(discr);
            }
            // Part of #3798: `discriminant_value(&non_enum)` can lower to
            // `Discriminant(*_ref)` where the referent is a function item or
            // other non-ADT type. If the deref chain is unresolvable, the
            // semantic result is still zero, not fallback.
            if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _) | RigidTy::Coroutine(..))) {
                debug!(
                    local = place.local,
                    ?ty,
                    "CHC translate_discriminant: unresolvable non-enum pointer-deref -> zero"
                );
                return Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
            }
            warn!(
                local = place.local,
                "CHC translate_discriminant: unresolvable pointer-deref, no type fallback"
            );
            return None;
        };

        // Delegate to extracted helper for ADT-specific discriminant dispatch.
        // Handles unit enums, option-like, 2-variant both-payload, general N-variant,
        // BV-flattened, coroutine fallback, and non-enum zero.
        self.translate_adt_discriminant(place, ty, enum_expr)
    }

    /// The discriminant of an enum whose layout is `VariantsShape::Single`:
    /// the value of its one inhabited variant. `None` for any other type.
    pub(in crate::codegen_ay::chc) fn single_layout_enum_discriminant(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use rustc_public::abi::VariantsShape;
        use rustc_public_bridge::IndexedVal;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        if def.kind() != rustc_public::ty::AdtKind::Enum || def.variants().len() < 2 {
            return None;
        }
        let VariantsShape::Single { index } = ty.layout().ok()?.shape().variants else {
            return None;
        };
        let internal_def = rustc_internal::internal(self.tcx, def);
        let discr = internal_def
            .discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(index.to_index()));
        let value = sign_extend_discr_val(discr.val, discr.ty, self.tcx, POINTER_WIDTH);
        Some(Expr::bitvec_const(value, POINTER_WIDTH))
    }

    /// `discr` is the discriminant VALUE of one of `def`'s variants: the
    /// disjunction of `discr == discriminant_for_variant(v)` over every
    /// variant (a superset of the inhabited ones, so a sound range).
    pub(in crate::codegen_ay::chc) fn enum_discriminant_value_set(
        &self,
        def: rustc_public::ty::AdtDef,
        discr: &Expr,
    ) -> Expr {
        let internal_def = rustc_internal::internal(self.tcx, def);
        let mut values: Vec<u128> = (0..def.variants().len())
            .map(|idx| {
                let d = internal_def
                    .discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(idx));
                sign_extend_discr_val(d.val, d.ty, self.tcx, POINTER_WIDTH)
            })
            .collect();
        values.sort_unstable();
        values.dedup();
        values
            .into_iter()
            .map(|v| discr.clone().eq(Expr::bitvec_const(v, POINTER_WIDTH)))
            .reduce(Expr::or)
            .unwrap_or_else(|| Expr::bool_const(false))
    }

    fn try_coroutine_discriminant_expr(expr: &Expr) -> Option<Expr> {
        let discr = crate::codegen_ay::types::coroutine_discriminant_select(expr.clone())?;
        Some(match discr.sort().bitvec_width() {
            Some(width) if width < POINTER_WIDTH => discr.zero_extend(POINTER_WIDTH - width),
            Some(width) if width > POINTER_WIDTH => discr.extract(POINTER_WIDTH - 1, 0),
            _ => discr,
        })
    }
}

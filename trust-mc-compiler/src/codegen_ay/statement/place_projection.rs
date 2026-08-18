// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Projection chain application for place translation.
//!
//! Handles Deref (with ref_pointees/heap_pointees/synthesize fallbacks),
//! Field (datatype extraction), Downcast (variant tracking), Index (array select),
//! and ConstantIndex (constant array select) projections.
//!
//! Extracted from place.rs per #2140 for reviewability.

use super::{
    Expr, IndexedVal, IntoOption, Place, ProjectionElem, RigidTy, StatementCodegen, TyKind,
};
use crate::codegen_ay::provenance::is_transparent_pointer_wrapper_repr;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};
use ay_bindings::ExprValue;
use tracing::{debug, warn};

/// Cap on Ackermann-expanding a symbolic index over a nested array's length.
/// Lookup tables that need this (enum join/policy tables) are tiny; the cap
/// keeps the worst case bounded if the heuristic ever fires on a large array
/// (which falls back to a single `select` — sound, just AY-incomplete for the
/// array-valued case). 256 covers every realistic fieldless-enum table.
const NESTED_INDEX_ACKERMANN_LIMIT: usize = 256;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// If `expr` is a slice-like datatype carrying `fld_data`, return that
    /// backing array expression. Otherwise return None.
    fn try_select_backing_array(expr: &Expr) -> Option<Expr> {
        let dt_name = expr.sort().datatype_name()?;
        let dt = expr.sort().datatype_sort()?;
        let data_field = dt.constructors.first()?.field("fld_data")?;
        if !data_field.sort.is_array() {
            return None;
        }
        Some(expr.clone().field_select(dt_name, "fld_data", data_field.sort.clone()))
    }

    /// Static length `N` of the array being indexed by the `Index` projection at
    /// `proj_idx` in `place` (i.e. the type of `place` truncated to *before* this
    /// projection must be `[T; N]`). Returns `None` if the prefix type is not a
    /// fixed-length array or the length is not a known constant. Used to
    /// Ackermann-expand symbolic indices into nested arrays.
    fn array_len_before_index(&self, place: &Place, proj_idx: usize) -> Option<usize> {
        let base = Place { local: place.local, projection: place.projection[..proj_idx].to_vec() };
        let ty = base.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Array(_, len_const)) = ty.kind() else {
            return None;
        };
        Some(len_const.eval_target_usize().into_option()? as usize)
    }

    /// `select(expr, idx)`, but pushed through any `ite` spine first:
    /// `select(ite(c, A, B), idx)` → `ite(c, select(A, idx), select(B, idx))`,
    /// recursively. AY's array theory does not distribute `select` over an
    /// array-valued `ite` (the rows produced by Ackermann-expanding a symbolic
    /// nested-array index), so we do it here. Once the spine bottoms out at a
    /// real array term, a plain `select` is emitted — concrete-index after the
    /// expansion, which AY resolves soundly.
    fn select_distribute_ite(expr: Expr, idx: Expr) -> Expr {
        if let ExprValue::Ite { cond, then_expr, else_expr } = expr.value() {
            let cond = cond.clone();
            let then_sel = Self::select_distribute_ite(then_expr.clone(), idx.clone());
            let else_sel = Self::select_distribute_ite(else_expr.clone(), idx);
            Expr::ite(cond, then_sel, else_sel)
        } else {
            expr.select(idx)
        }
    }

    /// Apply the full projection chain to a root expression.
    ///
    /// Handles Deref (with ref_pointees/heap_pointees/synthesize fallbacks),
    /// Field (datatype extraction), Downcast (variant tracking), Index (array select),
    /// and ConstantIndex (constant array select) projections.
    ///
    /// Extracted from codegen_place per #2140 for reviewability.
    pub(super) fn apply_projection_chain(
        &mut self,
        place: &Place,
        root_expr: Expr,
        fn_name: &str,
        assert_downcast_variant_guards: bool,
    ) -> Option<Expr> {
        let mut expr = self.resolve_concrete_expr(&root_expr);
        let mut active_variant: Option<usize> = None; // Track Downcast variant for Field lookup
        for (proj_idx, proj) in place.projection.iter().enumerate() {
            match proj {
                ProjectionElem::Deref => {
                    // Handle Deref at any position in the projection chain (#431).
                    // Use projection-aware ref key to look up ref_pointees.
                    let ref_base = self.ssa_base_name_for_prefix(place, proj_idx);
                    if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() {
                        warn!(
                            "codegen_place: Deref ref_base={} -> pointee_base={}",
                            ref_base, pointee_base
                        );
                        if let Some(pointee_expr) = self.env_lookup(&pointee_base) {
                            warn!("codegen_place: Deref SUCCESS - sort {:?}", pointee_expr.sort());
                            expr = pointee_expr.clone();
                            active_variant = None;
                            continue;
                        }
                        if let Some(pointee_expr) =
                            self.ensure_derived_pointee_in_env(&pointee_base)
                        {
                            warn!(
                                "codegen_place: Deref fallback resolved pointee_base={} (sort={:?})",
                                pointee_base,
                                pointee_expr.sort()
                            );
                            expr = pointee_expr;
                            active_variant = None;
                            continue;
                        }
                        let deref_place = Place {
                            local: place.local,
                            projection: place.projection[..=proj_idx].to_vec(),
                        };
                        if let Some(pointee_expr) =
                            self.synthesize_pointee_expr(&pointee_base, &deref_place)
                        {
                            warn!(
                                "codegen_place: Deref synthesized pointee_base={} (sort={:?})",
                                pointee_base,
                                pointee_expr.sort()
                            );
                            expr = pointee_expr;
                            active_variant = None;
                            continue;
                        }
                        warn!(
                            "codegen_place: DEREF FAIL - env missing pointee_base={}",
                            pointee_base
                        );
                    } else {
                        debug!(
                            "codegen_place: ref_pointees missing ref_base={}, checking heap_pointees",
                            ref_base
                        );

                        let prefix_place = Place {
                            local: place.local,
                            projection: place.projection[..proj_idx].to_vec(),
                        };
                        if let Some(pointee_expr) =
                            self.try_ref_pointee_from_env_value(&ref_base, &prefix_place)
                        {
                            debug!(
                                "codegen_place Deref: recovered pointee from env value for {} (sort={:?})",
                                ref_base,
                                pointee_expr.sort()
                            );
                            expr = pointee_expr;
                            active_variant = None;
                            continue;
                        }

                        // #1112: Check heap_pointees for Box<T> fields and heap-allocated values.
                        // This handles derefs of Box fields in enum variants.
                        let heap_key = self.root_ssa_base_name(place);
                        if let Some(heap_value) = self.heap_pointees.get(heap_key.as_str()).cloned()
                        {
                            debug!(
                                "codegen_place Deref: found in heap_pointees[{}] (sort={:?})",
                                heap_key,
                                heap_value.sort()
                            );
                            // Apply remaining projections after this Deref
                            if proj_idx == place.projection.len() - 1 {
                                return Some(heap_value);
                            }
                            expr = heap_value;
                            active_variant = None;
                            continue;
                        }

                        // Also try ref_base as heap key
                        if let Some(heap_value) = self.heap_pointees.get(ref_base.as_str()).cloned()
                        {
                            debug!(
                                "codegen_place Deref: found in heap_pointees[{}] (ref_base, sort={:?})",
                                ref_base,
                                heap_value.sort()
                            );
                            if proj_idx == place.projection.len() - 1 {
                                return Some(heap_value);
                            }
                            expr = heap_value;
                            active_variant = None;
                            continue;
                        }

                        if self.ensure_ref_pointee_for_place(&prefix_place).is_some()
                            && let Some(pointee_base) =
                                self.ref_pointees.get(ref_base.as_str()).cloned()
                        {
                            debug!(
                                "codegen_place: Deref derived ref_base={} -> pointee_base={}",
                                ref_base, pointee_base
                            );
                            if let Some(pointee_expr) = self.env_lookup(&pointee_base) {
                                expr = pointee_expr.clone();
                                active_variant = None;
                                continue;
                            }
                            if let Some(pointee_expr) =
                                self.ensure_derived_pointee_in_env(&pointee_base)
                            {
                                expr = pointee_expr;
                                active_variant = None;
                                continue;
                            }
                            let deref_place = Place {
                                local: place.local,
                                projection: place.projection[..=proj_idx].to_vec(),
                            };
                            if let Some(pointee_expr) =
                                self.synthesize_pointee_expr(&pointee_base, &deref_place)
                            {
                                expr = pointee_expr;
                                active_variant = None;
                                continue;
                            }
                        }

                        // #1128: Final fallback - only synthesize for raw pointers.
                        // References should be tracked via ref_pointees; if missing, treat as unsupported.
                        let is_raw_ptr =
                            prefix_place.ty(self.body.locals()).into_option().is_some_and(|ty| {
                                matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
                            });
                        if is_raw_ptr {
                            // #1112: Final fallback - synthesize a fresh symbolic value for untracked deref.
                            // This handles dead code paths (e.g., derived PartialEq for enum variants
                            // with Box fields when only comparing A vs A).
                            let deref_place = Place {
                                local: place.local,
                                projection: place.projection[..=proj_idx].to_vec(),
                            };
                            // Part of #2267: pre-allocate instead of format!().
                            let synth_key = {
                                use std::fmt::Write;
                                let mut s = String::with_capacity(ref_base.len() + 12);
                                s.push_str(&ref_base);
                                s.push('_');
                                let _ = write!(s, "{}", proj_idx);
                                s
                            };
                            if let Some(pointee_expr) =
                                self.synthesize_pointee_expr(&synth_key, &deref_place)
                            {
                                debug!(
                                    "codegen_place: Deref synthesized fallback for {} (sort={:?})",
                                    ref_base,
                                    pointee_expr.sort()
                                );
                                if proj_idx == place.projection.len() - 1 {
                                    return Some(pointee_expr);
                                }
                                expr = pointee_expr;
                                active_variant = None;
                                continue;
                            }
                        }

                        // #1112: Final fallback for references - synthesize symbolic value.
                        // This handles cases like derived PartialEq for enums with Box<T> fields
                        // when the reference pointee wasn't tracked (e.g., unwrap() return value).
                        // Audit fix: Single type lookup instead of redundant calls.
                        if let Some(ref_ty) = prefix_place.ty(self.body.locals()).into_option()
                            && let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = ref_ty.kind()
                            && let Some(sort) = Self::infer_sort_from_ty(pointee_ty)
                        {
                            let name = self.ctx.fresh_name("ref_symbolic");
                            debug!(
                                "codegen_place Deref: synthesized symbolic ref pointee for {} (sort={:?})",
                                ref_base, sort
                            );
                            let symbolic_value = self.ctx.declare_var(&name, sort);
                            // Store in heap_pointees for consistency
                            self.heap_pointees.insert(
                                std::sync::Arc::from(ref_base.as_str()),
                                symbolic_value.clone(),
                            );
                            if proj_idx == place.projection.len() - 1 {
                                return Some(symbolic_value);
                            }
                            expr = symbolic_value;
                            active_variant = None;
                            continue;
                        }
                    }
                    // Fallback: Deref not tracked - report unsupported
                    let location = format!("{:?} (Deref at proj_idx {})", place, proj_idx);
                    self.ctx.unsupported("Deref projection not tracked", location);
                    return None;
                }
                ProjectionElem::Field(field, _ty) => {
                    // Part of #944: Handle transparent wrapper encoded as bv64 (NonNull/Unique).
                    // For field 0 projection on a pointer-width bitvector, the value IS the wrapper.
                    //
                    // Part of #1100: Also allow active_variant == Some(0) for ControlFlow::Continue
                    // from Try::branch stubs. When we Downcast to variant 0 on a bv64, the Field(0)
                    // should return the bv64 itself (it IS the Continue output).
                    // The shared REPRESENTATION predicate, identical to the one
                    // the post-deref walker and the CHC select/update pair use:
                    // it answers "was a wrapper flattened to this bv?", never
                    // "is this bv an address?". One definition keeps the four
                    // walkers from disagreeing about which slot field 0 is.
                    if is_transparent_pointer_wrapper_repr(expr.sort())
                        && *field == 0
                        && (active_variant.is_none() || active_variant == Some(0))
                    {
                        // Transparent wrapper or ControlFlow::Continue(bv64) - field(0) returns value unchanged
                        active_variant = None; // Reset after use
                        continue;
                    }
                    // Flattened Option<T> payloads can be represented directly as the payload
                    // bitvector in inlined Option methods. In the Some arm, Downcast(1)+Field(0)
                    // is transparent over that flattened payload.
                    if expr.sort().is_bitvec()
                        && *field == 0
                        && active_variant == Some(1)
                        && fn_name.contains("Option")
                    {
                        active_variant = None;
                        continue;
                    }
                    if let Some(selected) = crate::codegen_ay::types::coroutine_root_select(
                        expr.clone(),
                        active_variant,
                        *field,
                    ) {
                        expr = selected;
                        active_variant = None;
                        continue;
                    }
                    // Resolve constructor index: multi-variant requires Downcast
                    let cons_idx = match expr.sort().datatype_sort() {
                        Some(dt) if dt.constructors.len() > 1 => {
                            if let Some(idx) = active_variant {
                                idx
                            } else {
                                // SwitchInt→variant bridge (#3017): if a live fact provably
                                // pins the variant of this exact term, assert it and use
                                // that constructor instead of failing closed.
                                let enum_key = self.variant_fact_place_key(&Place {
                                    local: place.local,
                                    projection: place.projection[..proj_idx].to_vec(),
                                });
                                if let Some(ci) =
                                    self.bridge_variant_for_field(&expr, enum_key.as_ref())
                                {
                                    ci
                                } else {
                                    self.ctx.unsupported(
                                        "Field projection",
                                        format!(
                                            "Multi-variant enum '{}' requires Downcast before Field",
                                            dt.name
                                        ),
                                    );
                                    return None;
                                }
                            }
                        }
                        // Single-constructor: variant 0 is the only valid index.
                        Some(_) => active_variant.unwrap_or(0),
                        None => {
                            let location = format!("{:?}", place);
                            self.ctx.unsupported("Place field projection sort", location);
                            return None;
                        }
                    };

                    let field_idx = *field;
                    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
                        && let Some(selected) = args.get(field_idx)
                    {
                        expr = selected.clone();
                        active_variant = None;
                        continue;
                    }
                    if let Some(selected) =
                        crate::codegen_ay::types::datatype_field_select(expr, cons_idx, field_idx)
                    {
                        expr = selected;
                    } else {
                        let location = format!("{:?}", place);
                        self.ctx.unsupported("Place datatype field index", location);
                        return None;
                    }
                    active_variant = None; // Reset after use
                }
                ProjectionElem::Downcast(variant_idx) => {
                    // Downcast is used when matching on enum variants.
                    // Track the variant index for subsequent Field projections.
                    if !expr.sort().is_datatype() {
                        // Part of #1100: Allow Downcast on pointer-width bitvecs from Try::branch stubs.
                        // When Try::branch returns a raw bv64 (the success value) instead of a proper
                        // ControlFlow datatype, we allow the Downcast to proceed if:
                        // 1. It's a bv64 (pointer-width)
                        // 2. It's variant 0 (Continue - the success path we assume)
                        // Same shared representation predicate as the `Field`
                        // arm below and as `apply_post_deref_projections`.
                        if is_transparent_pointer_wrapper_repr(expr.sort())
                            && variant_idx.to_index() == 0
                        {
                            // Treat as transparent - the bv64 IS the Continue payload
                            active_variant = Some(0);
                            debug!(
                                "Downcast on bv64 to variant 0 - treating as transparent ControlFlow::Continue"
                            );
                        } else if expr.sort().is_bitvec()
                            && variant_idx.to_index() == 1
                            && fn_name.contains("Option")
                        {
                            active_variant = Some(1);
                            debug!(
                                "Downcast on flattened Option payload to Some - treating as transparent"
                            );
                        } else {
                            let location = format!("{:?}", place);
                            self.ctx.unsupported("Downcast on non-datatype", location);
                            return None;
                        }
                    } else {
                        let variant_index = variant_idx.to_index();
                        if assert_downcast_variant_guards
                            && let Some(dt) = expr.sort().datatype_sort()
                            && let Some(cons) = dt.constructors.get(variant_index)
                        {
                            let variant_guard = expr.clone().is_constructor(&dt.name, &cons.name);
                            debug!(
                                "codegen_place: emitting variant guard for {:?} -> is_{}",
                                place, cons.name
                            );
                            self.ctx.assert(variant_guard);
                        }
                        active_variant = Some(variant_index);
                        debug!(
                            "Downcast projection to variant {} - tracking for Field",
                            variant_index
                        );
                    }
                }
                ProjectionElem::Index(local) => {
                    // Index projection: arr[i] where local holds the index value.
                    // The expression should be an array. For slice datatypes, select
                    // the backing `fld_data` array first.
                    let indexed_base = self.ssa_base_name_for_prefix(place, proj_idx);
                    if let Some((elem_expr, _len)) =
                        self.repeat_array_values.get(indexed_base.as_str()).cloned()
                    {
                        expr = elem_expr;
                        active_variant = None;
                        debug!("Index projection: resolved repeated datatype array element");
                        continue;
                    }
                    if !expr.sort().is_array() {
                        if let Some(backing_array) = Self::try_select_backing_array(&expr) {
                            debug!(
                                "Index projection: extracted fld_data backing array from datatype {}",
                                expr.sort().datatype_name().unwrap_or("<unknown>")
                            );
                            expr = backing_array;
                        } else {
                            let location = format!("{:?} (sort: {:?})", place, expr.sort());
                            self.ctx.unsupported("Index projection on non-array", location);
                            return None;
                        }
                    }
                    let idx_name = crate::codegen_ay::names::local_name(fn_name, *local);
                    let idx_expr = if let Some(e) = self.env_lookup(&idx_name).cloned() {
                        e
                    } else {
                        // Try to look up the SSA-versioned name
                        let idx_ssa_name = self.ssa_name_from_base(&idx_name, false);
                        if let Some(e) = self.ctx.lookup_var(&idx_ssa_name) {
                            e.clone()
                        } else {
                            let location = format!("{:?} (index local: {})", place, local);
                            self.ctx.unsupported("Index projection - index not found", location);
                            return None;
                        }
                    };
                    // Extend index to pointer width if needed (arrays use POINTER_WIDTH index)
                    let idx_coerced = match idx_expr.sort().bitvec_width() {
                        Some(w) if w == POINTER_WIDTH => idx_expr,
                        Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
                        _ => {
                            // non-enum: Option<u32> from bitvec_width()
                            let location = format!("{:?}", place);
                            self.ctx.unsupported("Index projection - non-bitvec index", location);
                            return None;
                        }
                    };
                    // Select from the array.
                    //
                    // Nested arrays (element sort is itself an array, e.g. an
                    // `[[E; J]; N]` lookup table) trip AY's incomplete handling of
                    // array-valued selects (ay#5148): `select(outer, i)` for a
                    // *symbolic* `i` over array-valued elements is left unconstrained
                    // (→ spurious/`unknown` results), even though AY resolves a
                    // *concrete*-index select soundly. We Ackermann-expand the index
                    // over the array's statically-known Rust length:
                    //   select(a,i) = ite(i=0, a[0], ite(i=1, a[1], … ite(i=N-1, a[N-1], a[i])))
                    // Every `a[k]` is a concrete-index select (sound in AY). The row
                    // is an array-valued `ite`; AY does not push `select` through an
                    // array-valued `ite`, so `select_distribute_ite` does it for the
                    // *next* index, yielding `ite(i=k, select(a[k], j), …)` — all
                    // concrete-outer selects AY handles. The trailing symbolic `a[i]`
                    // fallback is reachable only out of bounds, where the separately
                    // emitted `array_bounds` check already fails, so this changes no
                    // in-bounds semantics and masks no OOB bug. Flat (scalar-element)
                    // arrays keep a single `select`, which AY handles directly.
                    let nested =
                        expr.sort().array_sort().is_some_and(|arr| arr.element_sort.is_array());
                    if nested
                        && let Some(n) = self.array_len_before_index(place, proj_idx)
                        && (1..=NESTED_INDEX_ACKERMANN_LIMIT).contains(&n)
                    {
                        let mut acc =
                            Self::select_distribute_ite(expr.clone(), idx_coerced.clone());
                        for k in (0..n).rev() {
                            let kc = Expr::bitvec_const(k as i128, POINTER_WIDTH);
                            let hit = Self::select_distribute_ite(expr.clone(), kc.clone());
                            acc = Expr::ite(idx_coerced.clone().eq(kc), hit, acc);
                        }
                        expr = acc;
                        debug!(
                            "Index projection: Ackermann-expanded symbolic select over \
                             nested array (len {}) to sidestep ay#5148",
                            n
                        );
                    } else {
                        expr = Self::select_distribute_ite(expr, idx_coerced);
                        debug!("Index projection: selected from array with index");
                    }
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    // ConstantIndex projection: arr[N] where N is a constant.
                    // Used in slice patterns and constant array indexing. For slice
                    // datatypes, select backing `fld_data` first.
                    // Part of #3186: parity with CHC ConstantIndex from_end handling.
                    // from_end means count from end: actual_index = min_length - offset.
                    // MIR guarantees min_length >= offset when from_end is true.
                    let actual_offset =
                        if *from_end { min_length.saturating_sub(*offset) } else { *offset };
                    let indexed_base = self.ssa_base_name_for_prefix(place, proj_idx);
                    if let Some((elem_expr, len)) =
                        self.repeat_array_values.get(indexed_base.as_str()).cloned()
                        && actual_offset < len
                    {
                        expr = elem_expr;
                        active_variant = None;
                        debug!(
                            "ConstantIndex projection: resolved repeated datatype array element"
                        );
                        continue;
                    }
                    if !expr.sort().is_array() {
                        if let Some(backing_array) = Self::try_select_backing_array(&expr) {
                            debug!(
                                "ConstantIndex projection: extracted fld_data backing array from datatype {}",
                                expr.sort().datatype_name().unwrap_or("<unknown>")
                            );
                            expr = backing_array;
                        } else {
                            let location = format!("{:?} (sort: {:?})", place, expr.sort());
                            self.ctx.unsupported("ConstantIndex projection on non-array", location);
                            return None;
                        }
                    }
                    let idx_expr = Expr::bitvec_const(actual_offset as i128, POINTER_WIDTH);
                    // Distribute through any `ite` spine (e.g. a row produced by
                    // Ackermann-expanding a symbolic outer index in `TABLE[a][CONST]`),
                    // so the constant select lands on real array terms AY can resolve.
                    expr = Self::select_distribute_ite(expr, idx_expr);
                    debug!(
                        "ConstantIndex projection: selected from array at offset {} (from_end={})",
                        actual_offset, from_end
                    );
                }
                _ => {
                    // external enum: ProjectionElem
                    let location = format!("{:?}", proj);
                    self.ctx.unsupported("Place projection", location);
                    return None;
                }
            }
        }

        Some(expr)
    }
}

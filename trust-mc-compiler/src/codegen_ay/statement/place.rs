// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Place translation for AY codegen.
//!
//! This module handles MIR Place translation to AY expressions:
//! - Local variable lookups with SSA versioning
//! - Field projections on structs/tuples
//! - Reference dereferencing with pointee tracking
//! - Raw pointer safety checks (null, alignment, provenance)
//! - Array indexing and slice operations

use super::place_deref_first::DerefFirstResult;
use super::place_post_deref::DerefProjectionResult;
use super::{Expr, IntoOption, Place, ProjectionElem, Sort, StatementCodegen};
use crate::codegen_ay::names::struct_sort;
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_public::ty::{RigidTy, TyKind};
use std::fmt::Write as _;
use std::sync::Arc;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn is_marker_bv32_sort(sort: &Sort) -> bool {
        sort.is_bitvec() && sort.bitvec_width() == Some(32)
    }

    /// Get the root SSA base name for a place (without projections).
    ///
    /// Returns `fn::local_N` format for use as a ref_pointees key.
    pub(super) fn root_ssa_base_name(&self, place: &Place) -> String {
        let fn_name = self.ctx.current_fn().map_or("unknown", |f| f.name.as_str());
        crate::codegen_ay::names::local_name(fn_name, place.local)
    }

    /// Bridge a FLATTENED Option value to its native-datatype view
    /// (#multi-hop-flattened-option, Link A).
    ///
    /// When a base is demanded as a whole value but exists only as the dotted
    /// flattened family — `{base}.0` = discriminant (Some = 1 / None = 0),
    /// `{base}.1` / `{base}_variant_1_field_0` = Some payload — and the place's
    /// inferred sort is an Option-shaped datatype (exactly one nullary None-like
    /// and one single-field Some-like constructor), rebuild the datatype value
    /// as `ite({base}.0 == 1, Some({payload}), None)`.
    ///
    /// Faithful by construction: every sub-expression is the REAL env value —
    /// never a fresh const (the previous behavior) or a default. Returns `None`
    /// on ANY shape/sort mismatch so the caller keeps its existing fallback:
    /// - non-datatype / non-Option-shaped sorts (incl. the `{base}_field_0/1`
    ///   CheckedBinaryOp tuple family, which has different semantics and no
    ///   dotted keys — it must NOT be bridged here);
    /// - a missing payload key, or a payload whose sort differs from the Some
    ///   field's sort (no width guessing);
    /// - a non-bitvec discriminant.
    fn try_reconstruct_option_from_flattened(&mut self, base: &str, place: &Place) -> Option<Expr> {
        let discrim = self.env_lookup(&crate::codegen_ay::names::discrim_name(base)).cloned()?;
        let discrim_width = discrim.sort().bitvec_width()?;

        let sort = self.infer_sort_from_place(place)?;
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() != 2 {
            return None;
        }
        let some_ctor = dt.constructors.iter().find(|c| {
            c.fields.len() == 1 && crate::codegen_ay::names::is_some_constructor(&c.name)
        })?;
        let none_ctor = dt.constructors.iter().find(|c| {
            c.fields.is_empty() && crate::codegen_ay::names::is_none_constructor(&c.name)
        })?;
        let dt_name = dt.name.clone();
        let some_name = some_ctor.name.clone();
        let none_name = none_ctor.name.clone();
        let payload_sort = some_ctor.fields[0].sort.clone();

        let payload = self
            .env_lookup(&crate::codegen_ay::names::payload_name(base))
            .cloned()
            .or_else(|| {
                self.env_lookup(&crate::codegen_ay::names::base_variant_field_name(base, 1, 0))
                    .cloned()
            })?;
        // Exact payload sort match only — a width or representation mismatch
        // means this is not the value the datatype view describes.
        if *payload.sort() != payload_sort {
            return None;
        }

        let is_some = discrim.eq(Expr::bitvec_const(1u64, discrim_width));
        let some_value =
            Expr::datatype_constructor(&dt_name, &some_name, vec![payload], sort.clone());
        let none_value = Expr::datatype_constructor(&dt_name, &none_name, vec![], sort);
        debug!(
            base,
            dt = %dt_name,
            "codegen_place: reconstructed flattened Option as datatype (Link A)"
        );
        Some(Expr::ite(is_some, some_value, none_value))
    }

    /// Translate a MIR Place into a AY expression.
    ///
    /// Handles local variables, references (via ref_pointees), raw pointers,
    /// and field/index projections.
    ///
    /// REQUIRES: place is a valid place from self.body
    /// ENSURES: Returns Some(expr) with expr.sort() matching place type
    /// ENSURES: Returns None if place cannot be translated (unsupported projection)
    pub(super) fn codegen_place(&mut self, place: &Place) -> Option<Expr> {
        // #408: For ZST types, return a canonical value immediately.
        // Fieldless structs are encoded as Bool in BMC sort inference, so they
        // must use a Bool sentinel here rather than the generic Unit datatype.
        // Other ZSTs continue using the Unit datatype sentinel.
        if let Some(ty) = place.ty(self.body.locals()).into_option()
            && Self::is_zst_type(ty)
        {
            if matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.kind() == rustc_public::ty::AdtKind::Struct
                        && def.variants().first().is_some_and(|variant| variant.fields().is_empty())
            ) {
                debug!(
                    "codegen_place: fieldless struct ZST {:?}, returning canonical Bool false",
                    ty
                );
                return Some(Expr::bool_const(false));
            }

            debug!("codegen_place: ZST type {:?}, returning phantom Unit", ty);
            let unit_sort = struct_sort("Unit", Vec::<(&str, Sort)>::new());
            // Constructor name is always "Unit_mk" per struct_type convention.
            let unit_value = Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort);
            return Some(unit_value);
        }

        self.emit_raw_ptr_deref_checks(place);

        // #1210: Handle Box<T> field access where Deref is not first projection.
        // For Box<T>, MIR generates: (*((b.0).0)).field
        // Projection chain: [Field(0), Field(0), Deref, Field(?)]
        // We detect this pattern and use heap_pointees with the Box local.
        if let Some(box_result) = self.try_codegen_box_field_access(place) {
            return Some(box_result);
        }

        // Handle Deref projection: follow reference to pointee.
        // Extracted to codegen_place_deref_first for readability.
        // NotDeref and Unresolved both fall through to non-deref paths (env lookup,
        // flattened tuples, etc.) — this preserves the original fallthrough behavior
        // where a Deref-first place that couldn't be resolved through deref-specific
        // paths would still try generic resolution.
        match self.codegen_place_deref_first(place) {
            DerefFirstResult::Resolved(expr) => return Some(expr),
            DerefFirstResult::Unsupported => return None,
            DerefFirstResult::NotDeref | DerefFirstResult::Unresolved => {}
        }

        // First, try looking up the full projected name directly in the environment.
        // This handles cases like CheckedBinaryOp where tuple fields are stored separately
        // (e.g., `fn::local_N_field_0` instead of as a datatype).
        let full_base_name = self.ssa_base_name(place);
        if let Some(expr) = self.env_lookup(&full_base_name) {
            return Some(expr.clone());
        }

        if place.projection.is_empty() {
            // Link A (#multi-hop-flattened-option): a value that exists ONLY in
            // the flattened dotted family (`{base}.0` discriminant / `{base}.1`
            // payload — e.g. `checked_sub`'s Option<u32>) but is demanded as a
            // whole datatype here used to get a FRESH UNCONSTRAINED const,
            // silently decoupling the datatype view from the real flattened
            // value (a spurious-CEX source on the ay-pb eval_lit chain).
            // Reconstruct `ite(.0 == 1, Some(.1), None)` from the REAL keys.
            if let Some(expr) = self.try_reconstruct_option_from_flattened(&full_base_name, place) {
                if let Some(v) = self.ssa_version.get_mut(full_base_name.as_str()) {
                    *v = (*v).max(1);
                } else {
                    self.ssa_version.insert(Arc::from(full_base_name.as_str()), 1);
                }
                self.env_update(full_base_name, expr.clone());
                return Some(expr);
            }

            // No projection - declare variable if not found
            let name = self.ssa_name_from_base(&full_base_name, false);
            let expr = if let Some(expr) = self.ctx.lookup_var(&name) {
                expr.clone()
            } else {
                let sort = self.infer_sort_from_place(place).unwrap_or_else(|| Sort::bitvec(32));
                self.ctx.declare_var(&name, sort)
            };

            // If the variable was never written, reserve `_0` for initial reads so the first
            // write produces version 1.  Use get_mut/insert to avoid cloning the key
            // in the common case (key already exists).
            if let Some(v) = self.ssa_version.get_mut(full_base_name.as_str()) {
                *v = (*v).max(1);
            } else {
                self.ssa_version.insert(Arc::from(full_base_name.as_str()), 1);
            }
            self.env_update(full_base_name, expr.clone());
            return Some(expr);
        }

        // Check if all projections are Field projections (needed for fallback path)
        let all_field_projections =
            place.projection.iter().all(|p| matches!(p, ProjectionElem::Field(..)));

        // Try to look up the root in the environment
        let base_name = self.root_ssa_base_name(place);
        let fn_name = base_name.rsplit_once("::local_").map_or("unknown", |(prefix, _)| prefix);

        let root_expr = self.env_lookup(&base_name).cloned();

        // Check if this is a flattened tuple (from kani::any() optimization #398).
        // If so, handle field projections directly from stored field expressions.
        if root_expr.is_none() && all_field_projections && !place.projection.is_empty() {
            if let Some(field_exprs) = self.flattened_tuples.get(base_name.as_str()) {
                // Extract the first Field projection index
                if let ProjectionElem::Field(field_idx, _) = &place.projection[0] {
                    let idx = *field_idx;
                    if idx < field_exprs.len() {
                        let mut result = field_exprs[idx].clone();
                        // Handle nested field projections if any
                        for proj in &place.projection[1..] {
                            if let ProjectionElem::Field(nested_field, _) = proj {
                                // Part of #944: Handle transparent wrapper bv64.
                                if result.sort().is_bitvec()
                                    && result.sort().bitvec_width() == Some(POINTER_WIDTH)
                                    && *nested_field == 0
                                {
                                    // Transparent wrapper - field(0) returns value unchanged
                                    continue;
                                }
                                // Nested field on a flattened tuple field.
                                // For multi-constructor enums, reject nested field access (#411)
                                if let Some(dt) = result.sort().datatype_sort()
                                    && dt.constructors.len() > 1
                                {
                                    self.ctx.unsupported(
                                        "Flattened tuple nested field",
                                        format!(
                                            "Multi-variant enum '{}' requires Downcast before Field",
                                            dt.name
                                        ),
                                    );
                                    return None;
                                }
                                // Single-constructor (struct/tuple): use first constructor.
                                // Expr clone is Arc-backed (O(1) refcount increment).
                                if let Some(selected) =
                                    crate::codegen_ay::types::datatype_field_select(
                                        result.clone(),
                                        0,
                                        *nested_field,
                                    )
                                {
                                    result = selected;
                                }
                            }
                        }
                        self.env_update(full_base_name, result.clone());
                        return Some(result);
                    }
                }
            }

            // Check for flattened tuple fields in current_env (#483).
            // Literal tuple aggregates store fields as `local_N_field_0`, `local_N_field_1`
            // directly in current_env (not in flattened_tuples which is for kani::any()).
            // For nested access like t.0.0, we need to:
            //   1. Find `local_N_field_0` in env (the inner tuple datatype)
            //   2. Apply remaining projections (field 0 of that datatype)
            if place.projection.len() >= 2
                && let ProjectionElem::Field(first_field_idx, _) = &place.projection[0]
            {
                let first_field_base =
                    crate::codegen_ay::names::indexed_field_name(&base_name, *first_field_idx);
                if let Some(first_field_expr) = self.env_lookup(&first_field_base).cloned() {
                    let mut result = first_field_expr;
                    let remaining_projections = place.projection.len() - 1;
                    let mut projections_applied = 0usize;
                    // Apply remaining projections (skip the first Field we already resolved)
                    for proj in &place.projection[1..] {
                        if let ProjectionElem::Field(nested_field, _) = proj {
                            // Part of #944: Handle transparent wrapper bv64.
                            if result.sort().is_bitvec()
                                && result.sort().bitvec_width() == Some(POINTER_WIDTH)
                                && *nested_field == 0
                            {
                                // Transparent wrapper - field(0) returns value unchanged
                                projections_applied += 1;
                                continue;
                            }
                            // For multi-constructor enums, reject nested field access (#411)
                            if let Some(dt) = result.sort().datatype_sort() {
                                if dt.constructors.len() > 1 {
                                    self.ctx.unsupported(
                                        "Nested field on flattened tuple",
                                        format!(
                                            "Multi-variant enum '{}' requires Downcast before Field",
                                            dt.name
                                        ),
                                    );
                                    return None;
                                }
                            } else {
                                // Not a datatype - can't project further, fall through
                                break;
                            }
                            match crate::codegen_ay::types::datatype_field_select(
                                result.clone(),
                                0,
                                *nested_field,
                            ) {
                                Some(selected) => {
                                    result = selected;
                                    projections_applied += 1;
                                }
                                None => {
                                    // Field index out of bounds or no constructors
                                    break;
                                }
                            }
                        } else {
                            // Non-field projection - fall through to fallback
                            break;
                        }
                    }
                    // Only return if ALL remaining projections were successfully applied
                    if projections_applied == remaining_projections {
                        self.env_update(full_base_name, result.clone());
                        return Some(result);
                    }
                    // Otherwise fall through to the fallback path below
                }
            }
        }

        // If root doesn't exist and we have only field projections, we can declare the
        // flattened name directly (for tuples stored field-by-field like CheckedBinaryOp).
        let root_expr = match root_expr {
            Some(expr) => expr,
            None if all_field_projections => {
                // Root not found but all projections are fields - declare flattened field variable
                let name = self.ssa_name_from_base(&full_base_name, false);
                let expr = if let Some(expr) = self.ctx.lookup_var(&name) {
                    expr.clone()
                } else {
                    let sort =
                        self.infer_sort_from_place(place).unwrap_or_else(|| Sort::bitvec(32));
                    self.ctx.declare_var(&name, sort)
                };

                if let Some(v) = self.ssa_version.get_mut(full_base_name.as_str()) {
                    *v = (*v).max(1);
                } else {
                    self.ssa_version.insert(Arc::from(full_base_name.as_str()), 1);
                }
                self.env_update(full_base_name, expr.clone());
                return Some(expr);
            }
            None => {
                // Root not in env - check if this is a flattened tuple with Deref (#431).
                // For places like (*_tuple.field).x, try to find the prefix up to Deref
                // in the environment as a flattened tuple field.
                let deref_idx =
                    place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref));
                if let Some(deref_idx) = deref_idx {
                    // Check if prefix is all fields (flattened tuple pattern)
                    let prefix_all_fields = place.projection[..deref_idx]
                        .iter()
                        .all(|p| matches!(p, ProjectionElem::Field(..)));
                    if prefix_all_fields && deref_idx > 0 {
                        // Try to look up the flattened field entry
                        let prefix_base = self.ssa_base_name_for_prefix(place, deref_idx);
                        if self.env_lookup(&prefix_base).is_some() {
                            debug!(
                                "codegen_place: found flattened tuple field {} for Deref",
                                prefix_base
                            );
                            // Now resolve Deref via ref_pointees.
                            // Try direct lookup, then attempt to derive mapping if missing (#697).
                            let pointee_base_opt =
                                self.ref_pointees.get(prefix_base.as_str()).cloned().or_else(
                                    || {
                                        self.ensure_ref_pointee_for_place(place);
                                        self.ref_pointees.get(prefix_base.as_str()).cloned()
                                    },
                                );
                            if let Some(pointee_base) = pointee_base_opt {
                                // Check if remaining projections after Deref are all fields
                                let remaining = &place.projection[deref_idx + 1..];
                                let remaining_all_fields = remaining
                                    .iter()
                                    .all(|p| matches!(p, ProjectionElem::Field(..)));

                                // Try direct lookup first (pointee is a non-flattened value)
                                if let Some(pointee_expr) = self.env_lookup(pointee_base.as_ref()) {
                                    let pointee_expr = pointee_expr.clone();
                                    // SwitchInt→variant bridge (#3017): `remaining` is the
                                    // tail after `deref_idx`, so the base offset is
                                    // `deref_idx + 1`.
                                    self.stage_bridge_enum_read(place, deref_idx + 1);
                                    // Apply remaining projections after Deref
                                    match self.apply_post_deref_projections(
                                        pointee_expr,
                                        remaining,
                                        true,  // strict: require Downcast before Field
                                        false, // hard failure
                                        "Flattened tuple Deref projection",
                                    ) {
                                        DerefProjectionResult::Success(expr) => {
                                            self.env_update(full_base_name, expr.clone());
                                            return Some(expr);
                                        }
                                        DerefProjectionResult::Unsupported => return None,
                                        DerefProjectionResult::Fallthrough => {
                                            warn!(
                                                "Flattened tuple Deref: unexpected Fallthrough with hard_failure=false"
                                            );
                                            return None;
                                        }
                                    }
                                } else if remaining_all_fields && !remaining.is_empty() {
                                    // Pointee is a flattened tuple - look up the flattened field directly
                                    // For (*_ref.field).0 where _ref.field -> _tuple (flattened),
                                    // construct _tuple_field_0 and look it up
                                    let mut flattened_name = String::with_capacity(
                                        pointee_base.len()
                                            + 16usize.saturating_mul(remaining.len()),
                                    );
                                    flattened_name.push_str(pointee_base.as_ref());
                                    for proj in remaining {
                                        if let ProjectionElem::Field(field, _) = proj {
                                            let _ = write!(flattened_name, "_field_{field}");
                                        }
                                    }
                                    if let Some(result) = self.env_lookup(&flattened_name).cloned()
                                    {
                                        debug!(
                                            "codegen_place: resolved flattened pointee field {}",
                                            flattened_name
                                        );
                                        self.env_update(full_base_name, result.clone());
                                        return Some(result);
                                    }
                                }
                            }
                        }
                    }
                }
                // Part of #949: Handle Downcast projections when root is not in env.
                // This occurs when a function call result (e.g., Entry::Vacant, Result::Ok)
                // wasn't codegenned but we're trying to access the variant's payload.
                // Solution: declare the root as a fresh symbolic value of its enum type,
                // then let the normal projection loop handle Downcast+Field.
                let first_is_downcast =
                    matches!(place.projection.first(), Some(ProjectionElem::Downcast(_)));
                if first_is_downcast {
                    // Get the root local's type (the enum type, not the projected field type)
                    let root_place = Place { local: place.local, projection: vec![] };
                    if let Some(root_sort) = self.infer_sort_from_place(&root_place) {
                        // Only handle datatype sorts (enums/structs)
                        if root_sort.is_datatype() {
                            let name = self.ssa_name_from_base(&base_name, false);
                            let expr = if let Some(expr) = self.ctx.lookup_var(&name) {
                                expr.clone()
                            } else {
                                debug!(
                                    "codegen_place #949: declaring fresh symbolic for Downcast root {} with sort {:?}",
                                    base_name, root_sort
                                );
                                self.ctx.declare_var(&name, root_sort)
                            };

                            // Track SSA version — use get_mut/insert to avoid
                            // cloning the key in the common case.
                            if let Some(v) = self.ssa_version.get_mut(base_name.as_str()) {
                                *v = (*v).max(1);
                            } else {
                                self.ssa_version.insert(Arc::from(base_name.as_str()), 1);
                            }
                            self.env_update(base_name.clone(), expr.clone());
                            if let Some(result_expr) =
                                self.apply_projection_chain(place, expr, &fn_name, true)
                            {
                                self.env_update(full_base_name, result_expr.clone());
                                return Some(result_expr);
                            }
                        }
                    }
                }

                // Root not in env and we have non-field projections - cannot handle
                let location = format!("{:?}", place);
                self.ctx.unsupported("Place projection base env missing", location);
                return None;
            }
        };

        self.apply_projection_chain(place, root_expr, &fn_name, false)
    }
}

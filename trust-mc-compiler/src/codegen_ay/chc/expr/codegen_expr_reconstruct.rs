// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Datatype reconstruction from flattened state variable slots.
//!
//! Split from codegen_expr.rs per #3199.
//! Contains: reconstruct_option_like_enum, reconstruct_result_like_enum,
//! reconstruct_nested_datatype_from_slots.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn omitted_flattened_enum_field_expr(sort: &Sort) -> Option<Expr> {
        if sort.is_bool() {
            return Some(Expr::bool_const(true));
        }
        Self::sort_default_expr(sort)
    }

    /// Reconstruct a flattened Option/Result-like enum (2 constructors) as an ITE.
    ///
    /// Flattened Option<T>: fld0 = Bool (is_some), fld1.. = payload leaf slots.
    /// Produces: `ITE(fld0, Some_ctor(payload), None_ctor())`.
    ///
    /// Part of #2876: recover test_option_array_simple where `[Some(4u8); 2]`
    /// requires bare-reading a flattened Option<u8> local for `Rvalue::Repeat`.
    pub(in crate::codegen_ay::chc) fn reconstruct_option_like_enum(
        &self,
        local_idx: usize,
        dt: &ay_bindings::DatatypeSort,
        sort: &ay_bindings::Sort,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::names::{is_none_constructor, is_some_constructor};

        // Identify None (0-field) and Some (1-field) constructors.
        let (none_ctor, some_ctor) =
            if dt.constructors[0].fields.is_empty() && dt.constructors[1].fields.len() == 1 {
                (&dt.constructors[0], &dt.constructors[1])
            } else if dt.constructors[1].fields.is_empty() && dt.constructors[0].fields.len() == 1 {
                (&dt.constructors[1], &dt.constructors[0])
            } else {
                debug!(
                    local_idx,
                    "reconstruct_option_like_enum: not an Option-like pattern (field counts)"
                );
                return None;
            };

        // Verify constructor names match Option convention.
        if !is_none_constructor(&none_ctor.name) || !is_some_constructor(&some_ctor.name) {
            debug!(
                local_idx,
                none = %none_ctor.name,
                some = %some_ctor.name,
                "reconstruct_option_like_enum: constructor names don't match Option pattern"
            );
            return None;
        }

        // fld0 = Bool (discriminant)
        let discr_expr = self.flattened_local_field_expr(local_idx, 0, modified_locals)?;

        if !discr_expr.sort().is_bool() {
            debug!(local_idx, "reconstruct_option_like_enum: fld0 is not Bool");
            return None;
        }

        let dt_name = &*dt.name;
        let payload_sort = &some_ctor.fields[0].sort;
        let total_fields = self.flattened_field_count(local_idx);
        let reconstruct_payload = || {
            let (payload_expr, consumed) = self.reconstruct_nested_datatype_from_slots(
                local_idx,
                1,
                payload_sort,
                modified_locals,
            )?;
            if 1 + consumed != total_fields {
                debug!(
                    local_idx,
                    total_fields,
                    consumed,
                    expected_payload_sort = ?payload_sort,
                    "reconstruct_option_like_enum: payload slot count mismatch"
                );
                return None;
            }
            Some(payload_expr)
        };

        // Part of #3507: When the discriminant is a concrete boolean constant,
        // return the active branch constructor directly. For None (false), skip
        // reading fld1 (payload may be unconstrained). For Some (true), skip
        // the ITE wrapper. Same rationale as the Result-like optimization.
        if let ExprValue::BoolConst(discr_val) = discr_expr.value() {
            if *discr_val {
                // Some variant — need the payload.
                let payload_expr = reconstruct_payload()?;
                if *payload_expr.sort() != *payload_sort {
                    debug!(
                        local_idx,
                        payload_sort = ?payload_expr.sort(),
                        expected = ?payload_sort,
                        "reconstruct_option_like_enum: payload sort mismatch (const discr)"
                    );
                    return None;
                }
                debug!(
                    local_idx,
                    dt_name, "translate_place: const-discr Option reconstruction → Some (#3507)"
                );
                return Some(Expr::datatype_constructor(
                    dt_name,
                    &*some_ctor.name,
                    vec![payload_expr],
                    sort.clone(),
                ));
            }
            // None variant — no payload needed.
            debug!(
                local_idx,
                dt_name, "translate_place: const-discr Option reconstruction → None (#3507)"
            );
            return Some(Expr::datatype_constructor(
                dt_name,
                &*none_ctor.name,
                vec![],
                sort.clone(),
            ));
        }

        // Symbolic discriminant — read payload and construct ITE.
        let payload_expr = reconstruct_payload()?;

        // Verify payload sort matches the Some constructor's field sort.
        if *payload_expr.sort() != *payload_sort {
            debug!(
                local_idx,
                payload_sort = ?payload_expr.sort(),
                expected = ?payload_sort,
                "reconstruct_option_like_enum: payload sort mismatch"
            );
            return None;
        }

        let some_expr =
            Expr::datatype_constructor(dt_name, &*some_ctor.name, vec![payload_expr], sort.clone());
        let none_expr = Expr::datatype_constructor(dt_name, &*none_ctor.name, vec![], sort.clone());

        debug!(
            local_idx,
            dt_name, "translate_place: reconstructed flattened Option-like enum as ITE"
        );
        Some(Expr::ite(discr_expr, some_expr, none_expr))
    }

    /// Reconstruct a flattened Result-like enum as an ITE expression.
    ///
    /// Supported layouts:
    /// - hetero `Result<T, E>`: fld0 = Bool (is_ok), fld1 = T, fld2 = E
    /// - same-sort `Result<T, T>`: fld0 = Bool (is_ok), fld1 = shared payload
    ///
    /// Produces `ITE(fld0, TrueCtor(payload), FalseCtor(payload_or_err))` where
    /// `TrueCtor` is the variant whose index matches
    /// `flattened_enum_discr.true_discr`.
    ///
    /// Part of #3490: inline Result comparison encoding gap. Without this, bare
    /// reads of flattened Result locals return None, causing PartialEq comparison
    /// to fall through to unconstrained fallback. Part of #3901 extends the same
    /// reconstruction to same-sort two-slot layouts like `Result<bool, bool>`.
    pub(in crate::codegen_ay::chc) fn reconstruct_result_like_enum(
        &self,
        local_idx: usize,
        dt: &ay_bindings::DatatypeSort,
        sort: &ay_bindings::Sort,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let n_fields = self.flattened_field_count(local_idx);
        let shared_payload = n_fields == 2;
        if !matches!(n_fields, 2 | 3) {
            debug!(local_idx, n_fields, "reconstruct_result_like_enum: unsupported flat arity");
            return None;
        }
        // Both constructors must have exactly 1 field (Result<T, E> where
        // T and E each occupy a single scalar slot).
        if dt.constructors[0].fields.len() != 1 || dt.constructors[1].fields.len() != 1 {
            debug!(local_idx, "reconstruct_result_like_enum: not a 2×1-field pattern");
            return None;
        }

        // Determine which variant maps to fld0=true (fld1) vs fld0=false (fld2)
        // using the precomputed flattened_enum_discr.
        let &(true_discr, _) = self.flatten.flattened_enum_discr.get(&local_idx)?;
        let true_discr_idx = true_discr as usize;
        if true_discr_idx >= dt.constructors.len() {
            return None;
        }
        let false_discr_idx = 1 - true_discr_idx;
        let true_ctor = &dt.constructors[true_discr_idx];
        let false_ctor = &dt.constructors[false_discr_idx];

        // fld0 = Bool discriminant
        let discr_expr = self.flattened_local_field_expr(local_idx, 0, modified_locals)?;

        if !discr_expr.sort().is_bool() {
            debug!(local_idx, "reconstruct_result_like_enum: fld0 is not Bool");
            return None;
        }

        let dt_name = &*dt.name;

        // Part of #3507: When the discriminant is a concrete boolean constant,
        // return the active branch constructor directly without reading the dead
        // branch's payload. This avoids introducing unconstrained state variables
        // from the inactive variant into the expression. For inline Result
        // temporaries (e.g., `Ok(true)` in `assert!(r == Ok(true))`), the dead
        // branch's fld is unconstrained. Including it in an ITE creates an
        // expression like `ITE(true, Ok(true), Err(FREE_VAR))` that PDR's
        // CHC invariant synthesis cannot simplify, producing spurious CTREX.
        if let ExprValue::BoolConst(discr_val) = discr_expr.value() {
            if *discr_val {
                // Discriminant is true — return the true-variant constructor.
                let true_payload =
                    self.flattened_local_field_expr(local_idx, 1, modified_locals)?;
                // Part of #4068: coerce payload sort when flattened slot sort
                // diverges from the DT field sort (e.g., ControlFlow with
                // Bool-flattened Break(BV128) from Result<Infallible, AccessError>).
                let true_payload =
                    Self::coerce_result_payload(true_payload, &true_ctor.fields[0].sort)
                        .or_else(|| {
                            debug!(
                                local_idx,
                                true_payload_sort = ?self.flattened_local_field_expr(local_idx, 1, modified_locals).map(|e| e.sort().clone()),
                                expected = ?true_ctor.fields[0].sort,
                                "reconstruct_result_like_enum: true_payload sort mismatch (const discr)"
                            );
                            None
                        })?;
                debug!(
                    local_idx,
                    dt_name,
                    variant = %true_ctor.name,
                    "translate_place: const-discr Result reconstruction → true variant (#3507)"
                );
                return Some(Expr::datatype_constructor(
                    dt_name,
                    &*true_ctor.name,
                    vec![true_payload],
                    sort.clone(),
                ));
            }
            // Discriminant is false — return the false-variant constructor.
            let false_payload = self.flattened_local_field_expr(
                local_idx,
                if shared_payload { 1 } else { 2 },
                modified_locals,
            )?;
            // Part of #4068: coerce payload sort (same rationale as true branch).
            let false_payload =
                Self::coerce_result_payload(false_payload, &false_ctor.fields[0].sort)
                    .or_else(|| {
                        debug!(
                            local_idx,
                            false_payload_sort = ?self.flattened_local_field_expr(local_idx, if shared_payload { 1 } else { 2 }, modified_locals).map(|e| e.sort().clone()),
                            expected = ?false_ctor.fields[0].sort,
                            "reconstruct_result_like_enum: false_payload sort mismatch (const discr)"
                        );
                        None
                    })?;
            debug!(
                local_idx,
                dt_name,
                variant = %false_ctor.name,
                "translate_place: const-discr Result reconstruction → false variant (#3507)"
            );
            return Some(Expr::datatype_constructor(
                dt_name,
                &*false_ctor.name,
                vec![false_payload],
                sort.clone(),
            ));
        }

        // Symbolic discriminant — read both payloads and construct ITE.
        let true_payload = self.flattened_local_field_expr(local_idx, 1, modified_locals)?;
        let false_payload = self.flattened_local_field_expr(
            local_idx,
            if shared_payload { 1 } else { 2 },
            modified_locals,
        )?;

        // Verify payload sorts match constructor field sorts, coercing if needed.
        // Part of #4068: flattened ControlFlow/Result types may have Bool or
        // narrow-BV payload slots representing wider DT fields (e.g., Bool for
        // Break(BV128) when the Break payload is Result<Infallible, AccessError>
        // opaqued as BV128). Use coerce_result_payload to bridge the gap.
        let true_payload =
            Self::coerce_result_payload(true_payload, &true_ctor.fields[0].sort).or_else(|| {
                debug!(
                    local_idx,
                    true_payload_sort = ?self.flattened_local_field_expr(local_idx, 1, modified_locals).map(|e| e.sort().clone()),
                    expected = ?true_ctor.fields[0].sort,
                    "reconstruct_result_like_enum: true_payload sort mismatch"
                );
                None
            })?;
        if shared_payload && true_ctor.fields[0].sort != false_ctor.fields[0].sort {
            debug!(
                local_idx,
                true_sort = ?true_ctor.fields[0].sort,
                false_sort = ?false_ctor.fields[0].sort,
                "reconstruct_result_like_enum: shared payload requires equal constructor field sorts"
            );
            return None;
        }
        let false_payload =
            Self::coerce_result_payload(false_payload, &false_ctor.fields[0].sort).or_else(|| {
                debug!(
                    local_idx,
                    false_payload_sort = ?self.flattened_local_field_expr(local_idx, if shared_payload { 1 } else { 2 }, modified_locals).map(|e| e.sort().clone()),
                    expected = ?false_ctor.fields[0].sort,
                    "reconstruct_result_like_enum: false_payload sort mismatch"
                );
                None
            })?;

        let true_expr =
            Expr::datatype_constructor(dt_name, &*true_ctor.name, vec![true_payload], sort.clone());
        let false_expr = Expr::datatype_constructor(
            dt_name,
            &*false_ctor.name,
            vec![false_payload],
            sort.clone(),
        );

        debug!(
            local_idx,
            dt_name,
            true_variant = %true_ctor.name,
            false_variant = %false_ctor.name,
            "translate_place: reconstructed flattened Result-like enum as ITE (#3490)"
        );
        Some(Expr::ite(discr_expr, true_expr, false_expr))
    }

    /// Reconstruct a BV-flattened multi-constructor enum as a Datatype ITE chain.
    ///
    /// Part of #4032: whole-enum reads for niche-encoded enums must rebuild the
    /// semantic enum value instead of concatenating the tag/payload slots into a
    /// raw BV. The raw concat is lossy for omitted ZST/unit fields and breaks
    /// derived `PartialEq` proofs on `niche_many_variants`.
    pub(in crate::codegen_ay::chc) fn reconstruct_multi_ctor_enum_from_layout(
        &self,
        local_idx: usize,
        dt: &ay_bindings::DatatypeSort,
        sort: &ay_bindings::Sort,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let layout = self.flatten.enum_bv_layouts.get(&local_idx)?;
        if dt.constructors.len() != layout.num_constructors || layout.num_constructors < 2 {
            return None;
        }

        let tag_expr = self.flattened_local_field_expr(local_idx, 0, modified_locals)?;
        let tag_is_bool = tag_expr.sort().is_bool();
        if tag_is_bool != (layout.num_constructors == 2) {
            debug!(
                local_idx,
                tag_sort = ?tag_expr.sort(),
                ctor_count = layout.num_constructors,
                "reconstruct_multi_ctor_enum_from_layout: tag sort mismatch"
            );
            return None;
        }

        let mut ctor_exprs = Vec::with_capacity(layout.num_constructors);
        for (ctor_idx, ctor) in dt.constructors.iter().enumerate() {
            let mut ctor_args = Vec::with_capacity(ctor.fields.len());
            for (field_idx, field) in ctor.fields.iter().enumerate() {
                if let Some(payload_slot) = layout.payload_slot(ctor_idx, field_idx) {
                    let (field_expr, _) = self.reconstruct_nested_datatype_from_slots(
                        local_idx,
                        1 + payload_slot,
                        &field.sort,
                        modified_locals,
                    )?;
                    ctor_args.push(field_expr);
                } else {
                    ctor_args.push(Self::omitted_flattened_enum_field_expr(&field.sort)?);
                }
            }
            ctor_exprs.push(Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                ctor_args,
                sort.clone(),
            ));
        }

        let mut result = ctor_exprs.last()?.clone();
        for ctor_idx in (0..layout.num_constructors.saturating_sub(1)).rev() {
            let guard = if tag_is_bool {
                match ctor_idx {
                    0 => tag_expr.clone().not(),
                    1 => tag_expr.clone(),
                    _ => return None,
                }
            } else {
                tag_expr.clone().eq(Expr::bitvec_const(ctor_idx as u64, layout.tag_bits))
            };
            result = Expr::ite(guard, ctor_exprs[ctor_idx].clone(), result);
        }

        debug!(
            local_idx,
            ctor_count = layout.num_constructors,
            "reconstruct_flattened_bare_read: rebuilt BV-flattened enum as Datatype"
        );
        Some(result)
    }

    /// Coerce a flattened payload expression to match a DT constructor field sort.
    ///
    /// Part of #4068: flattened enum locals may have payload slots whose sort
    /// diverges from the Datatype constructor field sort. This happens when:
    /// - `ControlFlow<Result<Infallible, AccessError>, &T>` has Break(BV128) but
    ///   the flattened fld2 is Bool (the AccessError part, opaqued during flatten)
    /// - `Result<(), AccessError>` has Bool fields but the DT expects BV
    ///
    /// Returns `Some(coerced_expr)` if the sorts already match or coercion
    /// succeeds, `None` if the sort gap is unbridgeable.
    fn coerce_result_payload(payload: Expr, target_sort: &Sort) -> Option<Expr> {
        if *payload.sort() == *target_sort {
            return Some(payload);
        }
        Self::coerce_flatten_slot_value(target_sort, payload)
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened Datatype reconstruction from leaf state variable slots.
//!
//! Extracted from `codegen_expr_reconstruct.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn reconstruct_nested_datatype_from_slots(
        &self,
        local_idx: usize,
        slot_offset: usize,
        sort: &Sort,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, usize)> {
        // Recursive flattening stops after MAX_FLATTEN_DEPTH and keeps the
        // remaining subtree in a single slot with its original Datatype sort.
        // Reuse that opaque leaf directly instead of drilling into children
        // that were never split into separate state vars.
        if sort.is_datatype()
            && let Some(expr) =
                self.flattened_local_field_expr(local_idx, slot_offset, modified_locals)
            && *expr.sort() == *sort
        {
            return Some((expr, 1));
        }

        // Base case: leaf scalar sort → consume one slot.
        if sort.is_bitvec() || sort.is_bool() || sort.is_int() || sort.is_real() || sort.is_array()
        {
            let expr = self.flattened_local_field_expr(local_idx, slot_offset, modified_locals)?;
            // Sort match guard: state var sort must match the expected leaf sort.
            if *expr.sort() != *sort {
                // Part of #4022 D5: BV-flattened enum payload slots may be wider
                // than a specific variant's field. E.g., Result<Percentage(u8), String>
                // shares payload slot 0 across Ok(BV8) and Err(BV64) — the slot sort
                // is BV(64) but Percentage::0 expects BV(8). Extract the low bits.
                if sort.is_bitvec() && expr.sort().is_bitvec() {
                    let expected_width = sort.bitvec_width().unwrap_or(0);
                    let actual_width = expr.sort().bitvec_width().unwrap_or(0);
                    if expected_width > 0 && actual_width > expected_width {
                        return Some((expr.extract(expected_width - 1, 0), 1));
                    }
                }
                return None;
            }
            return Some((expr, 1));
        }

        // Recursive case: single-constructor Datatype.
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let cons = &dt.constructors[0];
        let mut offset = slot_offset;
        let mut field_exprs = Vec::with_capacity(cons.fields.len());

        for field in &cons.fields {
            let (field_expr, consumed) = self.reconstruct_nested_datatype_from_slots(
                local_idx,
                offset,
                &field.sort,
                modified_locals,
            )?;
            field_exprs.push(field_expr);
            offset += consumed;
        }

        Some((
            Expr::datatype_constructor(&*dt.name, &*cons.name, field_exprs, sort.clone()),
            offset - slot_offset,
        ))
    }

    /// Reconstructs a flattened local from its leaf state variables when no projections
    /// are present. Tries each reconstruction strategy in order:
    /// 1. Single-constructor Datatype (struct-like)
    /// 2. Recursive nested Datatype
    /// 3. Option-like 2-ctor enum
    /// 4. Result-like 2-ctor 3-field enum
    /// 5. BV-flattened multi-ctor enum concat
    /// 6. Scalar-sort opaque Result payload
    ///
    /// Part of #3908: extracted from translate_place_with_modified bare-read section.
    pub(in crate::codegen_ay::chc) fn reconstruct_flattened_bare_read(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let n_fields = self.flattened_field_count(local_idx);
        if let Some(local_decl) = self.body.locals().get(local_idx)
            && let Some(sort) = Self::translate_ty(local_decl.ty)
            && let Some(dt) = sort.datatype_sort()
        {
            // Single-constructor (struct-like) Datatype reconstruction.
            if dt.constructors.len() == 1 && dt.constructors[0].fields.len() == n_fields {
                let ctor = &dt.constructors[0];
                let mut ctor_args = Vec::with_capacity(n_fields);
                for i in 0..n_fields {
                    let field_expr =
                        self.flattened_local_field_expr(local_idx, i, modified_locals)?;
                    ctor_args.push(field_expr);
                }
                // Verify state var sorts match Datatype field sorts.
                // Int-lifted locals (Range<T>) have Int state vars but
                // BV Datatype fields — reconstruction would create an
                // invalid or PDR-incompatible expression.
                let sorts_match = ctor_args
                    .iter()
                    .zip(ctor.fields.iter())
                    .all(|(arg, field)| *arg.sort() == field.sort);
                if sorts_match {
                    let dt_name = dt.name.clone();
                    let ctor_name = ctor.name.clone();
                    debug!(
                        local_idx,
                        n_fields,
                        dt_name = %dt_name,
                        "reconstruct_flattened_bare_read: reconstructed as Datatype"
                    );
                    return Some(Expr::datatype_constructor(dt_name, ctor_name, ctor_args, sort));
                }
                // Part of #3973: Int-lifted locals (Range<T>) have Int state
                // vars but BV Datatype fields. Datatype reconstruction is not
                // possible without sort conversion, but the flattened fields
                // ARE properly constrained via field-by-field assignment
                // (codegen_stmt_flatten Pattern 4). Return None WITHOUT
                // recording a translation drop — the encoding is sound and
                // precise at the field level.
                let is_int_lifted_mismatch =
                    ctor_args.iter().zip(ctor.fields.iter()).all(|(arg, field)| {
                        *arg.sort() == field.sort
                            || (arg.sort().is_int() && field.sort.bitvec_width().is_some())
                    });
                if is_int_lifted_mismatch {
                    debug!(
                        local_idx,
                        n_fields,
                        "reconstruct_flattened_bare_read: Int-lifted sort mismatch — \
                         suppressing translation drop (#3973)"
                    );
                    return None;
                }
                debug!(
                    local_idx,
                    n_fields,
                    "reconstruct_flattened_bare_read: skipping Datatype — sort mismatch (not Int-liftable)"
                );
            }
            // Part of #2970, #3589: Recursive reconstruction for recursively
            // flattened locals. Handles both:
            // - leaf count > field count (e.g., Outer{inner: Point{x,y}, val})
            // - leaf count == field count with nested single-field structs
            //   (e.g., Outer{outer_id: u8, inner: Inner{id: u8}}) where direct
            //   reconstruction fails sort mismatch (BV8 vs Inner{id: BV8}).
            // Groups consecutive leaf state vars into nested Datatype constructors.
            if dt.constructors.len() == 1 && dt.constructors[0].fields.len() <= n_fields {
                if let Some((expr, consumed)) = self.reconstruct_nested_datatype_from_slots(
                    local_idx,
                    0,
                    &sort,
                    modified_locals,
                ) {
                    if consumed == n_fields {
                        debug!(
                            local_idx,
                            n_fields,
                            consumed,
                            "reconstruct_flattened_bare_read: reconstructed recursively nested Datatype"
                        );
                        return Some(expr);
                    }
                }
            }
            // Option-like enum reconstruction (2 constructors).
            // Flattened Option<T>: fld0=Bool (is_some), fld1..=payload leaf slots.
            // Reconstruct as ITE(fld0, Some(payload), None()).
            // Part of #2876/#3207/#3814: recover flattened Option payloads
            // ranging from scalars to recursively flattened structs.
            if dt.constructors.len() == 2
                && let Some(result) =
                    self.reconstruct_option_like_enum(local_idx, &dt, &sort, modified_locals)
            {
                return Some(result);
            }
            // Result-like enum reconstruction (2 constructors, 2/3 fields).
            // Flattened Result<T, E>: fld0=Bool (is_ok), fld1=T, fld2=E.
            // Flattened Result<T, T>: fld0=Bool (is_ok), fld1=shared payload.
            // Reconstruct as ITE(fld0, Ok(payload), Err(payload_or_err)).
            // Part of #3490: inline Result comparison encoding gap.
            if dt.constructors.len() == 2
                && n_fields >= 2
                && let Some(result) =
                    self.reconstruct_result_like_enum(local_idx, &dt, &sort, modified_locals)
            {
                return Some(result);
            }
            if let Some(result) =
                self.reconstruct_multi_ctor_enum_from_layout(local_idx, &dt, &sort, modified_locals)
            {
                return Some(result);
            }
        }
        // Part of #3215 Phase 4: BV-flattened multi-ctor enum whole-local read.
        // Concat all state vars (tag + payload slots) into a single BV expression.
        // This enables stores, comparisons, and function arg passing for
        // multi-constructor enums without ADT reconstruction roundtrip.
        if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx) {
            let total_slots = 1 + layout.max_payload_slots; // tag + payload
            let mut parts: Vec<Expr> = Vec::with_capacity(total_slots);
            for i in 0..total_slots {
                let fld = self.flattened_local_field_expr(local_idx, i, modified_locals)?;
                // Bool tag (2-ctor enums) → BV1 for concat compatibility
                if fld.sort().is_bool() {
                    parts.push(Expr::ite(
                        fld,
                        Expr::bitvec_const(1u64, 1),
                        Expr::bitvec_const(0u64, 1),
                    ));
                } else if fld.sort().is_bitvec() {
                    parts.push(fld);
                } else if fld.sort().is_array() {
                    // Part of #4012: Array-sorted payload slots (e.g. [u8; 8]
                    // from Result<[u8; 8], _>) must be coerced to BV before concat.
                    // Compute the target BV width from the Array element sort and
                    // the Rust type's byte size (which encodes the array length).
                    let coerced = fld.sort().array_sort().and_then(|arr| {
                        let elem_bits = arr.element_sort.bitvec_width()?;
                        // Find the Rust array type in the enum's variant fields
                        // to get the element count, since SMT Array sort is unbounded.
                        let local_ty = self.body.locals().get(local_idx)?.ty;
                        let array_byte_size = Self::find_array_field_byte_size(local_ty)?;
                        let total_bits = byte_size_to_bv_width(array_byte_size);
                        if total_bits == 0 || total_bits % elem_bits != 0 {
                            return None;
                        }
                        Self::reinterpret_fixed_layout_expr(&fld, &Sort::bitvec(total_bits))
                    });
                    parts.push(coerced?);
                } else {
                    return None;
                }
            }
            // Concat from MSB (tag) to LSB (last payload slot)
            if let Some(result) = parts.into_iter().reduce(|acc, part| acc.concat(part)) {
                debug!(
                    local_idx,
                    total_slots,
                    "reconstruct_flattened_bare_read: reconstructed BV-flattened enum via concat (#3215)"
                );
                return Some(result);
            }
        }
        // Part of #3677: Scalar-sort flattened Result/enum reconstruction.
        // When translate_ty returns a scalar (BV128) for a flattened enum
        // (e.g., Result<Layout, LayoutError> opaqued by has_alloc_infra_arg),
        // the Datatype paths above don't fire. For same-sort Result<T,E>
        // flattened as (Bool tag, BV payload), return the payload field
        // directly — the opaque BV128 representation doesn't include the
        // discriminant, which is tracked separately in the tag state var.
        if n_fields == 2 {
            if let Some(tag_fld) = self.flattened_local_field_expr(local_idx, 0, modified_locals)
                && tag_fld.sort().is_bool()
                && let Some(payload_fld) =
                    self.flattened_local_field_expr(local_idx, 1, modified_locals)
            {
                if payload_fld.sort().is_bitvec() {
                    debug!(
                        local_idx,
                        n_fields,
                        "reconstruct_flattened_bare_read: returning payload of opaque-scalar flattened Result (#3677)"
                    );
                    return Some(payload_fld);
                }
                // Part of #4068: Handle (Bool tag, Bool payload) pattern for
                // unit-like Result types (e.g., Result<Infallible, AccessError>)
                // where translate_ty returns BV. Concat the two Bool fields as
                // BV1 values to produce the opaque BV representation.
                if payload_fld.sort().is_bool() {
                    let target_sort =
                        self.body.locals().get(local_idx).and_then(|ld| Self::translate_ty(ld.ty));
                    if let Some(sort) = target_sort
                        && sort.is_bitvec()
                    {
                        let target_width = sort.bitvec_width().unwrap_or(128);
                        let tag_bv1 = Expr::ite(
                            tag_fld,
                            Expr::bitvec_const(1u64, 1),
                            Expr::bitvec_const(0u64, 1),
                        );
                        let payload_bv1 = Expr::ite(
                            payload_fld,
                            Expr::bitvec_const(1u64, 1),
                            Expr::bitvec_const(0u64, 1),
                        );
                        let concat2 = tag_bv1.concat(payload_bv1);
                        // Zero-extend to target BV width.
                        let result = if target_width > 2 {
                            Expr::bitvec_const(0u64, target_width - 2).concat(concat2)
                        } else {
                            concat2
                        };
                        debug!(
                            local_idx,
                            n_fields,
                            target_width,
                            "reconstruct_flattened_bare_read: Bool/Bool → BV opaque Result (#4068)"
                        );
                        return Some(result);
                    }
                }
            }
        }
        self.diagnostics.place_translation_drop.inc();
        record_translation_drop_site_reason_for_fn(&self.fn_name, "flattened_bare_read");
        warn!(local_idx, n_fields, "reconstruct_flattened_bare_read: bare read failed");
        None
    }

    /// Part of #4012: Find the byte size of the first Array-typed field in an
    /// enum's variants. Used when a BV-flattened enum has an Array-sorted
    /// payload slot that must be coerced to BV for concat.
    fn find_array_field_byte_size(ty: rustc_public::ty::Ty) -> Option<u64> {
        use rustc_public::ty::{RigidTy, TyKind};
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        for variant in def.variants() {
            for field in variant.fields() {
                let fty = field.ty_with_args(&args);
                if matches!(fty.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                    return Some(fty.layout().ok()?.shape().size.bytes() as u64);
                }
            }
        }
        None
    }
}

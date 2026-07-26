// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BV-level projection update for flattened struct field assignments.
//!
//! Extracted from codegen_stmt_projection.rs per #3254 (packet 3).
//! Handles `root.field_chain = new_val` where `root` is a BV-encoded struct
//! by replacing the target field's bits via extract/concat.

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::projection_path::FieldProjection;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Shared BV projection update for direct-local and array-element field assignments.
    ///
    /// Handles `root.field_chain = new_val` where `root` is a BV-encoded struct by
    /// replacing the target field's bits via extract/concat. Supports multi-level
    /// projections (e.g., `x.inner.b = val`) through `compute_nested_flat_slot`.
    ///
    /// Part of #3086: Reuse BV projection logic for direct-local field assignments.
    pub(in crate::codegen_ay::chc) fn bv_projection_update(
        root: &Expr,
        root_ty: rustc_public::ty::Ty,
        field_projections: &[FieldProjection],
        new_val: Expr,
    ) -> Option<Expr> {
        if !root.sort().is_bitvec() || field_projections.is_empty() {
            return None;
        }
        // Only handle single-constructor (non-enum) shapes.
        if field_projections.iter().any(|fp| fp.cons_idx.is_some()) {
            return None;
        }
        let container_width = root.sort().bitvec_width()?;

        // Get the AY Datatype sort for the Rust type (pre-flattening).
        let type_sort = Self::translate_ty(root_ty)?;

        // Extract field indices from projections.
        let field_indices: Vec<usize> = field_projections.iter().map(|fp| fp.field_idx).collect();

        // Find the target leaf slot in the flattened layout.
        let leaf_slot = crate::codegen_ay::chc::codegen_decl_flatten::compute_nested_flat_slot(
            &type_sort,
            &field_indices,
        )?;

        // Get all leaf sorts and compute their BV widths.
        let leaf_sorts =
            crate::codegen_ay::chc::codegen_decl_flatten::collect_leaf_sorts(&type_sort, 0);
        let leaf_widths: Option<Vec<u32>> = leaf_sorts.iter().map(leaf_sort_bv_width).collect();
        let leaf_widths = leaf_widths?;

        // Verify total width matches the root BV.
        let total: u32 = leaf_widths.iter().sum();
        if total != container_width {
            debug!(
                container_width,
                total,
                ?field_indices,
                "bv_projection_update: total leaf width mismatch"
            );
            return None;
        }

        if leaf_slot >= leaf_widths.len() {
            return None;
        }
        let target_width = leaf_widths[leaf_slot];

        // Coerce new_val to the target BV width. Derive signedness from the
        // final field projection's type (MIR carries the concrete type).
        let signed = field_projections
            .last()
            .and_then(|fp| fp.field_ty)
            .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
            .unwrap_or(false);
        let new_val_bv =
            coerce_bitvec_width_safe(new_val, target_width, SignExtension::for_signedness(signed));
        // Post-coercion BV check — non-BV value causes sort mismatch in concat/extract.
        if new_val_bv.sort().bitvec_width().is_none() {
            warn!(
                sort = ?new_val_bv.sort(),
                target_width,
                ?field_indices,
                "bv_projection_update: non-BV value after coercion"
            );
            return None;
        }

        // BV flattening: leaf_0 at MSB, leaf_n at LSB.
        let bits_below: u32 = leaf_widths[leaf_slot + 1..].iter().sum();
        let bits_above: u32 = leaf_widths[..leaf_slot].iter().sum();

        let result = match (bits_above > 0, bits_below > 0) {
            (false, false) => new_val_bv,
            (false, true) => {
                // First leaf (MSB): new_val ++ lower_bits
                new_val_bv.concat(root.clone().extract(bits_below - 1, 0))
            }
            (true, false) => {
                // Last leaf (LSB): upper_bits ++ new_val
                root.clone()
                    .extract(container_width - 1, bits_below + target_width)
                    .concat(new_val_bv)
            }
            (true, true) => {
                // Middle leaf: upper ++ new_val ++ lower
                let upper = root.clone().extract(container_width - 1, bits_below + target_width);
                let lower = root.clone().extract(bits_below - 1, 0);
                upper.concat(new_val_bv).concat(lower)
            }
        };

        debug!(
            ?field_indices,
            leaf_slot,
            target_width,
            bits_above,
            bits_below,
            container_width,
            "bv_projection_update: extract/concat update (Part of #3086)"
        );
        Some(result)
    }

    /// BV field select: extract a field's bits from a flattened BV-encoded struct.
    ///
    /// Read-side counterpart to `bv_projection_update`. For a struct flattened to
    /// a single BV (e.g., `Copyable{a:u8, b:u32, c:Option<u16>}` → BV57), this
    /// extracts the target field's bits via `extract(hi, lo)`.
    ///
    /// Uses `compute_nested_flat_span` to handle both leaf (scalar) and non-leaf
    /// (nested struct/enum) fields. For non-leaf Datatype fields, attempts to
    /// unflatten the extracted bits back to the Datatype sort.
    pub(in crate::codegen_ay::chc) fn bv_field_select(
        root: &Expr,
        root_ty: rustc_public::ty::Ty,
        field_projections: &[FieldProjection],
    ) -> Option<Expr> {
        if !root.sort().is_bitvec() || field_projections.is_empty() {
            return None;
        }
        // Only handle single-constructor (non-enum) shapes.
        if field_projections.iter().any(|fp| fp.cons_idx.is_some()) {
            return None;
        }
        let container_width = root.sort().bitvec_width()?;

        // Get the AY Datatype sort for the Rust type (pre-flattening).
        let type_sort = Self::translate_ty(root_ty)?;

        // Extract field indices from projections.
        let field_indices: Vec<usize> = field_projections.iter().map(|fp| fp.field_idx).collect();

        // Find the target field's span in the flattened layout.
        // compute_nested_flat_span works for both leaf and non-leaf fields.
        let (span_offset, span_count) =
            crate::codegen_ay::chc::codegen_decl_flatten::compute_nested_flat_span(
                &type_sort,
                &field_indices,
            )?;

        // Get all leaf sorts and compute their BV widths.
        let leaf_sorts =
            crate::codegen_ay::chc::codegen_decl_flatten::collect_leaf_sorts(&type_sort, 0);
        let leaf_widths: Option<Vec<u32>> = leaf_sorts.iter().map(leaf_sort_bv_width).collect();
        let leaf_widths = leaf_widths?;

        // Verify total width matches the root BV.
        let total: u32 = leaf_widths.iter().sum();
        if total != container_width {
            debug!(
                container_width,
                total,
                ?field_indices,
                "bv_field_select: total leaf width mismatch"
            );
            return None;
        }

        if span_offset + span_count > leaf_widths.len() {
            return None;
        }

        // Compute bit range for the target field span.
        let target_width: u32 = leaf_widths[span_offset..span_offset + span_count].iter().sum();
        let bits_below: u32 = leaf_widths[span_offset + span_count..].iter().sum();

        if target_width == 0 {
            return None;
        }

        let extracted = root.clone().extract(bits_below + target_width - 1, bits_below);

        // For multi-leaf fields (nested struct/enum like Option<u16> encoded as BV17),
        // try to unflatten the extracted bits back to the Datatype sort.
        let result = if span_count > 1 {
            if let Some(field_ty) = field_projections.last().and_then(|fp| fp.field_ty)
                && let Some(target_sort) = Self::translate_ty(field_ty)
                && target_sort.is_datatype()
            {
                crate::codegen_ay::types::unflatten_bitvec_to_datatype(&extracted, &target_sort)
                    .unwrap_or(extracted)
            } else {
                extracted
            }
        } else {
            extracted
        };

        debug!(
            ?field_indices,
            span_offset,
            span_count,
            target_width,
            bits_below,
            container_width,
            "bv_field_select: extract field from flattened BV"
        );
        Some(result)
    }
}

/// Compute the BV width for a leaf sort in the flattened BV encoding.
///
/// Mirrors the convention used by the CHC encoder:
/// - BV(n) → n bits
/// - Bool → 8 bits (matching the existing flattening convention)
/// - Datatype → recursive sum via `flattenable_datatype_sort_width`
///
/// Part of #3086: shared helper for BV projection updates.
fn leaf_sort_bv_width(sort: &Sort) -> Option<u32> {
    if sort.is_bitvec() {
        sort.bitvec_width()
    } else if sort.is_bool() {
        Some(8)
    } else if sort.is_datatype() {
        crate::codegen_ay::types::flattenable_datatype_sort_width(sort)
    } else {
        None
    }
}

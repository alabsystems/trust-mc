// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT (struct/enum) aggregate construction for CHC encoding.
//!
//! Extracted from codegen_stmt_aggregate.rs per #2246 (500 LOC threshold).
//! Dispatcher method delegates to extracted helpers:
//! - `codegen_stmt_aggregate_adt_special.rs`: special-case early returns
//! - `codegen_stmt_aggregate_adt_struct_enum.rs`: struct + general enum paths
//! - `codegen_stmt_aggregate_adt_option.rs`: (inline) option-like 2-variant path
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgs, RigidTy, TyKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use crate::codegen_ay::chc::decl::codegen_types_adt::CodegenTypesAdt;
use crate::codegen_ay::names;
use crate::rustc_public_bridge::IndexedVal;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates an ADT (struct/enum) aggregate construction to a AY expression.
    ///
    /// Called from codegen_stmt_aggregate.rs.
    /// Matches the datatype encoding in translate_adt_sort:
    /// - Option-like enums: enum with None | Some(value: T)
    /// - Structs: struct with named fields
    /// - Unit enums: bitvec discriminant
    ///
    /// Delegates to extracted helpers for each major path:
    /// - `try_translate_adt_aggregate_special`: SIMD, transparent, BigInt, Layout, etc.
    /// - `try_translate_option_like_aggregate`: 2-variant one-empty/one-payload enums
    /// - `translate_struct_aggregate`: regular structs (Range, String, etc.)
    /// - `translate_general_enum_aggregate`: multi-variant enums (Result, ControlFlow)
    /// - `translate_union_aggregate`: union types
    pub(crate) fn translate_adt_aggregate(
        &mut self,
        def: AdtDef,
        variant_idx: rustc_public::ty::VariantIdx,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let variant_index = variant_idx.to_index();

        // Phase 1: Special-case early returns (SIMD, BigInt, Layout, unit enum, etc.)
        if let Some(result) = self.try_translate_adt_aggregate_special(
            def,
            variant_idx,
            args,
            operands,
            modified_locals,
        ) {
            return result;
        }

        // Phase 2: Option-like 2-variant enum (one empty + one payload).
        // Part of #4087: Returns None to fall through to general enum path
        // when deref_ref_ty fails (e.g., &str payload).
        let variants = def.variants();
        if variants.len() == 2 {
            if let Some(result) = self.try_translate_option_like_aggregate(
                def,
                variant_index,
                args,
                operands,
                modified_locals,
            ) {
                return Some(result);
            }
            // Option-like path failed. Fall through to general paths below.
        }

        // Phase 3: Array IntoIter special case.
        let adt_name = Self::adt_sort_name(def, args);
        let base_name = def.trimmed_name();
        if base_name == "IntoIter" && def.kind() == AdtKind::Struct && operands.len() == 2 {
            if let Some(result) =
                self.try_translate_into_iter_aggregate(def, args, operands, modified_locals)
            {
                debug!(
                    fn_name = %self.fn_name,
                    adt_name = %adt_name,
                    "Part of #3984: IntoIter aggregate special case applied"
                );
                return Some(result);
            }
            // Fall through to generic struct path if the special case didn't apply.
        }

        // Phase 4: Regular struct construction.
        if def.kind() == AdtKind::Struct && !variants.is_empty() {
            return self.translate_struct_aggregate(def, args, operands, modified_locals);
        }

        // Phase 5: General enum construction (multi-variant).
        if def.kind() == AdtKind::Enum {
            return self.translate_general_enum_aggregate(
                def,
                variant_index,
                args,
                operands,
                modified_locals,
            );
        }

        // Phase 6: Union aggregate.
        if def.kind() == AdtKind::Union {
            return self.translate_union_aggregate(
                def,
                variant_idx,
                args,
                operands,
                modified_locals,
            );
        }

        warn!(?def, "translate_adt_aggregate: unsupported ADT kind");
        // Part of #3369: Reclassified SOUND_APPROXIMATION -> DEMOTED.
        // Returning None triggers caller's self-loop (identity).
        self.record_fallback();
        None
    }

    /// Try to translate an Option-like 2-variant enum with payload sort coercion.
    ///
    /// This inline helper handles the Option-like path that was previously a
    /// closure inside translate_adt_aggregate. The full method with payload
    /// coercion lives in codegen_stmt_aggregate_adt_option.rs; this is the
    /// remaining inline logic for payload sort mismatches that needs access
    /// to the full set of coercion utilities.
    ///
    /// The actual method `try_translate_option_like_aggregate` is defined in
    /// `codegen_stmt_aggregate_adt_struct_enum.rs`.

    /// Part of #3984: Construct an Array IntoIter aggregate from MIR operands.
    ///
    /// MIR `IntoIter { data: [MaybeUninit<T>; N], alive: IndexRange }` has 2 fields,
    /// but our sort `IntoIter { fld_inner: PolymorphicIter { fld_alive, fld_data } }`
    /// has 1 field (PolymorphicIter wrapping both). This method bridges the structural
    /// mismatch by identifying the data array and alive range operands, then constructing
    /// the nested PolymorphicIter -> IntoIter Datatype expression.
    ///
    /// Returns `Some(expr)` on success, `None` to fall through to generic struct path.
    fn try_translate_into_iter_aggregate(
        &mut self,
        def: AdtDef,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let adt_name = Self::adt_sort_name(def, args);
        let into_iter_sort = Self::translate_adt_ty(def, args.clone())?;

        // Translate both MIR operands.
        let op0 = self.translate_operand_with_modified(&operands[0], modified_locals)?;
        let op1 = self.translate_operand_with_modified(&operands[1], modified_locals)?;

        // Identify which operand is the data array and which is the alive range.
        // MIR field order is [data, alive] per Rust's IntoIter struct definition.
        let (array_expr, range_expr) = if op0.sort().is_array() {
            (op0, op1)
        } else if op1.sort().is_array() {
            (op1, op0)
        } else {
            debug!(
                adt_name = %adt_name,
                op0_sort = ?op0.sort(),
                op1_sort = ?op1.sort(),
                "IntoIter aggregate: no Array operand, falling through"
            );
            return None;
        };

        // Extract PolymorphicIter sort from IntoIter { fld_inner: PolymorphicIter }.
        let dt = into_iter_sort.datatype_sort()?;
        let poly_sort = dt.constructors.first()?.fields.first()?.sort.clone();
        let poly_dt = poly_sort.datatype_sort()?;

        // Verify the PolymorphicIter has expected fields (fld_alive, fld_data).
        if poly_dt.constructors.len() != 1 || poly_dt.constructors[0].fields.len() != 2 {
            debug!(
                adt_name = %adt_name,
                poly_fields = poly_dt.constructors.first().map_or(0, |c| c.fields.len()),
                "IntoIter aggregate: unexpected PolymorphicIter shape"
            );
            return None;
        }

        // Construct PolymorphicIter(alive, data).
        // Field order in sort: [fld_alive (IndexRange), fld_data (Array)].
        let poly_ctor = names::resolve_ctor_name(&poly_sort, "PolymorphicIter");
        self.declare_datatype_sort_if_needed(&poly_sort);
        let poly_expr = Expr::datatype_constructor(
            "PolymorphicIter",
            poly_ctor,
            vec![range_expr, array_expr],
            poly_sort,
        );

        // Construct IntoIter(poly_expr).
        let into_iter_ctor = names::resolve_ctor_name(&into_iter_sort, "IntoIter");
        self.declare_datatype_sort_if_needed(&into_iter_sort);
        debug!(
            adt_name = %adt_name,
            "translate_adt_aggregate: IntoIter special case -- \
             constructed from MIR data + alive operands"
        );
        Some(Expr::datatype_constructor(adt_name, into_iter_ctor, vec![poly_expr], into_iter_sort))
    }
}

/// Sign-extend a discriminant value from the discriminant type's width to the target width.
///
/// `discriminant_for_variant` returns `val` as the unsigned bit pattern truncated to the
/// discriminant type width. For signed types (e.g., i8 with -1 = 0xFF = 255), this must
/// be sign-extended to the target bitvec width so that `bitvec_const(val, target_bits)`
/// produces the correct two's complement representation (e.g., 0xFFFFFFFF for -1 in BV32).
pub(crate) fn sign_extend_discr_val(
    val: u128,
    discr_ty: rustc_middle::ty::Ty<'_>,
    tcx: rustc_middle::ty::TyCtxt<'_>,
    target_bits: u32,
) -> u128 {
    let stable_ty = rustc_internal::stable(discr_ty);
    let (is_signed, src_bits) = match stable_ty.kind() {
        TyKind::RigidTy(RigidTy::Int(i)) => {
            (true, crate::codegen_ay::types::int_ty_to_bitvec_width(i))
        }
        TyKind::RigidTy(RigidTy::Uint(_)) => return val, // unsigned: no sign-extension
        _ => return val,
    };
    let _ = tcx; // used only for the stable conversion above
    if !is_signed || src_bits >= target_bits {
        return val;
    }
    // Check if sign bit is set in the source width.
    let sign_bit = 1u128 << (src_bits - 1);
    if val & sign_bit == 0 {
        return val; // positive value, no extension needed
    }
    // Fill bits above src_bits with 1s, then mask to target_bits.
    let ext_mask = !((1u128 << src_bits) - 1);
    let extended = val | ext_mask;
    if target_bits < 128 { extended & ((1u128 << target_bits) - 1) } else { extended }
}

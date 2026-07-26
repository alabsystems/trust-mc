// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Special-case ADT aggregate construction for CHC encoding.
//!
//! Extracted from codegen_stmt_aggregate_adt.rs per #4130 (500 LOC threshold).
//! Contains early-return handlers for specific ADT types that bypass the
//! normal struct/enum construction paths:
//! - SIMD aggregates (repr-SIMD passthrough)
//! - Transparent wrappers (ManuallyDrop, MaybeUninit, etc.)
//! - str::pattern internals (SplitInternal, SplitWhitespace, etc.)
//! - Opaque iterator adapters (FlatMap, Chain, Fuse)
//! - BigInt/BigUint/BigRational (SMT Int/Real)
//! - Layout and allocator infrastructure ADTs (bv128)
//! - Alloc-infra enum wrappers (Result<Layout, LayoutError>)
//! - Unit enums (discriminant as bitvec)

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use crate::rustc_public_bridge::IndexedVal;
use ay_bindings::{Expr, Sort};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgKind, GenericArgs, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::{ChcCtx, UNDEF_COUNTER, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::decl::codegen_decl_flatten::byte_size_to_bv_width;
use crate::codegen_ay::chc::decl::codegen_types_adt::CodegenTypesAdt;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to handle special-case ADT aggregate construction.
    ///
    /// Returns `Some(Some(expr))` if handled, `Some(None)` to signal a
    /// translation failure (caller should record fallback and return None),
    /// or `None` to fall through to normal struct/enum/option paths.
    pub(in crate::codegen_ay::chc) fn try_translate_adt_aggregate_special(
        &mut self,
        def: AdtDef,
        variant_idx: rustc_public::ty::VariantIdx,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Option<Expr>> {
        let variants = def.variants();
        let adt_name = Self::adt_sort_name(def, args);
        let variant_index = variant_idx.to_index();
        let base_name = def.trimmed_name();

        // Part of #3792: Single-field array wrapper aggregate -> passthrough to inner
        // array operand. Matches the structural check in translate_adt_sort (codegen_types_adt.rs)
        // which delegates these types to the inner array sort. Previously gated on
        // `def.0.name().contains("simd")` which missed user-defined types like `CustomSimd`
        // (case-sensitive mismatch) and `i64x2` (no "simd" substring at all).
        // The structural check (1 variant, 1 field of type [T; N], 1 operand) is sufficient.
        if variants.len() == 1 && variants[0].fields().len() == 1 && operands.len() == 1 {
            let field_ty = variants[0].fields()[0].ty_with_args(args);
            if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                debug!(
                    adt_name = %adt_name,
                    "translate_adt_aggregate: single-field array wrapper -> returning inner array operand"
                );
                return Some(self.translate_operand_with_modified(&operands[0], modified_locals));
            }
        }

        // Part of #912 / #2075: Transparent wrapper dispatch.
        if let Some(result) =
            self.try_translate_transparent_wrapper(&base_name, operands, modified_locals)
        {
            return Some(result);
        }

        // Part of #4117: str::pattern internals mapped to Bool.
        {
            let full_name = def.0.name();
            if base_name == "SplitInternal"
                || base_name == "SplitWhitespace"
                || base_name == "CharPredicateSearcher"
                || base_name == "IsWhitespace"
                || base_name == "IsNotEmpty"
                || (base_name == "Split" && full_name.contains("str"))
                || (base_name == "Filter"
                    && args.0.iter().any(|arg| format!("{arg:?}").contains("IsWhitespace")))
            {
                debug!(
                    adt_name = %adt_name,
                    "translate_adt_aggregate: str::pattern internal -> Bool (opaque, #4117)"
                );
                return Some(Some(Expr::bool_const(true)));
            }
        }

        // Part of #4160: opaque iterator adapters.
        if matches!(base_name.as_str(), "FlatMap" | "FlattenCompat" | "Chain" | "Fuse") {
            let name = chc_fresh_name("__opaque_iter_adapter_agg");
            debug!(
                adt_name = %adt_name,
                base_name = %base_name,
                "translate_adt_aggregate: opaque iterator adapter -> symbolic ptr_sort"
            );
            self.record_aggregate_gap("adt_opaque_iterator_adapter_symbolic");
            return Some(Some(declare_pending_var(name, ptr_sort())));
        }

        // Part of #3687: BigInt/BigUint -> SMT Int, BigRational/Ratio -> SMT Real.
        if base_name == "BigInt" || base_name == "BigUint" {
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let name = format!("bigint_agg_{undef_id}");
            debug!(
                adt_name = %adt_name,
                base_name = %base_name,
                "translate_adt_aggregate: BigInt/BigUint -> unconstrained Int"
            );
            self.record_aggregate_gap("adt_bigint_unconstrained");
            return Some(Some(declare_pending_var(name, Sort::int())));
        }
        if base_name == "BigRational" || base_name == "Ratio" {
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let name = format!("bigrational_agg_{undef_id}");
            debug!(
                adt_name = %adt_name,
                base_name = %base_name,
                "translate_adt_aggregate: BigRational/Ratio -> unconstrained Real"
            );
            self.record_aggregate_gap("adt_bigrational_unconstrained");
            return Some(Some(declare_pending_var(name, Sort::real())));
        }

        // #1979: Layout packs fields as concat(size, align).
        if base_name == "Layout" && operands.len() == 2 {
            let size_expr =
                self.translate_operand_with_modified(&operands[0], modified_locals).map_or_else(
                    || Expr::bitvec_const(0, POINTER_WIDTH),
                    |e| {
                        let coerced =
                            coerce_bitvec_width_safe(e, POINTER_WIDTH, SignExtension::ZeroExtend);
                        if coerced.sort().bitvec_width().is_some() {
                            coerced
                        } else {
                            warn!(sort = ?coerced.sort(), "Layout size: non-BV after coercion (#2992)");
                            Expr::bitvec_const(0, POINTER_WIDTH)
                        }
                    },
                );
            let align_expr =
                self.translate_operand_with_modified(&operands[1], modified_locals).map_or_else(
                    || Expr::bitvec_const(8, POINTER_WIDTH),
                    |e| {
                        let coerced =
                            coerce_bitvec_width_safe(e, POINTER_WIDTH, SignExtension::ZeroExtend);
                        if coerced.sort().bitvec_width().is_some() {
                            coerced
                        } else {
                            warn!(sort = ?coerced.sort(), "Layout align: non-BV after coercion (#2992)");
                            Expr::bitvec_const(8, POINTER_WIDTH)
                        }
                    },
                );
            debug!(
                adt_name = %adt_name,
                "translate_adt_aggregate: Layout -> concat(size, align)"
            );
            return Some(Some(size_expr.concat(align_expr)));
        }
        if Self::is_opaque_alloc_infra(def) {
            debug!(
                adt_name = %adt_name,
                "translate_adt_aggregate: allocator infra ADT -> unconstrained bv128"
            );
            return Some(Some(Expr::bitvec_const(0u128, 128)));
        }

        // Part of #2161: Enum wrappers around opaque alloc-infra types.
        if def.kind() == AdtKind::Enum {
            let has_alloc_infra_arg = args.0.iter().any(|arg| {
                if let GenericArgKind::Type(ty) = arg
                    && let TyKind::RigidTy(RigidTy::Adt(inner_def, _)) = ty.kind()
                {
                    return Self::is_opaque_alloc_infra(inner_def);
                }
                false
            });
            // Part of #3521: ControlFlow is now a proper Datatype, skip BV128 passthrough.
            if has_alloc_infra_arg && base_name != "ControlFlow" {
                let variant = &variants[variant_index];
                if !operands.is_empty() {
                    // Payload variant -> pass through inner bv128 value.
                    let inner = self
                        .translate_operand_with_modified(&operands[0], modified_locals)
                        .and_then(|e| {
                            let coerced =
                                coerce_bitvec_width_safe(e, 128, SignExtension::ZeroExtend);
                            if coerced.sort().bitvec_width() == Some(128) {
                                Some(coerced)
                            } else {
                                None
                            }
                        })
                        .unwrap_or_else(|| Expr::bitvec_const(0u128, 128));
                    debug!(
                        adt_name = %adt_name,
                        variant = %variant.name(),
                        "translate_adt_aggregate: alloc-infra enum payload -> bv128 passthrough"
                    );
                    return Some(Some(inner));
                }
                // Empty variant -> zero
                debug!(
                    adt_name = %adt_name,
                    variant = %variant.name(),
                    "translate_adt_aggregate: alloc-infra enum empty variant -> bv128(0)"
                );
                return Some(Some(Expr::bitvec_const(0u128, 128)));
            }
        }

        // Unit enum: return actual discriminant value as bitvector. This
        // matches translate_adt_sort, which encodes every fieldless enum as
        // BV32/BV64, including single-variant enums with explicit repr values.
        let is_unit_enum =
            def.kind() == AdtKind::Enum && variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            let internal_def = rustc_internal::internal(self.tcx, def);
            let variant_idx_internal = InternalVariantIdx::from_usize(variant_idx.to_index());
            let discr = internal_def.discriminant_for_variant(self.tcx, variant_idx_internal);
            let bits = Self::translate_adt_ty(def, args.clone())
                .and_then(|sort| sort.bitvec_width())
                .unwrap_or(POINTER_WIDTH);
            let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, self.tcx, bits);
            debug!(
                adt_name = %adt_name,
                variant_index,
                discriminant_val,
                bits,
                "CHC translate_adt_aggregate: unit enum -> bitvec const"
            );
            return Some(Some(Expr::bitvec_const(discriminant_val, bits)));
        }

        // Not a special case -- fall through to normal paths.
        None
    }

    /// Union aggregate construction.
    ///
    /// Models as BV write to union-sized bitvector. Matches translate_adt_sort
    /// which encodes unions as Sort::bitvec(byte_size * 8).
    pub(in crate::codegen_ay::chc) fn translate_union_aggregate(
        &mut self,
        def: AdtDef,
        variant_idx: rustc_public::ty::VariantIdx,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let variants = def.variants();
        let adt_name = Self::adt_sort_name(def, args);
        let variant_index = variant_idx.to_index();

        let union_ty = rustc_public::ty::Ty::from_rigid_kind(RigidTy::Adt(def, args.clone()));
        let layout = union_ty.layout().ok()?;
        let byte_size = layout.shape().size.bytes();
        if byte_size == 0 {
            debug!(adt_name = %adt_name, "union aggregate (0 bytes) -> Bool true");
            return Some(Expr::bool_const(true));
        }
        let bits = byte_size_to_bv_width(byte_size);
        if operands.is_empty() {
            // No operands -- ZST variant construction
            debug!(adt_name = %adt_name, bits, "union aggregate: ZST field -> bv zero");
            return Some(Expr::bitvec_const(0u64, bits));
        }
        // Translate the single operand and coerce to union width.
        let variant = &variants[variant_index];
        let field_ty = if !variant.fields().is_empty() {
            let f = &variant.fields()[0];
            Self::resolve_generic_ty(f.ty(), args)
        } else {
            None
        };
        // Check if the field is ZST
        let field_is_zst = field_ty
            .and_then(|ty| ty.layout().ok())
            .map(|l| l.shape().size.bytes() == 0)
            .unwrap_or(false);
        if field_is_zst {
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let name = format!("union_zst_{undef_id}");
            debug!(adt_name = %adt_name, bits, "union aggregate: ZST field -> unconstrained");
            return Some(declare_pending_var(name, Sort::bitvec(bits)));
        }
        if let Some(val) = self.translate_operand_with_modified(&operands[0], modified_locals) {
            let result = coerce_bitvec_width_safe(val, bits, SignExtension::ZeroExtend);
            debug!(adt_name = %adt_name, bits, "union aggregate: field -> coerced BV");
            return Some(result);
        }
        None
    }
}

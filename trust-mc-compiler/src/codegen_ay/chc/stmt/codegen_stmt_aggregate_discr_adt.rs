// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ADT-specific discriminant extraction for CHC encoding.
//!
//! Extracted from codegen_stmt_aggregate_discr.rs per #4130 (500 LOC threshold).
//! Contains `translate_adt_discriminant` which handles the final ADT-based
//! discriminant dispatch: unit enums, Option-like enums, 2-variant enums with
//! both payloads, general N-variant enums, BV-flattened enums, and fallbacks.

use ay_bindings::{Expr, Sort, SortInner};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::Place;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtDef, RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use super::codegen_stmt_aggregate_discr_literal_opt::literal_option_ctor_discr;
use crate::codegen_ay::names;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::{ChcCtx, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate a discriminant for an ADT type given the resolved enum expression.
    ///
    /// This is the final dispatch stage of `translate_discriminant`, handling
    /// all ADT-based discriminant extraction patterns:
    /// - Unit enums: value IS the discriminant, normalize to POINTER_WIDTH
    /// - Option-like (1 empty + 1 payload variant): has_payload predicate
    /// - 2-variant both-payload (Result<T,E>): is_constructor test
    /// - General N-variant: ITE chain over is_constructor tests
    /// - BV-flattened 2-variant: Bool tag or BV scalar normalization
    /// - Fallback: constrained symbolic discriminant
    ///
    /// Also handles coroutine and non-enum type fallbacks at the end.
    pub(in crate::codegen_ay::chc) fn translate_adt_discriminant(
        &mut self,
        place: &Place,
        ty: Ty,
        enum_expr: Expr,
    ) -> Option<Expr> {
        if let TyKind::RigidTy(RigidTy::Adt(def, _args)) = ty.kind() {
            let variants = def.variants();

            // Unit enum: value IS the discriminant.
            if let Some(result) = self.translate_unit_enum_discriminant(&def, &enum_expr) {
                return Some(result);
            }

            // Option-like enum: extract "has payload" predicate
            if let Some(result) = self.translate_option_like_discriminant(place, &def, &enum_expr) {
                return Some(result);
            }

            // 2-variant enum with both payloads (e.g., Result<T, E>)
            if let Some(result) = self.translate_two_variant_discriminant(place, &def, &enum_expr) {
                return Some(result);
            }

            // General enum (3+ variants): ITE chain
            let num_variants = variants.len();
            if let Some(result) = self.translate_general_enum_discriminant(place, &def, &enum_expr)
            {
                return Some(result);
            }

            // BV-flattened N-variant enum: tag in MSB, payload in remaining bits.
            // Extract tag bits and map to discriminant values via ITE chain.
            // This handles both 2-variant and 3+ variant BV-flattened enums
            // whose expression sort is a bitvec wider than the tag.
            if let Some(result) =
                self.translate_bv_flattened_nvariant_discriminant(&def, place, &enum_expr)
            {
                return Some(result);
            }

            // BV-flattened 2-variant Bool tag
            if num_variants == 2 && enum_expr.sort().is_bool() {
                return Some(self.translate_bv_flattened_bool_discriminant(&def, place, enum_expr));
            }

            // BV scalar discriminant normalization
            if let Some(result) = self.translate_bv_scalar_discriminant(&def, place, &enum_expr) {
                return Some(result);
            }

            // Fallback: non-Datatype sort -- constrained symbolic discriminant
            warn!(?place, num_variants, sort = ?enum_expr.sort(), "translate_discriminant: general enum non-Datatype sort");
            self.record_aggregate_gap("discr_non_datatype_sort");
            let discr_name =
                crate::codegen_ay::names::discr_sym_name(place.local, place.projection.len());
            let discr = declare_pending_var(discr_name, ptr_sort());
            let upper = Expr::bitvec_const(num_variants as u64, POINTER_WIDTH);
            self.heap_state.pending_updates.push(discr.clone().bvult(upper));
            Some(discr)
        } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            let discr_name =
                crate::codegen_ay::names::discr_sym_name(place.local, place.projection.len());
            warn!(?place, "translate_discriminant: coroutine fallback -> symbolic discriminant");
            self.record_aggregate_gap("discr_coroutine_fallback");
            let discr = declare_pending_var(discr_name, ptr_sort());
            let upper = Expr::bitvec_const(256u64, POINTER_WIDTH);
            self.heap_state.pending_updates.push(discr.clone().bvult(upper));
            Some(discr)
        } else {
            // Part of #3798: non-enum referents have discriminant value 0.
            debug!(?ty, "translate_discriminant: non-enum type -> zero");
            Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
        }
    }

    /// Unit enum: value IS the discriminant. Normalize to POINTER_WIDTH.
    fn translate_unit_enum_discriminant(&self, def: &AdtDef, enum_expr: &Expr) -> Option<Expr> {
        let variants = def.variants();
        if !variants.iter().all(|v| v.fields().is_empty()) {
            return None;
        }
        // Part of #3536: sign_extend for signed repr; default is isize (signed).
        let is_signed = {
            use rustc_public::abi::IntegerType;
            let dt = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
            matches!(
                dt,
                IntegerType::Fixed { is_signed: true, .. }
                    | IntegerType::Pointer { is_signed: true }
            )
        };
        Some(match enum_expr.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => enum_expr.clone(),
            Some(w) if w < POINTER_WIDTH && is_signed => {
                enum_expr.clone().sign_extend(POINTER_WIDTH - w)
            }
            Some(w) if w < POINTER_WIDTH => enum_expr.clone().zero_extend(POINTER_WIDTH - w),
            Some(w) if w > POINTER_WIDTH => enum_expr.clone().extract(POINTER_WIDTH - 1, 0),
            _ => enum_expr.clone(),
        })
    }

    /// Option-like enum discriminant: extract "has payload" predicate.
    fn translate_option_like_discriminant(
        &mut self,
        place: &Place,
        def: &AdtDef,
        enum_expr: &Expr,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return None;
        }

        let payload_idx = if v0_fields > 0 { 0 } else { 1 };
        let empty_idx = 1 - payload_idx;
        let sort = enum_expr.sort().clone();

        // Part of #4290: Fast-path for literal datatype constructors and
        // ITE-over-constructors. AY does NOT simplify `(is C (C v))` to `true`
        // during PDR projection, so emitting `ite(is-Some(Some_Option_t true),
        // 1, 0)` for a known-Some value leaves the discriminant expression
        // symbolic. PDR then explores the error rule `¬(v=0) ∧ ¬(v=1)`
        // as reachable, producing a false-CTREX (genuine-looking but
        // encoder-introduced). Inline the known discriminant value here.
        if let SortInner::Datatype(dt) = sort.inner() {
            let dt_name = dt.name.as_str();
            let payload_ctor_name =
                dt.constructors.iter().find(|c| !c.fields.is_empty()).map(|c| c.name.clone());
            if let Some(payload_ctor_name) = payload_ctor_name {
                if let Some(discr) = literal_option_ctor_discr(
                    enum_expr.value(),
                    dt_name,
                    &payload_ctor_name,
                    payload_idx,
                    empty_idx,
                ) {
                    debug!(
                        ?place,
                        payload_idx, "translate_option_like_discriminant: literal ctor fast-path"
                    );
                    return Some(discr);
                }
            }
        }

        let has_payload = match sort.inner() {
            SortInner::Datatype(dt) => {
                let dt_name = dt.name.as_str();
                let is_struct = dt.constructors.len() == 1
                    && dt.constructors[0].fields.len() == 2
                    && dt.constructors[0].fields[0].name == "is_some";
                if is_struct {
                    // Struct-style encoding (legacy)
                    enum_expr.clone().field_select(dt_name, "is_some", Sort::bool())
                } else {
                    // Part of #3041: use Sort metadata constructor names.
                    let ctor_name = match dt.constructors.iter().find(|c| !c.fields.is_empty()) {
                        Some(c) => c.name.as_str(),
                        None => return None,
                    };
                    enum_expr.clone().is_constructor(dt_name, ctor_name)
                }
            }
            _ if sort.is_bool() => {
                // Part of #2876: Bool proxy for Option/Result discriminants.
                enum_expr.clone()
            }
            _ => {
                if let Some(width) = sort.bitvec_width() {
                    // Bitvec scalar proxy: non-zero means payload variant.
                    enum_expr.clone().ne(Expr::bitvec_const(0u64, width))
                } else {
                    // Fallback: symbolic range
                    warn!(
                        ?place,
                        ?sort,
                        "translate_discriminant: option-like enum on unsupported sort -- symbolic fallback"
                    );
                    self.record_aggregate_gap("discr_option_like_unsupported_sort");
                    let discr_name = crate::codegen_ay::names::discr_sym_name(
                        place.local,
                        place.projection.len(),
                    );
                    let discr = declare_pending_var(discr_name, ptr_sort());
                    let upper = Expr::bitvec_const(2u64, POINTER_WIDTH);
                    self.heap_state.pending_updates.push(discr.clone().bvult(upper));
                    return Some(discr);
                }
            }
        };

        // Convert Bool to isize: ite(has_payload, payload_idx, empty_idx)
        Some(Expr::ite(
            has_payload,
            Expr::bitvec_const(payload_idx as u64, POINTER_WIDTH),
            Expr::bitvec_const(empty_idx as u64, POINTER_WIDTH),
        ))
    }

    /// 2-variant enum with both payloads (e.g., Result<T, E>).
    fn translate_two_variant_discriminant(
        &mut self,
        place: &Place,
        def: &AdtDef,
        enum_expr: &Expr,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let dt_name = enum_expr.sort().datatype_name()?;
        if !enum_expr.sort().is_datatype() {
            return None;
        }
        // Part of #4090: ensure the datatype sort is declared
        self.declare_datatype_sort_if_needed(enum_expr.sort());
        // Part of #3041: use Sort metadata constructor names.
        let variant_0_name = if let SortInner::Datatype(dt) = enum_expr.sort().inner()
            && !dt.constructors.is_empty()
        {
            dt.constructors[0].name.clone()
        } else {
            names::scope_option_ctor(variants[0].name(), dt_name)
        };
        let is_variant_0 = enum_expr.clone().is_constructor(dt_name, variant_0_name);
        debug!(
            ?place,
            "CHC translate_discriminant: 2-variant enum with payloads -- using is_constructor"
        );
        Some(Expr::ite(
            is_variant_0,
            Expr::bitvec_const(0u64, POINTER_WIDTH),
            Expr::bitvec_const(1u64, POINTER_WIDTH),
        ))
    }

    /// General enum (3+ variants): ITE chain over is_constructor tests.
    fn translate_general_enum_discriminant(
        &mut self,
        place: &Place,
        def: &AdtDef,
        enum_expr: &Expr,
    ) -> Option<Expr> {
        let variants = def.variants();
        let num_variants = variants.len();
        let dt_name = enum_expr.sort().datatype_name()?;
        if !enum_expr.sort().is_datatype() {
            return None;
        }
        // Part of #4090: ensure the datatype sort is declared
        self.declare_datatype_sort_if_needed(enum_expr.sort());
        let internal_def = rustc_internal::internal(self.tcx, *def);
        let last_idx = num_variants - 1;
        // Start with the last variant's discriminant as the default.
        let last_variant_idx = InternalVariantIdx::from_usize(last_idx);
        let last_discr = internal_def.discriminant_for_variant(self.tcx, last_variant_idx);
        let last_val =
            sign_extend_discr_val(last_discr.val, last_discr.ty, self.tcx, POINTER_WIDTH);
        let mut result = Expr::bitvec_const(last_val, POINTER_WIDTH);
        // Part of #3041: use Sort metadata constructor names.
        let mut sort_ctor_names: Vec<String> =
            if let SortInner::Datatype(dt) = enum_expr.sort().inner() {
                dt.constructors.iter().map(|c| c.name.clone()).collect()
            } else {
                (0..num_variants)
                    .map(|i| names::scope_option_ctor(variants[i].name(), dt_name))
                    .collect()
            };
        for i in (0..last_idx).rev() {
            let ctor_name = std::mem::take(&mut sort_ctor_names[i]);
            let is_variant = enum_expr.clone().is_constructor(dt_name, ctor_name);
            let variant_idx = InternalVariantIdx::from_usize(i);
            let discr = internal_def.discriminant_for_variant(self.tcx, variant_idx);
            let dv = sign_extend_discr_val(discr.val, discr.ty, self.tcx, POINTER_WIDTH);
            let discr_val = Expr::bitvec_const(dv, POINTER_WIDTH);
            result = Expr::ite(is_variant, discr_val, result);
        }
        debug!(
            ?place,
            num_variants, "CHC translate_discriminant: {num_variants}-variant enum -- ITE chain"
        );
        Some(result)
    }

    /// BV-flattened N-variant enum discriminant: extract tag from MSB of the
    /// concatenated BV representation and map to MIR discriminant values.
    ///
    /// For BV-flattened enums, the expression sort is `BV(tag_bits + payload_bits)`.
    /// The tag occupies the MSBs and encodes the constructor index (0..N-1).
    /// This method extracts the tag, then builds an ITE chain mapping each
    /// constructor index to its actual MIR discriminant value.
    fn translate_bv_flattened_nvariant_discriminant(
        &mut self,
        def: &AdtDef,
        place: &Place,
        enum_expr: &Expr,
    ) -> Option<Expr> {
        let total_width = enum_expr.sort().bitvec_width()?;
        let num_variants = def.variants().len();
        if num_variants < 2 {
            return None;
        }
        // Compute tag_bits: 1 for 2 variants, ceil(log2(N)) for N > 2.
        let tag_bits: u32 =
            if num_variants <= 2 { 1 } else { (num_variants as f64).log2().ceil() as u32 };
        // The expression must be wider than the tag (tag + payload).
        // If total_width == tag_bits, the enum has no payload (unit enum)
        // and should be handled by the unit enum or BV scalar path.
        if total_width <= tag_bits {
            return None;
        }
        let tag = enum_expr.clone().extract(total_width - 1, total_width - tag_bits);
        let d = |v: u64| Expr::bitvec_const(v, POINTER_WIDTH);
        let internal_def = rustc_internal::internal(self.tcx, *def);
        let discr_for = |i: usize| -> u64 {
            let disc =
                internal_def.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(i));
            sign_extend_discr_val(disc.val, disc.ty, self.tcx, POINTER_WIDTH) as u64
        };
        // Build ITE chain: if tag==0 then discr[0] else if tag==1 then discr[1] ... else discr[N-1]
        let last_discr = discr_for(num_variants - 1);
        let mut result = d(last_discr);
        for i in (0..num_variants - 1).rev() {
            let cond = tag.clone().eq(Expr::bitvec_const(i as u64, tag_bits));
            result = Expr::ite(cond, d(discr_for(i)), result);
        }
        debug!(
            ?place,
            num_variants,
            tag_bits,
            total_width,
            "CHC translate_discriminant: BV-flattened N-variant tag extract"
        );
        Some(result)
    }

    /// BV-flattened 2-variant Bool tag discriminant.
    fn translate_bv_flattened_bool_discriminant(
        &self,
        def: &AdtDef,
        place: &Place,
        enum_expr: Expr,
    ) -> Expr {
        let internal_def = rustc_internal::internal(self.tcx, *def);
        let discr0 =
            internal_def.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(0));
        let d0 = sign_extend_discr_val(discr0.val, discr0.ty, self.tcx, POINTER_WIDTH);
        let discr1 =
            internal_def.discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(1));
        let d1 = sign_extend_discr_val(discr1.val, discr1.ty, self.tcx, POINTER_WIDTH);
        debug!(
            ?place,
            d0, d1, "CHC translate_discriminant: BV-flattened 2-variant Bool tag via deref"
        );
        Expr::ite(
            enum_expr,
            Expr::bitvec_const(d1, POINTER_WIDTH),
            Expr::bitvec_const(d0, POINTER_WIDTH),
        )
    }

    /// BV scalar discriminant normalization to POINTER_WIDTH.
    fn translate_bv_scalar_discriminant(
        &self,
        def: &AdtDef,
        place: &Place,
        enum_expr: &Expr,
    ) -> Option<Expr> {
        let w = enum_expr.sort().bitvec_width()?;
        debug!(?place, bv_width = w, "CHC translate_discriminant: BV scalar for 2-variant enum");
        Some(match w.cmp(&POINTER_WIDTH) {
            std::cmp::Ordering::Equal => enum_expr.clone(),
            std::cmp::Ordering::Less => {
                // Sign-extend for signed repr, zero-extend otherwise.
                use rustc_public::abi::IntegerType;
                let is_signed = {
                    let dt = def.repr().int.unwrap_or(IntegerType::Pointer { is_signed: true });
                    matches!(
                        dt,
                        IntegerType::Fixed { is_signed: true, .. }
                            | IntegerType::Pointer { is_signed: true }
                    )
                };
                if is_signed {
                    enum_expr.clone().sign_extend(POINTER_WIDTH - w)
                } else {
                    enum_expr.clone().zero_extend(POINTER_WIDTH - w)
                }
            }
            std::cmp::Ordering::Greater => enum_expr.clone().extract(POINTER_WIDTH - 1, 0),
        })
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cast dispatch for CHC rvalue translation.
//!
//! Contains:
//! - `translate_rvalue_cast`
//! - `translate_reify_fn_pointer`

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{CastKind, Operand, PointerCoercion};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::canonical_zst_expr;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::codegen_call_cmp_string::float_to_int_saturating;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::super::codegen_expr_heap::obj_valid_out;
use super::super::codegen_expr_signedness::ExprSignedness;
use super::super::codegen_types::CodegenTypes;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Cast dispatch for rvalue translation.
    ///
    /// Extracted from translate_rvalue_with_modified per #3199.
    /// Handles CastKind dispatch including PointerCoercion, float casts, and Transmute.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_cast(
        &mut self,
        kind: &CastKind,
        operand: &Operand,
        target_ty: &rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        match kind {
            // Width-based casts: sort-based dispatch in translate_cast is correct.
            CastKind::IntToInt
            | CastKind::PtrToPtr
            | CastKind::FnPtrToPtr
            | CastKind::PointerExposeAddress
            | CastKind::Subtype => self.translate_cast(operand, *target_ty, modified_locals),
            // #3350: Integer-to-pointer cast has no allocation provenance.
            // obj_valid defaults to const_array(true), making validity checks
            // trivially true for never-allocated addresses. Invalidate the
            // resulting pointer's obj_id so dereference checks can catch it.
            CastKind::PointerWithExposedProvenance => {
                let result = self.translate_cast(operand, *target_ty, modified_locals);
                if !self.int_lift {
                    if let Some(ref ptr_expr) = result {
                        if let Some((obj_id, _offset)) = self.split_pointer(ptr_expr) {
                            let current_valid = self.current_obj_valid_array();
                            let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
                            self.heap_state.pending_updates.push(obj_valid_out().eq(invalidated));
                            self.mark_heap_metadata_modified();
                            debug!("#3350: invalidated obj_valid for PointerWithExposedProvenance");
                        }
                    }
                }
                result
            }
            // Pointer coercions: most are no-ops at BV level.
            CastKind::PointerCoercion(coercion) => match coercion {
                PointerCoercion::MutToConstPointer
                | PointerCoercion::UnsafeFnPointer
                | PointerCoercion::ArrayToPointer => {
                    self.translate_cast(operand, *target_ty, modified_locals)
                }
                // Part of #3470: ReifyFnPointer/ClosureFnPointer need unique IDs
                // so that fn pointer equality/inequality assertions work.
                // Without this, all reified fn pointers get the same BV64 value.
                PointerCoercion::ReifyFnPointer | PointerCoercion::ClosureFnPointer(_) => {
                    self.translate_reify_fn_pointer(operand)
                }
                // Unsize: thin → fat pointer (e.g., &[T; N] → &[T]).
                // Width cast loses vtable/length metadata.
                // Part of #3099: Skip fallback for ALL array-to-slice unsizing
                // (&[T;N]→&[T], Box<[T;N]>→Box<[T]>, *const etc.) because
                // array data is preserved in type-indexed memory.
                PointerCoercion::Unsize => {
                    // Part of #3159: dyn Trait coercion — construct Dyn_Trait
                    // with vtable discriminant for multi-impl dispatch.
                    if let Some(dyn_expr) =
                        self.try_translate_dyn_trait_coercion(operand, target_ty, modified_locals)
                    {
                        return Some(dyn_expr);
                    }
                    if !self.is_array_to_slice_unsize(operand, target_ty)
                        && !self.is_custom_dst_unsize(target_ty)
                    {
                        debug!(
                            ?target_ty,
                            "CHC: PointerCoercion::Unsize — metadata lost in BV cast (sound)"
                        );
                        self.diagnostics.place_translation_drop.inc();
                        record_translation_drop_site_reason_for_fn(
                            &self.fn_name,
                            "unsize_metadata_lost",
                        );
                    }
                    self.translate_cast(operand, *target_ty, modified_locals)
                }
            },
            // Float casts: not natively supported in CHC BV mode.
            // translate_cast's sort-based fallback catches Real↔BV mismatches,
            // but we record here explicitly so the cast kind is visible in metrics.
            // Part of #3099: Reclassified to SOUND_APPROXIMATION — float casts
            // produce a valid BV via translate_cast; imprecise but value-preserving.
            CastKind::FloatToInt => {
                // Part of #3668: try BV-level IEEE 754 extraction before fallback.
                use rustc_public::ty::{IntTy, UintTy};
                let width_signed = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Int(i)) => Some(match i {
                        IntTy::I8 => (8u32, true),
                        IntTy::I16 => (16, true),
                        IntTy::I32 => (32, true),
                        IntTy::I64 => (64, true),
                        IntTy::I128 => (128, true),
                        IntTy::Isize => (POINTER_WIDTH, true),
                    }),
                    TyKind::RigidTy(RigidTy::Uint(u)) => Some(match u {
                        UintTy::U8 => (8u32, false),
                        UintTy::U16 => (16, false),
                        UintTy::U32 => (32, false),
                        UintTy::U64 => (64, false),
                        UintTy::U128 => (128, false),
                        UintTy::Usize => (POINTER_WIDTH, false),
                    }),
                    _ => None,
                };
                if let Some((tw, signed)) = width_signed
                    && let Some(src) =
                        self.translate_operand_with_modified(operand, modified_locals)
                {
                    // Part of #3787: keep CHC float-to-int casts on the BV
                    // extractor path, but wrap them in saturating `as`
                    // semantics for NaN, infinities, and out-of-range values.
                    let result = float_to_int_saturating::build_float_to_int_saturating_expr(
                        &src, tw, signed,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::float_to_int_saturating_bv(
                            src.clone(),
                            tw,
                            signed,
                        )
                    });

                    if let Some(result) = result {
                        debug!(
                            ?kind,
                            "CHC: FloatToInt saturating cast via precise lowering (Part of #3787)"
                        );
                        return Some(result);
                    }
                }
                debug!(?kind, "CHC: FloatToInt fallback — sound over-approximation");
                self.record_sound_fallback_reason("float_to_int_fallback");
                self.translate_cast(operand, *target_ty, modified_locals)
            }
            CastKind::IntToFloat => {
                // Part of #3465: precise integer→float via pure BV operations.
                // Uses IEEE 754 bit manipulation with RNE rounding — no FP
                // rounding-mode terms emitted, so Z3's CHC parser accepts it.
                // Falls back to FP-theory version for BMC/SMT paths.
                use rustc_public::ty::FloatTy;
                let target_float_width = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32u32),
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
                    _ => None,
                };
                if let Some(fw) = target_float_width
                    && let Some(src) =
                        self.translate_operand_with_modified(operand, modified_locals)
                {
                    let signed = self.operand_signedness_for_cast(operand).unwrap_or(false);
                    // Try pure BV first (CHC-safe), then FP theory fallback.
                    if let Some(result) = crate::codegen_ay::float_arithmetic::int_to_float_bv_pure(
                        src.clone(),
                        signed,
                        fw,
                    )
                    .or_else(|| {
                        crate::codegen_ay::float_arithmetic::int_to_float_bv(src, signed, fw)
                    }) {
                        debug!(?kind, "CHC: IntToFloat via pure BV (Part of #3465)");
                        return Some(result);
                    }
                }
                debug!(?kind, "CHC: IntToFloat fallback — sound over-approximation");
                self.record_sound_fallback_reason("int_to_float_fallback");
                self.translate_cast(operand, *target_ty, modified_locals)
            }
            CastKind::FloatToFloat => {
                // Part of #3465: precise float↔float via AY FP theory.
                use rustc_public::ty::FloatTy;
                let src_float_width = match operand.ty(self.body.locals()).ok().map(|t| t.kind()) {
                    Some(TyKind::RigidTy(RigidTy::Float(FloatTy::F32))) => Some(32u32),
                    Some(TyKind::RigidTy(RigidTy::Float(FloatTy::F64))) => Some(64),
                    _ => None,
                };
                let tgt_float_width = match target_ty.kind() {
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32u32),
                    TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
                    _ => None,
                };
                if let (Some(sw), Some(tw)) = (src_float_width, tgt_float_width)
                    && let Some(src) =
                        self.translate_operand_with_modified(operand, modified_locals)
                {
                    // Try pure BV first (CHC-safe), then FP theory fallback. Part of #3870.
                    if let Some(result) =
                        crate::codegen_ay::float_arithmetic::float_to_float_bv_pure(
                            src.clone(),
                            sw,
                            tw,
                        )
                        .or_else(|| {
                            crate::codegen_ay::float_arithmetic::float_to_float_bv(src, sw, tw)
                        })
                    {
                        debug!(?kind, "CHC: FloatToFloat via pure BV (Part of #3870)");
                        return Some(result);
                    }
                }
                debug!(?kind, "CHC: FloatToFloat fallback — sound over-approximation");
                self.record_sound_fallback_reason("float_to_float_fallback");
                self.translate_cast(operand, *target_ty, modified_locals)
            }
            // Transmute: bit reinterpretation. Same-sort → identity in SMT.
            // Cross-sort → unsound (e.g., f32→u32 when f32 maps to Real).
            CastKind::Transmute => {
                let expr = self.translate_operand_with_modified(operand, modified_locals)?;
                let target_sort = Self::translate_ty(*target_ty);

                // `transmute_unchecked` with size_of(Src) != size_of(Dst) is
                // UNCONDITIONAL Rust UB. rustc emits `CastKind::Transmute` only for
                // `transmute` / `transmute_unchecked`, and `mem::transmute` is
                // compile-time size-checked equal (a mismatch never reaches MIR), so
                // any size-mismatched `Transmute` came from `transmute_unchecked` and
                // is UB on every execution that reaches it. Emit an unconditional
                // (block-reachability-gated) per-property error via `pending_checks`,
                // and havoc the destination through an ACCOUNTED sound approximation
                // (Task #78 `place_translation_drop` — routed via
                // `record_sound_fallback_reason_identified`, NOT the DEMOTED
                // coercion/`chc_fallback` path) so the genuine counterexample can
                // recertify Genuine instead of being demoted EncodingGap. Compares
                // exact Rust ABI byte sizes, never SMT sort widths; requires BOTH
                // layouts to resolve concretely (else no new check — sound).
                if let Some(ref ts) = target_sort
                    && let Ok(src_ty) = operand.ty(self.body.locals())
                    && let (Some(src_sz), Some(dst_sz)) = (
                        src_ty.layout().ok().map(|l| l.shape().size.bytes()),
                        (*target_ty).layout().ok().map(|l| l.shape().size.bytes()),
                    )
                    && src_sz != dst_sz
                {
                    debug!(
                        src_sz,
                        dst_sz,
                        ?src_ty,
                        ?target_ty,
                        "CHC: transmute_unchecked size mismatch — emitting unconditional UB check"
                    );
                    self.heap_state.pending_checks.push(Expr::bool_const(false));
                    self.record_sound_fallback_reason_identified(
                        "transmute_size_mismatch_ub",
                        None,
                    );
                    return Some(declare_pending_var(
                        chc_fresh_name("__transmute_size_mismatch_ub"),
                        ts.clone(),
                    ));
                }

                match target_sort {
                    Some(ref ts) if *ts == *expr.sort() => Some(expr),
                    Some(ref ts) => {
                        if let Ok(src_ty) = operand.ty(self.body.locals())
                            && self.transmute_requires_layout_fallback(
                                src_ty,
                                *target_ty,
                                expr.sort(),
                                ts,
                            )
                        {
                            debug!(
                                src_sort = ?expr.sort(),
                                target_sort = ?ts,
                                ?src_ty,
                                ?target_ty,
                                "CHC: layout-sensitive cross-ADT transmute requires sound fallback (Part of #3808)"
                            );
                            self.record_sound_fallback_reason("transmute_layout_fallback");
                            let nondet = declare_pending_var(
                                chc_fresh_name("__transmute_layout_nondet"),
                                ts.clone(),
                            );
                            return Some(nondet);
                        }

                        // Part of #3099: try sort coercion before recording unsound
                        // fallback. Common transmutes (newtype wrappers like NonZeroU32,
                        // BV width matches) succeed via coerce_assignment_rhs_to_sort.
                        // These produce precise coercions — no over-approximation
                        // counter is needed (Part of #3719).
                        if expr.sort().is_bool()
                            && ts.is_array()
                            && matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                            && is_zst_ty(*target_ty)
                            && let Some(canonical) = canonical_zst_expr(*target_ty)
                        {
                            debug!(
                                src_sort = ?expr.sort(),
                                target_sort = ?ts,
                                ?target_ty,
                                "CHC: transmute canonicalized Bool-backed ZST array target"
                            );
                            Some(canonical)
                        } else if let Some(coerced) =
                            Self::coerce_assignment_rhs_to_sort(expr.clone(), ts, None)
                        {
                            debug!(
                                src_sort = ?expr.sort(),
                                target_sort = ?ts,
                                "CHC: transmute coerced via sort coercion (precise)"
                            );
                            Some(coerced)
                        } else if let Some(coerced) = Self::reinterpret_fixed_layout_expr(&expr, ts)
                        {
                            // Part of #3457/#3596: layout-preserving reinterpretation.
                            // Part of #3252: Array→Datatype(multi-field) transmute.
                            debug!(
                                src_sort = ?expr.sort(),
                                target_sort = ?ts,
                                "CHC: transmute coerced via fixed-layout reinterpretation (precise)"
                            );
                            Some(coerced)
                        } else {
                            debug!(
                                src_sort = ?expr.sort(),
                                target_sort = ?ts,
                                "CHC: transmute cross-sort coercion failed — recording fallback"
                            );
                            self.record_fallback();
                            // Fall through to translate_cast for best-effort conversion.
                            self.translate_cast(operand, *target_ty, modified_locals)
                        }
                    }
                    None => {
                        debug!(
                            src_sort = ?expr.sort(),
                            "CHC: transmute target type has no AY sort — recording fallback"
                        );
                        self.record_fallback();
                        self.translate_cast(operand, *target_ty, modified_locals)
                    }
                }
            }
        }
    }

    /// Translate ReifyFnPointer/ClosureFnPointer to a unique BV64 constant.
    ///
    /// Each distinct FnDef monomorphization (e.g., `poly::<usize>` vs `poly::<isize>`)
    /// gets a unique pointer value. Same monomorphization reified multiple times gets
    /// the same value. This enables fn pointer equality/inequality assertions.
    /// Part of #3470: fn pointer identity encoding.
    fn translate_reify_fn_pointer(&mut self, operand: &Operand) -> Option<Expr> {
        // Extract the FnDef identity from the operand type.
        let key = match operand.ty(self.body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                format!("{}_{:?}", def.trimmed_name(), args)
            }
            TyKind::RigidTy(RigidTy::Closure(def, args)) => {
                format!("closure_{}_{:?}", def.trimmed_name(), args)
            }
            _ => {
                // Non-FnDef/Closure operand: fall back to BV64(0).
                return Some(Expr::bitvec_const(0, POINTER_WIDTH));
            }
        };

        if let Some(expr) = self.fn_ptr_ids.get(&key) {
            return Some(expr.clone());
        }

        let id = self.next_fn_ptr_id;
        self.next_fn_ptr_id += 1;
        let expr = Expr::bitvec_const(id as i128, POINTER_WIDTH);
        self.fn_ptr_ids.insert(key, expr.clone());
        Some(expr)
    }
}

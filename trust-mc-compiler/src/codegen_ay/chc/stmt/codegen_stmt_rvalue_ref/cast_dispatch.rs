// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cast dispatch for CHC rvalue translation.
//!
//! Contains:
//! - `translate_rvalue_cast`
//! - `translate_reify_fn_pointer`

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{CastKind, Operand, PointerCoercion};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::canonical_zst_expr;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::chc::heap::stack_address::{
    cast_exposes_address, transmute_makes_niche_pointer_enum, transmute_makes_pointer_from_integer,
};
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::codegen_call_cmp_string::float_to_int_saturating;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::super::codegen_expr_signedness::ExprSignedness;
use super::super::codegen_stmt_transmute_layout::AggregateTransmute;
use super::super::codegen_types::CodegenTypes;
use super::super::{ChcCtx, chc_fresh_name};

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
            #[cfg(all(trust_toolchain, version("1.101")))]
            CastKind::BoxDerefTransmute => {
                let checked =
                    self.checked_host_native_dyn_box_deref(operand, *target_ty).or_else(|| {
                        operand.ty(self.body.locals()).ok().and_then(|source| {
                            let value = self
                                .host_native_thin_box_address(operand, *target_ty)
                                .or_else(|| {
                                    self.translate_operand_with_modified(operand, modified_locals)
                                })?;
                            self.checked_native_box_deref(source, *target_ty, value)
                        })
                    });
                if let Some(checked) = checked {
                    self.heap_state.pending_checks.extend(checked.checks);
                    return Some(checked.value);
                }
                // Every unsupported shape retains the original refusal.
                self.diagnostics.place_translation_drop.inc();
                record_translation_drop_site_reason_for_fn(
                    &self.fn_name,
                    "box_deref_validity_unmodeled",
                );
                None
            }
            // Width-based casts: sort-based dispatch in translate_cast is correct.
            CastKind::IntToInt | CastKind::PtrToPtr | CastKind::FnPtrToPtr | CastKind::Subtype => {
                self.translate_cast(operand, *target_ty, modified_locals)
            }
            // A pointer-to-integer cast reads the address (heap/stack_address.rs).
            CastKind::PointerExposeAddress => {
                let value = self.translate_cast(operand, *target_ty, modified_locals)?;
                Some(self.ptr_to_int_value(value))
            }
            // #3350: Integer-to-pointer cast has no allocation provenance.
            // obj_valid defaults to const_array(true), making validity checks
            // trivially true for never-allocated addresses. Invalidate the
            // resulting pointer's obj_id so dereference checks can catch it.
            //
            // FAIL-CLOSED, not exact, on both lanes: Rust gives this pointer
            // the provenance of any previously EXPOSED allocation, and the
            // lane keeps no exposed set. The integer of a pointer whose object
            // has no tracked base is that pointer's identity term
            // (`ptr_to_int_value`), so a legitimate expose-then-reconstruct
            // round trip names the pointer's own object here, and the
            // invalidation makes every later access to that object a
            // violation (`E as *const u32 as usize` then `(a + 4) as *const
            // u32` read `[1, 2, 3][2]` as a use after free: a false
            // certificate, const_pointer_raw_from_ref_dual.rs::
            // safe_int_roundtrip). The invalidation only ADDS violations, so
            // a proof stays a proof; a counterexample is never certified
            // Genuine. `invalidate_int_to_ptr_object` (expr/codegen_expr_heap.rs)
            // is the one place the CHC lane states this: it records
            // `int_to_ptr_obj_invalidated` (SoundHavoc), the CHC spelling of
            // what the BMC lane records as `pointer_with_exposed_provenance`
            // (statement/codegen_assign_ref.rs); soundness.md, "Integer-to-
            // pointer casts: one rule, both lanes".
            CastKind::PointerWithExposedProvenance => {
                // An address inside a tracked stack allocation names that
                // allocation again (heap/stack_address.rs).
                let result = self
                    .translate_cast(operand, *target_ty, modified_locals)
                    .map(|addr| self.int_to_ptr_value_of_operand(addr));
                if !self.int_lift {
                    if let Some(ref ptr_expr) = result {
                        if let Some((obj_id, _offset)) = self.split_pointer(ptr_expr) {
                            self.invalidate_int_to_ptr_object(obj_id, Some(operand));
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
                PointerCoercion::ReifyFnPointer { .. } | PointerCoercion::ClosureFnPointer(_) => {
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
                    // Design 4 A: an array-to-slice unsize writes the source's
                    // compile-time length into the metadata half. The width
                    // cast below zero-extends the thin operand, and a reader of
                    // the wide slot (a loop-carried or joined slice local) then
                    // takes the zero padding as the length.
                    if let Some(packed) =
                        self.pack_array_unsize_len(operand, *target_ty, modified_locals)
                    {
                        return Some(packed);
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

                // Transmuting a pointer to an integer reads its address, as a cast
                // does; `<*const T>::addr` is this transmute (heap/stack_address.rs).
                if let Ok(src_ty) = operand.ty(self.body.locals())
                    && cast_exposes_address(kind, src_ty, *target_ty)
                    && target_sort.as_ref().and_then(|s| s.bitvec_width()) == Some(64)
                {
                    return Some(self.ptr_to_int_value(expr));
                }
                // And the reverse: transmuting an integer into a pointer is the
                // integer-to-pointer lane, spelled differently, and gets its
                // treatment: the identity whose address it is (`int_to_ptr_value`,
                // as an exposed-provenance cast gives; the integer taken as the
                // identity term read `without_provenance(1 << 40).addr()` back
                // through the address view as another value), and the named
                // object invalidated (`invalidate_int_to_ptr_object`). Passed
                // through as bits, a round trip read past its object unchecked:
                // `transmute::<usize, *const u16>(addr + 4)` over a `Box<[u16; 2]>`
                // verified SUCCESSFUL on main, where Kani reports the
                // out-of-bounds read (heap_access_checks checks bounds only for a
                // constant object lane). `ptr::without_provenance` is this
                // transmute, and so is one into a `NonNull` (`ty_is_pointer_like`).
                //
                // dfebf493c gave raw-pointer targets an earlier arm that took
                // `int_to_ptr_value` and skipped the invalidation, so in a body
                // that carries the pointer into another block (its object lane
                // symbolic at the access) a pointer made from a number naming no
                // object read clean: `transmute::<usize, *const u32>(6 << 32)` and
                // `without_provenance(hi << 32)` verified SUCCESSFUL where Kani
                // reports an invalid integer address
                // (`int_to_ptr_const_lane_dual.rs`, found merging main dbfe268fc
                // into fix/chc-lost-writes). That arm is this one now.
                if let Ok(src_ty) = operand.ty(self.body.locals())
                    && transmute_makes_pointer_from_integer(
                        kind,
                        self.resolve_body_ty(src_ty),
                        self.resolve_body_ty(*target_ty),
                    )
                    && expr.sort().bitvec_width() == Some(64)
                    && target_sort.as_ref().and_then(|s| s.bitvec_width()) == Some(64)
                {
                    let result = self.int_to_ptr_value_of_operand(expr);
                    // A pointer's exposed address moved by a small constant names
                    // that pointer's object again, so its round trip is exact
                    // without the invalidation (`int_operand_is_exposed_address`):
                    // dfebf493c's arm proved `safe_transmute_roundtrip_box`, and so
                    // does this one, while a number naming no object fails.
                    if self.int_operand_is_exposed_address(operand) {
                        debug!("CHC: transmute of an exposed address keeps its object");
                    } else if !self.int_lift
                        && let Some((obj_id, _offset)) = self.split_pointer(&result)
                    {
                        self.invalidate_int_to_ptr_object(obj_id, Some(operand));
                        debug!("#3350: invalidated obj_valid for an integer-to-pointer transmute");
                    }
                    return Some(result);
                }

                // An integer or raw pointer transmuted into a niche-encoded
                // pointer enum (`Option<&T>`): the sort coercion below does not
                // decode the niche (`None` iff the bits are zero), so the value
                // is decoded here (`transmute_makes_niche_pointer_enum`,
                // niche_transmute.rs).
                if let Ok(src_ty) = operand.ty(self.body.locals())
                    && transmute_makes_niche_pointer_enum(kind, src_ty, *target_ty)
                    && let Some(ref ts) = target_sort
                {
                    return Some(self.translate_niche_pointer_enum_transmute(
                        operand, expr, src_ty, *target_ty, ts,
                    ));
                }

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
                    let booked = self.record_sound_fallback_reason_identified(
                        "transmute_size_mismatch_ub",
                        None,
                    );
                    return Some(Havoc::booked(
                        booked,
                        chc_fresh_name("__transmute_size_mismatch_ub"),
                        ts.clone(),
                    ));
                }

                if operand
                    .ty(self.body.locals())
                    .ok()
                    .is_some_and(|source| self.native_dyn_transmute_needs_bytes(source, *target_ty))
                {
                    let booked =
                        self.record_sound_fallback_reason("native_dyn_pointer_bytes_unmodeled");
                    let sort = Self::translate_ty(*target_ty)?;
                    self.declare_datatype_sort_if_needed(&sort);
                    return Some(Havoc::booked(
                        booked,
                        chc_fresh_name("__native_dyn_bytes_unmodeled"),
                        sort,
                    ));
                }
                // A multi-field struct or tuple facing a bitvector is
                // reinterpreted in MEMORY order, or havocked; never through the
                // declaration-order flatten below, which transposes the words
                // (codegen_stmt_transmute_layout.rs).
                if let Some(ref ts) = target_sort
                    && let Ok(src_ty) = operand.ty(self.body.locals())
                {
                    match self.transmute_aggregate_memory_order(&expr, src_ty, *target_ty) {
                        AggregateTransmute::NotApplicable => {}
                        AggregateTransmute::Precise(reinterpreted) => return Some(reinterpreted),
                        AggregateTransmute::Unsupported(why) => {
                            debug!(
                                why,
                                ?src_ty,
                                ?target_ty,
                                "CHC: aggregate transmute layout not modeled; fresh value"
                            );
                            let booked =
                                self.record_sound_fallback_reason("transmute_layout_fallback");
                            return Some(Havoc::booked(
                                booked,
                                chc_fresh_name("__transmute_layout_nondet"),
                                ts.clone(),
                            ));
                        }
                    }
                }

                // An ARRAY facing an integer (`u32::to_le_bytes` is
                // `transmute::<u32, [u8; 4]>`, `[u16; 2]` from a `u32`) is
                // reinterpreted through both memory images, element 0 at the
                // low address. The sort coercions below mapped the integer's
                // bytes onto the elements in the wrong order: `0x0403_0201.
                // to_le_bytes() == [1, 2, 3, 4]` FAILED certified Genuine
                // (review probe t1_bytes.rs). A shape the image lane does not
                // model is a fresh value when one side is a plain integer, whose
                // bytes the coercions have no layout for.
                //
                // The value itself is kept only when the two sides have ONE
                // representation, element for element: the same element type,
                // or integers, floats and chars of one size, over the same
                // count (`transmute::<i8x2, [i8; 2]>` of a `repr(simd)` struct,
                // which translates to its bare array; `[u32; 4]` to `[f32; 4]`).
                // Rebuilding those from their bits over a fresh base array only
                // slowed the solver (kani/Intrinsics/SIMD/Operators/bitwise.rs
                // went from a 2.7 s proof to a 105 s unknown). A matching SORT
                // is not a matching layout: every fieldless enum translates to
                // a 32-bit bitvector whatever its size, and a thin pointer's
                // 64-bit term is its (object, offset) identity, not its address,
                // so `[E8; 4]` to `[u32; 1]` and `[*const u8; 2]` to
                // `[usize; 2]` kept the wrong value (review probes
                // t_same_sort.rs `e8_to_u32_bug` SUCCESSFUL where Kani fails,
                // t_ptr.rs `ptr_arr_transmute_safe` FAILED certified Genuine).
                if let Some(ref ts) = target_sort
                    && let Ok(src_ty) = operand.ty(self.body.locals())
                    && (is_array_ty(src_ty) || is_array_ty(*target_ty))
                    && !self.array_transmute_keeps_representation(src_ty, *target_ty)
                {
                    use super::super::codegen_stmt_union_bits::UnionLane;
                    match self.transmute_via_memory_image(&expr, src_ty, *target_ty) {
                        UnionLane::Exact(value) => {
                            debug!(?src_ty, ?target_ty, "CHC: array transmute in memory order");
                            return Some(value);
                        }
                        // One sort, another layout, and no image: the kept value
                        // would be the wrong one, so it is fresh.
                        UnionLane::Unmodeled(why) if ts == expr.sort() => {
                            debug!(
                                why,
                                ?src_ty,
                                ?target_ty,
                                "CHC: same-sort array transmute of another layout not modeled; fresh"
                            );
                            let booked =
                                self.record_sound_fallback_reason("transmute_layout_fallback");
                            return Some(Havoc::booked(
                                booked,
                                chc_fresh_name("__transmute_layout_nondet"),
                                ts.clone(),
                            ));
                        }
                        UnionLane::Unmodeled(why)
                            if is_integer_bits_ty(src_ty) || is_integer_bits_ty(*target_ty) =>
                        {
                            debug!(
                                why,
                                ?src_ty,
                                ?target_ty,
                                "CHC: array transmute not modeled; fresh"
                            );
                            let booked =
                                self.record_sound_fallback_reason("transmute_layout_fallback");
                            return Some(Havoc::booked(
                                booked,
                                chc_fresh_name("__transmute_layout_nondet"),
                                ts.clone(),
                            ));
                        }
                        UnionLane::Unmodeled(_) => {}
                    }
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
                            let booked =
                                self.record_sound_fallback_reason("transmute_layout_fallback");
                            let nondet = Havoc::booked(
                                booked,
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

    /// Translate ReifyFnPointer/ClosureFnPointer to the target's identity.
    ///
    /// Each distinct instance (e.g., `poly::<usize>` vs `poly::<isize>`, or
    /// `m1::op2` vs `m2::op2`) gets its own pointer value, and the same
    /// instance reified twice gets the same one, so fn pointer equality and
    /// the dispatch on a pointer's value are exact (#3470; design 3, D1:
    /// `call/fn_ptr_targets.rs`). An operand that names no function gets a
    /// fresh value and a fail-closed reason instead of the constant 0.
    pub(in crate::codegen_ay::chc) fn translate_reify_fn_pointer(
        &mut self,
        operand: &Operand,
    ) -> Option<Expr> {
        let ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        Some(self.fn_ptr_value_for_reified_ty(ty))
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether a transmute between `src_ty` and `target_ty` (one of them an
    /// array or a `repr(simd)` wrapper of one) maps every element onto an
    /// element of the SAME representation: equal counts, and element types
    /// that are equal or are integers, floats and chars of one size, whose
    /// encoding is their bits. Only then is the value itself the result.
    fn array_transmute_keeps_representation(
        &self,
        src_ty: rustc_public::ty::Ty,
        target_ty: rustc_public::ty::Ty,
    ) -> bool {
        let src_ty = self.resolve_body_ty(src_ty);
        let target_ty = self.resolve_body_ty(target_ty);
        if src_ty == target_ty {
            return true;
        }
        let elements = |ty: rustc_public::ty::Ty| {
            Some((self.resolve_body_ty(self.get_array_element_ty(ty)?), self.get_array_length(ty)?))
        };
        let (Some((src_elem, src_len)), Some((target_elem, target_len))) =
            (elements(src_ty), elements(target_ty))
        else {
            return false;
        };
        if src_len != target_len {
            return false;
        }
        if src_elem == target_elem {
            return true;
        }
        let size = |ty: rustc_public::ty::Ty| ty.layout().ok().map(|l| l.shape().size.bytes());
        is_integer_bits_ty(src_elem)
            && is_integer_bits_ty(target_elem)
            && size(src_elem).is_some()
            && size(src_elem) == size(target_elem)
    }
}

fn is_array_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
}

fn is_integer_bits_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Char)
    )
}

#[cfg(test)]
mod modern_box_cast_tests {
    #![cfg(all(trust_toolchain, version("1.101")))]
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use crate::kani_middle::transform::RustcInternalMir;
    use rustc_public::mir::{Rvalue, StatementKind};

    #[test]
    fn actual_box_cast_keeps_native_kind_and_chc_refuses_extra_validity() {
        with_test_ay_ctx_for_source("pub fn probe_box(b: Box<u32>) -> u32 { *b }", |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_box");
            let body = instance.body().expect("box dereference body");
            let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_box", ChcConfig::default());
            let mut observed = 0;
            for block in &body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(
                        _,
                        Rvalue::Cast(kind @ CastKind::BoxDerefTransmute, operand, target),
                    ) = &stmt.kind
                    {
                        assert!(matches!(
                            kind.internal_mir(ctx.tcx),
                            rustc_middle::mir::CastKind::BoxDerefTransmute,
                        ));
                        let before = chc.diagnostics.place_translation_drop.get();
                        assert!(
                            chc.translate_rvalue_cast(kind, operand, target, &HashSet::new())
                                .is_none(),
                            "Box validity cannot be replaced by a bit-preserving cast",
                        );
                        assert_eq!(chc.diagnostics.place_translation_drop.get(), before + 1);
                        observed += 1;
                    }
                }
            }
            assert!(observed > 0, "the genuine compiler must supply the BoxDerefTransmute control");
            assert!(matches!(
                CastKind::Transmute.internal_mir(ctx.tcx),
                rustc_middle::mir::CastKind::Transmute,
            ));
        });
    }
}

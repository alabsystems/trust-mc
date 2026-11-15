// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Slice type utilities and codegen stubs for AY - Part of #1354.
//!
//! Contains functions for:
//! - Slice/wide pointer type checking
//! - Array length extraction from pointer types
//! - Slice indexing and equality codegen stubs

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names::struct_sort;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    // === Type checking utilities ===

    /// Check if a type is a wide pointer (fat pointer).
    ///
    /// Wide pointers (fat pointers) include:
    /// - Pointers to slices (`&[T]`, `*const [T]`)
    /// - Pointers to str (`&str`, `*const str`)
    /// - Trait objects (`&dyn Trait`, `*const dyn Trait`)
    pub(super) fn is_wide_pointer_ty(ty: rustc_public::ty::Ty) -> bool {
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return false, // external enum: TyKind
        };

        matches!(
            pointee.kind(),
            TyKind::RigidTy(RigidTy::Slice(_))
                | TyKind::RigidTy(RigidTy::Str)
                | TyKind::RigidTy(RigidTy::Dynamic(..))
        )
    }

    /// Check if a pointer type specifically points to a slice.
    ///
    /// Returns true for:
    /// - References to slices (`&[T]`, `&mut [T]`)
    /// - Raw pointers to slices (`*const [T]`, `*mut [T]`)
    ///
    /// Returns false for str pointers, trait objects, and thin pointers.
    pub(super) fn is_slice_pointer_ty(ty: rustc_public::ty::Ty) -> bool {
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return false, // external enum: TyKind
        };

        matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
    }

    /// #1129: Check if a pointer to this type should be a thin pointer.
    ///
    /// Returns true for:
    /// - Sized types (thin pointer, no metadata)
    /// - Foreign types (unsized but thin pointer, no metadata)
    ///
    /// Returns false for:
    /// - Slices/str (fat pointer with length metadata)
    /// - Trait objects (fat pointer with vtable metadata)
    pub(super) fn use_thin_pointer_for_pointee(pointee_ty: rustc_public::ty::Ty) -> bool {
        // Check for unsized types that need fat pointers
        let kind = pointee_ty.kind();
        !matches!(
            kind,
            TyKind::RigidTy(RigidTy::Slice(_))
                | TyKind::RigidTy(RigidTy::Str)
                | TyKind::RigidTy(RigidTy::Dynamic(..))
        )
        // Note: Foreign types are unsized but use thin pointers (no metadata)
    }

    /// Check if type is a reference/pointer to a slice, array, or Vec.
    pub(super) fn is_slice_or_array_ref_ty(ty: rustc_public::ty::Ty) -> bool {
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => return false, // external enum: TyKind
        };

        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Array(..)) => true,
            TyKind::RigidTy(RigidTy::Adt(def, _)) => def.trimmed_name() == "Vec",
            _ => false, // external enum: TyKind
        }
    }

    /// Extract array length from a pointer-to-array type.
    pub(super) fn array_len_from_pointer_ty(ty: rustc_public::ty::Ty) -> Option<u64> {
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return None, // external enum: TyKind
        };

        let TyKind::RigidTy(RigidTy::Array(_elem, len)) = pointee.kind() else {
            return None;
        };

        len.eval_target_usize().into_option()
    }

    // === Slice codegen stubs ===

    /// Codegen SlicePartialEq::equal for slices.
    ///
    /// For slices of ZST elements, equality is length equality.
    /// For other cases, fall back to PartialEq::eq handling.
    pub(super) fn codegen_slice_partial_eq_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_zst = self.slice_elem_is_zst(&args[0]);
        let rhs_zst = self.slice_elem_is_zst(&args[1]);

        if lhs_zst
            && rhs_zst
            && let (Some(lhs_len), Some(rhs_len)) =
                (self.slice_len_expr(&args[0]), self.slice_len_expr(&args[1]))
        {
            let eq_result = lhs_len.eq(rhs_len);
            self.assign_value_to_place(destination, eq_result);
            return target;
        }

        self.codegen_partial_eq(args, destination, target)
    }

    /// Codegen `core::slice::<impl [T]>::is_empty` — returns `len == 0`.
    ///
    /// Part of #3713: mirrors CHC parity. Resolves slice/array length via
    /// `slice_len_expr` and assigns `len == 0` as a bool to destination.
    pub(super) fn codegen_slice_is_empty_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let receiver = args.first()?;
        if let Some(len_expr) = self.slice_len_expr(receiver) {
            let zero =
                Expr::bitvec_const(0, len_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH));
            let is_empty = len_expr.eq(zero);
            self.assign_value_to_place(destination, is_empty);
        } else {
            // Cannot resolve length — leave unconstrained (sound over-approximation).
            let name = self.ctx.fresh_name("ay_slice_is_empty");
            let symbolic = self.ctx.declare_var(&name, crate::codegen_ay::types::bool_sort());
            self.ctx.bmc_sound_havoc("slice_is_empty");
            self.assign_value_to_place(destination, symbolic);
        }
        target
    }

    /// Codegen `core::slice::<impl [T]>::partition_point` — returns 0..=len.
    ///
    /// Part of dterm#6841: Sound over-approximation. The real partition_point
    /// returns the first index where the predicate is false (0..=len). We model
    /// this as a symbolic usize constrained to [0, len]. This explores all
    /// possible return values, which is sound (may produce spurious CTREX but
    /// won't miss real bugs).
    pub(super) fn codegen_slice_partition_point(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let receiver = args.first()?;
        let name = self.ctx.fresh_name("ay_partition_point");
        let result = self.ctx.declare_var(&name, ptr_sort());
        self.ctx.bmc_sound_havoc("slice_partition_point");

        // Constrain result to [0, len] if we can resolve the slice/vec length.
        let zero = Expr::bitvec_const(0, POINTER_WIDTH);
        if let Some(len_expr) = self.slice_len_expr(receiver) {
            // result >= 0 is trivially true for unsigned bitvec, but assert result <= len.
            let in_range = result.clone().bvule(len_expr);
            self.ctx.assert(in_range);
        }
        // Also assert result >= 0 (trivial for unsigned, but explicit for clarity).
        let _ = zero; // used above for documentation; unsigned bvule handles [0, len].

        self.assign_value_to_place(destination, result);
        target
    }

    /// Model `core::slice::memchr::{memchr,memchr_naive,memchr_aligned,...}(needle, haystack)
    /// -> Option<usize>` as a SOUND over-approximation. Real memchr returns the index of the
    /// first `needle` byte in `haystack`, else `None`. It is SIMD stdlib with no inlinable MIR,
    /// so without a stub it becomes an unsupported `Call terminator` -> #3017 fallback.
    ///
    /// The model uses a fresh nondet discriminant (both `Some` and `None` are explored) and a
    /// fresh nondet payload index, deliberately DROPPING the `haystack[i] == needle` and the
    /// `None only if the byte is absent` correlations. Dropping correlations only ADDS
    /// behaviors, which is sound for a safety / state-validity proof (at worst spurious
    /// counterexamples, never a missed bug). The single tightening — `Some(i) => i <= len` —
    /// is provably true of real memchr (it never returns an out-of-range index), so it excludes
    /// only behaviors that can never occur.
    ///
    /// Returns `None` (so dispatch falls through to the fail-closed unsupported fallback) on an
    /// unusual Option encoding — NEVER `Some(None)`, which claims the call diverges (see the
    /// invariant on `try_codegen_stdlib_stub_call`). Modeled on `codegen_slice_partition_point` +
    /// `build_option_expr`.
    pub(super) fn codegen_slice_memchr(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let some_name = self.ctx.fresh_name("ay_memchr_some");
        let is_some = self.ctx.declare_var(&some_name, crate::codegen_ay::types::bool_sort());
        let idx_name = self.ctx.fresh_name("ay_memchr_idx");
        let idx = self.ctx.declare_var(&idx_name, ptr_sort());
        self.ctx.bmc_sound_havoc("slice_memchr");

        // Sound tightening: real memchr never returns i >= haystack.len(). The haystack is
        // whichever arg resolves to a slice (arg order differs across the memchr variants).
        if let Some(len_expr) = args.iter().find_map(|a| self.slice_len_expr(a)) {
            self.ctx.assert(is_some.clone().implies(idx.clone().bvule(len_expr)));
        }

        // build_option_expr returns None for a non-datatype Option destination encoding -> we
        // return None so dispatch falls through to the fail-closed fallback (sound INCONCLUSIVE).
        let opt = self.build_option_expr(destination, is_some, idx)?;
        self.assign_value_to_place(destination, opt);
        target
    }

    /// Codegen SliceIndex::index / Index::index for slices and arrays.
    ///
    /// Creates a reference result by synthesizing a pointee value and tracking ref_pointees.
    pub(super) fn codegen_slice_index_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let (slice_arg, index_arg) = self.split_slice_index_args(args)?;

        if self.is_range_full_index_operand(index_arg) {
            let frozen = self.slice_view_is_frozen(destination);
            if !frozen {
                self.ctx.unsupported_with_fallback(
                    "slice index RangeFull: mutable view of a copy",
                    format!("{destination:?}"),
                );
            }
            let slice_expr = self.range_full_identity_value(slice_arg, frozen)?;
            self.assign_reference_to_place(destination, slice_expr);
            // A FULL view is a view too. The denylist below asks whether a
            // source-reading model was handed a VIEW, not whether the view was
            // shifted: `let s = &a[..]; assert!(s.contains(&1))` was FAILED
            // [AY:CTREX_CAT:Genuine] on a program with no bug, with no offset
            // anywhere, because a full view was never recorded (fourth
            // adversarial review of m3/soundness-fixes-2, 2026-09-14, defect
            // M5/D6). Every view a slicing operation produces is recorded,
            // whatever the range.
            let view_base = self.ssa_base_name(destination);
            self.shifted_subslice_views.insert(std::sync::Arc::from(view_base));
            return target;
        }

        // A sub-slice *range* index (`buf[a..b]`, `buf[..n]`, `buf[n..]`, ...) yields
        // a `&mut [T]` we do not model element-wise. FAIL CLOSED: record the
        // unsupported fallback and continue with an unconstrained destination.
        // Do NOT `return None` here: this arm records the fallback itself and
        // continues to `target`, keeping the post-call path. (An inner `None` was
        // once mapped to Diverge, which pruned that path for a non-diverging
        // index_mut; see the invariant on `try_codegen_stdlib_stub_call`.) This is
        // the only sound option until sub-slice ranges carry a bounded length
        // through to their iterator — tracked for the Drop-glue PROVED-green
        // frontier.
        if self.is_range_index_operand(index_arg) {
            // Model the sub-slice EXACTLY as a slice (Vec datatype) value:
            // fld_data = the backing array, fld_len = the range length, so the
            // downstream iterator (VecIterMut) is bounded and element select/store
            // stays sound. Exact for RangeTo/Range; FAIL CLOSED otherwise: record
            // the unsupported fallback and `return target`, never `return None`.
            if self.try_codegen_subslice_range_ref(slice_arg, index_arg, destination) {
                if !self.slice_view_is_frozen(destination) {
                    self.ctx.unsupported_with_fallback(
                        "slice index range: mutable view of a copy",
                        format!("{destination:?}"),
                    );
                }
                return target;
            }
            self.ctx.unsupported_with_fallback(
                "slice index range: unmodelled sub-slice",
                format!("{:?}", destination),
            );
            return target;
        }

        let elem_ty = self
            .slice_elem_ty_from_operand(slice_arg)
            .or_else(|| self.destination_pointee_ty(destination))?;

        let idx_expr = self.codegen_operand(index_arg)?;
        let idx_coerced = match idx_expr.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => idx_expr,
            Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
            Some(_) => idx_expr.extract(POINTER_WIDTH - 1, 0),
            None => return None,
        };

        if let Some(len_expr) = self.slice_len_expr(slice_arg) {
            let len_coerced = match len_expr.sort().bitvec_width() {
                Some(w) if w == POINTER_WIDTH => len_expr,
                Some(w) if w < POINTER_WIDTH => len_expr.zero_extend(POINTER_WIDTH - w),
                Some(_) => len_expr.extract(POINTER_WIDTH - 1, 0),
                None => return None,
            };
            let oob = idx_coerced.clone().bvuge(len_coerced);
            self.record_violation_guarded(oob, "bounds_check");
        }

        // Part of #3392: save index expr before it's moved into select().
        let idx_for_propagation = idx_coerced.clone();

        let elem_expr = self.slice_element_value(slice_arg, elem_ty, idx_coerced);

        self.assign_reference_to_place(destination, elem_expr);

        // Part of #3392: register stub-created indexed ref for write propagation.
        // Without this, `*ref = val` writes through stub-dispatched IndexMut don't
        // propagate back to the backing array because the pointee name uses
        // `slice_index_pointee_N` instead of the `_idx_by_` convention.
        self.register_stub_indexed_ref(slice_arg, destination, idx_for_propagation);

        target
    }

    /// Read the element VALUE at `a[idx]` for a slice / array / Vec receiver.
    ///
    /// Shared by `codegen_slice_index_stub` (which wraps the result in a `&T`
    /// reference) and `codegen_slice_get` (which wraps it in a flattened
    /// `Option<&T>`): ZST → canonical `Unit`; SMT array → `select`; Vec / Slice
    /// datatype → backing-field (`fld_data` / `fld_buf`) `select`, else `fld_ptr`
    /// memory load; otherwise a constrained symbolic. `idx_coerced` MUST already
    /// be `POINTER_WIDTH`.
    fn slice_element_value(
        &mut self,
        slice_arg: &Operand,
        elem_ty: rustc_public::ty::Ty,
        idx_coerced: Expr,
    ) -> Expr {
        if Self::is_zst_type(elem_ty) {
            let unit_sort = struct_sort("Unit", Vec::<(&str, Sort)>::new());
            // Constructor name is always "Unit_mk" per struct_type convention.
            Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort)
        } else if let Some(slice_expr) = self.get_value_through_ref(slice_arg) {
            if slice_expr.sort().is_array() {
                slice_expr.select(idx_coerced)
            } else if let Some(dt_name) = slice_expr.clone().sort().datatype_name() {
                // Backing-array field: Vec/Slice use "fld_data"; ArrayVec/inline
                // buffers use "fld_buf" (the fld_-prefixed Rust field name). Part
                // of the PROVED-green ArrayVec store/select modelling.
                let backing = self
                    .get_datatype_field_sort(&slice_expr, "fld_data")
                    .map(|s| ("fld_data", s))
                    .or_else(|| {
                        self.get_datatype_field_sort(&slice_expr, "fld_buf").map(|s| ("fld_buf", s))
                    });
                if let Some((fld_name, data_sort)) = backing {
                    let data = slice_expr.field_select(dt_name, fld_name, data_sort);
                    data.select(idx_coerced)
                } else {
                    // Fallback: Vec/String/Slice datatypes use "fld_ptr" field naming convention
                    let ptr_expr = slice_expr.field_select(dt_name, "fld_ptr", ptr_sort());
                    if let Some(elem_size) = LayoutOf::new(elem_ty).size_of() {
                        let size_expr = Expr::bitvec_const(elem_size as i128, POINTER_WIDTH);
                        let offset = idx_coerced.bvmul(size_expr);
                        let addr = ptr_expr.bvadd(offset);
                        self.ctx.load_memory_bytes(addr, elem_size as u32)
                    } else {
                        self.create_constrained_symbolic(elem_ty, "ay_slice_index")
                    }
                }
            } else {
                self.create_constrained_symbolic(elem_ty, "ay_slice_index")
            }
        } else {
            self.create_constrained_symbolic(elem_ty, "ay_slice_index")
        }
    }

    /// Codegen `core::slice::<impl [T]>::get(self, index) -> Option<&T>` for a
    /// SCALAR `usize` index (R2 — ay-pb `eval_lit`'s `assignment.get(index)`).
    ///
    /// Models the method EXACTLY as `ite(index < len, Some(&a[index]), None)` in
    /// the flattened-Option encoding (#2076), mirroring what a real
    /// `Aggregate(Adt(Option, Some/None))` flatten produces so the existing
    /// `.copied()` MIR-inline and `Option::unwrap_or` handlers consume it
    /// unchanged:
    ///   - `{dest}.0`  (BV32) = discriminant: 1 (Some) when in-bounds, else 0 (None)
    ///   - `{dest}` / `{dest}_variant_1_field_0` = the element VALUE (references
    ///     are transparent under value semantics, #3133), out-of-bounds selecting
    ///     the canonical zero so BOTH arms stay bitvec-typed (ay has no datatype
    ///     theory to mix, #517/#3260)
    ///   - `ref_pointees` wires a synthesized pointee so a downstream `*payload`
    ///     deref (inside the inlined `.copied()`) resolves to the element.
    ///
    /// SOUNDNESS: returns `None` — the caller records a fail-closed fallback and
    /// leaves the destination unconstrained (never a false Some) — for a range
    /// index (`Option<&[T]>`, not modelled element-wise), a non-Option / non-std
    /// destination, or when the element type / length / index / element VALUE
    /// can't be resolved to a bitvec payload.
    pub(super) fn codegen_slice_get(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }
        let (slice_arg, index_arg) = self.split_slice_index_args(args)?;

        // Only a SCALAR index yields `Option<&T>`; a range yields `Option<&[T]>`,
        // not modelled element-wise — fail closed rather than fabricate a value.
        if self.is_range_full_index_operand(index_arg) || self.is_range_index_operand(index_arg) {
            return None;
        }

        // Destination must be a std-shaped 2-variant Option (None fieldless,
        // Some 1-field) so the flattened `.0` / payload keys line up with the
        // downstream discriminant reads (Some is variant index 1).
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = dest_ty.kind() else {
            return None;
        };
        if def.trimmed_name() != "Option" {
            return None;
        }
        let variants = def.variants();
        if variants.len() != 2
            || !variants[0].fields().is_empty()
            || variants[1].fields().len() != 1
        {
            return None;
        }

        let elem_ty = self.slice_elem_ty_from_operand(slice_arg)?;

        // Index and length, both coerced to POINTER_WIDTH.
        let idx_expr = self.codegen_operand(index_arg)?;
        let idx_coerced = Self::coerce_bv_to_pointer_width(idx_expr)?;
        // Length: prefer the concrete slice/array length (`slice_len_expr`
        // resolves an `[T; N]` const length and a Vec/Slice datatype `fld_len`);
        // fall back to the fat-pointer metadata — the SAME source `<[T]>::len()` /
        // `PtrMetadata` reads (`codegen_ptr_metadata`, set to the concrete length
        // by the `&[T; N] -> &[T]` unsize). Using the identical source means a
        // co-located `.len()` in the spec (e.g. ay-pb's `ref_lit`) resolves to the
        // SAME expression, so the `get` Some/None boundary agrees exactly.
        let len_expr =
            self.slice_len_expr(slice_arg).or_else(|| self.codegen_ptr_metadata(slice_arg))?;
        let len_coerced = Self::coerce_bv_to_pointer_width(len_expr)?;
        // in_bounds = !(idx >= len) = idx < len (unsigned).
        let in_bounds = idx_coerced.clone().bvuge(len_coerced).not();

        // Element value at a[index]; coerce a Bool element to BV1 so BOTH Option
        // arms live in bitvec land (mirrors the aggregate-flatten payload
        // coercion, #3260 / G1).
        let elem_val = self.slice_element_value(slice_arg, elem_ty, idx_coerced);
        let payload = if elem_val.sort().is_bool() {
            Expr::ite(elem_val, Expr::bitvec_const(1u64, 1), Expr::bitvec_const(0u64, 1))
        } else {
            elem_val
        };
        if !payload.sort().is_bitvec() {
            // A non-bitvec payload would mix DT+BV theory; fail closed.
            return None;
        }
        let payload_width = payload.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

        let dest_base = self.ssa_base_name(destination);

        // Discriminant `{dest}.0` = ite(in_bounds, 1, 0).
        let discrim_key = crate::codegen_ay::names::discrim_name(&dest_base);
        let discrim_val = Expr::ite(
            in_bounds.clone(),
            Expr::bitvec_const(1u64, 32),
            Expr::bitvec_const(0u64, 32),
        );
        let discrim_name = self.ssa_name_from_base(&discrim_key, true);
        let discrim_var = self.ctx.declare_var(&discrim_name, Sort::bitvec(32));
        self.assert_ssa_def(discrim_var.clone(), discrim_val, &discrim_key);
        self.env_update(discrim_key, discrim_var);

        // Payload under the Some piecewise key `{dest}_variant_1_field_0` and the
        // base key. Out-of-bounds selects the canonical zero (never read — the
        // None arm carries no payload — but keeps both arms bitvec-typed).
        let payload_or_zero =
            Expr::ite(in_bounds, payload.clone(), Expr::bitvec_const(0u64, payload_width));
        let field_key = crate::codegen_ay::names::base_variant_field_name(&dest_base, 1, 0);
        let field_name = self.ssa_name_from_base(&field_key, true);
        let field_var = self.ctx.declare_var(&field_name, Sort::bitvec(payload_width));
        self.assert_ssa_def(field_var.clone(), payload_or_zero.clone(), &field_key);
        self.env_update(field_key.clone(), field_var);

        let base_name = self.ssa_name_from_base(&dest_base, true);
        let base_var = self.ctx.declare_var(&base_name, Sort::bitvec(payload_width));
        self.assert_ssa_def(base_var.clone(), payload_or_zero, &dest_base);
        self.env_update(dest_base.clone(), base_var);

        // Synthesized pointee so a downstream `*payload` deref (inside the inlined
        // `.copied()`) resolves to the element VALUE. Wire ref_pointees for both
        // the base and the Some field key (mirrors codegen_assign_flatten's
        // Some(&x) ref propagation).
        let pointee_base: std::sync::Arc<str> = {
            use std::fmt::Write;
            let fn_name = self.ctx.current_fn_name();
            let mut s = String::with_capacity(fn_name.len() + 25);
            s.push_str(fn_name);
            s.push_str("::slice_get_pointee_");
            let _ = write!(s, "{}", self.synthetic_pointee_counter);
            std::sync::Arc::from(s)
        };
        self.synthetic_pointee_counter += 1;
        let pointee_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
        let pointee_var = self.ctx.declare_var(&pointee_name, Sort::bitvec(payload_width));
        self.assert_ssa_def(pointee_var.clone(), payload, pointee_base.as_ref());
        // Publish the pointee VALUE in the env under its base name.
        //
        // Multi-hop residual (flattened `Option<&T>` composed through `and_then`):
        // when this `slice::get` Option flows through an `and_then` MIR-inline
        // re-key and is then consumed by a `.copied()` that takes the library
        // MIR-inline path, that path emits a `*payload` Deref. `apply_projection_chain`
        // resolves a Deref by (1) `ref_pointees[ref_base] -> pointee_base` then
        // (2) `env_lookup(pointee_base)`. The ref_pointees link below survives the
        // re-key, but without this env entry step (2) misses, step (3)
        // `ensure_derived_pointee_in_env` cannot reparse the synthetic
        // `::slice_get_pointee_N` name, and codegen falls through to
        // `synthesize_pointee_expr` — an UNCONSTRAINED symbolic (the
        // `pointee_synthesis_fallback` EncodingGap that fail-closed the whole
        // `eval_lit` chain). Storing the exact `payload` (a[index]) here is
        // FAITHFUL — it is the identical value the ref_pointees link points at,
        // never an over-approximation — and additionally lets
        // `propagate_inline_return_ref_pointees` carry the value back across the
        // inline boundary (it copies `inline_env[pointee_base]` into the parent
        // env only when present). Part of #multi-hop-flattened-option.
        //
        // Additionally persist the CONSTRAINED pointee value in the DURABLE
        // `heap_pointees` map, not only the SSA-versioned `current_env`. The env
        // entry is fragile: the opaque synthetic name `::slice_get_pointee_N` has
        // no `::local_` structure, so once env_lookup misses on a later block /
        // phi-rebuilt path, `ensure_derived_pointee_in_env` cannot reparse it and
        // codegen falls through to `synthesize_pointee_expr` — an UNCONSTRAINED
        // symbolic (the `pointee_synthesis_fallback` EncodingGap that classifies
        // the r2_slice_get_probe CEX as EncodingGap instead of Genuine).
        // `heap_pointees` survives those rebuilds and is inherited across inline
        // boundaries (cloned into InlineParentState and extended back), so the
        // Deref resolver recovers the exact `a[index]` element value from it
        // (see the recovery added in `ensure_derived_pointee_in_env`). SOUNDNESS:
        // this stores the identical constrained `pointee_var` (never a fresh /
        // over-approximated symbolic), on a key namespace (`::slice_get_pointee_N`)
        // disjoint from Box / root-local keys, so it only REMOVES an unconstrained
        // symbolic and cannot create a false-verify surface.
        self.heap_pointees.insert(std::sync::Arc::clone(&pointee_base), pointee_var.clone());
        self.env_update(std::sync::Arc::clone(&pointee_base), pointee_var);

        let dest_base_arc: std::sync::Arc<str> = std::sync::Arc::from(dest_base.as_str());
        let field_key_arc: std::sync::Arc<str> = std::sync::Arc::from(field_key.as_str());
        self.ref_pointees.insert(dest_base_arc, std::sync::Arc::clone(&pointee_base));
        self.ref_pointees.insert(field_key_arc, pointee_base);

        target
    }

    /// The slice VALUE that `<[T] as Index<RangeFull>>::index(s, ..)` returns.
    ///
    /// `s[..]` is the IDENTITY on `s`, so the result must alias BOTH halves of
    /// `s`'s fat pointer. The previous code resolved only `get_value_through_ref`,
    /// which unwraps a `&[T]` to its BACKING ARRAY — an SMT `Array` carries no
    /// length, so the destination became a `&[T]` whose `fld_len` was never
    /// constrained. `.len()` and every bounds check through it then read a FRESH
    /// symbol, which is why `s.len() == 4` and `s.len() == 99` were BOTH
    /// satisfiable for `let s = &[0u8; 4][..]`.
    ///
    /// Prefer the receiver's own fat-pointer value when it carries metadata —
    /// the `&[T; N] -> &[T]` unsize cast (`try_construct_slice_datatype_from_cast`)
    /// builds it with the EXACT static `N` and the tracked backing array — and
    /// splice the referent's backing array into `fld_data` when one is tracked,
    /// so neither half is lost. Falls back to the previous resolution order
    /// whenever the receiver has no fat-pointer value, so nothing that used to
    /// resolve stops resolving.
    fn range_full_identity_value(&mut self, slice_arg: &Operand, frozen: bool) -> Option<Expr> {
        if frozen && let Some(value) = self.range_full_path_merged_value(slice_arg) {
            return Some(value);
        }
        let through_ref = self.get_value_through_ref(slice_arg);
        let own = self.codegen_operand(slice_arg);

        if let Some(fat) = own.clone().filter(|e| super::extract_fat_ptr_metadata(e).is_some()) {
            if let Some(backing) = through_ref.clone().filter(|e| e.sort().is_array())
                && let Some(spliced) = Self::replace_fat_ptr_backing(&fat, &backing)
            {
                return Some(spliced);
            }
            return Some(fat);
        }

        through_ref.or(own)
    }

    /// Whether the slice view a range index stores in `destination` can be the
    /// copy of the referent the index stubs build: a shared reference to elements
    /// whose copy cannot go stale ([`ty_copy_can_go_stale`]), so nothing the copy
    /// holds can change while the view lives. Writes through a `&mut` view land in the copy and never reach the
    /// referent (`let full = &mut source[..]; full[0] = 9; assert!(lhs[0] == 1)`
    /// and the `s[a..b]` / `s[..b]` twins verified SUCCESSFUL on main 31793ccc3),
    /// and a `Cell` element set through another alias is not seen through the
    /// copy (`let full = &source[..]; lhs[0].set(7); assert!(full[0].get() == 1)`
    /// verified SUCCESSFUL). The decision is about what the copy INLINES, not
    /// about `Freeze`: an element that is a pointer (`&Cell<u8>`, `Box<Cell<u8>>`,
    /// `Rc<Cell<u8>>`, `Arc<AtomicU8>`) is `Freeze` by type, yet the copy holds
    /// the pointer and the state behind it keeps changing, so
    /// `let view: &[&Cell<u8>] = &refs[..]; view[1].set(7); assert!(cells[1].get()
    /// == 2)` verified SUCCESSFUL and the safe twins FAILED with a Genuine
    /// counterexample (negative/frozen_views_indirect.rs, bundle edec8fd8a).
    /// Callers fail closed on any other view.
    ///
    /// A shared view built here is exact for `RangeFull` and `RangeTo`, and for a
    /// `Range` / `RangeFrom` whose backing `try_codegen_subslice_range_ref`
    /// shifted by the start (see there).
    fn slice_view_is_frozen(&self, destination: &Place) -> bool {
        destination.ty(self.body.locals()).into_option().is_some_and(|ty| {
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, pointee, rustc_public::mir::Mutability::Not))
                    if !crate::codegen_ay::foreign_defs::ty_copy_can_go_stale(
                        self.ctx.tcx,
                        pointee,
                    )
            )
        })
    }

    /// `s[..]` for a slice reference `s` merged at a join from references to
    /// different arrays.
    ///
    /// `ref_pointees` names one arm's array for such an `s` and poisons the entry,
    /// so the splice in `range_full_identity_value` read that one array for every
    /// path, and reading it failed the statement closed:
    /// `let source = if c { &lhs } else { &rhs }; let full = &source[..];
    /// assert!(full.len() == 4)` was demoted (`slice_len_range_full_safe.rs`).
    /// The array of every path is known, so the backing is spliced per path,
    /// selected by the edge predicates of the join in the order the phi that
    /// merged `s` itself uses. Taken only for a frozen view
    /// (`slice_view_is_frozen`). `None` (the route that fails closed) unless `s`
    /// is poisoned with alternatives, carries fat-pointer metadata, and every path
    /// names an array of the one sort `fld_data` has.
    fn range_full_path_merged_value(&mut self, slice_arg: &Operand) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = slice_arg else {
            return None;
        };
        let ref_key = self.ssa_base_name(place);
        if !self.ref_pointees.is_poisoned(ref_key.as_str()) {
            return None;
        }
        let fat = self
            .codegen_operand(slice_arg)
            .filter(|e| super::extract_fat_ptr_metadata(e).is_some())?;
        let backing =
            self.path_merged_pointee_value(ref_key.as_str()).filter(|e| e.sort().is_array())?;
        Self::replace_fat_ptr_backing(&fat, &backing)
    }

    /// The value `*r` has on each path into the join that poisoned `r`'s
    /// `ref_pointees` entry, merged the way a phi is:
    /// `ite(p0, v0, ite(p1, v1, .. vn))`. `None` unless every path names a pointee
    /// whose value is in the environment, the values share one sort, and every
    /// predicate but the last is known. Records no hit.
    fn path_merged_pointee_value(&self, ref_key: &str) -> Option<Expr> {
        const MAX_ALTERNATIVES: usize = 64;
        let alternatives = self.ref_pointees.merged_alternatives(ref_key)?;
        if alternatives.is_empty() || alternatives.len() > MAX_ALTERNATIVES {
            return None;
        }
        let mut arms: Vec<(Option<Expr>, Expr)> = Vec::with_capacity(alternatives.len());
        for alternative in alternatives {
            let value = self.env_lookup(alternative.pointee.as_deref()?)?.clone();
            if arms.first().is_some_and(|(_, first)| first.sort() != value.sort()) {
                return None;
            }
            arms.push((alternative.edge_predicate.clone(), value));
        }
        let mut arms = arms.into_iter().rev();
        let (_, mut merged) = arms.next()?;
        for (predicate, value) in arms {
            merged = Expr::ite(predicate?, value, merged);
        }
        Some(merged)
    }

    /// Rebuild a fat-pointer datatype value with `fld_data` replaced by `backing`,
    /// every other field projected out of the original. Returns None (caller keeps
    /// the original untouched) unless `fat` really is a single-constructor datatype
    /// carrying a `fld_data` field whose sort matches `backing`.
    fn replace_fat_ptr_backing(fat: &Expr, backing: &Expr) -> Option<Expr> {
        let sort = fat.sort().clone();
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = dt.constructors.first()?;
        if !ctor.fields.iter().any(|f| &*f.name == "fld_data") {
            return None;
        }
        let dt_name = dt.name.to_string();
        let ctor_name = ctor.name.to_string();
        let mut fields = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            if &*field.name == "fld_data" {
                if &field.sort != backing.sort() {
                    return None;
                }
                fields.push(backing.clone());
            } else {
                fields.push(fat.clone().field_select(
                    dt_name.as_str(),
                    &*field.name,
                    field.sort.clone(),
                ));
            }
        }
        Some(Expr::datatype_constructor(dt_name.as_str(), ctor_name.as_str(), fields, sort.clone()))
    }

    /// Fat-pointer metadata (the slice LENGTH) read off the REFERENT of a
    /// `&[T]` / `&str` operand, rather than off the pointer variable itself.
    ///
    /// `assign_reference_to_place` declares the destination of a reference
    /// assignment with the destination's SORT and leaves it UNCONSTRAINED — it
    /// constrains the pointee instead. For a thin pointer that is harmless (the
    /// variable is just an address), but a slice reference's sort is the fat
    /// pointer `Slice_T{fld_ptr, fld_len, fld_data}`, so selecting `fld_len`
    /// straight off that variable yields a fresh unconstrained symbol. The slice
    /// VALUE reached through `ref_pointees` is the constrained one, so read the
    /// metadata there first.
    ///
    /// Returns None — caller keeps its existing fallback — unless the operand is
    /// a pointer to a slice/str AND its referent is a datatype carrying `fld_len`
    /// (a raw backing `Array` referent has no length and falls through).
    pub(in crate::codegen_ay::statement) fn slice_len_through_ref(
        &mut self,
        operand: &Operand,
    ) -> Option<Expr> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => return None, // external enum: TyKind
        };
        if !matches!(
            pointee.kind(),
            TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str)
        ) {
            return None;
        }
        let value = self.get_value_through_ref(operand)?;
        let sort = value.sort().clone();
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let len_sort = ctor.fields.iter().find(|f| &*f.name == "fld_len")?.sort.clone();
        Some(value.field_select(&*dt.name, "fld_len", len_sort))
    }

    fn is_range_full_index_operand(&self, operand: &Operand) -> bool {
        self.is_exact_core_range_full_operand(operand)
    }

    /// True when the index operand is a non-full range (`a..b`, `..n`, `n..`,
    /// `a..=b`, `..=n`) — a sub-slice op, as opposed to a scalar index. Used to
    /// fail closed (not Diverge) on sub-slice `index`/`index_mut` we don't model.
    fn is_range_index_operand(&self, operand: &Operand) -> bool {
        operand.ty(self.body.locals()).into_option().is_some_and(|ty| {
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if matches!(
                        def.trimmed_name().as_str(),
                        "Range" | "RangeTo" | "RangeFrom" | "RangeInclusive" | "RangeToInclusive"
                    )
            )
        })
    }

    /// Model `slice[..n]` / `slice[a..b]` / `slice[a..]` as a slice (Vec datatype)
    /// value with a bounded `fld_len` (the range length), assigning a reference to
    /// it into `destination`. This makes the downstream iterator (`VecIterMut` →
    /// `IntoIterNext`) terminate (bounded loop) and element select/store sound.
    ///
    /// The backing array is indexed from the sub-slice's own zero: a `RangeTo`
    /// view shares the source array, and a `Range` / `RangeFrom` view whose start
    /// is not provably zero gets a SHIFTED copy, `shifted[i] = source[start + i]`
    /// for every `i` below a bound the sub-slice's length cannot exceed
    /// ([`Self::shifted_subslice_backing`]). Before that shift `fld_data` was the
    /// SOURCE array unshifted while `fld_len` was `end - start`, so `sub[i]` read
    /// `source[i]`: `let s = &[1u8, 2, 3, 4][1..3]; assert!(s[0] == 1)` verified
    /// SUCCESSFUL and `assert!(s[0] == 2)` FAILED with a Genuine counterexample,
    /// through a `&[u8]`, a callee parameter, a symbolic start, `&s.as_bytes()[1..]`
    /// and `a[1..3].iter().fold(..)` alike (negative/subslice_offsets.rs,
    /// negative/subslice_producers.rs; main 31793ccc3 and bundle edec8fd8a).
    ///
    /// Returns false (caller fails closed) when the backing array, the EXACT
    /// range length, or — for a nonzero start — a bound on the sub-slice length
    /// can't be resolved. Part of the PROVED-green ArrayVec Drop-glue modelling.
    fn try_codegen_subslice_range_ref(
        &mut self,
        slice_arg: &Operand,
        index_arg: &Operand,
        destination: &Place,
    ) -> bool {
        // Backing array (fld_data). For `&mut self.buf` this resolves to the bare
        // fld_buf Array; for a Vec/slice datatype receiver, field-select backing.
        let Some(backing) =
            self.get_value_through_ref(slice_arg).or_else(|| self.codegen_operand(slice_arg))
        else {
            return false;
        };
        let (data_array, elem_sort) = if backing.sort().is_array() {
            let Some(arr) = backing.sort().array_sort() else {
                return false;
            };
            (backing.clone(), arr.element_sort.clone())
        } else if let Some(dt_name) = backing.clone().sort().datatype_name() {
            let resolved = self
                .get_datatype_field_sort(&backing, "fld_data")
                .map(|s| ("fld_data", s))
                .or_else(|| {
                    self.get_datatype_field_sort(&backing, "fld_buf").map(|s| ("fld_buf", s))
                });
            let Some((fld_name, data_sort)) = resolved else {
                return false;
            };
            let Some(arr) = data_sort.array_sort() else {
                return false;
            };
            let es = arr.element_sort.clone();
            (backing.clone().field_select(dt_name, fld_name, data_sort), es)
        } else {
            return false;
        };

        let len_expr = match self.range_subslice_length(slice_arg, index_arg) {
            Some(len) => len,
            // `RangeFrom` (`slice[start..]`) needs the SOURCE length: its length is
            // `source_len - start`. Tying it to the source `fld_len` (rather than
            // failing closed to an unmodelled sub-slice) means an empty source folds
            // the sub-slice to length 0 — exactly the OSC `osc_data[n..]` case.
            None => match self.range_from_subslice_length(slice_arg, index_arg) {
                Some(len) => len,
                None => return false,
            },
        };

        // Element `i` of the view is element `start + i` of the source. A view
        // that starts at zero shares the source array; any other view gets a
        // copy shifted by the start, or the statement fails closed when the
        // sub-slice's length has no bound to copy up to.
        let Some(start) = self.range_subslice_start(index_arg) else {
            return false;
        };
        let start_is_zero = self.const_bv_value_followed(&start) == Some(0);
        // Reads THROUGH this view use the backing built below and are exact; a
        // model that reads the SOURCE by another path is not. A zero start is
        // recorded too: `let s = &a[..2]; assert!(s.contains(&1) &&
        // s.contains(&2))` was FAILED [AY:CTREX_CAT:Genuine] with no offset
        // involved at all, so it is the MODEL, not the shift, that misreads.
        let view_base = self.ssa_base_name(destination);
        self.shifted_subslice_views.insert(std::sync::Arc::from(view_base));
        let data_array = if start_is_zero {
            data_array
        } else {
            match self.subslice_shift_bound(slice_arg, &backing, &len_expr) {
                Some(bound) => self.shifted_subslice_backing(&data_array, &start, bound),
                // The ELEMENTS cannot be shifted exactly: the view's length has
                // no bound to copy up to (`&input[start..]` over a parameter
                // slice). The view's LENGTH is still exact, and it is what a
                // `tail.len() == input.len() - start` obligation reads, so keep
                // the length and HAVOC the elements rather than abandoning the
                // whole view. Nothing rests on the elements: they are a fresh
                // array, and the statement records the fail-closed fallback, so
                // the harness cannot come back clean. Abandoning the view
                // instead left `fld_len` unconstrained too, and the guarded
                // `bmc_range_from_len_safe` / `bmc_range_len_safe` end-to-end
                // harnesses stopped proving unsat.
                None => {
                    debug!(
                        ?destination,
                        "sub-slice with a nonzero start and no bound on its length: \
                         elements havocked, fail closed"
                    );
                    self.ctx.unsupported_with_fallback(
                        "slice index range: sub-slice elements not shifted",
                        format!("{destination:?}"),
                    );
                    let name = self.ctx.fresh_name("ay_subslice_unshifted");
                    self.ctx.declare_var(&name, data_array.sort().clone())
                }
            }
        };

        // Build a `Vec<elem>` datatype value {ptr, len, cap, data}. ptr/cap are not
        // observed for iteration; `len` bounds the iterator, `data` holds the
        // view's elements from index 0 so reads through the sub-slice return the
        // stored values.
        let elem_suffix = crate::codegen_ay::names::sort_short_name(&elem_sort);
        let sort_name = crate::codegen_ay::names::vec_sort_name(&elem_suffix);
        let array_sort = Sort::array(ptr_sort(), elem_sort);
        let vec_sort =
            struct_sort(sort_name.as_str(), crate::codegen_ay::names::vec_fields(array_sort));
        let cons = crate::codegen_ay::names::cons_name(&sort_name);
        let zero = Expr::bitvec_const(0, POINTER_WIDTH);
        let vec_val = Expr::datatype_constructor(
            sort_name.as_str(),
            cons.as_str(),
            vec![zero.clone(), len_expr, zero, data_array],
            vec_sort,
        );
        self.assign_reference_to_place(destination, vec_val);
        true
    }

    /// The start of a sub-slice range operand as a `POINTER_WIDTH` bitvector:
    /// `RangeTo` → 0, `Range` / `RangeFrom` → `fld_start`. None for the inclusive
    /// ranges (not modelled here) or an operand that does not resolve.
    fn range_subslice_start(&mut self, index_arg: &Operand) -> Option<Expr> {
        let ty = index_arg.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        match def.trimmed_name().as_str() {
            "RangeTo" => Some(Expr::bitvec_const(0, POINTER_WIDTH)),
            "Range" | "RangeFrom" => {
                let range_val = self.codegen_operand(index_arg)?;
                let dt = range_val.sort().datatype_sort()?;
                let dt_name = dt.name.to_string();
                let cons = dt.constructors.first()?;
                let start_sort =
                    cons.fields.iter().find(|f| &*f.name == "fld_start")?.sort.clone();
                Self::coerce_bv_to_pointer_width(range_val.field_select(
                    dt_name.as_str(),
                    "fld_start",
                    start_sort,
                ))
            }
            _ => None,
        }
    }

    /// A number of elements the sub-slice can never exceed, for the shifted copy
    /// of [`Self::shifted_subslice_backing`]: the sub-slice's own length when it
    /// folds to a constant, else the source's length when that does (an array's
    /// static `N`, or the literal `fld_len` a `&[T; N] -> &[T]` unsize, a `&str`
    /// literal or an earlier sub-slice built). A sub-slice is never longer than
    /// its source on a path that passes the `end > len` / `start > len` bounds
    /// obligations the range stubs record. None when neither folds or the bound
    /// exceeds [`Self::MAX_SHIFTED_SUBSLICE_ELEMS`] (the caller fails closed).
    fn subslice_shift_bound(
        &mut self,
        slice_arg: &Operand,
        backing: &Expr,
        len_expr: &Expr,
    ) -> Option<u64> {
        let bound = self
            .const_bv_value_followed(len_expr)
            .or_else(|| self.slice_len_expr(slice_arg).and_then(|l| self.const_bv_value_followed(&l)))
            .or_else(|| self.datatype_len_field_const(backing))?;
        (bound <= Self::MAX_SHIFTED_SUBSLICE_ELEMS).then_some(bound)
    }

    /// Largest sub-slice copied element by element when its start is not zero.
    const MAX_SHIFTED_SUBSLICE_ELEMS: u64 = 4096;

    /// A fresh array `shifted` with `shifted[i] = data[start + i]` for every
    /// `i < bound`, asserted as select equalities (no store chain), so a view
    /// starting at `start` is read from its own index 0. Elements at or past
    /// `bound` are unconstrained; the caller guarantees the view is never that
    /// long on a path without a bounds violation.
    fn shifted_subslice_backing(&mut self, data: &Expr, start: &Expr, bound: u64) -> Expr {
        let name = self.ctx.fresh_name("ay_subslice_shifted");
        let shifted = self.ctx.declare_var(&name, data.sort().clone());
        let index_width =
            data.sort().array_sort().and_then(|a| a.index_sort.bitvec_width()).unwrap_or(POINTER_WIDTH);
        let start = match start.sort().bitvec_width() {
            Some(w) if w == index_width => start.clone(),
            Some(w) if w < index_width => start.clone().zero_extend(index_width - w),
            _ => start.clone().extract(index_width - 1, 0),
        };
        for i in 0..bound {
            let idx = Expr::bitvec_const(i as u128, index_width);
            let src = start.clone().bvadd(idx.clone());
            self.ctx.assert(shifted.clone().select(idx).eq(data.clone().select(src)));
        }
        debug!(bound, "sub-slice backing shifted by its start");
        shifted
    }

    /// The constant value of a bitvector expression made of constants, `bvadd`,
    /// `bvsub`, zero-extension, extraction and `fld_len` selection, following
    /// SSA definitions AT EVERY NODE.
    ///
    /// Following only the root is not enough: `end - start` of a range local is
    /// a `BvSub` whose two operands are SSA registers, so a root-only fold left
    /// `&a[1..3]` with no constant length and [`Self::subslice_shift_bound`]
    /// returned None — every nonzero-start view then failed closed
    /// ("sub-slice with a nonzero start and no bound on its length"), which is
    /// sound but proves nothing (`array_range_read_safe` FAILED with
    /// `unsupported_construct_fallback=1` on bundle 58a916fe3).
    fn const_bv_value_followed(&self, expr: &Expr) -> Option<u64> {
        self.const_bv_value_at(expr, Self::CONST_FOLD_DEPTH)
    }

    /// Recursion budget for [`Self::const_bv_value_followed`] and
    /// [`Self::datatype_len_field_const`], which call each other.
    const CONST_FOLD_DEPTH: usize = 32;

    fn const_bv_value_at(&self, expr: &Expr, depth: usize) -> Option<u64> {
        use ay_bindings::ExprValue;
        if depth == 0 {
            return None;
        }
        let e = self.follow_ssa(expr, 64);
        match e.value() {
            ExprValue::BitVecConst { value, .. } => value.clone().try_into().ok(),
            ExprValue::BvAdd(a, b) => Some(
                self.const_bv_value_at(a, depth - 1)?
                    .wrapping_add(self.const_bv_value_at(b, depth - 1)?),
            ),
            ExprValue::BvSub(a, b) => Some(
                self.const_bv_value_at(a, depth - 1)?
                    .wrapping_sub(self.const_bv_value_at(b, depth - 1)?),
            ),
            ExprValue::BvZeroExtend { expr, .. } => self.const_bv_value_at(expr, depth - 1),
            ExprValue::BvExtract { expr, high, low } if *low == 0 && *high < 64 => self
                .const_bv_value_at(expr, depth - 1)
                .map(|v| v & ((1u64 << (high + 1)) - 1)),
            // ANY field selected off a constructor value: read that constructor
            // argument. Restricting this to `fld_len` was not enough — a
            // sub-slice's length is `fld_end - fld_start` of the Range value, so
            // `&a[1..3]` still folded to nothing and every nonzero-start view
            // failed closed (measured on bundle 50d0d4789:
            // `const_range_view_exact_safe` FAILED with
            // `unsupported_construct_fallback=1`).
            ExprValue::DatatypeSelector { expr, selector_name, .. } => {
                self.datatype_field_const_at(expr, selector_name, depth - 1)
            }
            _ => None,
        }
    }

    /// The constant value of the `field_name` argument of a datatype value that
    /// follows to a constructor.
    fn datatype_field_const_at(&self, value: &Expr, field_name: &str, depth: usize) -> Option<u64> {
        use ay_bindings::ExprValue;
        if depth == 0 {
            return None;
        }
        let target = self.follow_ssa(value, 64);
        let ExprValue::DatatypeConstructor { args, .. } = target.value() else {
            return None;
        };
        let dt = target.sort().datatype_sort()?;
        let idx = dt.constructors.first()?.fields.iter().position(|f| &*f.name == field_name)?;
        self.const_bv_value_at(args.get(idx)?, depth - 1)
    }

    /// The constant `fld_len` of a slice / Vec datatype value that follows to a
    /// constructor, or the constant a `fld_len` selector over such a value reads.
    fn datatype_len_field_const(&self, value: &Expr) -> Option<u64> {
        self.datatype_len_field_const_at(value, Self::CONST_FOLD_DEPTH)
    }

    fn datatype_len_field_const_at(&self, value: &Expr, depth: usize) -> Option<u64> {
        use ay_bindings::ExprValue;
        if depth == 0 {
            return None;
        }
        let followed = self.follow_ssa(value, 64);
        match followed.value() {
            ExprValue::DatatypeSelector { expr, selector_name, .. } if selector_name == "fld_len" => {
                self.datatype_field_const_at(expr, "fld_len", depth - 1)
            }
            ExprValue::DatatypeSelector { .. } => None,
            _ => self.datatype_field_const_at(&followed, "fld_len", depth - 1),
        }
    }

    /// Exact length of a sub-slice range operand, as a `POINTER_WIDTH` bitvector:
    /// `RangeTo{end}` → end, `Range{start,end}` → end − start, recording the
    /// `end > len` (and `start > end`) bounds obligations Rust panics on. Returns None for
    /// RangeFrom (the caller then tries [`Self::range_from_subslice_length`],
    /// which needs the SOURCE length), for RangeInclusive / RangeToInclusive
    /// (their exact length is not modelled here — the caller fails closed), or
    /// if the operand can't be resolved.
    fn range_subslice_length(&mut self, slice_arg: &Operand, index_arg: &Operand) -> Option<Expr> {
        let ty = index_arg.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        let kind = def.trimmed_name();
        // Only exclusive RangeTo/Range have an exactly-modelled length here.
        if kind != "RangeTo" && kind != "Range" {
            return None;
        }
        let range_val = self.codegen_operand(index_arg)?;
        let dt = range_val.sort().datatype_sort()?;
        let dt_name = dt.name.to_string();
        let cons = dt.constructors.first()?;
        let end_sort = cons.fields.iter().find(|f| &*f.name == "fld_end")?.sort.clone();
        let end = Self::coerce_bv_to_pointer_width(range_val.clone().field_select(
            dt_name.as_str(),
            "fld_end",
            end_sort,
        ))?;
        // `slice[..end]` / `slice[start..end]` with `end > len` is a Rust panic
        // (`slice_end_index_len_fail`); record it whenever the source length
        // resolves. A source whose length does not resolve keeps the previous
        // (obligation-free) modelling rather than failing the whole sub-slice.
        if let Some(source_len) = self.slice_len_expr(slice_arg) {
            if let Some(source_len) = Self::coerce_bv_to_pointer_width(source_len) {
                self.record_violation_guarded(end.clone().bvugt(source_len), "bounds_check");
            }
        }
        if kind == "RangeTo" {
            return Some(end);
        }
        // Range { start, end } → end - start; `start > end` is a Rust panic too
        // (`slice_index_order_fail`) and would wrap the length.
        let start_sort = cons.fields.iter().find(|f| &*f.name == "fld_start")?.sort.clone();
        let start = Self::coerce_bv_to_pointer_width(range_val.field_select(
            dt_name.as_str(),
            "fld_start",
            start_sort,
        ))?;
        self.record_violation_guarded(start.clone().bvugt(end.clone()), "bounds_check");
        Some(end.bvsub(start))
    }

    /// Exact length of a `RangeFrom` sub-slice `slice[start..]`, as a `POINTER_WIDTH`
    /// bitvector: `source_len - start`. Unlike [`Self::range_subslice_length`], this
    /// needs the SOURCE slice (for its `fld_len`), so it takes `slice_arg` too.
    ///
    /// Rust panics if `start > source_len`, so the in-bounds length is exactly
    /// `source_len - start`. That panic is recorded HERE as a `bounds_check`
    /// obligation (the range path of the index stub emits none of its own), so
    /// the wrapped `bvsub` is only ever observed on a path the obligation already
    /// flags. Tying the length to the source `fld_len` is what lets an empty
    /// source (`osc_data` in the contract harness) fold the sub-slice to length 0
    /// instead of leaving an unmodelled sub-slice.
    fn range_from_subslice_length(
        &mut self,
        slice_arg: &Operand,
        index_arg: &Operand,
    ) -> Option<Expr> {
        let ty = index_arg.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        if def.trimmed_name() != "RangeFrom" {
            return None;
        }
        let range_val = self.codegen_operand(index_arg)?;
        let dt = range_val.sort().datatype_sort()?;
        let dt_name = dt.name.to_string();
        let cons = dt.constructors.first()?;
        let start_sort = cons.fields.iter().find(|f| &*f.name == "fld_start")?.sort.clone();
        let start = Self::coerce_bv_to_pointer_width(
            range_val.field_select(dt_name.as_str(), "fld_start", start_sort),
        )?;
        let source_len = Self::coerce_bv_to_pointer_width(self.slice_len_expr(slice_arg)?)?;
        // `slice[start..]` with `start > len` is a Rust panic
        // (`slice_start_index_len_fail`), and `source_len - start` would wrap
        // to 2^64 - (start - len) and drive the iterator bound with it. Record
        // the obligation on this path: before this modelling the shape failed
        // closed as an unmodelled sub-slice, so a missed obligation here would
        // turn an INCONCLUSIVE into a false PROVED.
        self.record_violation_guarded(start.clone().bvugt(source_len.clone()), "bounds_check");
        Some(source_len.bvsub(start))
    }

    /// Coerce a bitvector expression to `POINTER_WIDTH` (zero-extend / truncate).
    /// Returns None for a non-bitvector sort.
    fn coerce_bv_to_pointer_width(e: Expr) -> Option<Expr> {
        match e.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => Some(e),
            Some(w) if w < POINTER_WIDTH => Some(e.zero_extend(POINTER_WIDTH - w)),
            Some(_) => Some(e.extract(POINTER_WIDTH - 1, 0)),
            None => None,
        }
    }

    /// Register a stub-created indexed reference for write propagation. Part of #3392.
    ///
    /// When `codegen_slice_index_stub` creates a `slice_index_pointee_N` reference,
    /// the `_idx_by_` convention isn't used, so `try_propagate_indexed_ref_write_to_array`
    /// won't fire on `*ref = val` writes. This records the (container, index) pair
    /// so the propagation function can check it as a fallback.
    fn register_stub_indexed_ref(
        &mut self,
        slice_arg: &Operand,
        destination: &Place,
        idx_expr: Expr,
    ) {
        let dest_base: std::sync::Arc<str> = self.ssa_base_name(destination).into();
        let Some(pointee_base) = self.ref_pointees.get(dest_base.as_ref()).cloned() else {
            return;
        };
        // Resolve container env key from the slice operand.
        let container_base = match slice_arg {
            Operand::Copy(p) | Operand::Move(p) => {
                let ref_base = self.ssa_base_name(p);
                // Through ref_pointees for reference operands; direct name otherwise.
                self.ref_pointees
                    .get(ref_base.as_str())
                    .cloned()
                    .unwrap_or_else(|| std::sync::Arc::from(ref_base))
            }
            _ => return,
        };
        self.stub_indexed_refs.insert(pointee_base, (container_base, idx_expr));
    }

    /// Split slice index arguments into (slice, index) order.
    fn split_slice_index_args<'b>(
        &self,
        args: &'b [Operand],
    ) -> Option<(&'b Operand, &'b Operand)> {
        let is_slice = |op: &Operand| -> bool {
            op.ty(self.body.locals()).into_option().is_some_and(Self::is_slice_or_array_ref_ty)
        };

        match (args.first(), args.get(1)) {
            (Some(lhs), Some(rhs)) if is_slice(lhs) => Some((lhs, rhs)),
            (Some(lhs), Some(rhs)) if is_slice(rhs) => Some((rhs, lhs)),
            _ => None, // non-enum: tuple
        }
    }

    /// Check if slice element type is ZST.
    fn slice_elem_is_zst(&self, operand: &Operand) -> bool {
        self.slice_elem_ty_from_operand(operand).is_some_and(Self::is_zst_type)
    }

    /// Extract element type from a slice/array operand.
    fn slice_elem_ty_from_operand(&self, operand: &Operand) -> Option<rustc_public::ty::Ty> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => ty, // external enum: TyKind — non-pointer type used as-is
        };

        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => Some(elem),
            TyKind::RigidTy(RigidTy::Array(elem, _)) => Some(elem),
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
                args.0.first().and_then(|arg| {
                    if let rustc_public::ty::GenericArgKind::Type(elem_ty) = arg {
                        Some(*elem_ty)
                    } else {
                        None
                    }
                })
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Get the pointee type of a destination place.
    fn destination_pointee_ty(&self, destination: &Place) -> Option<rustc_public::ty::Ty> {
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(inner),
            _ => None, // external enum: TyKind
        }
    }

    /// Extract length expression from a slice/array operand.
    pub(in crate::codegen_ay::statement) fn slice_len_expr(
        &mut self,
        operand: &Operand,
    ) -> Option<Expr> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => ty, // external enum: TyKind — non-pointer type used as-is
        };

        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len)) => len
                .eval_target_usize()
                .into_option()
                .map(|n| Expr::bitvec_const(n as i128, POINTER_WIDTH)),
            TyKind::RigidTy(RigidTy::Slice(_)) => {
                let slice_expr = self.get_value_through_ref(operand)?;
                let slice_expr_for_sort = slice_expr.clone();
                let slice_sort = slice_expr_for_sort.sort();
                let dt_name = slice_sort.datatype_name()?;
                // Vec/String/Slice datatypes use "fld_len" field naming convention
                Some(slice_expr.field_select(dt_name, "fld_len", ptr_sort()))
            }
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Vec" => {
                let vec_expr = self.get_value_through_ref(operand)?;
                let vec_expr_for_sort = vec_expr.clone();
                let vec_sort = vec_expr_for_sort.sort();
                let dt_name = vec_sort.datatype_name()?;
                Some(vec_expr.field_select(dt_name, "fld_len", ptr_sort()))
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Get the sort of a specific field in a datatype expression.
    ///
    /// Returns None if the expression is not a datatype or doesn't have the field.
    fn get_datatype_field_sort(&self, expr: &Expr, field_name: &str) -> Option<Sort> {
        let dt = expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;
        ctor.field_sort(field_name)
    }
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Carry the "sub-slice view with a nonzero start" fact through the copies
    /// and reborrows between `&a[1..3]` and the call that consumes it.
    pub(in crate::codegen_ay::statement) fn propagate_shifted_subslice_view(
        &mut self,
        dest_base: &str,
        rhs: &rustc_public::mir::Rvalue,
    ) {
        use rustc_public::mir::{Operand, Rvalue};
        let src = match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
            | Rvalue::Ref(_, _, p)
            | Rvalue::AddressOf(_, p)
            | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => p,
            _ => return, // external enum: Rvalue
        };
        if self.shifted_subslice_view_base(src) {
            self.shifted_subslice_views.insert(std::sync::Arc::from(dest_base));
        }
    }

    /// Does `place` name a sub-slice view with a nonzero start — under its own
    /// name, its root local's name, or the referent its pointee entry names?
    pub(in crate::codegen_ay::statement) fn shifted_subslice_view_base(
        &mut self,
        place: &rustc_public::mir::Place,
    ) -> bool {
        let base = self.ssa_base_name(place);
        if self.shifted_subslice_views.contains(base.as_str()) {
            return true;
        }
        let root = self.root_ssa_base_name(place);
        if self.shifted_subslice_views.contains(root.as_str()) {
            return true;
        }
        if let Some(pointee) = self.ref_pointees.get(root.as_str()).cloned()
            && self.shifted_subslice_views.contains(pointee.as_ref())
        {
            return true;
        }
        false
    }

    /// The callee's own name, without its generic arguments, wherever they sit.
    fn callee_name_leaf(path: &str) -> &str {
        let bytes = path.as_bytes();
        let mut depth: i32 = 0;
        let mut segments: Vec<(usize, usize)> = Vec::new();
        let mut start = 0usize;
        let mut i = 0usize;
        while i < bytes.len() {
            match bytes[i] {
                b'<' => depth += 1,
                b'>' => depth = (depth - 1).max(0),
                b':' if depth == 0 && bytes.get(i + 1) == Some(&b':') => {
                    segments.push((start, i));
                    i += 2;
                    start = i;
                    continue;
                }
                _ => {}
            }
            i += 1;
        }
        segments.push((start, bytes.len()));
        for &(s, e) in segments.iter().rev() {
            let seg = &path[s..e];
            if !seg.is_empty() && !seg.starts_with('<') {
                return seg;
            }
        }
        path
    }

    /// FC-SUBSLICE (BMC): a sub-slice view with a nonzero start handed to a
    /// whole-slice model that reads the SOURCE array rather than the view's own
    /// shifted backing.
    ///
    /// The CHC lane has `subslice_consumer_fail_closed`; the BMC lane had no
    /// counterpart, and the shifted backing the branch added covers element
    /// access but not every model: `let a = [1u8,2,3,4]; let s = &a[1..3];
    /// assert!(s.contains(&2) && s.contains(&3))` — true in real Rust — was
    /// FAILED [AY:CTREX_CAT:Genuine] (adversarial review of
    /// m3/soundness-fixes-2, 2026-09-14; red on main too).
    ///
    /// This is a DENYLIST of the models measured not to read the view, not an
    /// allowlist of the ones that do: the element/iterator routes DO read the
    /// shifted backing, and demoting those would undo the sub-slice repair the
    /// branch already measured green.
    pub(in crate::codegen_ay::statement) fn bmc_subslice_consumer_fail_closed(
        &mut self,
        func: &rustc_public::mir::Operand,
        args: &[rustc_public::mir::Operand],
    ) {
        use rustc_public::mir::Operand;
        use rustc_public::ty::{RigidTy, TyKind};
        /// Whole-slice models that read the backing by a path the view's own
        /// shifted array does not reach.
        const SOURCE_READING_MODELS: &[&str] = &[
            "contains",
            "extend_from_slice",
            "binary_search",
            "binary_search_by",
            "binary_search_by_key",
            "starts_with",
            "ends_with",
            "copy_from_slice",
            "clone_from_slice",
            // Slice `PartialEq`: `let s = &a[1..3]; assert!(s == &[2,3][..])`
            // was FAILED [AY:CTREX_CAT:Genuine] — the comparison model reads the
            // source array, not the view (defect M5/D6). The slice-ref argument
            // test below keeps `eq`/`ne` on scalars out of this.
            "eq",
            "ne",
        ];
        if self.shifted_subslice_views.is_empty() {
            return;
        }
        let Some(path) = self.resolve_callee_path(func) else {
            return;
        };
        // A resolved callee path puts its generic arguments wherever the item
        // is generic: `core::slice::<impl [T]>::contains` has them in the
        // MIDDLE, so the leaf is the last `::` segment at angle-bracket depth 0
        // that is not itself a generic-argument group.
        let leaf = Self::callee_name_leaf(&path);
        if !SOURCE_READING_MODELS.contains(&leaf) {
            return;
        }
        let mut shifted = false;
        for arg in args {
            let (Operand::Copy(p) | Operand::Move(p)) = arg else { continue };
            let is_slice_ref = p.ty(self.body.locals()).into_option().is_some_and(|ty| {
                matches!(
                    ty.kind(),
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _))
                        if matches!(
                            pointee.kind(),
                            TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str | RigidTy::Array(..))
                        )
                )
            });
            if is_slice_ref && self.shifted_subslice_view_base(p) {
                shifted = true;
            }
        }
        if shifted {
            debug!(%path, "BMC: sub-slice with a nonzero start reaches a source-reading model — fail closed");
            self.ctx.unsupported_with_fallback(
                "subslice_start_ignored_by_consumer",
                format!("{path}: a shifted sub-slice reaches a model that reads the source"),
            );
        }
    }
}

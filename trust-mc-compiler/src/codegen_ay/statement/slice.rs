// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Slice type utilities and codegen stubs for AY - Part of #1354.
//!
//! Contains functions for:
//! - Slice/wide pointer type checking
//! - Array length extraction from pointer types
//! - Slice indexing and equality codegen stubs

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};

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
    /// unusual Option encoding — NEVER `Some(None)`, which would map to Diverge and unsoundly
    /// prune the post-call path. Modeled on `codegen_slice_partition_point` + `build_option_expr`.
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
            let slice_expr = self
                .get_value_through_ref(slice_arg)
                .or_else(|| self.codegen_operand(slice_arg))?;
            self.assign_reference_to_place(destination, slice_expr);
            return target;
        }

        // A sub-slice *range* index (`buf[a..b]`, `buf[..n]`, `buf[n..]`, ...) yields
        // a `&mut [T]` we do not model element-wise. FAIL CLOSED: record the
        // unsupported fallback and continue with an unconstrained destination.
        // Crucially do NOT `return None` here: the dispatcher maps a None stub
        // result (call_outcome.rs:35, from_nested_target(Some(None))) to Diverge,
        // which would UNSOUNDLY prune the post-call path for a non-diverging
        // index_mut. (This is the only sound option until sub-slice ranges carry a
        // bounded length through to their iterator — tracked for the Drop-glue
        // PROVED-green frontier.)
        if self.is_range_index_operand(index_arg) {
            // Model the sub-slice EXACTLY as a slice (Vec datatype) value:
            // fld_data = the backing array, fld_len = the range length, so the
            // downstream iterator (VecIterMut) is bounded and element select/store
            // stays sound. Exact for RangeTo/Range; FAIL CLOSED otherwise (never
            // `return None`, which would map to Diverge — unsoundly pruning the
            // post-call path for a non-diverging index_mut, call_outcome.rs:35).
            if self.try_codegen_subslice_range_ref(slice_arg, index_arg, destination) {
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

    fn is_range_full_index_operand(&self, operand: &Operand) -> bool {
        operand.ty(self.body.locals()).into_option().is_some_and(|ty| {
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeFull"
            )
        })
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

    /// Model `slice[..n]` / `slice[a..b]` as a slice (Vec datatype) value backed
    /// by the same array with a bounded `fld_len` (the range length), assigning a
    /// reference to it into `destination`. This makes the downstream iterator
    /// (`VecIterMut` → `IntoIterNext`) terminate (bounded loop) and element
    /// select/store sound. Returns false (caller fails closed) when the backing
    /// array or the EXACT range length can't be resolved. Part of the PROVED-green
    /// ArrayVec Drop-glue modelling.
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
            (backing.field_select(dt_name, fld_name, data_sort), es)
        } else {
            return false;
        };

        let Some(len_expr) = self.range_subslice_length(index_arg) else {
            return false;
        };

        // Build a `Vec<elem>` datatype value {ptr, len, cap, data}. ptr/cap are not
        // observed for iteration; `len` bounds the iterator, `data` is the real
        // backing array so reads through the sub-slice return stored values.
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

    /// Exact length of a sub-slice range operand, as a `POINTER_WIDTH` bitvector:
    /// `RangeTo{end}` → end, `Range{start,end}` → end − start. Returns None (caller
    /// fails closed) for RangeFrom / RangeInclusive / RangeToInclusive (their exact
    /// length is not modelled here) or if the operand can't be resolved.
    fn range_subslice_length(&mut self, index_arg: &Operand) -> Option<Expr> {
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
        if kind == "RangeTo" {
            return Some(end);
        }
        // Range { start, end } → end - start.
        let start_sort = cons.fields.iter().find(|f| &*f.name == "fld_start")?.sort.clone();
        let start = Self::coerce_bv_to_pointer_width(range_val.field_select(
            dt_name.as_str(),
            "fld_start",
            start_sort,
        ))?;
        Some(end.bvsub(start))
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

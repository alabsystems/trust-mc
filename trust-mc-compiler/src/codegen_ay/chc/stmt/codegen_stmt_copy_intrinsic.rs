// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CopyNonOverlapping intrinsic encoding — large method bodies.
//! Extracted from `codegen_stmt_copy.rs` per #4130.

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::ChcCtx;
use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_stmt_copy::CopyDestination;
use super::stmt_accumulator::StmtAccumulator;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Encode `copy_nonoverlapping(src, dst, count)` intrinsic when source/destination
    /// can be resolved to tracked array locals.
    ///
    /// For symbolic counts we emit guarded element-wise updates:
    /// `dst[i] = ite(i < count, src[i], dst[i])`.
    ///
    /// Part of #3517: replaced `CopyIntrinsicEncodeContext` with
    /// `StmtAccumulator` + `bb_idx` to consolidate the recurring
    /// `(modified, constraints, last_constraint_for_local)` triple.
    ///
    /// P4-1: `allow_overlap` selects the legal-overlap `copy` variant
    /// (`core::intrinsics::copy` / `volatile_copy_memory`, memmove semantics).
    /// It suppresses ONLY the same-object range-disjointness obligation, which
    /// is spurious for that variant — the src/dst room + alignment checks are
    /// emitted unconditionally. The element-wise value model below reads every
    /// source element from the PRE-copy source expression, which is exactly
    /// memmove (as-if-via-temporary) semantics, so it is correct for both
    /// variants. `copy_nonoverlapping` callers MUST pass `false`.
    pub(in crate::codegen_ay::chc) fn try_encode_copy_nonoverlapping_intrinsic(
        &mut self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
        allow_overlap: bool,
    ) -> bool {
        // UB obligations (span bounds / alignment / overlap) are independent
        // of whether the value copy below can be modeled precisely — emit
        // them first so every early return still carries the checks.
        self.push_copy_nonoverlapping_span_checks(copy, acc.modified, allow_overlap);
        for op in [&copy.src, &copy.dst] {
            if let rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place) = op
                && place.projection.is_empty()
            {
                let pointee = rustc_public::mir::Place {
                    local: place.local,
                    projection: vec![rustc_public::mir::ProjectionElem::Deref],
                };
                self.push_dead_raw_target_check(&pointee, acc.modified);
            }
        }

        let src_local = self.resolve_copy_intrinsic_target(&copy.src);

        // If we can at least identify dst, conservatively preserve it on unsupported shapes.
        let Some(dst) = self.resolve_copy_destination(&copy.dst, acc.modified) else {
            return false;
        };

        // Part of #3038: constraint-or-unchanged invariant.
        // When copy_nonoverlapping can't be modeled, emit a self-loop constraint
        // (output_var = input_var) to preserve the previous value instead of
        // leaving the output unconstrained (which causes spurious CTREX).
        let unsupported_havoc =
            |acc: &mut StmtAccumulator<'_>, dst: &CopyDestination, this: &mut Self| {
                this.copy_destination_self_loop(dst, acc);
            };

        // Part of #3798: when ref_targets resolution fails for src, try the
        // arg-ref pointee path for function parameters (&T / &mut T). Parameters
        // don't have ref_targets entries; their pointees are tracked via auxiliary
        // state variables in ref_arg_pointee_idx.
        let (src_local_idx, src_offset, src_expr) = if let Some((idx, off)) = src_local {
            let Some(expr) = self.local_expr_with_modified(idx, acc.modified) else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            (idx, off, expr)
        } else if let Some(arg_ref_expr) = self.resolve_copy_src_arg_ref(&copy.src) {
            // Use a sentinel local idx that won't conflict with real locals.
            // The src_local_idx is only used for type lookup (array length) which
            // we skip for scalar arg-ref copies.
            (usize::MAX, 0, arg_ref_expr)
        } else {
            unsupported_havoc(acc, &dst, self);
            debug!(
                "bb{} CopyNonOverlapping unsupported src resolution, dst key {} preserved",
                bb_idx, dst.constraint_key
            );
            return true;
        };
        let dst_expr_in = dst.expr_in.clone();
        let dst_out_name = dst.out_name.clone();
        let dst_out_sort = dst.out_sort.clone();
        let dst_offset = dst.offset;

        let Some(raw_count) = self.translate_operand_with_modified(&copy.count, acc.modified)
        else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };
        let const_count = Self::const_usize_from_expr(&raw_count);

        if !src_expr.sort().is_array() || !dst_expr_in.sort().is_array() {
            // P3-uninit: constant-size offset-0 copies into BV-sorted scalar
            // destinations get a precise little-endian byte splice (covers
            // punned multi-byte copies like `copy(p as *const u8, q as *mut u8, 8)`
            // that previously demoted via the self-loop havoc). Declines
            // (returns false) fall through to the existing paths unchanged.
            if self.try_copy_scalar_byte_splice(
                copy,
                &dst,
                src_local_idx,
                src_offset,
                &src_expr,
                const_count,
                acc,
            ) {
                return true;
            }
            if src_offset != 0 || dst_offset != 0 {
                unsupported_havoc(acc, &dst, self);
                return true;
            }
            let rhs = match const_count {
                Some(0) => dst_expr_in,
                Some(1) => src_expr,
                _ => {
                    unsupported_havoc(acc, &dst, self);
                    return true;
                }
            };
            let out_var = Expr::var(&*dst_out_name, dst_out_sort.clone());
            let signed = dst
                .local_idx
                .and_then(|local_idx| self.encode.local_signedness.get(&local_idx).copied());
            let Some(rhs) = Self::coerce_assignment_rhs_to_sort(rhs, &dst_out_sort, signed) else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            let Some(copy_constraint) =
                coerce_eq_constraint(&out_var, rhs.clone(), &dst_out_sort, false)
            else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            acc.replace_constraint(dst.constraint_key, copy_constraint);
            self.encode.local_expr_env.insert(dst.constraint_key, rhs);
            if let Some(local_idx) = dst.local_idx {
                acc.modified.insert(local_idx);
                self.encode.local_signedness.remove(&local_idx);
                // Part of #3938: invalidate stale constant so subsequent blocks
                // read the state variable (which carries the copy result) instead
                // of the pre-copy constant.
                self.encode.invalidate_local_cache(local_idx);
            }
            if let Some(pointee_vec_idx) = dst.pointee_vec_idx {
                self.mark_state_var_modified(pointee_vec_idx);
            }
            return true;
        }

        let Some(dst_array_sort) = dst_out_sort.array_sort() else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };

        let Some(dst_local_idx) = dst.local_idx else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };
        if src_local_idx == usize::MAX {
            unsupported_havoc(acc, &dst, self);
            return true;
        }
        let dst_ty = self.body.locals()[dst_local_idx].ty;
        let src_ty = self.body.locals()[src_local_idx].ty;
        // Everything below counts in ELEMENTS of the two arrays: offsets, the
        // room the count must fit, the element-wise value copy. A pointer PUNNED
        // to another element type (`&mut a[1] as *mut u64 as *mut u32`) counts
        // `count` in ITS elements, so the room checks compared the wrong units
        // (`copy(src_u8, a_u32[1] as *mut u8, 4)` failed a certified room check
        // on a 4-byte copy into a 4-byte element) and the element copy wrote u32
        // values into u64 slots (review probes c1_copy.rs `cast_elem_safe`,
        // c2_copy_cast.rs `cast2_safe` / `cast_src_safe`). The byte-exact span
        // checks were emitted above; the value copy takes the demoting fallback.
        let pointee_ty = |operand: &rustc_public::mir::Operand| {
            use rustc_public::ty::{RigidTy, TyKind};
            operand.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
                    Some(self.resolve_body_ty(inner))
                }
                _ => None,
            })
        };
        let element_ty =
            |array_ty| self.get_array_element_ty(array_ty).map(|ty| self.resolve_body_ty(ty));
        let punned = pointee_ty(&copy.src) != element_ty(self.resolve_body_ty(src_ty))
            || pointee_ty(&copy.dst) != element_ty(self.resolve_body_ty(dst_ty));
        if punned {
            // The room and same-array disjointness obligations, in BYTES. They
            // are independent of the value model below, whose splice and
            // fallback both return early: before these were emitted here, an
            // overlapping punned copy inside one array (UB; Kani reports
            // `memcpy src/dst overlap`) proved clean through the splice, and an
            // out-of-bounds one kept no violated check of its own (review
            // probes c4_punned_ub.rs `overlap_u16_bug`, c3_punned.rs
            // `dst_elem_oob_bug`).
            let always_out_of_room = self.push_punned_copy_byte_checks(
                copy,
                (src_local_idx, src_ty, src_offset),
                (dst_local_idx, dst_ty, dst_offset),
                &raw_count,
                allow_overlap,
            );
            if always_out_of_room {
                // Every execution reaching this copy violates a room check
                // above (a constant count past a constant offset): the copy is
                // undefined behaviour, and that violation is the verdict. The
                // destination keeps its value, one behaviour among any, with no
                // fallback booked, so the violation stays certifiable
                // (c3_punned.rs `dst_oob_bug`, `src_oob_bug`, `dst_elem_oob_bug`
                // FAILED certified Genuine on main).
                self.copy_destination_keep(&dst, acc);
                return true;
            }
            // A constant-count copy between two integer arrays through pointers
            // that are only casts of an element address is a BYTE splice of the
            // two memory images (element 0 at the low end); anything else takes
            // the demoting fallback.
            if let Some(count) = const_count
                && let Some(updated_dst) = self.punned_copy_byte_splice(
                    copy,
                    src_ty,
                    src_offset,
                    &src_expr,
                    dst_ty,
                    dst_offset,
                    &dst_expr_in,
                    count,
                )
            {
                let out_var = Expr::var(&*dst_out_name, dst_out_sort.clone());
                if let Some(copy_constraint) =
                    coerce_eq_constraint(&out_var, updated_dst.clone(), &dst_out_sort, false)
                {
                    acc.replace_constraint(dst.constraint_key, copy_constraint);
                    acc.modified.insert(dst_local_idx);
                    self.encode.local_expr_env.insert(dst.constraint_key, updated_dst);
                    self.encode.local_signedness.remove(&dst_local_idx);
                    self.encode.invalidate_local_cache(dst_local_idx);
                    debug!(bb_idx, count, "CHC: punned copy modeled as a byte splice");
                    return true;
                }
            }
            debug!(bb_idx, "CHC: copy through a pointer punned to another element type — fallback");
            unsupported_havoc(acc, &dst, self);
            return true;
        }
        let Some(dst_len) = self.get_array_length(dst_ty) else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };
        let Some(src_len) = self.get_array_length(src_ty) else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };

        // UB obligations for the tracked-array path. The value modeling below
        // clamps the copy at copy_len = min(remaining src, remaining dst),
        // which would otherwise silently hide an out-of-bounds count — the
        // FULL requested count must fit both allocations. Ranges must also be
        // disjoint when both sides resolve to the same local (element units
        // throughout; a huge count that wraps the end computation is already
        // flagged by the room checks).
        if self.memory_safety_checks {
            let count64 = coerce_bitvec_width_safe(
                raw_count.clone(),
                POINTER_WIDTH,
                SignExtension::ZeroExtend,
            );
            let src_room =
                Expr::bitvec_const(src_len.saturating_sub(src_offset) as u128, POINTER_WIDTH);
            let dst_room =
                Expr::bitvec_const(dst_len.saturating_sub(dst_offset) as u128, POINTER_WIDTH);
            // The full requested `count` must fit both the source and the
            // destination allocation. These are PRECISE, provenance-independent
            // bound obligations that are correct for BOTH the `copy_nonoverlapping`
            // and the legal-overlap `copy` variant — mark them eligible for
            // intrinsic-span tagging so a const-folded violation (a genuine
            // out-of-bounds / count-overflow bug) discharges this function's
            // offset-provenance doubt (see `ChcDiagnostics::span_check_exprs`).
            // The disjointness obligation pushed below is intentionally NOT
            // marked: it is spurious for the legal-overlap `copy` variant.
            let src_room_check = count64.clone().bvule(src_room);
            let dst_room_check = count64.clone().bvule(dst_room);
            self.diagnostics.span_check_exprs.insert(src_room_check.clone());
            self.diagnostics.span_check_exprs.insert(dst_room_check.clone());
            self.heap_state.pending_checks.push(src_room_check);
            self.heap_state.pending_checks.push(dst_room_check);

            // P4-1: overlap of the two ranges is UB only for the
            // `copy_nonoverlapping` variant — the legal-overlap `copy`
            // (memmove) variant must not carry this obligation.
            if src_local_idx == dst_local_idx && !allow_overlap {
                let src_off = Expr::bitvec_const(src_offset as u128, POINTER_WIDTH);
                let dst_off = Expr::bitvec_const(dst_offset as u128, POINTER_WIDTH);
                let src_end = src_off.clone().bvadd(count64.clone());
                let dst_end = dst_off.clone().bvadd(count64.clone());
                let disjoint = Expr::or(
                    count64.eq(Expr::bitvec_const(0u64, POINTER_WIDTH)),
                    Expr::or(src_end.bvule(dst_off), dst_end.bvule(src_off)),
                );
                self.heap_state.pending_checks.push(disjoint);
            }
        }

        let copy_len = dst_len.saturating_sub(dst_offset).min(src_len.saturating_sub(src_offset));
        if copy_len == 0 {
            // Zero-sized arrays: no-op copy, preserve destination.
            let out_var = Expr::var(&*dst_out_name, dst_out_sort.clone());
            let Some(copy_constraint) =
                coerce_eq_constraint(&out_var, dst_expr_in.clone(), &dst_out_sort, false)
            else {
                warn!(
                    bb_idx,
                    dst_local = dst_local_idx,
                    dst_sort = ?dst_out_sort,
                    dst_expr_sort = ?dst_expr_in.sort(),
                    "CHC: CopyNonOverlapping zero-length result sort mismatch; destination havoced"
                );
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            acc.replace_constraint(dst.constraint_key, copy_constraint);
            acc.modified.insert(dst_local_idx);
            self.encode.local_expr_env.insert(dst.constraint_key, dst_expr_in);
            self.encode.local_signedness.remove(&dst_local_idx);
            return true;
        }

        let Some(count_expr) =
            Self::coerce_expr_to_target_sort(raw_count, &dst_array_sort.index_sort, false)
        else {
            unsupported_havoc(acc, &dst, self);
            return true;
        };

        // Part of #1739: Extract constant count to simplify CHC encoding.
        // When count is a known constant, we eliminate ite guards entirely:
        // - count == 0: identity (dst_out = dst_in), no stores needed
        // - 0 < count < copy_len: direct copy for i < count, identity for rest
        // - count >= copy_len: direct copy for all elements
        // This reduces CHC expression complexity for PDR.
        if const_count == Some(0) {
            let out_var = Expr::var(&*dst_out_name, dst_out_sort.clone());
            let Some(copy_constraint) =
                coerce_eq_constraint(&out_var, dst_expr_in.clone(), &dst_out_sort, false)
            else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            acc.replace_constraint(dst.constraint_key, copy_constraint);
            acc.modified.insert(dst_local_idx);
            self.encode.local_expr_env.insert(dst.constraint_key, dst_expr_in);
            self.encode.local_signedness.remove(&dst_local_idx);
            debug!("bb{} CopyNonOverlapping constant count=0, identity (no stores)", bb_idx);
            return true;
        }

        let mut updated_dst = dst_expr_in;
        for i in 0..copy_len {
            let idx = if let Some(width) = dst_array_sort.index_sort.bitvec_width() {
                Expr::bitvec_const(i as u64, width)
            } else if dst_array_sort.index_sort.is_int() {
                Expr::int_const(i as u64)
            } else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            let Some(src_idx) = Self::shift_copy_index(idx.clone(), src_offset) else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };
            let Some(dst_idx) = Self::shift_copy_index(idx.clone(), dst_offset) else {
                unsupported_havoc(acc, &dst, self);
                return true;
            };

            if let Some(known_count) = const_count {
                let src_value = src_expr.clone().select(src_idx.clone());
                if i < known_count {
                    // Part of #4212: coerce source element to match dst array sort.
                    let src_value = Self::coerce_store_value(
                        updated_dst.sort(),
                        src_value,
                        false,
                        &self.diagnostics,
                    );
                    updated_dst = updated_dst.store(dst_idx, src_value);
                }
            } else {
                // Symbolic count: full guarded encoding with ite.
                let Some(in_bounds) = Self::build_copy_index_guard(idx.clone(), count_expr.clone())
                else {
                    unsupported_havoc(acc, &dst, self);
                    return true;
                };
                let src_value = src_expr.clone().select(src_idx);
                let dst_old_value = updated_dst.clone().select(dst_idx.clone());
                let dst_new_value = Expr::ite(in_bounds, src_value, dst_old_value);
                // Part of #4212: coerce ite result to match dst array sort.
                let dst_new_value = Self::coerce_store_value(
                    updated_dst.sort(),
                    dst_new_value,
                    false,
                    &self.diagnostics,
                );
                updated_dst = updated_dst.store(dst_idx, dst_new_value);
            }
        }

        let out_var = Expr::var(&*dst_out_name, dst_out_sort.clone());
        let Some(copy_constraint) =
            coerce_eq_constraint(&out_var, updated_dst.clone(), &dst_out_sort, false)
        else {
            warn!(
                bb_idx,
                dst_local = dst_local_idx,
                dst_sort = ?dst_out_sort,
                updated_sort = ?updated_dst.sort(),
                "CHC: CopyNonOverlapping result sort mismatch; destination havoced"
            );
            unsupported_havoc(acc, &dst, self);
            return true;
        };
        acc.replace_constraint(dst.constraint_key, copy_constraint);
        acc.modified.insert(dst_local_idx);
        self.encode.local_expr_env.insert(dst.constraint_key, updated_dst);
        self.encode.local_signedness.remove(&dst_local_idx);
        // Part of #3938: invalidate stale constant for array-copy destinations.
        self.encode.invalidate_local_cache(dst_local_idx);

        debug!(
            "bb{} modeled CopyNonOverlapping src_local={} src_offset={} dst_local={} dst_offset={} len={} const_count={:?}",
            bb_idx, src_local_idx, src_offset, dst_local_idx, dst_offset, copy_len, const_count
        );
        true
    }

    /// Fail on every path that reaches this point when the raw pointer local
    /// `ptr_local` takes its `ref_targets` entry to a local whose storage is
    /// dead here, as the load side does (`try_resolve_deref_via_ref_targets`,
    /// #762): an access through it is a dangling access. A heap owner's
    /// moved buffer is told apart from the dead owner's own storage by
    /// [`Self::access_through_dead_ref_target`].
    ///
    /// `access` is the place the store or copy touches through the pointer
    /// (`*p`, `(*p).f`), whose local is the pointer.
    ///
    /// A constant pointer's pointee (`ref_target_through_constant`: a static or
    /// constant memory) never dies, so it gets no dead-target obligation; as on
    /// the read side, the access is then bounded by the global-object lane or
    /// fails closed (`bound_access_through_constant_or_fail_close`, main's
    /// LIVE-statics rule).
    pub(in crate::codegen_ay::chc) fn push_dead_raw_target_check(
        &mut self,
        access: &rustc_public::mir::Place,
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        use rustc_public::ty::{RigidTy, TyKind};
        let ptr_local = access.local;
        let is_raw = self
            .body
            .locals()
            .get(ptr_local)
            .is_some_and(|decl| matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..))));
        if is_raw
            && let Some(rt) = self.ref_resolution.ref_targets.get(&ptr_local)
            && self.liveness.dead_locals.contains(&rt.local)
            && self.ref_target_through_constant(rt.local, &rt.projections)
        {
            self.bound_access_through_constant_or_fail_close(access, modified_locals);
            return;
        }
        if is_raw && self.access_through_dead_ref_target(ptr_local) {
            debug!(
                ptr_local,
                target_local = self.ref_resolution.ref_targets.get(&ptr_local).map(|t| t.local),
                "CHC: dead_object violation — access through a pointer to a dead local"
            );
            self.heap_state.pending_checks.push(Expr::bool_const(false));
        }
    }

    /// `copy_nonoverlapping::<T>(src, dst, 1)` of an integer `T` that the copy
    /// lane above would leave to its demoting fallback (a destination or
    /// source it cannot resolve to a tracked local at a constant element
    /// offset), encoded as the typed store `*dst = *src` it is.
    ///
    /// The copy moves `size_of::<T>()` bytes from `src` to `dst`; for an
    /// integer `T` (no padding, no invalid bit pattern, no provenance) that is
    /// exactly reading a `T` through `src` and writing it through `dst`, which
    /// the dereference load and store handlers encode (or fail closed) as they
    /// do for the MIR statement `(*dst) = copy (*src)`. A one-element copy into
    /// a field at a non-zero offset (`&mut p.b`), through a capture of an
    /// `FnMut` closure (`(*self).1`), or inside a contract closure under
    /// `#[kani::modifies(p)]` had no definition chain to its ref target, so the
    /// copy lane's chain-less refusal took the fallback and a program Kani and
    /// main prove failed closed (second review of round 9 of
    /// fix/chc-false-certificates, `r2_copy.rs` `c13`/`c16`/`c17`/`c18`,
    /// `r2_contract_copy.rs` `k01`/`k05`/`k08`); main's proofs of some of them
    /// came from dropping the target's projection, which also certified the
    /// field-`b` copies' safe twins falsely. The span, alignment and overlap
    /// obligations of the copy are emitted first, as the copy lane does.
    ///
    /// Only the statement form calls this: its block drains the store chains
    /// and pending memory updates a dereference store leaves.
    pub(in crate::codegen_ay::chc) fn try_encode_copy_as_typed_store(
        &mut self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue};
        use rustc_public::ty::{RigidTy, TyKind};
        let whole_local = |op: &Operand| match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        let (Some(src_local), Some(dst_local)) = (whole_local(&copy.src), whole_local(&copy.dst))
        else {
            return false;
        };
        let pointee = |local: usize| {
            let ty = self.resolve_body_ty(self.body.locals().get(local)?.ty);
            match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
                    Some(self.resolve_body_ty(inner))
                }
                _ => None,
            }
        };
        let (Some(src_pointee), Some(dst_pointee)) = (pointee(src_local), pointee(dst_local))
        else {
            return false;
        };
        if src_pointee != dst_pointee
            || !matches!(src_pointee.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
        {
            return false;
        }
        let count_is_one = match &copy.count {
            Operand::Constant(c) => c.const_.eval_target_usize().ok() == Some(1),
            count => self.body_constant_int(count) == Some(1),
        };
        if !count_is_one {
            return false;
        }
        let lane_falls_back = self.resolve_copy_destination(&copy.dst, acc.modified).is_none()
            || (self.resolve_copy_intrinsic_target(&copy.src).is_none()
                && self.resolve_copy_src_arg_ref(&copy.src).is_none());
        if !lane_falls_back {
            return false;
        }
        let rhs = rvalue_use!(Rvalue::Use(Operand::Copy(Place {
            local: src_local,
            projection: vec![ProjectionElem::Deref],
        })));
        let Some(rhs_expr) = self.translate_rvalue_with_modified(&rhs, acc.modified, None) else {
            return false;
        };
        self.push_copy_nonoverlapping_span_checks(copy, acc.modified, false);
        let lhs = Place { local: dst_local, projection: vec![ProjectionElem::Deref] };
        self.loop_modifies_store_check(&lhs, acc.modified);
        debug!(bb_idx, src_local, dst_local, "CHC: one-element integer copy encoded as a typed store");
        self.encode_projection_assignment(&lhs, rhs_expr, dst_local, bb_idx, acc);
        true
    }

    /// The stack address a pointer local holds on every path: its own record
    /// (`known_stack_addr_expr`), or that of the local its single whole
    /// definition copies, casts pointer-to-pointer (`p as *mut u8` keeps the
    /// address) or reborrows whole (`&raw mut (*q)`).
    fn traced_known_stack_addr(&self, local: usize, depth: u32) -> Option<Expr> {
        use rustc_public::mir::{
            CastKind, Operand, PointerCoercion, ProjectionElem, Rvalue, StatementKind,
        };
        if let Some(addr) = self.known_stack_addr_expr(local) {
            return Some(addr);
        }
        if depth > 8 || self.local_has_multiple_whole_definitions(local) {
            return None;
        }
        let definition = self.body.blocks.iter().flat_map(|b| b.statements.iter()).find_map(|st| {
            match &st.kind {
                StatementKind::Assign(place, rvalue)
                    if place.local == local && place.projection.is_empty() =>
                {
                    Some(rvalue)
                }
                _ => None,
            }
        })?;
        let source = match definition {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
            | Rvalue::Cast(
                CastKind::PtrToPtr
                | CastKind::PointerCoercion(
                    PointerCoercion::MutToConstPointer | PointerCoercion::ArrayToPointer,
                ),
                Operand::Copy(p) | Operand::Move(p),
                _,
            ) if p.projection.is_empty() => p.local,
            Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p)
                if matches!(p.projection.as_slice(), [ProjectionElem::Deref]) =>
            {
                p.local
            }
            _ => return None,
        };
        self.traced_known_stack_addr(source, depth + 1)
    }

    /// Whether the pointer `operand` is a chain of whole-local copies,
    /// reborrows and pointer casts back to the address of an array element or
    /// an array (`&mut a[1] as *mut u64 as *mut u32`, `src.as_ptr()`): no
    /// arithmetic moved it, so the copy target's element offset is its byte
    /// offset over the element size.
    fn copy_pointer_is_cast_of_element_address(&self, operand: &rustc_public::mir::Operand) -> bool {
        use rustc_public::CrateDef;
        use rustc_public::mir::{CastKind, Operand, ProjectionElem, Rvalue, StatementKind};
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return false };
        if !place.projection.is_empty() {
            return false;
        }
        let arg_count = self.body.arg_locals().len();
        let mut pending = vec![place.local];
        let mut seen = std::collections::HashSet::new();
        while let Some(local) = pending.pop() {
            if !seen.insert(local) {
                continue;
            }
            if local == 0 || (1..=arg_count).contains(&local) {
                return false;
            }
            let mut defined = false;
            for block in &self.body.blocks {
                if let rustc_public::mir::TerminatorKind::Call { func, args, destination, .. } =
                    &block.terminator.kind
                    && destination.local == local
                {
                    // `<[T]>::as_ptr` / `as_mut_ptr` (kept abstract, not inlined)
                    // return the slice's data address unchanged.
                    let identity = destination.projection.is_empty()
                        && func.ty(self.body.locals()).ok().is_some_and(|ty| {
                            matches!(ty.kind(), rustc_public::ty::TyKind::RigidTy(
                                rustc_public::ty::RigidTy::FnDef(def, _))
                                if {
                                    let name = def.name();
                                    name.starts_with("core::slice::<impl [")
                                        && (name.ends_with(">::as_ptr")
                                            || name.ends_with(">::as_mut_ptr"))
                                })
                        });
                    match args.as_slice() {
                        [Operand::Copy(arg) | Operand::Move(arg)]
                            if identity && arg.projection.is_empty() =>
                        {
                            defined = true;
                            pending.push(arg.local);
                        }
                        _ => return false,
                    }
                }
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != local {
                        continue;
                    }
                    if !lhs.projection.is_empty() {
                        return false;
                    }
                    defined = true;
                    match rhs {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                        | Rvalue::Cast(
                            CastKind::PtrToPtr | CastKind::PointerCoercion(_),
                            Operand::Copy(src) | Operand::Move(src),
                            _,
                        ) if src.projection.is_empty() => pending.push(src.local),
                        // A reborrow `&raw mut (*r)` is `r`'s address.
                        Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                            if matches!(src.projection.as_slice(), [ProjectionElem::Deref]) =>
                        {
                            pending.push(src.local);
                        }
                        Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                            if matches!(
                                src.projection.as_slice(),
                                []
                                    | [ProjectionElem::Index(_)]
                                    | [ProjectionElem::ConstantIndex { from_end: false, .. }]
                            ) => {}
                        _ => return false,
                    }
                }
            }
            if !defined {
                return false;
            }
        }
        true
    }

    /// Room and same-array disjointness obligations, in BYTES, for
    /// `copy_nonoverlapping(src, dst, count)` through PUNNED pointers into
    /// tracked arrays: `count * size_of::<T>()` bytes from each pointer's byte
    /// offset must fit its array, and when both pointers address one array
    /// (and this is not the legal-overlap `copy`) the two byte ranges must be
    /// disjoint. Emitted only when both pointers are casts of an element
    /// address ([`Self::copy_pointer_is_cast_of_element_address`]), where the
    /// resolved offsets are element offsets; any other punned copy takes the
    /// demoting fallback, which never leaves a clean proof. Returns whether a
    /// room check is violated on every execution (a constant count past a
    /// constant offset).
    fn push_punned_copy_byte_checks(
        &mut self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        (src_local_idx, src_ty, src_offset): (usize, rustc_public::ty::Ty, usize),
        (dst_local_idx, dst_ty, dst_offset): (usize, rustc_public::ty::Ty, usize),
        raw_count: &Expr,
        allow_overlap: bool,
    ) -> bool {
        use rustc_public::ty::{RigidTy, TyKind};
        if !self.memory_safety_checks {
            return false;
        }
        let size_of = |ty: rustc_public::ty::Ty| -> Option<u64> {
            let ty = self.resolve_body_ty(ty);
            u64::try_from(ty.layout().ok()?.shape().size.bytes()).ok()
        };
        let Some(pointee_size) =
            copy.src.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
                    size_of(inner)
                }
                _ => None,
            })
        else {
            return false;
        };
        let array = |ty: rustc_public::ty::Ty| -> Option<(u64, u64)> {
            let ty = self.resolve_body_ty(ty);
            let elem = size_of(self.get_array_element_ty(ty)?)?;
            let len = u64::try_from(self.get_array_length(ty)?).ok()?;
            Some((elem, len.checked_mul(elem)?))
        };
        let (Some((src_elem, src_total)), Some((dst_elem, dst_total))) =
            (array(src_ty), array(dst_ty))
        else {
            return false;
        };
        if pointee_size == 0
            || !self.copy_pointer_is_cast_of_element_address(&copy.src)
            || !self.copy_pointer_is_cast_of_element_address(&copy.dst)
        {
            return false;
        }
        let (Some(src_from), Some(dst_from)) = (
            u64::try_from(src_offset).ok().and_then(|off| off.checked_mul(src_elem)),
            u64::try_from(dst_offset).ok().and_then(|off| off.checked_mul(dst_elem)),
        ) else {
            return false;
        };
        let bv = |value: u64| Expr::bitvec_const(u128::from(value), POINTER_WIDTH);
        let count64 =
            coerce_bitvec_width_safe(raw_count.clone(), POINTER_WIDTH, SignExtension::ZeroExtend);
        // `count * size <= total - from` without the product wrapping.
        let src_room = src_total.saturating_sub(src_from) / pointee_size;
        let dst_room = dst_total.saturating_sub(dst_from) / pointee_size;
        let always_out_of_room = Self::const_usize_from_expr(raw_count)
            .and_then(|count| u64::try_from(count).ok())
            .is_some_and(|count| count > src_room || count > dst_room);
        let src_room_check = count64.clone().bvule(bv(src_room));
        let dst_room_check = count64.clone().bvule(bv(dst_room));
        self.diagnostics.span_check_exprs.insert(src_room_check.clone());
        self.diagnostics.span_check_exprs.insert(dst_room_check.clone());
        self.heap_state.pending_checks.push(src_room_check);
        self.heap_state.pending_checks.push(dst_room_check);
        if src_local_idx == dst_local_idx && !allow_overlap {
            // Within the room checks the byte count does not wrap; outside
            // them a room check is already violated.
            let bytes = count64.clone().bvmul(bv(pointee_size));
            let disjoint = Expr::or(
                count64.eq(bv(0)),
                Expr::or(
                    bv(src_from).bvadd(bytes.clone()).bvule(bv(dst_from)),
                    bv(dst_from).bvadd(bytes).bvule(bv(src_from)),
                ),
            );
            self.heap_state.pending_checks.push(disjoint);
        }
        debug!(
            src_local_idx,
            dst_local_idx, src_from, dst_from, pointee_size, "CHC: punned copy byte obligations"
        );
        always_out_of_room
    }

    /// The destination array after `copy_nonoverlapping(src, dst, count)`
    /// through PUNNED pointers (their pointee is not their array's element
    /// type), as a byte splice: the destination's memory image with
    /// `count * size_of::<T>()` bytes at its byte offset replaced by the
    /// source image's bytes at its byte offset, read back element by element
    /// into the destination array. `None` unless both arrays and `T` are
    /// integers, the count is a constant, both pointers are casts of an element
    /// address ([`Self::copy_pointer_is_cast_of_element_address`]), and both
    /// byte ranges lie inside their arrays (the span checks flag the rest).
    #[allow(clippy::too_many_arguments)]
    fn punned_copy_byte_splice(
        &self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        src_ty: rustc_public::ty::Ty,
        src_offset: usize,
        src_expr: &Expr,
        dst_ty: rustc_public::ty::Ty,
        dst_offset: usize,
        dst_expr: &Expr,
        count: usize,
    ) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};
        let int_size = |ty: rustc_public::ty::Ty| -> Option<usize> {
            let ty = self.resolve_body_ty(ty);
            if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))) {
                return None;
            }
            usize::try_from(ty.layout().ok()?.shape().size.bytes()).ok().filter(|size| *size > 0)
        };
        let pointee_size = int_size(match copy.src.ty(self.body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        })?;
        let src_ty = self.resolve_body_ty(src_ty);
        let dst_ty = self.resolve_body_ty(dst_ty);
        let src_elem = int_size(self.get_array_element_ty(src_ty)?)?;
        let dst_elem = int_size(self.get_array_element_ty(dst_ty)?)?;
        let src_len = usize::try_from(self.get_array_length(src_ty)?).ok()?;
        let dst_len = usize::try_from(self.get_array_length(dst_ty)?).ok()?;
        const MAX_IMAGE_BYTES: usize = 512;
        if src_len * src_elem > MAX_IMAGE_BYTES || dst_len * dst_elem > MAX_IMAGE_BYTES {
            return None;
        }
        if !self.copy_pointer_is_cast_of_element_address(&copy.src)
            || !self.copy_pointer_is_cast_of_element_address(&copy.dst)
        {
            return None;
        }
        let bytes = count.checked_mul(pointee_size)?;
        let src_from = src_offset.checked_mul(src_elem)?;
        let dst_from = dst_offset.checked_mul(dst_elem)?;
        if bytes == 0
            || src_from.checked_add(bytes)? > src_len * src_elem
            || dst_from.checked_add(bytes)? > dst_len * dst_elem
        {
            return None;
        }
        // The index width, when the array's elements are bitvectors of the
        // element's size.
        let index_bits = |array: &Expr, elem: usize| -> Option<u32> {
            let sort = array.sort().array_sort()?;
            (sort.element_sort.bitvec_width() == Some(u32::try_from(8 * elem).ok()?))
                .then(|| sort.index_sort.bitvec_width())
                .flatten()
        };
        let src_index_bits = index_bits(src_expr, src_elem)?;
        let dst_index_bits = index_bits(dst_expr, dst_elem)?;
        // Memory image, element 0 at the low end.
        let image = |array: &Expr, len: usize, index_bits: u32| -> Expr {
            let mut image: Option<Expr> = None;
            for i in 0..len {
                let elem = array.clone().select(Expr::bitvec_const(i as u128, index_bits));
                image = Some(match image {
                    None => elem,
                    Some(lower) => elem.concat(lower),
                });
            }
            image.expect("arrays with no element were declined")
        };
        let src_image = image(src_expr, src_len, src_index_bits);
        let dst_image = image(dst_expr, dst_len, dst_index_bits);
        let bits = |byte: usize| u32::try_from(8 * byte).ok();
        let piece = src_image.extract(bits(src_from + bytes)? - 1, bits(src_from)?);
        let dst_total = dst_len * dst_elem;
        let mut spliced = piece;
        if dst_from > 0 {
            spliced = spliced.concat(dst_image.clone().extract(bits(dst_from)? - 1, 0));
        }
        if dst_from + bytes < dst_total {
            spliced =
                dst_image.extract(bits(dst_total)? - 1, bits(dst_from + bytes)?).concat(spliced);
        }
        // Every destination element the splice touches, read back from the
        // new image; the others keep their value.
        let mut updated = dst_expr.clone();
        for i in (dst_from / dst_elem)..(dst_from + bytes).div_ceil(dst_elem) {
            let lo = bits(i * dst_elem)?;
            let value = spliced.clone().extract(lo + bits(dst_elem)? - 1, lo);
            updated = updated.store(Expr::bitvec_const(i as u128, dst_index_bits), value);
        }
        Some(updated)
    }

    /// Emit UB obligations for `copy_nonoverlapping(src, dst, count)`:
    /// src-readable / dst-writable span bounds + alignment
    /// (`heap_span_access_checks`), and range disjointness when both pointers
    /// const-fold into the same allocation. Pushed onto `pending_checks`;
    /// drained into error rules by the statement path (`codegen_stmt/mod.rs`)
    /// or the call path (`codegen_call_copy_nonoverlapping`).
    ///
    /// P4-1: `allow_overlap` (legal-overlap `copy` variant) suppresses ONLY
    /// the same-allocation disjointness obligation; span bounds and alignment
    /// are emitted for both variants.
    fn push_copy_nonoverlapping_span_checks(
        &mut self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        modified: &std::collections::HashSet<usize>,
        allow_overlap: bool,
    ) {
        use rustc_public::ty::{RigidTy, TyKind};

        if !self.memory_safety_checks {
            return;
        }
        // `Place::ty` indexes `locals` and panics on a local outside this body; such
        // an operand takes the same path as an untypeable one below.
        if let rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place) =
            &copy.src
            && place.local >= self.body.locals().len()
        {
            return;
        }
        let elem_ty = copy.src.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
            _ => None,
        });
        let Some(elem_ty) = elem_ty else {
            return;
        };
        let Some(count) = self.translate_operand_with_modified(&copy.count, modified) else {
            return;
        };
        // A pointer local whose stack address is known on every path
        // (`known_stack_addr_expr`) is checked at that constant address: its
        // state variable carried across blocks would leave the object lane
        // symbolic, and the span bound would range over every object
        // (`symbolic_lane_bounds`), which doubled `splice_value_pass`'s
        // solve time (lostwrite track round 1, finding 5).
        let known = |ctx: &Self, op: &rustc_public::mir::Operand| match op {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
                if place.projection.is_empty() =>
            {
                ctx.traced_known_stack_addr(place.local, 0)
            }
            _ => None,
        };
        let src = known(self, &copy.src)
            .or_else(|| self.translate_operand_with_modified(&copy.src, modified));
        let dst = known(self, &copy.dst)
            .or_else(|| self.translate_operand_with_modified(&copy.dst, modified));

        // Alignment / count-overflow / allocation-bound span checks are precise
        // and provenance-independent — mark them eligible for intrinsic-span
        // tagging (a const-folded violation is a genuine bug, see
        // `ChcDiagnostics::span_check_exprs`). The disjointness obligation below
        // is NOT marked: it is spurious for the legal-overlap `copy` variant.
        if let Some(src) = &src {
            let checks = self.heap_span_access_checks(src, elem_ty, &count);
            self.diagnostics.span_check_exprs.extend(checks.iter().cloned());
            self.heap_state.pending_checks.extend(checks);
        }
        if let Some(dst) = &dst {
            let checks = self.heap_span_access_checks(dst, elem_ty, &count);
            self.diagnostics.span_check_exprs.extend(checks.iter().cloned());
            self.heap_state.pending_checks.extend(checks);
        }

        // Disjointness: the two byte ranges are disjoint, or they lie in
        // different allocations. Different ids are disjoint, and id-equality
        // alone is never a violation — disjoint sub-ranges of one allocation
        // are legal. The offset-lane arithmetic here is guarded by the
        // span-fits / no-wrap obligations pushed above.
        //
        // When an id does not const-fold (a pointer read from a closure
        // capture, a parameter or a Vec's buffer field), the obligation is
        // the same comparison over the symbolic ids. It used to be emitted
        // only when both ids const-folded, so a copy of a value onto itself
        // (`copy_nonoverlapping(d, d, 1)` through an `FnMut` capture, a
        // contract's raw parameter or `v.as_mut_ptr()`) was proved where Kani
        // reports "memcpy src/dst overlap" once the one-element typed-store
        // lowering resolved such copies (third review of round 10 of
        // fix/chc-false-certificates, `r3_overlap.rs` o01, o05, o08, o10 and
        // `r3_copy.rs` c01; o05 the same on main f5dfb8d48).
        // P4-1: spurious for the legal-overlap `copy` variant — skip.
        if allow_overlap {
            return;
        }
        let (Some(src), Some(dst)) = (src, dst) else {
            return;
        };
        let (Some((src_id, src_off)), Some((dst_id, dst_off))) =
            (self.split_pointer(&src), self.split_pointer(&dst))
        else {
            return;
        };
        let const_ids = (Self::const_obj_id_u32(&src_id), Self::const_obj_id_u32(&dst_id));
        if let (Some(src_const_id), Some(dst_const_id)) = const_ids
            && src_const_id != dst_const_id
        {
            return;
        }
        let Some(elem_size) = self
            .get_type_size(elem_ty)
            .filter(|size| *size > 0)
            .and_then(|size| u32::try_from(size).ok())
        else {
            return;
        };

        let count64 = coerce_bitvec_width_safe(count, POINTER_WIDTH, SignExtension::ZeroExtend);
        let span64 = if elem_size == 1 {
            count64
        } else {
            count64.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
        };
        let span32 = span64.extract(31, 0);
        let src_end = src_off.clone().bvadd(span32.clone());
        let dst_end = dst_off.clone().bvadd(span32.clone());
        let mut disjoint = Expr::or(
            span32.eq(Expr::bitvec_const(0u64, 32)),
            Expr::or(src_end.bvule(dst_off), dst_end.bvule(src_off)),
        );
        if !matches!(const_ids, (Some(_), Some(_))) {
            disjoint = Expr::or(src_id.eq(dst_id).not(), disjoint);
        }
        self.heap_state.pending_checks.push(disjoint);
    }

    /// Part of #3687: Select BigInt value from typed memory array at `addr`.
    pub(in crate::codegen_ay::chc) fn load_bigint_from_typed_array(
        &mut self,
        addr: Expr,
        ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let ty = self.resolve_body_ty(ty);
        let type_key = self.type_key_for_body_ty(ty);
        let elem_sort = Sort::int();
        let addr = coerce_bitvec_width_safe(addr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let (arr_name, arr_out, _, is_new) =
            self.heap_state.get_or_create_type_array(&type_key, elem_sort.clone(), &self.fn_name);
        self.heap_state.mark_type_array_read(&arr_name, self.current_encode_bb);
        if is_new {
            let s = Sort::array(ptr_sort(), elem_sort.clone());
            self.push_late_state_var_pair(std::sync::Arc::clone(&arr_name), &arr_out, s);
        }
        let arr_sort = Sort::array(ptr_sort(), elem_sort);
        let arr_expr = self
            .heap_state
            .get_store_chain(&type_key)
            .cloned()
            .unwrap_or_else(|| Expr::var(&*arr_name, arr_sort));
        debug!(%type_key, "CHC: load_bigint_from_typed_array");
        Some(arr_expr.select(addr))
    }
}

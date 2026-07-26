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
        let src = self.translate_operand_with_modified(&copy.src, modified);
        let dst = self.translate_operand_with_modified(&copy.dst, modified);

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

        // Disjointness: only when BOTH pointers const-fold into the SAME
        // allocation. Different ids are trivially disjoint, and id-equality
        // alone is never a violation — disjoint sub-ranges of one allocation
        // are legal. The offset-lane arithmetic here is guarded by the
        // span-fits / no-wrap obligations pushed above.
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
        let (Some(src_const_id), Some(dst_const_id)) =
            (Self::const_obj_id_u32(&src_id), Self::const_obj_id_u32(&dst_id))
        else {
            return;
        };
        if src_const_id != dst_const_id {
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
        let disjoint = Expr::or(
            span32.eq(Expr::bitvec_const(0u64, 32)),
            Expr::or(src_end.bvule(dst_off), dst_end.bvule(src_off)),
        );
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

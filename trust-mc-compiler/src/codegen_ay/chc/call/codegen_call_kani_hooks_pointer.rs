// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer-query Kani hook handlers: `IsAllocated`, `PointerObject`, `PointerOffset`.
//!
//! Extracted from `codegen_call_kani_hooks.rs` for size management.
//! At `Ptr+` track level these hooks extract allocation metadata from the
//! composite 64-bit pointer representation; below `Ptr` they fall back to
//! nondeterministic (sound over-approximation).

use ay_bindings::Expr;
use tracing::warn;

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, bool_sort, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `KaniHook::IsAllocated`: query `obj_valid[obj_id]` at Ptr+ level.
    pub(in crate::codegen_ay::chc) fn hook_is_allocated(&mut self, dcx: &DispatchCallContext<'_>) {
        let bb_idx = dcx.bb_idx;
        let dest_local: usize = dcx.destination.local;
        // Part of #3768: graceful fallback instead of panic on unregistered locals
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_hook_is_allocated");
            if let Some(target) = dcx.target {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
            }
            return;
        };

        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
            let dest_var =
                Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());

            let is_alloc_expr = if self.track_level >= ChcTrackLevel::Ptr {
                if let Some(ptr_expr) = dcx.args.first().and_then(|ptr_op| {
                    self.translate_operand_with_modified(ptr_op, dcx.modified_locals)
                }) {
                    if let Some(expr) = self.is_allocated_expr_for_hook(&ptr_expr, dcx) {
                        expr
                    } else {
                        self.is_allocated_nondet_fallback()
                    }
                } else {
                    self.is_allocated_nondet_fallback()
                }
            } else {
                Expr::bool_const(true)
            };

            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                is_alloc_expr,
                &out_sort,
                dest_local,
                "codegen_call_kani_hook::IsAllocated",
            );
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            self.record_diverging_call_drop(dcx.func, Some(bb_idx), "kani_hook::IsAllocated", None);
        }
    }

    fn is_allocated_expr_for_hook(
        &mut self,
        ptr_expr: &Expr,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<Expr> {
        let (obj_id, _) = self.split_pointer(ptr_expr)?;
        let obj_valid = self.current_obj_valid_array();
        // Part of #3436: track that this block reads heap metadata.
        self.mark_heap_metadata_read();
        let base_valid = obj_valid.select(obj_id.clone());

        let Some(size_expr) = dcx
            .args
            .get(1)
            .and_then(|size_op| self.translate_operand_with_modified(size_op, dcx.modified_locals))
        else {
            return Some(base_valid);
        };

        let size_expr =
            coerce_bitvec_width_safe(size_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        size_expr.sort().bitvec_width()?;

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let size_is_zero = size_expr.clone().eq(zero);
        let checked_size = Expr::ite(size_is_zero.clone(), one.clone(), size_expr);
        let end_ptr = ptr_expr.clone().bvadd(checked_size).bvsub(one);
        let (end_obj_id, _) = self.split_pointer(&end_ptr)?;
        let same_object = obj_id.eq(end_obj_id);
        let range_ok = Expr::ite(size_is_zero, Expr::bool_const(true), same_object);
        Some(base_valid.and(range_ok))
    }

    fn is_allocated_nondet_fallback(&mut self) -> Expr {
        // Part of #3099: Reclassified to SOUND_APPROXIMATION —
        // nondeterministic bool explores both allocated/not-allocated paths.
        warn!(
            "IsAllocated: pointer arg translation failed at Ptr+ level, \
             falling back to nondeterministic (sound over-approximation)"
        );
        self.record_sound_fallback_reason("is_allocated_ptr_translation_failed");
        declare_pending_var(chc_fresh_name("__is_allocated_nondet"), bool_sort())
    }

    /// Handle `KaniHook::PointerObject`: extract allocation ID from pointer.
    ///
    /// Part of #3212: At Ptr+ level, `pointer_object(ptr)` extracts the high 32 bits
    /// (obj_id) from the 64-bit pointer via `split_pointer`. This makes
    /// `pointer_object` a deterministic function of its input, so
    /// `pointer_object(p) == pointer_object(p)` holds (enabling `same_allocation`
    /// reflexivity). Below Ptr level, falls back to nondeterministic.
    pub(in crate::codegen_ay::chc) fn hook_pointer_object(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let dest_local: usize = dcx.destination.local;
        // Part of #3768: graceful fallback instead of panic on unregistered locals
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_hook_pointer_object");
            if let Some(target) = dcx.target {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
            }
            return;
        };

        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
            let dest_var =
                Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());

            let result_expr = if self.track_level >= ChcTrackLevel::Ptr {
                if let Some((obj_id, _offset)) = dcx
                    .args
                    .first()
                    .and_then(|ptr_op| {
                        self.translate_operand_with_modified(ptr_op, dcx.modified_locals)
                    })
                    .and_then(|ptr_expr| self.split_pointer(&ptr_expr))
                {
                    obj_id
                } else {
                    warn!(
                        "PointerObject: pointer arg translation failed at Ptr+ level, \
                         falling back to nondeterministic (sound over-approximation)"
                    );
                    self.record_sound_fallback_reason("ptr_object_translation_failed");
                    declare_pending_var(chc_fresh_name("__ptr_obj_nondet"), out_sort.clone())
                }
            } else {
                // Part of #3447: Record that pointer object ID is unconstrained
                // at below-Ptr track level.
                self.record_sound_fallback_reason("ptr_object_below_ptr_level");
                declare_pending_var(chc_fresh_name("__ptr_obj_nondet"), out_sort.clone())
            };

            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                &out_sort,
                dest_local,
                "codegen_call_kani_hook::PointerObject",
            );
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "kani_hook::PointerObject",
                None,
            );
        }
    }

    /// Handle `KaniHook::PointerOffset`: extract byte offset from pointer.
    ///
    /// Part of #3212: At Ptr+ level, `pointer_offset(ptr)` extracts the low 32 bits
    /// (offset) from the 64-bit pointer via `split_pointer`. Below Ptr level,
    /// falls back to nondeterministic.
    pub(in crate::codegen_ay::chc) fn hook_pointer_offset(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let dest_local: usize = dcx.destination.local;
        // Part of #3768: graceful fallback instead of panic on unregistered locals
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_hook_pointer_offset");
            if let Some(target) = dcx.target {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
            }
            return;
        };

        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
            let dest_var =
                Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());

            let result_expr = if self.track_level >= ChcTrackLevel::Ptr {
                if let Some((_obj_id, offset)) = dcx
                    .args
                    .first()
                    .and_then(|ptr_op| {
                        self.translate_operand_with_modified(ptr_op, dcx.modified_locals)
                    })
                    .and_then(|ptr_expr| self.split_pointer(&ptr_expr))
                {
                    offset
                } else {
                    warn!(
                        "PointerOffset: pointer arg translation failed at Ptr+ level, \
                         falling back to nondeterministic (sound over-approximation)"
                    );
                    self.record_sound_fallback_reason("ptr_offset_translation_failed");
                    declare_pending_var(chc_fresh_name("__ptr_off_nondet"), out_sort.clone())
                }
            } else {
                // Part of #3447: Record that pointer offset is unconstrained
                // at below-Ptr track level.
                self.record_sound_fallback_reason("ptr_offset_below_ptr_level");
                declare_pending_var(chc_fresh_name("__ptr_off_nondet"), out_sort.clone())
            };

            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                &out_sort,
                dest_local,
                "codegen_call_kani_hook::PointerOffset",
            );
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "kani_hook::PointerOffset",
                None,
            );
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation-path extra stub handlers: HandleAllocError, UniqueNewUnchecked,
//! BoxIntoRawWithAllocator, AlignmentNew, AlignmentAsUsize, LayoutMaxSizeForAlign.
//! Part of #2408 S1: codegen_call_misc decomposition.

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_public::mir::Operand;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;
use super::super::stubs_option_helpers::OptionHelpers;
use super::CallMisc;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle allocation-path extra stubs (Part of #2196).
    ///
    /// - `HandleAllocError` -> diverging, no successor emitted
    /// - `RustNoAllocShimIsUnstable` -> no-op signal
    /// - `UniqueNewUnchecked` / `BoxIntoRawWithAllocator` -> pointer identity (dest = arg[0])
    /// - Others -> unconstrained destination
    pub(in crate::codegen_ay::chc) fn codegen_call_alloc_extra_impl(
        &mut self,
        bb_idx: usize,
        cx: &ChcCallContext<'_>,
    ) {
        debug!("alloc_extra_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        match cx.stub {
            StubKind::HandleAllocError => {
                // Diverging: allocation error handler should never be reached.
                // Do NOT emit successor rule (infeasible path).
                debug!("HandleAllocError in bb{} — no successor emitted", bb_idx);
            }
            StubKind::RustNoAllocShimIsUnstable => {
                // No-op: unstable shim signal, just emit goto.
                let new_output_args =
                    self.build_output_args(cx.modified_locals, &[cx.destination.local]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
            StubKind::UniqueNewUnchecked | StubKind::BoxIntoRawWithAllocator => {
                self.codegen_alloc_extra_identity(cx);
            }
            StubKind::AlignmentNew => {
                self.codegen_alloc_extra_alignment_new(cx);
            }
            StubKind::AlignmentAsUsize => {
                self.codegen_alloc_extra_alignment_as_usize(cx);
            }
            StubKind::LayoutMaxSizeForAlign => {
                self.codegen_alloc_extra_layout_max_size(cx);
            }
            StubKind::AllocatorAllocate
            | StubKind::GlobalAllocImpl
            | StubKind::VecFromRawPartsIn => {
                // Sound over-approximation: destination left nondet. record_fallback()
                // is NOT called because nondeterministic allocation results cannot
                // produce false proofs — only more behaviors (#2753, Part of #3123).
                let dest_local: usize = cx.destination.local;
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
            _other => {
                // Unexpected stub — translation failure (Part of #3123).
                tracing::warn!(
                    ?_other,
                    "codegen_call_alloc_extra: unexpected stub — update routing"
                );
                let dest_local: usize = cx.destination.local;
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                );
            }
        }
    }

    /// Pointer identity: destination = arg[0].
    /// Part of #1739: no-op type conversions that must preserve pointer identity.
    fn codegen_alloc_extra_identity(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;

        let ptr_expr = cx.args.first().and_then(|arg| {
            self.resolve_ref_operand(arg, cx.modified_locals)
                .or_else(|| self.translate_operand_with_modified(arg, cx.modified_locals))
        });

        if let Some(ptr) = ptr_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                ptr,
                dest_var.sort(),
                dest_local,
                "codegen_call_alloc_extra_identity",
            ) {
                let src_local = match cx.args.first() {
                    Some(Operand::Copy(place) | Operand::Move(place))
                        if place.projection.is_empty() =>
                    {
                        Some(place.local)
                    }
                    _ => None,
                };
                if let Some(src_local) = src_local {
                    if let Some(obj_id) = self.known_alloc_ids.get(&src_local).copied() {
                        self.known_alloc_ids.insert(dest_local, obj_id);
                        debug!(
                            dest_local,
                            src_local,
                            obj_id,
                            "alloc_extra_identity: preserved allocation identity"
                        );
                    } else {
                        self.known_alloc_ids.remove(&dest_local);
                    }
                }
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    [eq],
                );
                return;
            }
        }
        // Fallback: arg not translatable — translation failure (Part of #3123).
        debug!("{:?} identity fallback — arg not translatable", cx.stub);
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }

    /// Model Alignment::new(x) precisely for Layout::from_size_align.
    fn codegen_alloc_extra_alignment_new(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        let align_expr = cx.args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, cx.modified_locals).or_else(|| {
                Self::resolve_bare_local(
                    arg,
                    &self.state_var_mgr.state_vars,
                    &self.state_var_mgr.output_state_vars,
                    cx.modified_locals,
                    &self.state_var_mgr.local_to_state_idx,
                    &self.fn_name,
                )
            })
        });

        if let Some(raw_align) = align_expr {
            let width = raw_align.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
            let nonzero = self.nonzero_bv_check(raw_align.clone(), width);
            let power_of_two = self.power_of_two_bv_check(raw_align.clone(), width);

            if let (Some(nonzero), Some(power_of_two)) = (nonzero, power_of_two) {
                let valid_alignment = nonzero.and(power_of_two);

                // Part of #2323: Option<Alignment> is often flattened to
                // (is_some, payload) at CHC Reg level.
                if self.flatten.flattened_tuple_locals.contains(&dest_local) {
                    self.emit_alignment_new_flattened(cx, dest_local, valid_alignment, raw_align);
                    return;
                }

                if self.emit_alignment_new_option(cx, dest_local, valid_alignment, raw_align) {
                    return;
                }

                debug!("AlignmentNew fallback — option destination unsupported");
            } else {
                debug!("AlignmentNew fallback — unable to build alignment checks");
            }
        } else {
            debug!("AlignmentNew fallback — argument not translatable");
        }

        // AlignmentNew translation failed — dest unconstrained (Part of #3123).
        debug!("AlignmentNew fallback — destination unconstrained");
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }

    /// Emit flattened-tuple alignment result (is_some, payload).
    fn emit_alignment_new_flattened(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        valid_alignment: Expr,
        raw_align: Expr,
    ) {
        let mut extra_constraints: Vec<Expr> = Vec::new();
        self.constrain_flattened_fields_for_call(
            dest_local,
            &[Some(valid_alignment), Some(raw_align)],
            &mut extra_constraints,
        );
        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
    }

    /// Emit Option<Alignment> datatype result via Some/None ITE. Returns true if emitted.
    fn emit_alignment_new_option(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        valid_alignment: Expr,
        raw_align: Expr,
    ) -> bool {
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        if dest_var.sort().datatype_sort().is_none() {
            return false;
        }
        let some_expr = self.make_some_expr_for_option(raw_align, dest_var.sort());
        let none_expr = self.make_none_expr_for_option(dest_var.sort());
        let (Some(some_expr), Some(none_expr)) = (some_expr, none_expr) else {
            return false;
        };
        let result_expr = Expr::ite(valid_alignment, some_expr, none_expr);
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result_expr,
            dest_var.sort(),
            dest_local,
            "codegen_call_alloc_extra_alignment_new",
        ) else {
            return false;
        };
        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            [eq],
        );
        true
    }

    /// Preserve flow for Alignment::as_usize.
    fn codegen_alloc_extra_alignment_as_usize(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        let align_expr = cx.args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, cx.modified_locals).or_else(|| {
                Self::resolve_bare_local(
                    arg,
                    &self.state_var_mgr.state_vars,
                    &self.state_var_mgr.output_state_vars,
                    cx.modified_locals,
                    &self.state_var_mgr.local_to_state_idx,
                    &self.fn_name,
                )
            })
        });

        if let Some(align_expr) = align_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                align_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_alloc_extra_alignment_as_usize",
            ) {
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    [eq],
                );
                return;
            }
        }

        // AlignmentAsUsize translation failed — dest unconstrained (Part of #3123).
        debug!("AlignmentAsUsize fallback — argument not translatable");
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }

    /// Conservative upper bound used by Layout::from_size_align checks.
    fn codegen_alloc_extra_layout_max_size(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let max_size_expr = Expr::bitvec_const(u64::MAX, POINTER_WIDTH);
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                max_size_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_alloc_extra_layout_max_size",
            ) {
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    [eq],
                );
                return;
            }
        }

        // LayoutMaxSizeForAlign translation failed — dest unconstrained (Part of #3123).
        debug!("LayoutMaxSizeForAlign fallback — destination unconstrained");
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }
}

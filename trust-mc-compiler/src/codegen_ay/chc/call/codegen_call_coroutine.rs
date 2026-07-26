// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Coroutine body call dispatch for CHC codegen.
//!
//! Detects calls to coroutine body functions (the state-machine closures that
//! rustc generates for `|| { yield ... }` coroutines). Tries a precise
//! `CoroutineState` encoding first. If that fails, tries fn_inline as fallback.
//! If fn_inline also bails, falls back to sound nondeterministic
//! over-approximation.
//!
//! Part of #3807, #4181: coroutine yield/resume state machine encoding.

use ay_bindings::Expr;
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_fn_inline::CallDispatchFnInline;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_rules::CodegenRules;

#[path = "codegen_call_coroutine_elision.rs"]
pub(in crate::codegen_ay::chc) mod elision;
#[path = "codegen_call_coroutine_sequence.rs"]
mod sequence;
#[path = "codegen_call_coroutine_state.rs"]
mod state;
#[path = "codegen_call_coroutine_support.rs"]
pub(in crate::codegen_ay::chc) mod support;

use elision::{
    try_dispatch_elided_pin_box_coroutine_drop_glue_call, try_dispatch_unused_box_new_coroutine,
    try_dispatch_unused_box_pin_coroutine,
};
use sequence::SequencedCoroutineTransition;
use state::{
    CoroutineStateBranch, coerce_coroutine_result_to_sort, coroutine_state_complete_is_zst,
    coroutine_state_complete_is_zst_for_local, coroutine_state_yield_is_zst,
    coroutine_state_yield_is_zst_for_local, try_construct_coroutine_state_expr,
    try_construct_coroutine_state_variant_expr,
};
use support::{has_coroutine_arg, has_simple_coroutine_yield_variant, returns_coroutine_state};

/// Extension trait for coroutine body call dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchCoroutine {
    /// Attempt to dispatch coroutine-related calls that must beat misc/stub
    /// dispatch (notably BoxNew allocation stubs).
    fn try_dispatch_call_coroutine_pre_misc(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Attempt to dispatch a coroutine body call. Returns `true` if handled.
    fn try_dispatch_call_coroutine(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchCoroutine for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_coroutine_pre_misc(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        try_dispatch_elided_pin_box_coroutine_drop_glue_call(self, dcx)
            || try_dispatch_unused_box_pin_coroutine(self, dcx)
            || try_dispatch_unused_box_new_coroutine(self, dcx)
    }

    fn try_dispatch_call_coroutine(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        if try_dispatch_unused_box_pin_coroutine(self, dcx) {
            return true;
        }

        let has_coro_arg = has_coroutine_arg(dcx.args, self);
        let returns_coro = returns_coroutine_state(dcx.func, self);
        if !has_coro_arg || !returns_coro {
            return false;
        }
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "coroutine_body", None);
            return true;
        };
        let live_receiver_state_idx = self.coroutine_live_receiver_state_idx(dcx, *target);

        let dest_local: usize = dcx.destination.local;
        let yield_is_zst = coroutine_state_yield_is_zst_for_local(dest_local, self)
            .or_else(|| coroutine_state_yield_is_zst(dcx.func, self))
            .unwrap_or(false);
        let complete_is_zst = coroutine_state_complete_is_zst_for_local(dest_local, self)
            .or_else(|| coroutine_state_complete_is_zst(dcx.func, self))
            .unwrap_or(false);
        let allow_complete_branch = !has_simple_coroutine_yield_variant(dcx.func, self);

        if !dcx.destination.projection.is_empty() {
            return self.handle_projected_destination(
                dcx,
                dest_local,
                *target,
                yield_is_zst,
                complete_is_zst,
                allow_complete_branch,
                live_receiver_state_idx,
            );
        }

        if self.flatten.enum_bv_layouts.contains_key(&dest_local) {
            return self.try_emit_flattened_coroutine_state(
                dcx,
                dest_local,
                *target,
                yield_is_zst,
                allow_complete_branch,
                live_receiver_state_idx,
            );
        }

        self.handle_direct_destination(
            dcx,
            dest_local,
            *target,
            yield_is_zst,
            complete_is_zst,
            allow_complete_branch,
            live_receiver_state_idx,
        )
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn handle_direct_destination(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        target: usize,
        yield_is_zst: bool,
        complete_is_zst: bool,
        allow_complete_branch: bool,
        live_receiver_state_idx: Option<usize>,
    ) -> bool {
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return self.emit_coroutine_sound_fallback(dcx, dest_local, target, None);
        };
        let dest_sort = dest_var.sort().clone();
        let sequenced_transition = live_receiver_state_idx
            .filter(|_| allow_complete_branch)
            .and_then(|idx| self.try_build_sequenced_coroutine_transition(dcx, idx));
        let receiver_eq = sequenced_transition
            .as_ref()
            .map(|transition| transition.receiver_eq.clone())
            .or_else(|| {
                live_receiver_state_idx
                    .and_then(|idx| self.try_build_simple_coroutine_receiver_writeback_eq(dcx, idx))
            });

        if let Some(receiver_state_idx) = live_receiver_state_idx
            && receiver_eq.is_none()
        {
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                receiver_state_idx,
                "CHC: coroutine mixed yield+complete → nondeterministic receiver+dest"
            );
            self.mark_state_var_modified(receiver_state_idx);
            let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule(dcx.from_app, target, &output_args, dcx.stmt_constraints);
            return true;
        }

        let result_expr = match sequenced_transition.as_ref() {
            Some(transition) => match (
                try_construct_coroutine_state_variant_expr(
                    &dest_sort,
                    CoroutineStateBranch::Yielded,
                    yield_is_zst,
                    complete_is_zst,
                ),
                try_construct_coroutine_state_variant_expr(
                    &dest_sort,
                    CoroutineStateBranch::Complete,
                    yield_is_zst,
                    complete_is_zst,
                ),
                try_construct_coroutine_state_expr(
                    &dest_sort,
                    yield_is_zst,
                    complete_is_zst,
                    allow_complete_branch,
                ),
            ) {
                (Some(yielded_expr), Some(complete_expr), Some(fallback_expr)) => Some(Expr::ite(
                    transition.known_state.clone(),
                    Expr::ite(transition.yielded_now.clone(), yielded_expr, complete_expr),
                    fallback_expr,
                )),
                _ => None,
            },
            None => try_construct_coroutine_state_expr(
                &dest_sort,
                yield_is_zst,
                complete_is_zst,
                allow_complete_branch,
            ),
        };
        if let Some(result_expr) = result_expr
            && let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                &dest_sort,
                dest_local,
                "coroutine_body_state",
            )
        {
            if let Some(receiver_state_idx) = live_receiver_state_idx {
                self.mark_state_var_modified(receiver_state_idx);
            }
            let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &output_args,
                dcx.stmt_constraints,
                receiver_eq.into_iter().chain(std::iter::once(eq)),
            );
            if allow_complete_branch {
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local,
                    sequenced = sequenced_transition.is_some(),
                    "CHC: coroutine body call → yield-or-complete encoding (Datatype)"
                );
            } else {
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local, "CHC: coroutine body call → precise Yielded encoding (Datatype)"
                );
            }
            return true;
        }

        // Part of #4181: precise CoroutineState encoding failed. Try fn_inline
        // as fallback before sound over-approximation. fn_inline can walk the
        // coroutine state machine if the inline walker handles the Pin deref
        // chain (#3807 Phase 1+2).
        if self.try_dispatch_call_fn_inline(dcx) {
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                "CHC: coroutine body call → fn_inline fallback (precise state unavailable)"
            );
            return true;
        }

        debug!(bb_idx = dcx.bb_idx, dest_local, "CHC: coroutine body call → sound fallback");
        self.emit_coroutine_sound_fallback(dcx, dest_local, target, None)
    }

    fn emit_coroutine_sound_fallback(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        target: usize,
        receiver_state_idx: Option<usize>,
    ) -> bool {
        if let Some(state_idx) = receiver_state_idx {
            self.mark_state_var_modified(state_idx);
        }
        emit_sound_fallback_goto(
            self,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        true
    }

    /// Emit a sound yield-or-complete over-approximation for a BV-flattened
    /// CoroutineState destination.
    ///
    /// `build_output_args` already materializes fresh output vars for the
    /// flattened tag/payload slots. Keep the receiver write-back constraint when
    /// available, but leave the destination itself unconstrained so the solver
    /// can explore both `Yielded(..)` and `Complete(..)` outcomes.
    fn try_emit_flattened_coroutine_state(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        target: usize,
        yield_is_zst: bool,
        allow_complete_branch: bool,
        live_receiver_state_idx: Option<usize>,
    ) -> bool {
        let sequenced_transition = live_receiver_state_idx
            .filter(|_| allow_complete_branch)
            .and_then(|idx| self.try_build_sequenced_coroutine_transition(dcx, idx));
        let receiver_eq = sequenced_transition
            .as_ref()
            .map(|transition| transition.receiver_eq.clone())
            .or_else(|| {
                live_receiver_state_idx
                    .and_then(|idx| self.try_build_simple_coroutine_receiver_writeback_eq(dcx, idx))
            });
        if let Some(receiver_state_idx) = live_receiver_state_idx
            && receiver_eq.is_none()
        {
            // Part of #4160: mixed yield+complete coroutines can't build a
            // specific discriminant writeback. Instead of the full
            // call_dispatch_fallback (which causes ERROR verdicts), emit a
            // clean goto with both receiver and destination nondeterministic.
            // This is sound: the solver explores all possible receiver states
            // and all possible CoroutineState values.
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                receiver_state_idx,
                "CHC: coroutine mixed yield+complete → nondeterministic receiver+dest"
            );
            self.mark_state_var_modified(receiver_state_idx);
            let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule(dcx.from_app, target, &output_args, dcx.stmt_constraints);
            return true;
        }
        if self.try_state_idx_for_local(dest_local).is_none() {
            debug!(dest_local, "CHC: coroutine dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_coroutine_dest");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
            return true;
        }

        if let Some(SequencedCoroutineTransition { yielded_now, .. }) = sequenced_transition {
            let layout = match self.flatten.enum_bv_layouts.get(&dest_local) {
                Some(layout) => layout.clone(),
                None => {
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                    return true;
                }
            };
            let yielded_tag = if layout.num_constructors == 2 {
                Expr::bool_const(false)
            } else {
                Expr::bitvec_const(layout.discriminants[0], layout.tag_bits)
            };
            let complete_tag = if layout.num_constructors == 2 {
                Expr::bool_const(true)
            } else {
                Expr::bitvec_const(layout.discriminants[1], layout.tag_bits)
            };
            let base_vec_idx = self.try_state_idx_for_local(dest_local).expect("checked above");
            let Some((tag_out_name, tag_out_sort)) =
                self.state_var_mgr.output_state_vars.get(base_vec_idx).cloned()
            else {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
                return true;
            };
            if let Some(receiver_state_idx) = live_receiver_state_idx {
                self.mark_state_var_modified(receiver_state_idx);
            }
            let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let tag_out_var = Expr::var(&*tag_out_name, tag_out_sort);
            let tag_eq = tag_out_var.eq(Expr::ite(yielded_now, yielded_tag, complete_tag));
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &output_args,
                dcx.stmt_constraints,
                std::iter::once(tag_eq).chain(receiver_eq),
            );
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local, "CHC: coroutine body call → sequenced yield-or-complete (BV-flattened)"
            );
            return true;
        }

        if let Some(receiver_state_idx) = live_receiver_state_idx {
            self.mark_state_var_modified(receiver_state_idx);
        }
        let output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        if !allow_complete_branch {
            let layout = match self.flatten.enum_bv_layouts.get(&dest_local) {
                Some(layout) => layout.clone(),
                None => {
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                    return true;
                }
            };
            let yielded_ctor_idx = 0usize;
            let tag_expr = if layout.num_constructors == 2 {
                Expr::bool_const(yielded_ctor_idx != 0)
            } else {
                Expr::bitvec_const(layout.discriminants[yielded_ctor_idx], layout.tag_bits)
            };

            let base_vec_idx = self.try_state_idx_for_local(dest_local).expect("checked above");
            let Some((tag_out_name, tag_out_sort)) =
                self.state_var_mgr.output_state_vars.get(base_vec_idx).cloned()
            else {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
                return true;
            };
            let tag_out_var = Expr::var(&*tag_out_name, tag_out_sort);
            let tag_eq = tag_out_var.eq(tag_expr);

            let mut payload_eqs = Vec::new();
            for slot_idx in 0..layout.max_payload_slots {
                let out_idx = base_vec_idx + 1 + slot_idx;
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(out_idx).cloned()
                else {
                    break;
                };
                let is_yielded_slot = layout
                    .ctor_field_slot
                    .get(yielded_ctor_idx)
                    .map_or(false, |slots| slots.contains(&slot_idx));
                if is_yielded_slot {
                    let payload = if yield_is_zst && out_sort.is_bool() {
                        Expr::bool_const(true)
                    } else {
                        declare_pending_var(
                            chc_fresh_name("__coro_yield_payload"),
                            out_sort.clone(),
                        )
                    };
                    let out_var = Expr::var(&*out_name, out_sort);
                    payload_eqs.push(out_var.eq(payload));
                }
            }

            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &output_args,
                dcx.stmt_constraints,
                std::iter::once(tag_eq).chain(payload_eqs).chain(receiver_eq),
            );
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                num_payload = layout.max_payload_slots,
                "CHC: coroutine body call → precise Yielded (BV-flattened)"
            );
            return true;
        }

        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &output_args,
            dcx.stmt_constraints,
            receiver_eq,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            dest_local, "CHC: coroutine body call → yield-or-complete over-approx (BV-flattened)"
        );
        true
    }
}

// Test-only wrappers — in codegen_call_coroutine_test_wrappers.rs
#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[path = "codegen_call_coroutine_test_wrappers.rs"]
pub(in crate::codegen_ay::chc) mod test_wrappers;

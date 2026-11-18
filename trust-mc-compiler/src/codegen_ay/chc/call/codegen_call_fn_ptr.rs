// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Function pointer call resolution for CHC codegen.
//!
//! Handles `TerminatorKind::Call` where the callee operand has type
//! `RigidTy::FnPtr(..)` — indirect calls through function pointers.
//!
//! Resolution strategy (design 3 of `docs/chc-hole-fix-designs-2026-09-24.md`,
//! `fn_ptr_targets.rs`): the pointer's value decides. A minted id names one
//! function exactly; an if-then-else of minted ids, or a local whose every
//! definition is a reification or a copy of such a local, names a complete
//! set, dispatched under `pointer == id` with the obligation "invalid
//! function pointer" as its default arm. Any other pointer takes the
//! fail-closed unhandled-call fallback. (This route used to walk the first
//! reification in the pointer's copy chain, or the first in the whole body,
//! unconditionally.)
//!
//! Part of #1739: UNKNOWN→PROOF smoke suite recovery.

use ay_bindings::Expr;
use rustc_public::mir::{CastKind, Operand, PointerCoercion, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::{MAX_INLINE_EFFECTIVE_BLOCKS, count_effective_blocks};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::inline_body::{InlineReturn, translate_inline_body};
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};

/// Extension trait for function pointer call resolution on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchFnPtr {
    /// Attempt to resolve and inline an indirect function pointer call.
    /// Returns `true` if handled.
    fn try_dispatch_call_fn_ptr(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchFnPtr for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_fn_ptr(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };

        // Only handle FnPtr calls.
        let func_ty = match dcx.func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        if !matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) {
            return false;
        }

        // A callee reached through a function pointer is WALKED, and the
        // walker receives a `&T` argument as its referent's VALUE
        // (`resolve_ref_operand` below) with no Cell store lane and no
        // write-back through a shared reference. A write the callee makes
        // through interior mutability was dropped with no record: `let f:
        // fn(&Cell<u8>) = set200; f(&c); assert!(c.get() < 100)` verified
        // SUCCESSFUL clean and its `== 200` twin FAILED Genuine (review of
        // fix/chc-cell-set-write, 2026-09-26). Such a call havocs everything
        // its arguments can write instead, and fails closed.
        if dcx.args.iter().any(|arg| {
            arg.ty(self.body.locals())
                .is_ok_and(|ty| self.ty_points_to_interior_mut(self.resolve_body_ty(ty), 4))
        }) {
            debug!(bb_idx = dcx.bb_idx, "fn_ptr: interior-mutable argument; havoc, not walked");
            self.emit_interior_mut_call_havoc(
                dcx.args,
                dcx.destination,
                *target,
                dcx.from_app,
                dcx.stmt_constraints,
                dcx.modified_locals,
                "fn_ptr_interior_mut_arg_havoc",
            );
            return true;
        }

        // Design 3 (fn_ptr_targets.rs): walk only a COMPLETE candidate set.
        // The pointer is one minted id, an if-then-else of minted ids, or a
        // closed local (every definition a reification or a local copy). Any
        // other pointer (a static, a const, a struct field, a call result)
        // takes the fail-closed unhandled-call fallback. This route used to
        // walk the FIRST reification in the pointer's copy chain, or failing
        // that the first anywhere in the body, unconditionally: a symbolic
        // choice between `add_safe` and `add_ub` verified the `add_ub` overflow
        // SUCCESSFUL clean (walker_fn_ptr_target_dual.rs::bug_samename_direct_symbolic).
        let pointer = self.translate_operand_with_modified(dcx.func, dcx.modified_locals);
        let candidates = self.fn_ptr_call_candidates(pointer.as_ref(), Some(func_ty));
        if !candidates.complete || candidates.targets.is_empty() {
            debug!(
                bb_idx = dcx.bb_idx,
                known = candidates.targets.len(),
                "fn_ptr: candidate set not complete; unhandled-call fallback"
            );
            return false;
        }
        if candidates.targets.iter().any(|(_, target)| {
            matches!(&target.kind, crate::codegen_ay::fn_ptr_identity::FnPtrTargetKind::Item { instance, .. }
                if crate::codegen_ay::native_string_unmodeled_operation_instance(self.tcx, *instance, true))
        }) {
            self.record_sound_fallback_reason("native_string_unmodeled_operation");
            return false;
        }
        let mut bodies = Vec::with_capacity(candidates.targets.len());
        for (id, fn_target) in &candidates.targets {
            let Some(body) = fn_target.target_body() else {
                debug!(target = %fn_target.label(), "fn_ptr: candidate has no body");
                return false;
            };
            // Complexity gate: only inline small bodies.
            if count_effective_blocks(&body) > MAX_INLINE_EFFECTIVE_BLOCKS {
                debug!(target = %fn_target.label(), "fn_ptr: candidate over the inline budget");
                return false;
            }
            bodies.push((*id, body, fn_target.is_closure()));
        }

        // Translate arguments using the same operand resolution as fn_inline.
        let params: Vec<Expr> = dcx
            .args
            .iter()
            .filter_map(|arg| {
                if let Some(expr) = self.resolve_ref_operand(arg, dcx.modified_locals) {
                    return Some(expr);
                }
                self.translate_operand_with_modified(arg, dcx.modified_locals)
            })
            .collect();
        if params.len() != dcx.args.len() {
            return false;
        }

        // Part of #4185: Snapshot heap state before speculative inline walks.
        let heap_snapshot = self.heap_state.snapshot_transient_rule_state();
        // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
        let modified_snapshot = self.encode.modified_state_indices.clone();

        if candidates.exact {
            let (_, body, is_closure) = bodies.pop().expect("one exact candidate");
            // Part of #3608: Mark type arrays read by the inline field map.
            self.mark_inline_field_reads(&body, &params, dcx.bb_idx);
            let (result, inline_address_constraints) =
                self.inline_fn_ptr_body(&body, &params, is_closure, dcx.bb_idx);
            let Some(inline_result) = result else {
                // Part of #4185: Restore heap state after failed inline walk.
                self.heap_state.restore_transient_rule_state(&heap_snapshot);
                self.encode.modified_state_indices = modified_snapshot;
                return false;
            };
            debug!(bb_idx = dcx.bb_idx, "fn_ptr: exact target inlined (#1739)");
            self.emit_fn_ptr_result(dcx, *target, inline_result, &inline_address_constraints);
            return true;
        }

        let Some(pointer) = pointer
            .filter(|p| p.sort().bitvec_width() == Some(crate::codegen_ay::types::POINTER_WIDTH))
        else {
            return false;
        };
        let multi = bodies.len() > 1;
        let mut walked: Vec<(u64, InlineReturn)> = Vec::new();
        let mut address_constraints: Vec<Expr> = Vec::new();
        // Phase 0 (inline_walk_guard.rs): a write mark per candidate. One mark
        // over the whole loop exists so a candidate cannot read what an
        // earlier one wrote; every such channel is a memory effect, and an arm
        // with one declines the dispatch below, so each candidate starts from
        // the host's state. A single mark made the second of two targets
        // reading `*a` after its own write look like a read after the first
        // target's write (walker_dyn_deref_write_dual.rs
        // `bug_add_after_write_fnptr` lost its Genuine certificate).
        let mut all_walked = true;
        for (id, body, is_closure) in &bodies {
            let effects_before = self.heap_state.effect_mark();
            let checks_before = self.heap_state.pending_checks.len();
            self.mark_inline_field_reads(body, &params, dcx.bb_idx);
            let (result, constraints) = self.with_inline_walk_write_mark(|ctx| {
                ctx.inline_fn_ptr_body(body, &params, *is_closure, dcx.bb_idx)
            });
            let Some(result) = result else {
                all_walked = false;
                break;
            };
            // A memory effect made inside one arm is applied by the host
            // unguarded, on every path: two arms storing different values to
            // one `static mut` made the transition unsatisfiable and the
            // harness VACUOUS. Such a dispatch fails closed whatever happens
            // (`walker_store_in_branch_arm`), so decline it and leave the call
            // to the unhandled-call fallback.
            if multi && self.heap_state.effect_mark() > effects_before {
                self.note_inline_branch_arm_effects(effects_before);
                all_walked = false;
                break;
            }
            address_constraints.extend(constraints);
            super::codegen_call_virtual_inline::guard_dispatch_arm_pending_checks(
                self,
                checks_before,
                &pointer,
                *id,
            );
            walked.push((*id, result));
        }
        if !all_walked {
            // A candidate that cannot be walked could be the one called.
            self.heap_state.restore_transient_rule_state(&heap_snapshot);
            self.encode.modified_state_indices = modified_snapshot;
            debug!(
                bb_idx = dcx.bb_idx,
                "fn_ptr: a candidate was not walked; unhandled-call fallback"
            );
            return false;
        }
        let default = self.fn_ptr_obligation_default(&candidates);
        let merged = super::codegen_call_virtual_inline::merge_guarded_dispatch_results(
            self, walked, &pointer, default,
        );
        debug!(bb_idx = dcx.bb_idx, "fn_ptr: complete candidate set merged under pointer guards");
        self.emit_fn_ptr_result(dcx, *target, merged, &address_constraints);
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Inline a resolved fn-ptr body (closure or plain function).
    fn inline_fn_ptr_body(
        &mut self,
        body: &rustc_public::mir::Body,
        params: &[Expr],
        is_closure: bool,
        bb_idx: usize,
    ) -> (Option<InlineReturn>, Vec<Expr>) {
        if is_closure {
            let no_captures: Vec<Expr> = Vec::new();
            let (address_hints, address_constraints) =
                self.build_inline_zst_param_address_hints(body, bb_idx);
            let saved_inline_hints = self.inline_local_address_hints.take();
            if !address_hints.is_empty() {
                let body_key = &raw const *body as usize;
                self.inline_local_address_hints = Some((body_key, address_hints));
            }
            // Value-only semantics for the vtable, but PRESERVE the
            // assert-guard side-channel from the closure walk, and the
            // closure's writes through its reference arguments, re-keyed to
            // this call's arguments. Dropping them lost the write for the
            // caller with no reason recorded (review finding M3,
            // walker_referent_write_dual.rs::bug_fnptr_closure_write).
            let result = super::inline_body::translate_closure_inline_result(
                self,
                body,
                params,
                &no_captures,
                bb_idx,
                0,
            )
            .map(|full| {
                let mut value_only = InlineReturn::value_only(full.value);
                value_only.deferred_checks = full.deferred_checks;
                value_only.alias_updates =
                    super::inline_walk_guard::rekey_closure_alias_updates_for_caller(
                        self,
                        full.alias_updates,
                    );
                value_only
            });
            self.inline_local_address_hints = saved_inline_hints;
            (result, address_constraints)
        } else {
            let caller_vtable_ids = std::collections::HashMap::new();
            (
                translate_inline_body(self, body, params, bb_idx, &caller_vtable_ids, None, 0),
                Vec::new(),
            )
        }
    }

    /// Emit a transition rule for a resolved function pointer call result.
    fn emit_fn_ptr_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        inline_result: InlineReturn,
        inline_address_constraints: &[Expr],
    ) {
        let dest_local: usize = dcx.destination.local;
        let InlineReturn { value: result_expr, vtable, alias_updates, deferred_checks, .. } =
            inline_result;
        // Assert-guard SIDE-CHANNEL host emission (see emit_deferred_inline_check_errors).
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let empty_pre_resolved = std::collections::BTreeMap::new();
        let (result_expr, mut extra_constraints) = self.take_inline_result_guards(dcx, result_expr);
        extra_constraints.extend_from_slice(inline_address_constraints);
        let prepared = prepare_inline_result_epilogue(
            self,
            InlineResultEpilogueSpec {
                dcx,
                target,
                dest_local,
                result_expr,
                inline_vtable: vtable,
                fallback_vtable: None,
                alias_updates: &alias_updates,
                pre_resolved_args: &empty_pre_resolved,
                eq_reason: "codegen_call_fn_ptr",
                alias_reason: "fn_ptr_alias_update",
                extra_constraints,
                extra_dests: Vec::new(),
                drain_pending_updates: false,
                drain_pending_checks: false,
            },
        );
        if self.operands_have_single_assign_sources(dcx.args) {
            self.cache_single_assign_scalar_expr(dest_local, &prepared.result_expr, true);
        }

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            // Sound over-approximation: destination unresolved, leave unconstrained.
            // Previous `bool_const(false)` killed the transition (dead rule in CHC).
            let effective_stmts = prepared.effective_stmts().to_vec();
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &prepared.extra_dests);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                &effective_stmts,
                prepared.extra_constraints,
            );
            self.record_sound_fallback_reason("fn_ptr_dest_unresolved");
        }
    }

    pub(in crate::codegen_ay::chc) fn build_inline_zst_param_address_hints(
        &self,
        body: &rustc_public::mir::Body,
        bb_idx: usize,
    ) -> (std::collections::HashMap<usize, Expr>, Vec<Expr>) {
        let mut address_taken_zst_params = std::collections::BTreeSet::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) if place.projection.is_empty() && place.local >= 2 => {
                        let Some(local_decl) = body.locals().get(place.local) else { continue };
                        let local_ty = self.resolve_body_ty(local_decl.ty);
                        if self.get_type_size(local_ty) == Some(0) {
                            address_taken_zst_params.insert(place.local);
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut hints = std::collections::HashMap::new();
        let pointer_width = crate::codegen_ay::types::POINTER_WIDTH;

        for (ordinal, local) in address_taken_zst_params.into_iter().enumerate() {
            // The address is synthetic and scoped to this inline walk. Use a
            // concrete non-zero/distinct value instead of fresh BV arithmetic:
            // AY's CHC engine currently cannot prove `(fresh & mask) | tag != 0`
            // in HORN mode, which turns provable ZST address checks into CTREX.
            let addr = Expr::bitvec_const(
                (((bb_idx as u128) + 1) << 16) | ((local as u128) << 4) | ((ordinal as u128) + 1),
                pointer_width,
            );
            hints.insert(local, addr);
        }

        (hints, Vec::new())
    }

    /// The LINK SYMBOL of a FOREIGN item reified into this call's function
    /// pointer.
    ///
    /// `Some(takes_int)` coerces a foreign `extern "C"` item to a fn pointer,
    /// and calling through it is still a call to that C function — but
    /// `Instance::body()` is `None` for a foreign item, so the inline path
    /// above declines and the call used to fall through to the unconstrained
    /// fallback. `ForeignItems/extern_fn_ptr.rs` asserts that the indirect and
    /// the direct call agree, which is unprovable while one of them is
    /// unconstrained.
    ///
    /// UNIQUENESS is the soundness condition. A function pointer that could
    /// designate more than one function must not be resolved to one of them —
    /// that is a mis-translation, not an approximation. So the local-value
    /// chain is tried first, and the whole-body fallback is accepted only when
    /// the body contains EXACTLY ONE fn-pointer coercion of any kind and it
    /// names a foreign item; every fn-pointer value in such a body comes from
    /// that single coercion, or the call is UB.
    pub(in crate::codegen_ay::chc) fn fn_ptr_foreign_link_symbol(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<String> {
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        if !matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) {
            return None;
        }

        if let Operand::Copy(p) | Operand::Move(p) = dcx.func
            && p.projection.is_empty()
            && let Some(symbol) = self.chain_reified_foreign_symbol(p.local)
        {
            return Some(symbol);
        }

        // Whole-body fallback, under the uniqueness condition.
        let mut coercions = 0usize;
        let mut foreign_symbol = None;
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
                let Rvalue::Cast(
                    CastKind::PointerCoercion(
                        PointerCoercion::ReifyFnPointer { .. }
                        | PointerCoercion::ClosureFnPointer(_),
                    ),
                    operand,
                    _,
                ) = rvalue
                else {
                    continue;
                };
                coercions += 1;
                foreign_symbol = self.reified_foreign_symbol(operand);
            }
        }
        (coercions == 1).then_some(foreign_symbol).flatten()
    }

    /// Walk the copy/move chain backwards from `fn_ptr_local` and return the
    /// foreign link symbol reified into it, when exactly one coercion feeds it.
    fn chain_reified_foreign_symbol(&self, fn_ptr_local: usize) -> Option<String> {
        let mut target_locals = std::collections::HashSet::new();
        target_locals.insert(fn_ptr_local);
        for _ in 0..5 {
            let mut new_locals = Vec::new();
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                    if !target_locals.contains(&place.local) {
                        continue;
                    }
                    if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue
                        && src.projection.is_empty()
                    {
                        new_locals.push(src.local);
                    }
                }
            }
            if new_locals.is_empty() {
                break;
            }
            target_locals.extend(new_locals);
        }

        let mut coercions = 0usize;
        let mut symbol = None;
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                if !target_locals.contains(&place.local) {
                    continue;
                }
                let Rvalue::Cast(
                    CastKind::PointerCoercion(
                        PointerCoercion::ReifyFnPointer { .. }
                        | PointerCoercion::ClosureFnPointer(_),
                    ),
                    operand,
                    _,
                ) = rvalue
                else {
                    continue;
                };
                coercions += 1;
                symbol = self.reified_foreign_symbol(operand);
            }
        }
        (coercions == 1).then_some(symbol).flatten()
    }

    /// The foreign link symbol of a coerced operand, or `None` when the
    /// operand is not a direct reference to a foreign item.
    fn reified_foreign_symbol(&self, operand: &Operand) -> Option<String> {
        let ty = operand.ty(self.body.locals()).ok()?;
        crate::codegen_ay::foreign_defs::foreign_link_symbol(self.tcx, ty)
    }
}

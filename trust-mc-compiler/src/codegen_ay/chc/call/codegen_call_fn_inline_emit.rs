// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Inline call result emission and fat-pointer widening for CHC codegen.
//!
//! Contains the shared `emit_translated_inline_call_result` epilogue used by
//! fn_inline, closure, virtual, and fn_ptr dispatch paths, along with moved-arg
//! invalidation, assert-guard error emission, and the `widen_inline_result_for_fat_pointer`
//! helper. Extracted from `codegen_call_fn_inline.rs` for module size compliance (#4130).

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::RelationApp;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::inline_body::{
    DeferredInlineCheck, extract_inline_assert_guard, extract_inline_assume_guard,
    strip_inline_assert_fallback, strip_inline_assume_pruned,
};
use super::inline_result_shared::{
    InlineResultEpilogueSpec, emit_prepared_inline_result, prepare_inline_result_epilogue,
};
use super::inline_shared::check_is_trivially_valid;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn emit_translated_inline_call_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        result_expr: Expr,
        inline_vtable: Option<Expr>,
        alias_updates: BTreeMap<usize, Expr>,
        deferred_checks: Vec<DeferredInlineCheck>,
        pre_resolved_args: &BTreeMap<usize, usize>,
        caller_vtable_ids: &HashMap<usize, Expr>,
        callee_path: Option<&str>,
        eq_reason: &'static str,
        alias_reason: &'static str,
    ) -> bool {
        // Assert-guard SIDE-CHANNEL: emit one real per-property error rule per
        // accumulated inline check, regardless of destination shape.
        self.emit_deferred_inline_check_errors(dcx, deferred_checks);
        let inline_assert_guard = extract_inline_assert_guard(&result_expr);
        let inline_assume_guard = extract_inline_assume_guard(&result_expr);
        let result_expr = strip_inline_assert_fallback(&result_expr).unwrap_or(result_expr);
        let result_expr = strip_inline_assume_pruned(&result_expr).unwrap_or(result_expr);
        let dest_local: usize = dcx.destination.local;
        // Part of #4014: When the inline result is a BV64 data pointer and the
        // destination state variable is BV128 (fat pointer: data + vtable), widen
        // the result by concatenating the vtable. Without this, BV64 cannot be
        // written to the BV128 slot and the destination stays unconstrained,
        // letting the solver pick unaligned addresses for kani_mem checks.
        let result_expr =
            widen_inline_result_for_fat_pointer(self, dest_local, result_expr, &inline_vtable);
        let fallback_vtable = inline_call_preserves_receiver_vtable(callee_path)
            .then(|| caller_vtable_ids.get(&1).cloned())
            .flatten();
        let mut extra_dests = Vec::new();
        let mut extra_constraints = self.emit_inline_assert_guard_error(dcx, inline_assert_guard);
        // An assume guard the host's dominating argument bounds already imply
        // cuts nothing (`host_bound_discharge.rs`).
        let inline_assume_guard =
            super::codegen_call_virtual_inline::host_bound_discharge::drop_host_discharged_assume_guard(
                self,
                dcx.bb_idx,
                dcx.modified_locals,
                inline_assume_guard,
            );
        if let Some(inline_assume_guard) = inline_assume_guard {
            extra_constraints.push(inline_assume_guard);
        }
        extra_constraints.append(&mut self.invalidate_moved_fn_inline_args(
            dcx,
            dest_local,
            &mut extra_dests,
        ));
        let prepared = prepare_inline_result_epilogue(
            self,
            InlineResultEpilogueSpec {
                dcx,
                target,
                dest_local,
                result_expr,
                inline_vtable,
                fallback_vtable,
                alias_updates: &alias_updates,
                pre_resolved_args,
                eq_reason,
                alias_reason,
                extra_constraints,
                extra_dests,
                drain_pending_updates: true,
                drain_pending_checks: true,
            },
        );

        if let Err(prepared) = emit_prepared_inline_result(self, prepared) {
            debug!(
                bb_idx = dcx.bb_idx,
                dest_local,
                fn_name = %self.fn_name,
                "fn_inline: untracked destination, sound over-approx"
            );
            self.record_sound_fallback_reason("fn_inline_dest_untracked");
            let effective_stmts = prepared.effective_stmts().to_vec();
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                &effective_stmts,
                prepared.extra_constraints,
            );
        }

        true
    }

    pub(in crate::codegen_ay::chc) fn invalidate_moved_fn_inline_args(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        extra_dests: &mut Vec<usize>,
    ) -> Vec<Expr> {
        let mut constraints = Vec::new();
        for arg in dcx.args {
            let Operand::Move(place) = arg else {
                continue;
            };
            if !place.projection.is_empty() || place.local == dest_local {
                continue;
            }

            let local_idx = place.local;
            if !extra_dests.contains(&local_idx) {
                extra_dests.push(local_idx);
            }
            self.known_alloc_ids.remove(&local_idx);
            self.clear_known_vtable_discriminant(local_idx);

            // A flattened local has one slot per leaf, and `resolve_destination`
            // names only the first: a default of THAT slot's sort, handed to the
            // whole-local builder, bound slot 0 and left the others free (a
            // value that does not tile the local, now refused fail-closed by
            // the builder). Every slot's dead placeholder is its own sort's
            // default.
            if self.flatten.flattened_tuple_locals.contains(&local_idx) {
                constraints.extend(self.moved_flattened_local_placeholders(local_idx));
                continue;
            }

            let Some((_, dest_var)) = self.resolve_destination(local_idx) else {
                continue;
            };
            let Some(default_expr) = ChcCtx::sort_default_expr(dest_var.sort()) else {
                continue;
            };
            // A moved-out local is never read before it is assigned again, so
            // its placeholder value is dead. For a wide slice slot, state the
            // same all-zero bits as an explicit (null, 0) slice, so the design 4
            // write boundary does not book a fresh length for a dead value.
            let default_expr = if crate::codegen_ay::chc::stmt::codegen_stmt_slice_len_write::is_slice_len_pointer_ty(
                self.body.locals()[local_idx].ty,
            ) {
                self.pack_slice_slot(
                    Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
                    Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
                )
            } else {
                default_expr
            };
            if let Some(mut local_constraints) = self.build_local_update_constraints(
                local_idx,
                default_expr,
                "fn_inline_move_arg_invalidated",
            ) {
                constraints.append(&mut local_constraints);
            }
        }
        constraints
    }

    /// The dead placeholder of every slot of the moved-out flattened local
    /// `local_idx`: each slot's output equals its sort's default. A slot whose
    /// sort has none (an array, a datatype left by the depth cap) stays free:
    /// a moved-out local is never read before it is assigned again, so the
    /// value is unobserved either way.
    fn moved_flattened_local_placeholders(&mut self, local_idx: usize) -> Vec<Expr> {
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else { return Vec::new() };
        let mut constraints = Vec::new();
        for slot in 0..self.flattened_field_count(local_idx) {
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx + slot).cloned()
            else {
                continue;
            };
            let Some(default) = ChcCtx::sort_default_expr(&out_sort) else { continue };
            self.encode.flattened_field_env.insert((local_idx, slot), default.clone());
            constraints.push(Expr::var(&*out_name, out_sort).eq(default));
        }
        constraints
    }

    /// Assert-guard SIDE-CHANNEL host emission: one error rule per check
    /// accumulated during the inline walk, through the standard per-property
    /// machinery (BSEM-18): `host_reach ∧ stmt_constraints ∧ ¬check → error_pN`.
    ///
    /// Each `check` carries its full inline path condition (assume guards at
    /// record time, SwitchInt/dispatch branch guards from the merge points), so
    /// the rule fires exactly when the host reaches the call AND the inline
    /// path to the check is taken AND the check is violated. This is the lane
    /// that makes a `kani::assert` inside ANY successfully-inlined nested body
    /// produce a REAL error rule at the host — the legacy return-value ITE
    /// (`emit_inline_assert_guard_error` below) drops the check whenever the
    /// value is discarded or re-wrapped (unit destinations, sort coercions).
    pub(in crate::codegen_ay::chc) fn emit_deferred_inline_check_errors(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        deferred_checks: Vec<DeferredInlineCheck>,
    ) {
        // An unwinding assertion the host's dominating argument bounds make
        // unviolable is not a property (`host_bound_discharge.rs`).
        let deferred_checks =
            super::codegen_call_virtual_inline::host_bound_discharge::drop_host_discharged_unwinding_checks(
                self,
                dcx.bb_idx,
                dcx.modified_locals,
                deferred_checks,
            );
        self.emit_deferred_inline_checks_at(
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.bb_idx,
            deferred_checks,
        );
    }

    /// [`Self::emit_deferred_inline_check_errors`] for hosts that are not a
    /// call dispatch (the drop consumers), from their own rule context.
    ///
    /// Two kinds of entry are not emitted, and neither can change a verdict:
    /// * a check that is valid whatever the host state
    ///   ([`check_is_trivially_valid`]: `checked_sub`'s `a >= b -> no
    ///   underflow`, `wrapping_shl`'s `(s & 7) < 8`). Its violation is
    ///   unsatisfiable, but as a property it still took a slice of the
    ///   harness's solve budget (measured 9-13 s each, enough to turn a proof
    ///   UNKNOWN).
    /// * an exact duplicate of a check already emitted here: the same
    ///   condition under the same path, so the same violation set. A walked
    ///   user `a / b` records its MIR `Assert` and, since the walker checks
    ///   Div/Rem itself, the identical divisor check; one property suffices.
    ///   The first (the MIR `Assert`'s) message is kept.
    ///
    /// Duplicates are found by node identity, and structurally only for a
    /// check small written out as a tree: `Hash` / `Eq` on `Expr` walk the
    /// term as a tree, and a check over a long walked replay shares its
    /// subterms exponentially, so the structural set spent the compile budget
    /// hashing it (walker fail-closed review 6 round 3, `iter().any(|_|
    /// false)`, a 600 s CompileTimeout).
    pub(in crate::codegen_ay::chc) fn emit_deferred_inline_checks_at(
        &mut self,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        bb_idx: usize,
        deferred_checks: Vec<DeferredInlineCheck>,
    ) {
        const MAX_STRUCTURAL_DEDUP_NODES: u64 = 4096;
        let mut emitted: HashSet<Expr> = HashSet::new();
        let mut emitted_nodes: HashSet<*const ay_bindings::ExprValue> = HashSet::new();
        let mut sizes = HashMap::new();
        for check in deferred_checks {
            if check_is_trivially_valid(&check.check) {
                debug!(bb_idx, message = ?check.message, "deferred inline check is valid, not emitted");
                continue;
            }
            let duplicate = !emitted_nodes.insert(std::ptr::from_ref(check.check.value()))
                || (super::codegen_call_virtual_inline::expr_written_out_size(
                    &check.check,
                    &mut sizes,
                    MAX_STRUCTURAL_DEDUP_NODES,
                ) <= MAX_STRUCTURAL_DEDUP_NODES
                    && !emitted.insert(check.check.clone()));
            if duplicate {
                debug!(bb_idx, message = ?check.message, "duplicate deferred inline check, not emitted");
                continue;
            }
            self.emit_error_rule_for_condition_with_kind(
                from_app,
                check.check,
                stmt_constraints,
                bb_idx,
                check.kind,
                check.message,
            );
        }
    }

    /// The inline walk's two path side channels in a result value, for a host
    /// emit: the assert guard (its error rule, plus the success edge's
    /// constraint) and the assume guard (a transition constraint), with both
    /// kinds of marker leaf stripped from the value. Returns the stripped
    /// value and the constraints for the success edge.
    ///
    /// The fn-pointer, virtual, closure and `block_on` emits took only the
    /// assert guard. A `kani::assume` in a body reached through them left its
    /// `__assume_pruned_inline` leaf in the value, as an unconstrained fresh
    /// variable, and the assume itself was lost: the caller's assertion of the
    /// assumed fact failed, certified Genuine, where Kani proves it
    /// (`walker_callee_assume_dual.rs`). The direct inline emit above always
    /// took both.
    pub(in crate::codegen_ay::chc) fn take_inline_result_guards(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        result_expr: Expr,
    ) -> (Expr, Vec<Expr>) {
        let inline_assert_guard = extract_inline_assert_guard(&result_expr);
        let inline_assume_guard = extract_inline_assume_guard(&result_expr);
        let result_expr = strip_inline_assert_fallback(&result_expr).unwrap_or(result_expr);
        let result_expr = strip_inline_assume_pruned(&result_expr).unwrap_or(result_expr);
        let mut constraints = self.emit_inline_assert_guard_error(dcx, inline_assert_guard);
        let inline_assume_guard =
            super::codegen_call_virtual_inline::host_bound_discharge::drop_host_discharged_assume_guard(
                self,
                dcx.bb_idx,
                dcx.modified_locals,
                inline_assume_guard,
            );
        constraints.extend(inline_assume_guard);
        (result_expr, constraints)
    }

    /// Part of #4048: Emit both edges for an inline assert guard.
    ///
    /// The success transition keeps the guard as an extra constraint, but the
    /// negated guard must also reach `error()` rather than silently pruning the
    /// path into a false proof. A guard valid whatever the state
    /// ([`check_is_trivially_valid`], as for the deferred checks above) has an
    /// unsatisfiable negation, so its error rule is not emitted; it is still
    /// returned as the success edge's constraint.
    pub(in crate::codegen_ay::chc) fn emit_inline_assert_guard_error(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        inline_assert_guard: Option<Expr>,
    ) -> Vec<Expr> {
        let Some(inline_assert_guard) = inline_assert_guard else {
            return Vec::new();
        };
        if check_is_trivially_valid(&inline_assert_guard) {
            debug!(bb_idx = dcx.bb_idx, "inline assert guard is valid, error rule not emitted");
            return vec![inline_assert_guard];
        }
        // Report this as the ASSERTION it is. `emit_error_rule_for_condition`
        // defaults to `PropertyKind::MemorySafety` with no message, so every
        // inline-assert-guard failure previously surfaced as
        // "CHC verification: memory safety" — sending triage to the heap model for
        // what is an assertion inside an inlined callee. Observed on
        // `expected/function-contract/modifies/zst_pass.rs`, whose headline failure
        // is this edge, not a heap check.
        self.emit_error_rule_for_condition_with_kind(
            dcx.from_app,
            inline_assert_guard.clone(),
            dcx.stmt_constraints,
            dcx.bb_idx,
            PropertyKind::Assertion,
            Some("assertion failed inside inlined callee".to_string()),
        );
        vec![inline_assert_guard]
    }
}

fn inline_call_preserves_receiver_vtable(callee_path: Option<&str>) -> bool {
    callee_path.is_some_and(|path| {
        path.ends_with("::deref")
            || path.ends_with("::as_ref")
            || path.ends_with("::borrow")
            || (path.contains("::pin::Pin")
                && (path.ends_with("::as_mut") || path.ends_with("::new_unchecked")))
    })
}

/// Part of #4014: Widen a BV64 inline result to BV128 when the destination is
/// a fat pointer (data + vtable). The inline walker tracks the vtable
/// separately in `inline_vtable_ids`, so `result_expr` is BV64 (data pointer
/// only). If the CHC state variable for `dest_local` is BV128, we must
/// concatenate `vtable || data` to produce the correct fat-pointer encoding.
/// Without this widening the BV64 value cannot be written to the BV128 slot,
/// leaving the destination unconstrained and letting the solver pick unaligned
/// addresses to violate kani_mem alignment checks.
pub(in crate::codegen_ay::chc) fn widen_inline_result_for_fat_pointer(
    ctx: &ChcCtx<'_, '_>,
    dest_local: usize,
    result_expr: Expr,
    inline_vtable: &Option<Expr>,
) -> Expr {
    let Some(result_width) = result_expr.sort().bitvec_width() else {
        return result_expr;
    };
    if result_width != POINTER_WIDTH {
        return result_expr;
    }
    // Check if destination expects BV128 (fat pointer).
    let dest_sort = ctx.resolve_destination(dest_local).map(|(_, var)| var.sort().clone());
    let dest_width = dest_sort.as_ref().and_then(|s| s.bitvec_width());
    let needs_widen = dest_width == Some(2 * POINTER_WIDTH);

    // Wave 4: both paths below build a wide pointer out of a data half and a
    // metadata half. The roles are DECLARED, not inferred: this function's
    // contract (see the doc comment) is that `result_expr` is the inline
    // callee's data pointer, and the metadata comes from a side table that
    // says what it is — `inline_vtable_ids` for a vtable id, `subslice_len`
    // for a slice length. Reporting them to `PtrRepr` as `(Loc, Val)` keeps
    // the `[meta:upper | data:lower]` byte order in one place; the bare
    // `concat`s replaced here took two same-sorted operands and would have
    // packed a vtable id into the data slot without complaint if transposed.
    let data = Loc::of_address(result_expr.clone());

    // Path 1: Vtable-based fat pointer (dyn Trait).
    if let Some(vtable_expr) = inline_vtable {
        if let Some(vtable_width) = vtable_expr.sort().bitvec_width() {
            if vtable_width == POINTER_WIDTH
                && needs_widen
                && let Some(packed) =
                    PtrRepr::from_declared_roles(data.clone(), Val::of_value(vtable_expr.clone()))
                        .into_packed()
            {
                debug!(
                    dest_local,
                    "fn_inline: widening BV64 result + vtable to BV128 fat pointer (#4014)"
                );
                return packed;
            }
        }
    }

    // Path 2: Slice-based fat pointer (slice/str/custom DST).
    // When subslice_len is seeded for the destination (by slice_from_raw_parts
    // or RawPtr aggregate), embed the length into the BV128 so metadata
    // survives array store/load round-trips and pointer casts.
    if needs_widen {
        if let Some(len_expr) = ctx.ref_resolution.subslice_len.get(&dest_local) {
            let len_bv = crate::codegen_ay::types::coerce_bitvec_width_safe(
                len_expr.clone(),
                POINTER_WIDTH,
                crate::codegen_ay::types::SignExtension::ZeroExtend,
            );
            if let Some(packed) =
                PtrRepr::from_declared_roles(data, Val::of_value(len_bv)).into_packed()
            {
                debug!(
                    dest_local,
                    "fn_inline: widening BV64 result + subslice_len to BV128 fat pointer"
                );
                return packed;
            }
        }
    }

    result_expr
}

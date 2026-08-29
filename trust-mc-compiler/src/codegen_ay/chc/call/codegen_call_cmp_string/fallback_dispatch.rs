// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Known-stdlib fallback and inferable-summary helpers for `codegen_call_cmp_string`.
//!
//! Extracted from `mod.rs` per #3254 packet 2.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Mutability, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::call_uf_table::established_pure_scalar_callee;

/// Outcome of the receiver-sensitive tail fallback decision.
///
/// Shared between `codegen_known_stdlib_unconstrained` and `codegen_unhandled_call`
/// in `tail_dispatch.rs`. The policy is: mutable receivers are DEMOTED (side effects
/// lost), immutable receivers get an inferable summary when possible, otherwise
/// sound over-approximation (only return value unconstrained).
pub(in crate::codegen_ay::chc) enum TailFallbackOutcome {
    /// Inferable uninterpreted-function summary emitted successfully.
    Inferable,
    /// Immutable receiver, inferable summary creation failed: destination
    /// return value unconstrained — sound over-approximation.
    SoundFallback,
    /// Mutable receiver: side effects on the receiver are lost — DEMOTED.
    DemotedMutReceiver,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Shared receiver-sensitive fallback decision and rule emission.
    ///
    /// Encapsulates the three-way split used by both `known_stdlib_unconstrained`
    /// and `unhandled_call` tail handlers. Callers handle only path-specific
    /// counters and logging after matching on the returned outcome.
    pub(in crate::codegen_ay::chc) fn resolve_tail_fallback(
        &mut self,
        func: &Operand,
        args: &[Operand],
        from_app: &super::super::RelationApp,
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
        target: BasicBlockIdx,
        dest_local: usize,
    ) -> TailFallbackOutcome {
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        if !self.has_mut_receiver(args)
            && let Some(constraint) =
                self.try_build_inferable_constraint(func, args, dest_local, modified_locals)
        {
            // NOTE: deliberately does NOT touch `diagnostics.inferable_predicate`
            // or `record_inferable_summary_name_for_fn`. That counter is the
            // DEMOTING category for the old, un-gated `P_inf_<callee>`
            // declare-fun summary, which assumed callee determinism with no
            // established purity fact (see `try_build_inferable_constraint`);
            // it stays intact with zero producers. The congruent-table lane is
            // a different construct with its own accounting — the builder
            // records `call_uf_congruent_summary` with the destination's var
            // identity, exactly once per event.
            self.emit_goto_rule_extra(
                from_app,
                target,
                &new_output_args,
                stmt_constraints,
                [constraint],
            );
            TailFallbackOutcome::Inferable
        } else if self.has_mut_receiver(args) {
            self.record_fallback();
            self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
            TailFallbackOutcome::DemotedMutReceiver
        } else {
            // Task #78: this SOUND fallback havocs the destination's output
            // state var. Plumb its SMT-var IDENTITY so the driver can run a real
            // dependency check on the violated `error_p{N}` (was:
            // `emit_sound_fallback_goto_prebuilt`, whose `record_sound_fallback_reason`
            // left the freed var UNIDENTIFIED). `freed = None` means the
            // destination has no live state slot (dead — provably unreadable);
            // it is still ACCOUNTED so a dead-result discard does not block
            // certification. `call_dispatch_fallback_prebuilt` is the same
            // reason `emit_sound_fallback_goto_prebuilt` records, so the counter
            // routing (place_translation_drop) is unchanged.
            let freed = self.freed_dest_output_var(dest_local);
            self.record_sound_fallback_reason_identified(
                "call_dispatch_fallback_prebuilt",
                freed.as_deref(),
            );
            self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
            TailFallbackOutcome::SoundFallback
        }
    }

    /// Task #78: the destination local's OUTPUT SMT-var name (the `_x__out` slot
    /// a sound fallback havocs), or `None` when the local has no live state slot.
    pub(in crate::codegen_ay::chc) fn freed_dest_output_var(
        &self,
        dest_local: usize,
    ) -> Option<String> {
        let idx = self.state_var_mgr.try_state_idx_for_local(dest_local)?;
        self.state_var_mgr.output_state_vars.get(idx).map(|(name, _)| name.to_string())
    }
    /// Detect whether the first argument (receiver) is `&mut T` (Part of #3589).
    ///
    /// Methods with `&mut self` receivers have mutation side effects that the
    /// inferable predicate mechanism cannot model: after a `&mut self` call, the
    /// struct state becomes a fresh unconstrained symbolic. PDR can then assign
    /// different return values to `P_inf(s_before)` vs `P_inf(s_after)` since
    /// `s_before != s_after`, producing false proofs.
    ///
    /// Intentionally narrow: only checks argument 0 (the receiver), not all `&mut`
    /// arguments. Read-only `&self` methods still get inferable summaries.
    pub(in crate::codegen_ay::chc) fn has_mut_receiver(&self, args: &[Operand]) -> bool {
        let Some(arg0) = args.first() else { return false };
        let Ok(ty) = arg0.ty(self.body.locals()) else { return false };
        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut)))
    }

    /// Summarise an unhandled call as an UNINTERPRETED FUNCTION of its
    /// arguments — but only behind an ESTABLISHED purity fact (Part of #4270 /
    /// TL18; supersedes the #3395 `P_inf_<callee>` declare-fun lane).
    ///
    /// Returns `Some(constraint)` binding the destination's output state var to
    /// a congruent summary term, or `None` to leave the caller's sound
    /// over-approximation (destination havoced) in place.
    ///
    /// # Why there is no `declare-fun` here any more
    ///
    /// The original lane declared `P_inf_<callee>(arg_sorts) -> ret_sort` and
    /// equated the destination to its application. `ay-chc`'s parser REJECTS
    /// any `declare-fun` whose return sort is not Bool (parser/commands.rs:
    /// "Non-predicate function declaration: '<name>' with return sort <S>.
    /// Only Bool-returning functions (predicates) are supported in ay-chc."),
    /// and that error aborts the parse of the WHOLE problem — a single such
    /// declaration cost the harness its entire verification, coming back
    /// UNKNOWN having never been solved. Observed in the corpus:
    ///   P_inf_std::…::alloc_zeroed  ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64)
    ///   P_inf_std::…::alloc         ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64)
    ///   P_inf_std::collections::VecDeque::<T>::new  ()             (_ BitVec 64)
    /// There is also no global-constant escape hatch: ay-chc aliases
    /// `declare-const` to `declare-var`, and any free symbol becomes a
    /// PER-CLAUSE universally quantified variable. Two calls are always two
    /// different Horn rules, so a shared free variable gives no sharing at all.
    /// `call_uf_table.rs` therefore encodes the UF the way this codebase
    /// already encodes symbolic float arithmetic: a frozen `Array` column
    /// threaded through every relation and never modified, so `select` over it
    /// is congruent along a trace while staying universally quantified.
    ///
    /// # Why the gate, and why it is not the signature
    ///
    /// A UF makes two calls with equal arguments return equal values. For
    /// alloc, RNG and I/O that is FALSE, and asserting it fabricates proofs.
    /// Demonstrated on the emitted shape `d1 := g(x); d2 := g(x); if d1 != d2
    /// { error }`:
    ///
    ///   UF summary  ->  sat    (a PROOF that d1 == d2)
    ///   havoc       ->  unsat  (error is reachable -- the sound answer)
    ///
    /// Same program, and the summary fabricates a proof the sound encoding
    /// refutes. Nor does an all-by-value-scalar prototype license it:
    /// `uint32_t takes_int(uint32_t i) { return i + c++; }` has exactly that
    /// prototype and `takes_int(x) != takes_int(x)`
    /// (see `codegen_call_foreign.rs`). SIGNATURE SHAPE IS NOT, AND MUST NEVER
    /// BECOME, THE GATE.
    ///
    /// `established_pure_scalar_callee` reads the callee's MIR body instead and
    /// admits it only with no `Deref`, no reference/raw-pointer constant, no
    /// pointer-creating rvalue, no memory intrinsic, no panicking terminator,
    /// and no nested call outside the same gate — see `call_uf_table.rs` for
    /// the full clause list and the soundness argument. A callee that fails it
    /// keeps the pre-existing fail-closed havoc.
    pub(in crate::codegen_ay::chc) fn try_build_inferable_constraint(
        &mut self,
        func: &Operand,
        args: &[Operand],
        dest_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let dest_vec_idx = self.state_var_mgr.try_state_idx_for_local(dest_local)?;
        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
        let dest_var_name = self.state_var_mgr.output_state_vars[dest_vec_idx].0.to_string();
        let dest_var = Expr::var(&*dest_var_name, out_sort.clone());

        // THE GATE FIRST — nothing is translated for a callee we may not
        // summarise, so a refusal costs no work and leaves no residue.
        if !self.call_uf_table_declared() {
            return None;
        }
        let callee_path = self.resolve_callee_path(func)?;
        if callee_path.contains("Drop>::drop") {
            return None;
        }
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) = func_ty.kind() else {
            return None;
        };
        let instance = Instance::resolve(fn_def, &fn_args).ok()?;
        if !established_pure_scalar_callee(&instance) {
            debug!(
                callee = %callee_path,
                ?out_sort,
                "UF summary refused: callee purity not ESTABLISHED — keeping sound havoc"
            );
            return None;
        }

        let mut arg_exprs: Vec<Expr> = Vec::with_capacity(args.len());
        for arg in args {
            arg_exprs.push(self.translate_operand_with_modified(arg, modified_locals)?);
        }

        let summary = self.call_uf_summary_term(&instance, &arg_exprs, &out_sort)?;

        // Accounted exactly once, with the destination's var identity (Task
        // #78). `call_uf_congruent_summary` is blessed SoundHavoc in
        // `codegen_ctx::fallback_soundness` under the audit written there and
        // in `call_uf_table.rs`; the un-gated `call_dispatch_fallback_prebuilt`
        // fail-close still covers every callee this gate refuses.
        self.record_sound_fallback_reason_identified(
            "call_uf_congruent_summary",
            Some(dest_var_name.as_str()),
        );
        debug!(
            callee = %callee_path,
            ?out_sort,
            "UF summary EMITTED: established-pure scalar callee, congruent table term"
        );
        Some(dest_var.eq(summary))
    }

    /// Detect known standard library functions that are too complex to model
    /// precisely but are recognized as sound over-approximation candidates.
    ///
    /// Matched functions share the receiver-sensitive fallback lattice with
    /// the catch-all (via `resolve_tail_fallback`) but are NOT counted in
    /// `unhandled_calls`. This improves
    /// diagnostic accuracy: `unhandled_calls` tracks genuinely unknown
    /// functions, while these are "known unconstrained" — we recognize them
    /// and acknowledge the over-approximation.
    ///
    /// Only matches functions from `core::`, `std::`, `alloc::` crates to
    /// avoid false matches on user-defined types. Only reached for calls that
    /// passed through ALL earlier dispatchers (kani hooks, collections,
    /// option/pointer, overapprox, misc/route-table, closure, virtual,
    /// fn_inline, fn_ptr) without being claimed.
    ///
    /// Part of #3323, Phase 3. Follows pattern from
    /// `codegen_call_unconstrained_stub_impl` (NonNull, BTreeMap internals).
    pub(in crate::codegen_ay::chc) fn is_known_stdlib_unconstrained(path: &str) -> bool {
        let is_std_crate = path.starts_with("core::")
            || path.starts_with("std::")
            || path.starts_with("alloc::")
            || path.starts_with("<core::")
            || path.starts_with("<std::")
            || path.starts_with("<alloc::");

        if path.starts_with("libc::") {
            return true;
        }

        if !is_std_crate {
            return false;
        }

        // Exclude as_array which has a dedicated handler in slice_as_array.rs
        // (Part of #3620). Without this exclusion, as_array is preempted by the
        // slice:: catch-all and treated as unconstrained, leaving the Option
        // discriminant opaque.
        if path.contains("slice::") && !path.contains("as_array") {
            return true;
        }
        if path.contains("string::String") || path.contains("string::ToString") {
            return true;
        }
        if path.contains("str::") {
            return true;
        }
        if path.contains("vec::Vec") || path.contains("raw_vec::RawVec") {
            return true;
        }
        if path.contains("Iterator>") || path.contains("IntoIterator>") {
            return true;
        }
        if path.contains("iter::") {
            return true;
        }
        if path.contains("Deref>") || path.contains("ToOwned") {
            return true;
        }
        if path.contains("From<") && path.contains(">") {
            return true;
        }
        if path.contains("Extend<") {
            return true;
        }
        if path.contains("Fn::call")
            || path.contains("FnMut::call")
            || path.contains("FnOnce::call")
        {
            return true;
        }
        if path.contains("ptr::") {
            return true;
        }
        if path.contains("::powi") || path.contains("::sqrt") || path.contains("::powf") {
            return true;
        }
        if path.contains("num::") {
            return true;
        }
        if path.contains("alloc::") && path.contains("Allocator") {
            return true;
        }
        if path.contains("HashMap") || path.contains("BTreeMap") || path.contains("BTreeSet") {
            return true;
        }
        if path.contains("ops::Range") {
            return true;
        }
        false
    }

    /// Detect Range/RangeInclusive constructors: `::new`, or direct struct
    /// construction paths like `<core::ops::range::RangeInclusive<T>>::new`.
    /// Part of #3470.
    pub(in crate::codegen_ay::chc) fn is_range_constructor(path: &str) -> bool {
        if !path.contains("ops::range::Range") && !path.contains("ops::Range") {
            return false;
        }
        path.ends_with("::new") || path.contains("::new::")
    }

    /// Try to constrain the destination of a Range/RangeInclusive constructor
    /// call by mapping the call arguments to the flattened state variables.
    /// Returns `Some(constraints)` if successful, `None` if the arguments
    /// can't be translated or the destination isn't flattened.
    /// Part of #3470.
    pub(in crate::codegen_ay::chc) fn try_constrain_range_constructor(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        path: &str,
    ) -> Option<Vec<Expr>> {
        let start_expr = self.translate_operand_with_modified(&args[0], modified_locals)?;
        let end_expr = self.translate_operand_with_modified(&args[1], modified_locals)?;

        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let expected_fields = if path.contains("RangeInclusive") { 3 } else { 2 };
        if self.flatten.flattened_local_field_count.get(&dest_local).copied()
            != Some(expected_fields)
        {
            return None;
        }
        let mut constraints = Vec::new();

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            self.push_coerced_eq_constraint(
                &mut constraints,
                &out_var,
                start_expr,
                &out_sort,
                dest_local,
                "range_constructor::start",
            );
        }
        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx + 1).cloned()
        {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            self.push_coerced_eq_constraint(
                &mut constraints,
                &out_var,
                end_expr,
                &out_sort,
                dest_local,
                "range_constructor::end",
            );
        }
        if path.contains("RangeInclusive")
            && let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx + 2).cloned()
        {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            self.push_coerced_eq_constraint(
                &mut constraints,
                &out_var,
                Expr::bool_const(false),
                &out_sort,
                dest_local,
                "range_constructor::exhausted",
            );
        }

        if constraints.is_empty() { None } else { Some(constraints) }
    }
}

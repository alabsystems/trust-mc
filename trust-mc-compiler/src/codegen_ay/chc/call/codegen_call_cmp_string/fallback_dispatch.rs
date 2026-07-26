// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Known-stdlib fallback and inferable-summary helpers for `codegen_call_cmp_string`.
//!
//! Extracted from `mod.rs` per #3254 packet 2.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Mutability, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use trust_mc_core::decl::Decl;

use super::super::ChcCtx;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_rules::CodegenRules;

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
            self.diagnostics.inferable_predicate.inc();
            // Part of #4031: record exact P_inf_<callee> name for provenance.
            if let Some(callee_path) = self.resolve_callee_path(func) {
                let summary_name = format!("P_inf_{}", callee_path);
                super::super::codegen_ctx::record_inferable_summary_name_for_fn(
                    &self.fn_name,
                    &summary_name,
                );
            }
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

    /// Try to build a solver-inferable constraint for an unhandled call (Part of #3395).
    ///
    /// Instead of leaving the destination completely unconstrained, declares an
    /// uninterpreted function `P_inf_<callee>(arg_sorts) -> ret_sort` and constrains
    /// the destination to equal the function application. PDR must synthesize a
    /// consistent function summary that satisfies the proof obligation.
    ///
    /// Returns `Some(constraint)` if the inferable function was successfully built,
    /// or `None` if arguments couldn't be translated or sorts are incompatible.
    pub(in crate::codegen_ay::chc) fn try_build_inferable_constraint(
        &mut self,
        func: &Operand,
        args: &[Operand],
        dest_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let dest_vec_idx = self.state_var_mgr.try_state_idx_for_local(dest_local)?;
        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
        let dest_var_name = &self.state_var_mgr.output_state_vars[dest_vec_idx].0;
        let dest_var = Expr::var(&**dest_var_name, out_sort.clone());

        let mut arg_exprs: Vec<Expr> = Vec::with_capacity(args.len());
        for arg in args {
            arg_exprs.push(self.translate_operand_with_modified(arg, modified_locals)?);
        }

        let callee_path = self.resolve_callee_path(func)?;
        if callee_path.contains("Drop>::drop") {
            return None;
        }
        // Part of #4270 (TL18): closure bodies reach this lane when fn-trait
        // dispatch doesn't inline. Emitting `Decl::Fun` with a non-Bool return
        // sort for `P_inf_*::{closure#N}` is rejected by ay-chc:
        //   "Non-predicate function declaration: 'P_inf_*::{closure#0}' with
        //    return sort BitVec(32). Only Bool-returning functions (predicates)
        //    are supported in ay-chc."
        // Skip the inferable summary so the caller falls back to sound
        // over-approximation (destination havoced) instead of producing a
        // parse-reject ERROR.
        if callee_path.contains("::{closure#") {
            return None;
        }

        let summary_name = format!("P_inf_{}", callee_path);
        let arg_sorts: Vec<Sort> = arg_exprs.iter().map(|expr| expr.sort().clone()).collect();

        if let Some((existing_sorts, existing_ret)) = self.declared_inferable_fns.get(&summary_name)
        {
            if existing_sorts != &arg_sorts || *existing_ret != out_sort {
                return None;
            }
        } else {
            self.vc.add_decl(Decl::Fun {
                name: summary_name.clone(),
                arg_sorts: arg_sorts.clone(),
                ret_sort: out_sort.clone(),
            });
            self.declared_inferable_fns.insert(summary_name.clone(), (arg_sorts, out_sort));
        }

        let summary_app =
            Expr::func_app_with_sort(&summary_name, arg_exprs, dest_var.sort().clone());
        Some(dest_var.eq(summary_app))
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

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reduction dispatch arms (IterFold, IterSum) for iterator adapter CHC call codegen.
//!
//! Extracted from mod.rs per #4129 (500 LOC threshold).

use crate::callee_body::CalleeBody;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, Body, LocalDecl, Operand, Place, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{AdtKind, ClosureKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::iter_sum_summand::{SumSummand, classify_iter_sum};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::bool_sort;
use crate::rustc_public_bridge::IndexedVal;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::chc_fresh_name;
use super::super::codegen_ctx::{Havoc, SoundHavocReason, sound_havoc};
use super::super::inline_body::{
    DeferredInlineCheck, extract_inline_assume_guard, strip_inline_assert_fallback,
    translate_closure_inline_result,
};
use super::fold_precise::{
    PreciseReduction, REDUCE_UNWINDING_MESSAGE, ReduceLoopRule, ReduceUnwinding, ReductionStep,
};
use trust_mc_core::violation::PropertyKind;
use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use crate::codegen_ay::chc::quantifier_encoding::{
    ClosureBodyResult, translate_closure_body_with_params,
};

fn closure_returns_option_like_success(body: &Body) -> bool {
    let mut block_idx = 0;
    let mut visited = HashSet::new();
    let mut return_rvalue = None;

    loop {
        if !visited.insert(block_idx) {
            return false;
        }
        let Some(block) = body.blocks.get(block_idx) else {
            return false;
        };

        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            if place.local == 0 && place.projection.is_empty() {
                return_rvalue = Some(rvalue);
            }
        }

        match block.terminator.kind {
            TerminatorKind::Goto { target } => block_idx = target,
            TerminatorKind::Return => {
                return return_rvalue.is_some_and(rvalue_is_option_like_payload_variant);
            }
            _ => return false,
        }
    }
}

fn rvalue_is_option_like_payload_variant(rvalue: &Rvalue) -> bool {
    let Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), operands) = rvalue else {
        return false;
    };
    if def.kind() != AdtKind::Enum || operands.len() != 1 {
        return false;
    }

    let variants = def.variants();
    let Some(returned_variant) = variants.get(variant.to_index()) else {
        return false;
    };
    variants.len() == 2
        && variants.iter().any(|candidate| candidate.fields().is_empty())
        && returned_variant.fields().len() == 1
}

/// Does any closure among `args` (by value or behind a reference) carry an
/// obligation the obligation walk sights, or one it cannot rule out? A
/// closure that cannot be resolved counts as one.
pub(in crate::codegen_ay::chc) fn closure_arg_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
) -> bool {
    let stubs = crate::kani_middle::transform::walker_stub_map();
    args.iter().any(|arg| {
        let Ok(ty) = arg.ty(ctx.body.locals()) else {
            return false;
        };
        let is_closure = |ty: &rustc_public::ty::Ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Closure(..)));
        let closure = is_closure(&ty)
            || matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _)) if is_closure(&inner));
        if !closure {
            return false;
        }
        let Some((instance, _)) = resolve_reduce_closure_for_operand(arg, ctx.body.locals()) else {
            return true;
        };
        crate::codegen_ay::obligation_free_walk::instance_obligation_verdict(ctx.tcx, instance, &stubs)
            != crate::codegen_ay::obligation_free_walk::Verdict::Free
    })
}

/// Can the closure of type `closure_ty` (by value or behind a reference)
/// carry an obligation the obligation walk sights, or one it cannot rule out?
/// A closure that cannot be resolved counts as one; a type that is not a
/// closure (a function item, a function pointer) counts as one too.
pub(in crate::codegen_ay::chc) fn closure_ty_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    closure_ty: rustc_public::ty::Ty,
) -> bool {
    let closure_ty = match closure_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
        _ => closure_ty,
    };
    let TyKind::RigidTy(RigidTy::Closure(def, args)) = closure_ty.kind() else {
        return true;
    };
    let stubs = crate::kani_middle::transform::walker_stub_map();
    let Some(instance) = [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
        .into_iter()
        .find_map(|kind| Instance::resolve_closure(def, &args, kind).ok())
    else {
        return true;
    };
    crate::codegen_ay::obligation_free_walk::instance_obligation_verdict(ctx.tcx, instance, &stubs)
        != crate::codegen_ay::obligation_free_walk::Verdict::Free
}

fn resolve_try_fold_closure_body_for_operand(
    operand: &Operand,
    locals: &[LocalDecl],
) -> Option<Body> {
    resolve_reduce_closure_for_operand(operand, locals).map(|(_, body)| body)
}

/// The closure a reduction is handed (`fold(init, f)`'s `f`), as the instance
/// its body is taken from and that body.
fn resolve_reduce_closure_for_operand(
    operand: &Operand,
    locals: &[LocalDecl],
) -> Option<(Instance, Body)> {
    let closure_ty = operand.ty(locals).ok()?;
    let (closure_def, closure_args, kinds) = match closure_ty.kind() {
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            (def, args, [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce])
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..))) =>
        {
            let TyKind::RigidTy(RigidTy::Closure(def, args)) = inner.kind() else {
                unreachable!("guard ensures inner closure type");
            };
            (def, args, [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce])
        }
        _ => return None,
    };

    kinds.into_iter().find_map(|kind| {
        let instance = Instance::resolve_closure(closure_def, &closure_args, kind).ok()?;
        instance.callee_body().map(|body| (instance, body))
    })
}

/// Kani's message for a `sum` step that overflows.
const SUM_OVERFLOW_MESSAGE: &str = "attempt to add with overflow";

/// How one replayed step of an integer `Iterator::sum` adds `acc + elem`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SumStep {
    /// Modular `bvadd`: `Wrapping<int>`, or a std integer sum compiled
    /// without overflow checks.
    Wrapping,
    /// A std integer sum under overflow checks: `bvadd`, plus the step's
    /// "attempt to add with overflow" obligation.
    Checked { signed: bool },
    /// `Saturating<uN>`: `acc + elem`, or all ones when that carries out.
    /// Never panics.
    Saturating,
}

/// The message of the conservative rule for a `Sum` impl the stub does not
/// model ([`ReducePanicObligation::unmodeled_impl`]).
pub(in crate::codegen_ay::chc) const SUM_IMPL_UNMODELED_MESSAGE: &str =
    "Iterator::sum: the Sum impl this call runs is not modelled and may panic";

/// What an `Iterator::sum` call can panic on, beyond the closures of its
/// receiver's adapter chain (`mod.rs`, `emit_unmodeled_closure_rule`) and
/// Kani's unwinding assertion on its loop (`push_reduce_unwinding_check`).
/// Each part is a VIOLATION predicate over the call's pre-state and the
/// replay's constraints. A `fold`'s closure states its own obligations
/// (`ReductionStep::checks`, `unreplayed_step_check`).
///
/// * An integer sum: the "attempt to add with overflow" std's integer `Sum`
///   raises (it adds under `#[rustc_inherit_overflow_checks]`).
/// * A `Sum` impl the stub does not model (`SumSummand::Unknown`): whatever
///   its body could panic on. The body is not encoded, so the obligation is
///   the conservative rule alone (AY alignment round 8, review round 3,
///   finding 2: it used to be no rule at all, and a user impl that overflows,
///   a `Duration` sum and a std sum the stub could not classify were proved
///   where Kani fails). Only core's numeric impls reach the stub at all
///   (`reduce_loop_rule::iter_sum_call_is_core_numeric_fold`, at the stub
///   lookup): a user impl, `Duration` and `Option<T>` take the ordinary call
///   path, so this is the rule for a core impl the classification does not
///   know.
/// * A float sum under `--nan-check`: std's `a + b` carries Kani's "NaN on
///   addition" check, and this lane has no FP theory to compute the partial
///   sums it reads, so the obligation is the conservative rule alone (AY
///   alignment round 8, review round 5: the sum carried none, and
///   `[f32::INFINITY, f32::NEG_INFINITY].iter().sum()` was proved).
///
/// std's `Wrapping`, `Saturating` and float sums cannot panic and get no
/// obligation. That is decided by the impl, never by the destination's sort:
/// a classified impl whose value this lane cannot encode at that sort keeps
/// its own obligation (round 8, review round 4, finding 1: `Saturating` was
/// `Unknown`, and the rule above reported a panic `saturating_add` cannot
/// raise).
pub(in crate::codegen_ay::chc) struct ReducePanicObligation {
    /// Some replayed step is taken and overflows. Exact, so a counterexample
    /// through it can be certified.
    pub exact: Option<Expr>,
    /// The panic the replay did not check (an integer sum adding elements past
    /// the replay bound or from a sequence the replay could not address; any
    /// panic of an unmodelled impl), conjoined with a freed flag so a
    /// counterexample through it is never certified Genuine. Conservative: it
    /// can only add failures.
    pub unchecked: Expr,
    /// The check's kind and description on the report.
    pub kind: PropertyKind,
    pub message: &'static str,
}

impl ReducePanicObligation {
    fn add_overflow(exact: Option<Expr>, unchecked: Expr) -> Self {
        Self {
            exact,
            unchecked,
            kind: PropertyKind::ArithmeticOverflow,
            message: SUM_OVERFLOW_MESSAGE,
        }
    }

    /// The impl's body is not encoded: a panic is possible whenever the call
    /// is reached, even over no items (a user `sum` may panic before reading
    /// one), so the violation is the freed flag alone.
    fn unmodeled_impl(flag: Expr) -> Self {
        Self {
            exact: None,
            unchecked: flag,
            kind: PropertyKind::Panic,
            message: SUM_IMPL_UNMODELED_MESSAGE,
        }
    }

    /// Kani's "NaN on addition" over partial sums this lane cannot compute:
    /// a step adds two values only when the iterator has an item, so the
    /// violation is `has_remaining` and the freed flag.
    fn float_nan(has_remaining: Expr, flag: Expr) -> Self {
        Self {
            exact: None,
            unchecked: has_remaining.and(flag),
            kind: PropertyKind::Other,
            message: SUM_NAN_MESSAGE,
        }
    }
}

/// Kani's description of the NaN check on a float add (CBMC `--nan-check`).
const SUM_NAN_MESSAGE: &str = "NaN on addition";

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn try_advance_or_symbolic_remaining(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        fallback_reason: &'static str,
    ) -> Expr {
        if let Some(has_remaining) = self
            .iterator_receiver_expr_and_local(args, modified_locals)
            .and_then(|(iter_expr, _)| {
                self.advance_iterator_expr(&iter_expr).map(|(_, has_remaining)| has_remaining)
            })
        {
            has_remaining
        } else {
            self.record_sound_fallback_reason(fallback_reason);
            self.fresh_adapter_symbol("iter_has_remaining", bool_sort())
        }
    }

    fn try_precise_try_fold_success_result(
        &mut self,
        args: &[Operand],
        dest_local: usize,
        dest_vec_idx: usize,
        init_expr: &Expr,
        has_remaining: &Expr,
        out_sort: &Sort,
    ) -> Option<(Option<Expr>, Option<Vec<Option<Expr>>>)> {
        let closure_body =
            resolve_try_fold_closure_body_for_operand(args.get(2)?, self.body.locals())?;
        if !closure_returns_option_like_success(&closure_body) {
            return None;
        }

        if self.flatten.flattened_tuple_locals.contains(&dest_local)
            && self.flatten.flattened_enum_discr.contains_key(&dest_local)
        {
            let field_count = self.flattened_field_count(dest_local);
            let mut fields = vec![None; field_count];
            let (true_discr, _) = self.flatten.flattened_enum_discr[&dest_local];
            let discr_sort = &self.state_var_mgr.output_state_vars.get(dest_vec_idx)?.1;
            fields[0] = if discr_sort.is_bool() {
                Some(Expr::bool_const(true))
            } else {
                discr_sort.bitvec_width().map(|width| Expr::bitvec_const(true_discr, width))
            };

            if field_count > 1 {
                let payload_sort =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx + 1)?.1.to_owned();
                let init_payload =
                    self.coerce_value_to_sort(init_expr.to_owned(), &payload_sort, false)?;
                let symbolic_payload = self.fresh_adapter_symbol("iter_try_fold_acc", payload_sort);
                fields[1] =
                    Some(Expr::ite(has_remaining.to_owned(), symbolic_payload, init_payload));
            }
            return Some((None, Some(fields)));
        }

        let payload_sort = option_value_sort(out_sort)?;
        let init_payload = self.coerce_value_to_sort(init_expr.to_owned(), &payload_sort, false)?;
        let symbolic_payload = self.fresh_adapter_symbol("iter_try_fold_acc", payload_sort);
        let payload = Expr::ite(has_remaining.to_owned(), symbolic_payload, init_payload);
        Some((self.make_some_expr_for_option(payload, out_sort), None))
    }

    /// Fold FOR REAL: replay the user closure once per element.
    ///
    /// Returns the folded accumulator, the coverage condition, the chain's
    /// defining constraints and every replayed step's obligations (the walked
    /// closure's checks) when the element sequence is addressable AND the
    /// closure body could be replayed for every step. The caller keeps its
    /// previous over-approximation on the `!fully_covered` side, so this lane
    /// can only add precision.
    ///
    /// The closure's checks used to be dropped here (the value-only walk,
    /// which then failed the harness closed for any closure with a check):
    /// they are the step's obligations, and the host emits them under each
    /// step's range condition.
    fn try_precise_fold(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        init_expr: &Expr,
        acc_sort: &Sort,
    ) -> Option<PreciseReduction> {
        let closure_body =
            resolve_try_fold_closure_body_for_operand(args.get(2)?, self.body.locals())?;
        // As for a sum: a receiver traced to an array is replayed whole
        // (`static_iter_len_bound`; coverage stays the program's own `len`).
        let min_bound = args.first().and_then(|receiver| self.static_iter_len_bound(receiver));
        let reduction = self.precise_reduce_chain(
            args,
            modified_locals,
            init_expr,
            acc_sort,
            min_bound,
            |ctx, acc, elem, _in_range| {
                // Closure locals: 0 = return, 1 = environment, 2 = accumulator,
                // 3 = item. An empty capture list fails CLOSED — a capturing
                // closure leaves its local unresolved and the walk returns None,
                // abandoning the whole chain rather than folding a wrong value.
                let params = [acc.clone(), elem.clone()];
                if let Some(walked) =
                    translate_closure_inline_result(ctx, &closure_body, &params, &[], 0, 0)
                {
                    // A closure that assumes or writes through a reference is
                    // not a value step: abandon the chain.
                    if extract_inline_assume_guard(&walked.value).is_some()
                        || !walked.alias_updates.is_empty()
                    {
                        return None;
                    }
                    // A path that panics leaves `__assert_fail_inline` in the
                    // value; its guard's deferred-check twin is the step's
                    // obligation, so the value keeps the other paths.
                    let value =
                        strip_inline_assert_fallback(&walked.value).unwrap_or_else(|| acc.clone());
                    return Some(ReductionStep { value, checks: walked.deferred_checks });
                }
                translate_closure_body_with_params(ctx, &closure_body, &params, &[], 0).map(
                    |ClosureBodyResult { pred, no_panic_guard }| {
                        // The replay keeps only the value: an Assert guard the
                        // closure carries (`acc + x` overflow, a user
                        // `assert!`) has no error rule here, so fail closed
                        // rather than drop it.
                        if no_panic_guard.as_ref().is_some_and(|guard| {
                            !crate::codegen_ay::chc::call::inline_shared::check_is_trivially_valid(
                                guard,
                            )
                        }) {
                            ctx.record_sound_fallback_reason("iter_fold_closure_guard_dropped");
                        }
                        ReductionStep { value: pred, checks: Vec::new() }
                    },
                )
            },
        )?;
        debug!("iter fold: precise per-element replay emitted (fold folds)");
        Some(reduction)
    }

    /// Can the closure a reduction is handed (`args[2]`) carry an obligation
    /// the walker would check if it replayed a step (`obligation_free_walk::
    /// instance_obligation_verdict` is not `Free`)? `true` when the closure
    /// does not resolve.
    fn reduce_closure_may_carry_obligation(&self, args: &[Operand]) -> bool {
        let Some((instance, _)) = args
            .get(2)
            .and_then(|closure| resolve_reduce_closure_for_operand(closure, self.body.locals()))
        else {
            return true;
        };
        let stubs = crate::kani_middle::transform::walker_stub_map();
        crate::codegen_ay::obligation_free_walk::instance_obligation_verdict(
            self.tcx, instance, &stubs,
        ) != crate::codegen_ay::obligation_free_walk::Verdict::Free
    }

    /// An uncertified reach check (`uncertified_check.rs`): `t` under
    /// `¬runs`, where `runs` is the condition under which a step the model
    /// does not replay executes. Fails exactly where such a step can run,
    /// never certified.
    fn unreplayed_step_check(
        &mut self,
        runs: Expr,
        kind: PropertyKind,
        message: String,
    ) -> DeferredInlineCheck {
        let t = super::super::codegen_call_virtual_inline::uncertified_check::uncertified_reach_check(
            self,
            super::super::codegen_call_virtual_inline::uncertified_check::ITER_REDUCE_STEP_UNCERTIFIED,
        );
        DeferredInlineCheck {
            check: runs.not().or(t),
            kind,
            message: Some(message),
            write_mark: self.heap_state.write_mark(),
            merge_key: None,
        }
    }

    /// Kani's unwinding assertion on the std loop a reduction runs, under a
    /// declared unwind bound with unwinding assertions on.
    ///
    /// With the precise chain (`unwinding`), the check fails exactly where
    /// Kani's does for a measured iterator shape, and is an uncertified
    /// reach check under `R >= U` for any other
    /// ([`super::fold_precise::ReduceUnwinding`]). Without it (`None`), the
    /// number of elements is unknown: the reach check fails wherever the
    /// iterator is not empty (`has_remaining`), unless a static bound on the
    /// elements (`iterator_count_upper_bound`) keeps the loop within `U`
    /// under the receiver's rule (`rule`; `try_fold` passes `None`, the
    /// conservative one). Nothing stated this failure: the reduction's value
    /// is sound either way, but a harness whose only failing check is Kani's
    /// unwinding assertion verified clean (walker fail-closed review 6
    /// round 2, finding 1).
    fn push_reduce_unwinding_check(
        &mut self,
        args: &[Operand],
        rule: Option<ReduceLoopRule>,
        unwinding: Option<ReduceUnwinding>,
        has_remaining: &Expr,
        reduce_checks: &mut Vec<DeferredInlineCheck>,
    ) {
        if self.recursive_unwind_depth == 0 || !self.unwinding_assertions {
            return;
        }
        if unwinding.is_none() {
            let unwind = u64::from(self.recursive_unwind_depth);
            let bounded = args
                .first()
                .and_then(|receiver| match receiver {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        self.iterator_count_upper_bound(place.local)
                    }
                    _ => None,
                })
                .is_some_and(|bound| ReduceLoopRule::holds_up_to(rule, bound, unwind));
            if bounded {
                return;
            }
        }
        let check = match unwinding {
            Some(ReduceUnwinding { fails, exact: true, .. }) => DeferredInlineCheck {
                check: fails.not(),
                kind: PropertyKind::Other,
                message: Some(REDUCE_UNWINDING_MESSAGE.to_string()),
                write_mark: self.heap_state.write_mark(),
                merge_key: None,
            },
            Some(ReduceUnwinding { fails, exact: false, .. }) => {
                self.unreplayed_unwinding_check(fails)
            }
            None => self.unreplayed_unwinding_check(has_remaining.clone()),
        };
        reduce_checks.push(check);
    }

    /// The uncertified form of [`Self::push_reduce_unwinding_check`]: `t`
    /// under `¬runs` (`uncertified_check.rs`).
    fn unreplayed_unwinding_check(&mut self, runs: Expr) -> DeferredInlineCheck {
        let t = super::super::codegen_call_virtual_inline::uncertified_check::uncertified_reach_check(
            self,
            super::super::codegen_call_virtual_inline::uncertified_check::ITER_REDUCE_UNWIND_UNCERTIFIED,
        );
        DeferredInlineCheck {
            check: runs.not().or(t),
            kind: PropertyKind::Other,
            message: Some(REDUCE_UNWINDING_MESSAGE.to_string()),
            write_mark: self.heap_state.write_mark(),
            merge_key: None,
        }
    }

    /// Sum FOR REAL: `acc + elem` per element, same coverage contract as
    /// [`Self::try_precise_fold`]. Integers only (`SumSummand::Int` /
    /// `WrappingInt` / `SaturatingUint`): the CHC lane has no FP theory, so a
    /// float sum is never replayed here.
    ///
    /// For an overflow-checked integer (`SumStep::Checked`) the replay also
    /// returns the disjunction, over the replayed steps, of "this step is taken
    /// and its `acc + elem` overflows" — std's integer `Sum` adds under
    /// `#[rustc_inherit_overflow_checks]`, so that is an "attempt to add with
    /// overflow" the stub must report. A saturating step
    /// (`SumStep::Saturating`) is `ite(carry, all ones, acc + elem)` over the
    /// same checked-add encoding's carry, and reports nothing.
    ///
    /// The replay runs at least as many steps as the receiver can have
    /// elements when that count is static (`static_iter_len_bound`, capped at
    /// `MAX_REDUCE_BOUND`): a constant-length sum is then fully covered and its
    /// conservative overflow rule is unreachable (AY alignment round 8, review
    /// round 3, finding 3: `[20u8; 12].iter().sum()` could not be proved).
    fn try_precise_sum(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        zero: &Expr,
        acc_sort: &Sort,
        sum_step: SumStep,
    ) -> Option<(PreciseReduction, Option<Expr>)> {
        if acc_sort.bitvec_width().is_none() {
            return None;
        }
        let min_bound = args.first().and_then(|receiver| self.static_iter_len_bound(receiver));
        let mut overflows: Vec<Expr> = Vec::new();
        let reduction = self.precise_reduce_chain(
            args,
            modified_locals,
            zero,
            acc_sort,
            min_bound,
            |ctx, acc, elem, in_range| {
                let elem = ctx.coerce_value_to_sort(elem.clone(), acc.sort(), true)?;
                let signed = match sum_step {
                    SumStep::Wrapping => {
                        return Some(ReductionStep {
                            value: acc.clone().bvadd(elem),
                            checks: Vec::new(),
                        });
                    }
                    SumStep::Checked { signed } => signed,
                    SumStep::Saturating => false,
                };
                // The lane's own encoding of a checked `a + b`
                // (`checked_binop_result_overflow`): the explicit sign/carry
                // comparisons it emits fold on constants, so the straight-line
                // discharge proves a sum of known elements as it proves the
                // program's own adds. `bvadd_no_overflow_*` has a node of its
                // own that the discharge does not fold, and with it a sum of
                // `[20u8; 2]` that main proved in 5 ms went to the solver and
                // timed out under load (AY alignment round 8, review round 3).
                let width = acc.sort().bitvec_width()?;
                let (sum, overflow) = ChcCtx::checked_binop_result_overflow(
                    rustc_public::mir::BinOp::Add,
                    acc.clone(),
                    elem,
                    signed,
                    width,
                    false,
                )?;
                if sum.sort() != acc.sort() {
                    return None;
                }
                if sum_step == SumStep::Saturating {
                    // `uN::saturating_add`: the unsigned carry of `acc + elem`
                    // saturates to `uN::MAX` (all ones).
                    let value = Expr::ite(overflow, Expr::bitvec_const(-1i128, width), sum);
                    return Some(ReductionStep { value, checks: Vec::new() });
                }
                overflows.push(in_range.clone().and(overflow));
                Some(ReductionStep { value: sum, checks: Vec::new() })
            },
        )?;
        let overflow = matches!(sum_step, SumStep::Checked { .. }).then(|| {
            overflows.into_iter().reduce(Expr::or).unwrap_or_else(|| Expr::bool_const(false))
        });
        debug!("iter sum: precise per-element replay emitted (sum sums)");
        Some((reduction, overflow))
    }

    /// A sum value the stub cannot compute: a fresh, universally quantified
    /// variable of `sort`, minted by Rule E's [`Havoc::mint`] under the audited
    /// reason `iter_sum_value_overapprox` and booked nowhere else.
    ///
    /// It used to be [`Self::fresh_adapter_symbol`] when that booked only an
    /// `aggregate_gap`, which never reached the driver's counterexample
    /// classification: a havocked reduction that refuted a safe assertion was
    /// certified Genuine (AY alignment review round 2, CHC lane, all Kani
    /// SUCCESSFUL: `[1u32; 12].iter().sum() == 12`, a symbolic-length `a[..n]`
    /// sum, `[1.5f32, 2.25].iter().sum() == 3.75`). `fresh_adapter_symbol` now
    /// books an identified havoc too, and still counts the function's
    /// `aggregate_encoding_gap` beside it; this one does not. A proof over the
    /// variable stays a proof; a counterexample that reads it is demoted, and
    /// one independent of it can be certified.
    fn reduce_havoc(&mut self, prefix: &str, sort: Sort) -> Expr {
        Havoc::mint(self, sound_havoc::ITER_SUM_VALUE_OVERAPPROX, chc_fresh_name(prefix), sort)
    }

    /// A fresh boolean that lets a conservative rule of an iterator call fire
    /// (see [`ReducePanicObligation::unchecked`]), minted by [`Havoc::mint`]
    /// under the audited `reason`. It occurs in that rule alone and can always be
    /// true, so the rule is reachable exactly when its guard is; because the
    /// violated check READS it, the driver never certifies a counterexample
    /// through that rule Genuine.
    pub(super) fn iter_conservative_flag(&mut self, reason: SoundHavocReason) -> Expr {
        Havoc::mint(self, reason, chc_fresh_name(reason.as_str()), bool_sort())
    }

    /// The `IterSum` arm: value, plus the panic obligation of the sum (an
    /// integer sum's overflow, or any panic of an impl the stub does not
    /// model).
    #[allow(clippy::too_many_arguments)]
    fn codegen_sum_arm(
        &mut self,
        func: Option<&Operand>,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        destination: &Place,
        dest_vec_idx: usize,
        extra_constraints: &mut Vec<Expr>,
        panic_obligation: &mut Option<ReducePanicObligation>,
        reduce_checks: &mut Vec<DeferredInlineCheck>,
    ) -> Option<Expr> {
        // The dispatch's model of the impl (`reduce_loop_rule::iter_sum_model`)
        // is read once per call; this arm classifies the same callee operand
        // itself (`classify_iter_sum`), which also names its width and
        // signedness, so the hint is only cleared here.
        let _ = self.pending_iter_sum_model.take();
        if args.is_empty() {
            return None;
        }
        let (_, out_sort) = self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()?;
        // From THIS call's callee operand: the arms of an `if`/`match` that
        // each end in `.sum()` write one place.
        let summand = func
            .map_or(SumSummand::Unknown, |func| classify_iter_sum(self.body, func, destination));
        // What the impl can PANIC on is the impl's: only an unclassified impl
        // gets the conservative rule. Whether its VALUE can be encoded is the
        // destination sort's (an Int sort under `--ay-chc-int-lift`, say): a
        // sort the summand does not fit havocs the value, and the impl's own
        // obligation below still applies (round 8, review round 4, finding 1).
        if summand == SumSummand::Unknown {
            let flag = self.iter_conservative_flag(sound_havoc::ITER_SUM_IMPL_UNMODELED);
            *panic_obligation = Some(ReducePanicObligation::unmodeled_impl(flag));
        }
        let encoded =
            if out_sort.bitvec_width() == summand.width() { summand } else { SumSummand::Unknown };
        let identity = encoded.identity_bits().map(|(bits, width)| Expr::bitvec_const(bits, width));
        let has_remaining = self.try_advance_or_symbolic_remaining(
            args,
            modified_locals,
            // Part of #3447: Iterator advance failed — has_remaining
            // is fully symbolic, making sum result nondeterministic.
            "iter_sum_advance_failed",
        );
        if self.nan_checks && matches!(summand, SumSummand::Float { .. }) {
            let flag = self.iter_conservative_flag(sound_havoc::ITER_SUM_NAN_UNCHECKED);
            *panic_obligation = Some(ReducePanicObligation::float_nan(has_remaining.clone(), flag));
        }
        let havoc = self.reduce_havoc("iter_sum_value", out_sort.clone());
        // The empty sum is the impl's identity when it is known; for an impl
        // the stub does not know, the empty case is havocked too.
        let overapprox = match &identity {
            Some(identity) => Expr::ite(has_remaining.clone(), havoc, identity.clone()),
            None => havoc,
        };
        let overflow_signedness = match summand {
            SumSummand::Int { signed, .. } if self.overflow_checks => Some(signed),
            _ => None,
        };
        let sum_step = match (encoded, overflow_signedness) {
            (SumSummand::Int { .. }, Some(signed)) => Some(SumStep::Checked { signed }),
            (SumSummand::Int { .. } | SumSummand::WrappingInt { .. }, None) => {
                Some(SumStep::Wrapping)
            }
            (SumSummand::SaturatingUint { .. }, _) => Some(SumStep::Saturating),
            _ => None,
        };
        let replay = match (sum_step, &identity) {
            (Some(sum_step), Some(zero)) => {
                self.try_precise_sum(args, modified_locals, zero, &out_sort, sum_step)
            }
            _ => None,
        };
        let sum_rule = self.reduce_receiver_loop_rule(args);
        let summed = match replay {
            Some((reduction, step_overflow)) => {
                extra_constraints.extend(reduction.constraints);
                reduce_checks.extend(reduction.step_checks);
                let covered = reduction.fully_covered;
                // Under a measured unwinding rule a chain of at least `U`
                // steps replays every step Kani runs: a step past it runs only
                // after the unwinding assertion failed, which ends Kani's path
                // (`ReduceUnwinding::covers_unreplayed`).
                let unwinding_covers = reduction
                    .unwinding
                    .as_ref()
                    .is_some_and(|unwinding| unwinding.covers_unreplayed);
                if overflow_signedness.is_some() {
                    let unchecked = if unwinding_covers || is_true_literal(&covered) {
                        Expr::bool_const(false)
                    } else {
                        let flag =
                            self.iter_conservative_flag(sound_havoc::ITER_SUM_OVERFLOW_UNCHECKED);
                        covered.clone().not().and(flag)
                    };
                    *panic_obligation =
                        Some(ReducePanicObligation::add_overflow(step_overflow, unchecked));
                }
                self.push_reduce_unwinding_check(
                    args,
                    sum_rule,
                    reduction.unwinding,
                    &has_remaining,
                    reduce_checks,
                );
                // A chain that provably covers every element is the value;
                // only a partial one needs the over-approximated remainder.
                if is_true_literal(&covered) {
                    reduction.acc
                } else {
                    Expr::ite(covered, reduction.acc, overapprox)
                }
            }
            None => {
                if overflow_signedness.is_some() {
                    let flag =
                        self.iter_conservative_flag(sound_havoc::ITER_SUM_OVERFLOW_UNCHECKED);
                    *panic_obligation = Some(ReducePanicObligation::add_overflow(
                        None,
                        has_remaining.clone().and(flag),
                    ));
                }
                self.push_reduce_unwinding_check(
                    args,
                    sum_rule,
                    None,
                    &has_remaining,
                    reduce_checks,
                );
                overapprox
            }
        };
        Some(summed)
    }

    /// Handle IterFold and IterSum reduction arms.
    ///
    /// `func` is the call's own callee operand. `panic_obligation` receives
    /// the panic obligation of an `IterSum` (`ReducePanicObligation`) and
    /// `reduce_checks` every replayed step's and unreplayed step's checks and
    /// the unwinding assertion; the caller turns both into error rules.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::codegen_ay::chc) fn codegen_reduce_arm(
        &mut self,
        stub: StubKind,
        func: Option<&Operand>,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        destination: &Place,
        dest_vec_idx: usize,
        extra_constraints: &mut Vec<Expr>,
        panic_obligation: &mut Option<ReducePanicObligation>,
        reduce_checks: &mut Vec<DeferredInlineCheck>,
    ) -> (Option<Expr>, Option<Vec<Option<Expr>>>) {
        let dest_local = destination.local;
        match stub {
            StubKind::IterFold => {
                if args.len() >= 2
                    && let Some(init_expr) = self
                        .translate_operand_with_modified(&args[1], modified_locals)
                        .or_else(|| self.resolve_ref_operand(&args[1], modified_locals))
                {
                    let has_remaining = self.try_advance_or_symbolic_remaining(
                        args,
                        modified_locals,
                        // Part of #3447: Iterator advance failed — has_remaining
                        // is fully symbolic, making fold result nondeterministic.
                        "iter_fold_advance_failed",
                    );
                    // Check if the destination sort differs from init sort.
                    // This happens for try_fold which returns Result<B,E> or
                    // ControlFlow while init is just B. In that case, use the
                    // destination output sort for a fully symbolic result
                    // (sound over-approximation).
                    let dest_sort = self
                        .state_var_mgr
                        .output_state_vars
                        .get(dest_vec_idx)
                        .map(|(_, s)| s.to_owned());
                    let init_sort = init_expr.sort().to_owned();
                    // Where a step is not replayed, the value is over-
                    // approximated, which is sound for the value and drops
                    // the step's obligations: a closure that can carry one
                    // records an uncertified reach check under the condition
                    // that such a step runs (`unreplayed_step_check`). A
                    // `try_fold` closure is never walked, and a `fold`
                    // closure the walker could not walk used to lose its
                    // `assert!` here with a blessed `iter_fold_value`
                    // (tools/soundness-duals/iter_reduce_obligation_dual.rs).
                    let closure_may_fail = self.reduce_closure_may_carry_obligation(args);
                    let unreplayed = "an iterator `fold`/`try_fold` step the CHC encoder does \
                                      not replay can fail its closure's checks";
                    if let Some(ref out_sort) = dest_sort
                        && let Some(success_result) = self.try_precise_try_fold_success_result(
                            args,
                            dest_local,
                            dest_vec_idx,
                            &init_expr,
                            &has_remaining,
                            out_sort,
                        )
                    {
                        if closure_may_fail {
                            reduce_checks.push(self.unreplayed_step_check(
                                has_remaining.clone(),
                                PropertyKind::Assertion,
                                unreplayed.to_string(),
                            ));
                        }
                        self.push_reduce_unwinding_check(
                            args,
                            None,
                            None,
                            &has_remaining,
                            reduce_checks,
                        );
                        return success_result;
                    }
                    if let Some(ref out_sort) = dest_sort
                        && *out_sort != init_sort
                    {
                        // try_fold: destination sort wraps the accumulator.
                        // When the closure may return a residual, keep the
                        // existing sound over-approximation.
                        let symbolic_result =
                            self.fresh_adapter_symbol("iter_try_fold_value", out_sort.to_owned());
                        if closure_may_fail {
                            reduce_checks.push(self.unreplayed_step_check(
                                has_remaining.clone(),
                                PropertyKind::Assertion,
                                unreplayed.to_string(),
                            ));
                        }
                        self.push_reduce_unwinding_check(
                            args,
                            None,
                            None,
                            &has_remaining,
                            reduce_checks,
                        );
                        (Some(symbolic_result), None)
                    } else {
                        let fold_rule = self.reduce_receiver_loop_rule(args);
                        let folded = match self
                            .try_precise_fold(args, modified_locals, &init_expr, &init_sort)
                        {
                            Some(reduction) => {
                                extra_constraints.extend(reduction.constraints);
                                reduce_checks.extend(reduction.step_checks);
                                let unwinding_covers = reduction
                                    .unwinding
                                    .as_ref()
                                    .is_some_and(|unwinding| unwinding.covers_unreplayed);
                                if closure_may_fail && !unwinding_covers {
                                    reduce_checks.push(self.unreplayed_step_check(
                                        reduction.fully_covered.clone().not(),
                                        PropertyKind::Assertion,
                                        unreplayed.to_string(),
                                    ));
                                }
                                self.push_reduce_unwinding_check(
                                    args,
                                    fold_rule,
                                    reduction.unwinding,
                                    &has_remaining,
                                    reduce_checks,
                                );
                                // A chain that provably covers every element
                                // is the value; only a partial one needs the
                                // over-approximated remainder.
                                if is_true_literal(&reduction.fully_covered) {
                                    reduction.acc
                                } else {
                                    let symbolic_result = self
                                        .fresh_adapter_symbol("iter_fold_value", init_sort.clone());
                                    let overapprox = Expr::ite(
                                        has_remaining.clone(),
                                        symbolic_result,
                                        init_expr.clone(),
                                    );
                                    Expr::ite(reduction.fully_covered, reduction.acc, overapprox)
                                }
                            }
                            None => {
                                if closure_may_fail {
                                    reduce_checks.push(self.unreplayed_step_check(
                                        has_remaining.clone(),
                                        PropertyKind::Assertion,
                                        unreplayed.to_string(),
                                    ));
                                }
                                self.push_reduce_unwinding_check(
                                    args,
                                    fold_rule,
                                    None,
                                    &has_remaining,
                                    reduce_checks,
                                );
                                let symbolic_result =
                                    self.fresh_adapter_symbol("iter_fold_value", init_sort.clone());
                                Expr::ite(has_remaining.clone(), symbolic_result, init_expr.clone())
                            }
                        };
                        (Some(folded), None)
                    }
                } else {
                    // No initial value to fold from: the stub encodes no step,
                    // so a closure that can carry an obligation stands for its
                    // checks wherever the call is reached.
                    if self.reduce_closure_may_carry_obligation(args) {
                        reduce_checks.push(self.unreplayed_step_check(
                            Expr::bool_const(true),
                            PropertyKind::Assertion,
                            "an iterator `fold`/`try_fold` step the CHC encoder does not replay \
                             can fail its closure's checks"
                                .to_string(),
                        ));
                    }
                    (None, None)
                }
            }
            StubKind::IterSum => (
                self.codegen_sum_arm(
                    func,
                    args,
                    modified_locals,
                    destination,
                    dest_vec_idx,
                    extra_constraints,
                    panic_obligation,
                    reduce_checks,
                ),
                None,
            ),
            _other => (None, None), // partial dispatch: StubKind
        }
    }
}

/// `a.saturating_add(b)` over bitvectors of one width: the sum where it does
/// not overflow, else the bound the overflow runs past (the type's maximum,
/// or for a signed add of a negative `b`, its minimum).
///
/// The sum stub's own saturating step is `SumStep::Saturating` (the checked-add
/// carry the straight-line discharge folds); this is kept for its tests.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay::chc) fn saturating_add(a: &Expr, b: &Expr, signed: bool) -> Option<Expr> {
    let width = a.sort().bitvec_width()?;
    if b.sort().bitvec_width()? != width || width == 0 || width > 128 {
        return None;
    }
    let sum = a.clone().bvadd(b.clone());
    if !signed {
        // Unsigned: overflow exactly when the sum wraps below `a`.
        let max = Expr::bitvec_const(u128::MAX >> (128 - width), width);
        return Some(Expr::ite(sum.clone().bvult(a.clone()), max, sum));
    }
    // Signed: overflow exactly when `a` and `b` share a sign the sum lacks.
    let zero = Expr::bitvec_const(0u64, width);
    let a_neg = a.clone().bvslt(zero.clone());
    let b_neg = b.clone().bvslt(zero.clone());
    let s_neg = sum.clone().bvslt(zero);
    let overflow = a_neg.clone().eq(b_neg.clone()).and(s_neg.eq(a_neg).not());
    let min = Expr::bitvec_const(1u128 << (width - 1), width);
    let max = Expr::bitvec_const((1u128 << (width - 1)) - 1, width);
    Some(Expr::ite(overflow, Expr::ite(b_neg, min, max), sum))
}

/// Is `expr` the literal `true`?
fn is_true_literal(expr: &Expr) -> bool {
    matches!(expr.value(), ay_bindings::ExprValue::BoolConst(true))
}

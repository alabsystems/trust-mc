// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SwitchInt translation into nested ITE expressions.
//!
//! Part of #3188: SwitchInt support for inline translators.
//! Part of #3639: Extracted from codegen_call_virtual_inline.rs.

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc, sound_havoc};
use ay_bindings::Expr;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::chc_fresh_name;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::DeferredInlineCheck;
use super::super::inline_shared::inline_operand_to_expr;
use super::execution_state::InlineExecutionState;
use super::walker::{InlineWalkCtx, walk_blocks_to_return};
use super::{InlineReturn, MAX_SWITCHINT_DEPTH, switchint_walk_node_budget};

/// Produce a fresh symbolic InlineReturn when a SwitchInt branch walk bails.
///
/// Sound over-approximation: the branch result is unconstrained. This
/// prevents a single failing branch from killing the entire SwitchInt ITE
/// chain. The return sort is derived from the body's return local (local 0).
///
/// Part of #4031: SwitchInt resilience for methods with nested call failures.
/// Part of #4050: edge-keyed caching — reuse the same symbolic variable for
/// repeated walks of the same (switchint_bb, target_bb) edge across loop replay
/// iterations. Reduces O(iterations × edges) to O(unique_edges).
/// The cache key uses the callee-local `switchint_bb` (the basic block
/// containing this SwitchInt terminator) as the site identifier. This is
/// precise per-site, unlike the earlier `walk_ctx.bb_idx` which was the outer
/// call-site block and could not distinguish two different SwitchInt sites
/// in the same callee body.
fn switchint_branch_fallback<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    switchint_bb: usize,
    target_bb: usize,
    at_entry: &HashMap<usize, Expr>,
    entry_path_guard: Option<&Expr>,
) -> Option<InlineReturn> {
    // Under a declared unwind bound the region's loops are obligations too
    // (`uncertified_check::region_may_fail_unwinding_assertion`): Kani's
    // unwinding assertion does not hold for every argument, whoever owns the
    // loop. (The branch's value-havoc exemption for an arm inside a
    // "contained" foreign function is not kept: Rule D reads one predicate at
    // this site, and a std function's internal checks do fail once unsafe
    // code has broken an invariant of its argument.)
    let may_fail_unwinding =
        super::uncertified_check::region_may_fail_unwinding_assertion(ctx, walk_ctx, target_bb);
    // Mechanism C (docs/chc-walker-missed-bugs-2026-09-23.md): the checks the
    // arm would have recorded went with its walk. When the region the arm
    // abandons can carry an obligation
    // (`uncertified_check::region_may_carry_obligation`), every such
    // obligation lies on paths through this arm, so the arm is recorded as a
    // check that fails wherever it is taken, never certified: `t` under the
    // entry path condition here, composed with the arm's own guard at the
    // merge below like any of its checks. Recorded on every occurrence: each
    // is a different path.
    //
    // Such a path has FAILED wherever it is feasible, so it also ENDS there
    // (package round 2 item b): the arm's value is the assume-pruned marker
    // (`pruned_path_return`), not a freed havoc. A counterexample that
    // reaches the arm fails the reach check, uncertified, as before; one that
    // does not (a walked loop that finishes within the replay, the arm being
    // the paths past it) no longer reads a freed value through the merged
    // result, so it can be certified. Nothing on the path after the arm reads
    // the lost writes either, so the lost-write record is not needed.
    //
    // Under a declared unwind bound the region's loops are obligations too:
    // Kani's unwinding assertion, which the abandoned passes would have met
    // (`uncertified_check::region_may_fail_unwinding_assertion`).
    if may_fail_unwinding
        || super::uncertified_check::region_may_carry_obligation(ctx, walk_ctx.body, target_bb)
    {
        debug!(
            switchint_bb,
            target_bb,
            may_fail_unwinding,
            "virtual body: bailed SwitchInt arm can carry an obligation — reach check"
        );
        // One freed `t` per abandoned edge, and one merge key: the walk
        // reaches the same edge on many paths (every branch combination of a
        // loop body that runs into the SwitchInt depth limit), and a check and
        // a fresh variable per path made thousands of both (2048 on a loop with
        // two `if`s under `unwind(6)`, which the solver could no longer parse).
        // The per-path checks are still recorded, each under its own path
        // condition; the SwitchInt merges join them (`merge_keyed_arm_checks`).
        let edge = (switchint_bb, target_bb);
        let cached = walk_ctx.bailed_arm_reach_cache.borrow().get(&edge).cloned();
        let reached = cached.unwrap_or_else(|| {
            let reached = super::uncertified_check::uncertified_reach_check(
                ctx,
                super::uncertified_check::WALKER_BAILED_ARM_OBLIGATION,
            );
            walk_ctx.bailed_arm_reach_cache.borrow_mut().insert(edge, reached.clone());
            reached
        });
        let check = match entry_path_guard {
            Some(guard) => guard.clone().not().or(reached.clone()),
            None => reached.clone(),
        };
        let callee =
            super::current_inline_callee_name(ctx).unwrap_or_else(|| "<walked body>".to_string());
        let merge_key = match reached.value() {
            ay_bindings::ExprValue::Var { name } => Some(format!("bailed-arm:{name}")),
            _ => None,
        };
        let cached_pruned = walk_ctx.bailed_arm_pruned_cache.borrow().get(&edge).cloned();
        let mut result = match cached_pruned {
            Some(pruned) => InlineReturn::value_only(pruned),
            None => {
                let result = pruned_path_return(
                    ctx,
                    walk_ctx,
                    InlineExecutionState::new(HashMap::new(), HashMap::new(), HashSet::new()),
                )?;
                walk_ctx.bailed_arm_pruned_cache.borrow_mut().insert(edge, result.value.clone());
                result
            }
        };
        result.deferred_checks.push(DeferredInlineCheck {
            check,
            kind: PropertyKind::Other,
            message: Some(if may_fail_unwinding {
                format!(
                    "{} (abandoned branch bb{target_bb} of `{callee}`, which can fail an \
                     unwinding assertion loop)",
                    super::host_bound_discharge::WALKER_BAILED_ARM_REACH_MESSAGE
                )
            } else {
                format!(
                    "{} (abandoned branch bb{target_bb} of `{callee}`)",
                    super::host_bound_discharge::WALKER_BAILED_ARM_REACH_MESSAGE
                )
            }),
            write_mark: ctx.heap_state.write_mark(),
            merge_key,
        });
        return Some(result);
    }
    let mut result = switchint_branch_fallback_value(ctx, walk_ctx, switchint_bb, target_bb)?;
    // Rule D (design trust-mc-reds-final §4.1; the lost-write record of
    // docs/chc-hole-fix-designs-2026-09-24.md section 2): the arm's checks and
    // writes are replaced by nothing — its heap effects were rolled back, its
    // asserts never reach the check list, and the merge fills its side of
    // every alias update with the entry value. The arm's sighted obligations
    // took the reach check above; when the region can still check (an
    // obligation walk that could not tell) or write, that is a lost
    // obligation: the harness fails closed, and every `&mut` / `*mut`
    // argument's pointee is havocked on this arm.
    // A check the walker's interval facts prove holds on every path is no
    // lost obligation (`region_intervals.rs`, the facts the reach-check scan
    // above discharges with): only the region's other checks, an obligation
    // walk that could not tell, and its writes book the lost effect.
    let intervals = super::region_intervals::BodyIntervals::analyse(walk_ctx.body, |ty| {
        ctx.resolve_body_ty(ty)
    });
    // Only a plain arithmetic, index or `assume` statement: its obligations
    // are the ones the facts discharge, and nothing else in it is unread
    // (no cast, aggregate or call whose verdict could also be "could not tell").
    let statement_discharged = |stmt: &rustc_public::mir::Statement| {
        use rustc_public::mir::{NonDivergingIntrinsic, Rvalue, StatementKind};
        let plain = match &stmt.kind {
            StatementKind::Assign(_, rvalue) => matches!(
                rvalue,
                Rvalue::BinaryOp(..)
                    | Rvalue::CheckedBinaryOp(..)
                    | Rvalue::UnaryOp(..)
                    | Rvalue::Use(..)
                    | Rvalue::Ref(..)
                    | Rvalue::CopyForDeref(..)
                    | Rvalue::Len(..)
                    | Rvalue::Discriminant(..)
            ),
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_)) => true,
            _ => false,
        };
        plain && intervals.statement_obligations_discharged(stmt)
    };
    let assert_holds = |cond: &Operand, expected: bool| intervals.assert_holds(cond, expected);
    let discharge = crate::codegen_ay::obligation_free_walk::RegionDischarge {
        statement: &statement_discharged,
        assert_holds: &assert_holds,
    };
    if super::super::inline_walk_guard::region_may_check_or_write_discharging(
        ctx,
        walk_ctx.body,
        target_bb,
        Some(&discharge),
    ) {
        debug!(
            switchint_bb,
            target_bb, "virtual body: bailed SwitchInt arm can check or write — fail closed"
        );
        let booked = super::super::inline_walk_guard::record_lost_obligation(
            ctx,
            super::super::inline_walk_guard::LostEffect::BailedArm,
        );
        for local in 1..=walk_ctx.body.arg_locals().len() {
            let writable = walk_ctx.locals.get(local).is_some_and(|decl| {
                matches!(
                    ctx.resolve_body_ty(decl.ty).kind(),
                    rustc_public::ty::TyKind::RigidTy(
                        rustc_public::ty::RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut)
                            | rustc_public::ty::RigidTy::RawPtr(
                                _,
                                rustc_public::mir::Mutability::Mut
                            )
                    )
                )
            });
            if let (true, Some(entry)) = (writable, at_entry.get(&local)) {
                result.alias_updates.insert(
                    local,
                    Havoc::booked(
                        booked,
                        chc_fresh_name("__switchint_bailed_arm_alias"),
                        entry.sort().clone(),
                    ),
                );
            }
        }
    }
    Some(result)
}

/// The value half of [`switchint_branch_fallback`].
fn switchint_branch_fallback_value<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    switchint_bb: usize,
    target_bb: usize,
) -> Option<InlineReturn> {
    let key = (switchint_bb, target_bb);
    if let Some(cached) = walk_ctx.switchint_overapprox_cache.borrow().get(&key) {
        // Cache HIT mints nothing: the same freed variable is reused, so the
        // taint count and the accounted-identity count stay in step.
        return Some(InlineReturn::value_only(cached.clone()));
    }
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = ChcCtx::translate_ty(ret_ty)?;
    // Do NOT unwrap with option_value_sort here — the sibling branch results
    // use the raw return sort, and ITE merge requires matching sorts.
    let name = chc_fresh_name("__switchint_branch_overapprox");
    // ACCOUNT the fresh symbol. This variable lands in a VALUE position — it
    // becomes the inlined call's result — so a counterexample may be reading a
    // value the real program can never produce. Recording it on the
    // sound-fallback channel (with its SMT identity) is what lets
    // `classify_ctrex` demote a counterexample that DEPENDS on it, while
    // `recertify_overapprox_ctrex` still certifies Genuine a counterexample
    // that is provably independent of it. Booking NOTHING — the previous
    // behaviour — made every such counterexample certify Genuine, which is how
    // a hand-written reference loop that merely outran the replay budget was
    // reported as a failed assertion.
    let booked =
        ctx.record_sound_fallback_reason_identified("switchint_branch_overapprox", Some(&name));
    let var = Havoc::booked(booked, name, ret_sort);
    walk_ctx.switchint_overapprox_cache.borrow_mut().insert(key, var.clone());
    Some(InlineReturn::value_only(var))
}

/// Stack red zone and segment for an arm walk (`stacker::maybe_grow`).
const WALK_STACK_RED_ZONE: usize = 256 * 1024;
const WALK_STACK_SEGMENT: usize = 8 * 1024 * 1024;

/// The walk result of a path that ENDS here without returning: Kani's
/// `assume(false)` after a failing check (an unwinding assertion,
/// `walker.rs`; an abandoned arm whose reach check fails wherever it is taken,
/// [`switchint_branch_fallback`]). The value is the assume-pruned marker, so
/// the host cuts the path (`extract_inline_assume_guard`) and nothing
/// downstream reads a made-up value on it, and the path's side-channel checks
/// ride along. No variable is freed: a counterexample elsewhere stays
/// certifiable.
pub(super) fn pruned_path_return(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    mut state: InlineExecutionState,
) -> Option<InlineReturn> {
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = match ret_ty.kind() {
        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Tuple(tys))
            if tys.is_empty() =>
        {
            Expr::bool_const(true).sort().clone()
        }
        _ => ChcCtx::translate_ty(ret_ty)?,
    };
    // Rule E: the path is cut, so no execution reads the value as data.
    let mut result = InlineReturn::value_only(ExactVar::unobserved(
        chc_fresh_name("__assume_pruned_inline"),
        ret_sort,
    ));
    result.deferred_checks = std::mem::take(&mut state.deferred_checks);
    Some(result)
}

/// Is `bb` an arm that goes straight to an `Unreachable` terminator: inert
/// statements (storage markers and the like) and `Unreachable` (#3889), or a
/// single `Goto` onto such a block (the one-hop chain #4050 recognised)?
///
/// The arm is filtered out of the walk either way; what it MEANS depends on
/// the SwitchInt ([`unreachable_arm_is_obligation`]).
fn is_unreachable_block(walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    super::super::inline_walk_guard::block_is_proven_dead(walk_ctx.body, bb)
}

/// Is the arm `bb`, selected by `value` (`None`: the `otherwise` arm), an
/// [`is_unreachable_block`] arm that is an OBLIGATION: Kani's "unreachable
/// code" check, whose "not taken" condition the walk records like a panic
/// arm's?
///
/// Yes, except for the `otherwise` arm of a SwitchInt that no encodable value
/// selects (`otherwise_invalid_only`,
/// `obligation_free_walk::switch_otherwise_is_invalid_only`): the arm rustc
/// adds to an exhaustive `match` on a data-carrying enum, a datatype sort
/// whose every term is one of its variants; it stays dead. Every other
/// `Unreachable` arm is code the program can reach: an explicit enum arm
/// (`core::intrinsics::unreachable()` lowers to exactly this, and treating it
/// as dead proved `d_iunreach_bug`, walker_unreachable_terminator_dual.rs),
/// and the exhaustive `otherwise` of a fieldless enum, a raw bitvector that a
/// write through memory can leave out of range (walker_invalid_enum_dual.rs).
fn unreachable_arm_is_obligation(
    walk_ctx: &InlineWalkCtx<'_>,
    value: Option<u128>,
    bb: usize,
    otherwise_invalid_only: bool,
) -> bool {
    !(value.is_none() && otherwise_invalid_only) && is_unreachable_block(walk_ctx, bb)
}

/// The diverging call a SwitchInt arm reaches: the arm's own
/// `Call { target: None }`, or the one behind its single `Goto` (rustc inserts
/// a setup block before a panic call). `None` for every other shape, including
/// an arm that reaches `Unreachable` ([`unreachable_arm_is_obligation`]).
fn diverging_arm_call<'b>(
    walk_ctx: &'b InlineWalkCtx<'_>,
    bb: usize,
) -> Option<(&'b Operand, &'b [Operand])> {
    let blocks = &walk_ctx.body.blocks;
    let block = blocks.get(bb)?;
    let block = match &block.terminator.kind {
        TerminatorKind::Goto { target } => blocks.get(*target)?,
        _ => block,
    };
    match &block.terminator.kind {
        TerminatorKind::Call { func, args, target: None, .. } => Some((func, args.as_slice())),
        _ => None,
    }
}

/// Is `bb` a PANIC arm: a diverging arm whose call resolves to the panic or
/// formatting machinery (`core::panicking::panic`, `assert_failed`,
/// `unwrap_failed`, ...)?
///
/// Part of #4050 filtered every diverging arm out of the ITE so an
/// `Option::unwrap` extract would not consume SwitchInt depth. A walked panic
/// arm leaves the walk through `execute_diverging_call` as
/// `__assert_fail_inline`, which the host turns into an error rule; a
/// FILTERED one left nothing behind, so the arm was silently assumed not
/// taken — `assert!(self.0 == Some(2))` in an inlined `Drop::drop` body
/// produced no error rule. Only a panic arm is filtered now, and
/// `translate_switchint_ite` records its "not taken" condition as the
/// obligation it is. A diverging call the walker cannot name, or one that is
/// not panic machinery (`process::exit`, a user `-> !`), is walked like any
/// other arm and keeps its pre-#4050 handling.
///
/// `kani::panic` (the `PanicHook`, what trust-mc's std lowers `panic!` and
/// `unreachable!` to) is a panic arm too, exactly as Kani's `codegen_panic`
/// makes it a failing assertion (`terminator_exec::is_kani_panic_callee`).
fn is_panic_arm(ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    diverging_arm_call(walk_ctx, bb).is_some_and(|(func, _)| {
        super::terminator_exec::is_kani_panic_callee(func, walk_ctx.locals)
            || super::terminator_exec::resolve_inline_callee_path(ctx, func, walk_ctx.locals)
                .is_some_and(|path| ChcCtx::is_formatting_path(&path))
    })
}

/// Is `bb` an arm whose diverging call is `unreachable_unchecked` (Mechanism D,
/// `terminator_exec::is_ub_unreachable_callee`)? Reaching it is Kani's
/// "unreachable code" failure, so it is filtered like a panic arm and its "not
/// taken" condition is recorded as an obligation of that kind.
fn is_ub_unreachable_arm(ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    diverging_arm_call(walk_ctx, bb).is_some_and(|(func, _)| {
        super::terminator_exec::resolve_inline_callee_path(ctx, func, walk_ctx.locals)
            .is_some_and(|path| super::terminator_exec::is_ub_unreachable_callee(&path))
    })
}

/// Check if a basic block is effectively dead for SwitchInt branch purposes:
/// Unreachable (#3889), or a panic arm (#4050) or `unreachable_unchecked` arm
/// whose obligation `translate_switchint_ite` records separately.
fn is_dead_branch_target(ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> bool {
    is_unreachable_block(walk_ctx, bb)
        || is_panic_arm(ctx, walk_ctx, bb)
        || is_ub_unreachable_arm(ctx, walk_ctx, bb)
}

/// The Kani-parity description of a panic arm: the panic's constant message
/// (`assertion failed: self.0 == Some(2)`), else the callee path.
fn panic_arm_message(ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, bb: usize) -> String {
    let Some((func, args)) = diverging_arm_call(walk_ctx, bb) else {
        return format!("panic arm bb{bb}");
    };
    if super::terminator_exec::is_kani_panic_callee(func, walk_ctx.locals) {
        return super::terminator_exec::kani_panic_message(ctx, args);
    }
    let message = args.first().and_then(|arg| match arg {
        Operand::Constant(_) => {
            let (bytes, _) = ctx.try_extract_const_str_bytes(arg)?;
            String::from_utf8(bytes).ok()
        }
        _ => None,
    });
    message.unwrap_or_else(|| {
        super::terminator_exec::resolve_inline_callee_path(ctx, func, walk_ctx.locals)
            .unwrap_or_else(|| format!("panic arm bb{bb}"))
    })
}

/// The obligation a filtered diverging arm carries: `(kind, message)` for a
/// panic arm (Assertion, its message), an `unreachable_unchecked` arm, or an
/// `Unreachable` arm that is an obligation ([`unreachable_arm_is_obligation`];
/// both Unreachable, Kani's "unreachable code"); `None` for any other block.
fn diverging_arm_obligation(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    value: Option<u128>,
    bb: usize,
    otherwise_invalid_only: bool,
) -> Option<(PropertyKind, String)> {
    if is_panic_arm(ctx, walk_ctx, bb) {
        Some((PropertyKind::Assertion, panic_arm_message(ctx, walk_ctx, bb)))
    } else if is_ub_unreachable_arm(ctx, walk_ctx, bb)
        || unreachable_arm_is_obligation(walk_ctx, value, bb, otherwise_invalid_only)
    {
        Some((
            PropertyKind::Unreachable,
            super::terminator_exec::UNREACHABLE_CODE_MESSAGE.to_string(),
        ))
    } else {
        None
    }
}

/// The condition under which the discriminant selects none of the filtered
/// panic arms: `discr != v` for an explicit case `v`, and `∨ discr == v_i` over
/// every explicit case when the `otherwise` arm is the panic arm. `None` when
/// the discriminant's sort has no equality here (the ITE merge below bails on
/// the same sorts).
fn panic_arms_not_taken(
    discr_expr: &Expr,
    branches: &[(u128, usize)],
    otherwise_bb: usize,
    panic_arms: &[(Option<u128>, usize)],
) -> Option<Expr> {
    let selects = |value: u128| -> Option<Expr> {
        if discr_expr.sort().is_bool() {
            Some(if value != 0 { discr_expr.clone() } else { discr_expr.clone().not() })
        } else if let Some(width) = discr_expr.sort().bitvec_width() {
            Some(discr_expr.clone().eq(Expr::bitvec_const(value, width)))
        } else if discr_expr.sort().is_int() {
            Some(discr_expr.clone().eq(Expr::int_const(value)))
        } else {
            None
        }
    };
    let mut not_taken: Option<Expr> = None;
    for &(value, bb) in panic_arms {
        let guard = match value {
            Some(value) => selects(value)?.not(),
            None => {
                debug_assert_eq!(bb, otherwise_bb);
                let mut any_explicit: Option<Expr> = None;
                for &(value, _) in branches {
                    let sel = selects(value)?;
                    any_explicit = Some(match any_explicit {
                        Some(acc) => acc.or(sel),
                        None => sel,
                    });
                }
                // No explicit case at all: `otherwise` is always taken.
                any_explicit.unwrap_or_else(|| Expr::bool_const(false))
            }
        };
        not_taken = Some(match not_taken {
            Some(acc) => acc.and(guard),
            None => guard,
        });
    }
    not_taken
}

/// The fresh, unconstrained symbols the inline walker mints where it GAVE UP.
///
/// Each is a `declare-var` with no defining constraint, so it ranges over every
/// value of its sort. The sites that mint them account for them
/// (`record_sound_fallback_reason_identified`), which is what lets a
/// counterexample depending on one be demoted rather than certified.
const OVERAPPROX_VAR_MARKERS: [&str; 4] = [
    "__nested_call_overapprox",
    "__switchint_branch_overapprox",
    "__assert_fail_inline",
    "__assume_pruned_inline",
];

/// Is every value in `expr` one of those invented symbols — no program term
/// anywhere in it?
///
/// An expression with no variable at all (a literal) is NOT over-approximated;
/// neither is one that mixes an invented symbol with a real term, because the
/// real term still carries program meaning the check can constrain. Only a
/// discriminant built WHOLLY out of invented symbols says nothing about the
/// program. The obligation is recorded either way — this only decides whether
/// the walker NAMES the residual, so a counterexample riding an invented
/// symbol can be told from one riding the code.
fn discriminant_is_wholly_overapproximated(expr: &Expr) -> bool {
    let mut saw_var = false;
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ay_bindings::ExprValue::Var { name } = node.value() {
            saw_var = true;
            if !OVERAPPROX_VAR_MARKERS.iter().any(|marker| name.contains(marker)) {
                return false;
            }
        }
        stack.extend(node.value().children());
    }
    saw_var
}

/// The SwitchInt discriminant as a term of its MIR type's width.
///
/// A SwitchInt's case values are the discriminant's bits at the width of its
/// type: `Ordering::Less`, an `i8` discriminant of -1, is case 255. The walker
/// holds an enum discriminant as a pointer-width term, sign-extended for a
/// signed repr (`inline_shared/discriminant.rs`), so `Less` was `0xFF..FF`
/// against a case `bitvec_const(255, 64)` and matched nothing: every walked
/// exhaustive `match` on an `Ordering` took its `otherwise` arm, a certified
/// false 'unreachable code', and an explicit `Less` arm was never selected, so
/// its value was never the result and a `Less => panic!()` arm's obligation was
/// vacuous (walker fail-closed review 6, findings 2 and 3; the statement path
/// was already right). The low `w` bits of the term are the value whichever
/// extension widened it, so the comparisons (the panic arms' not-taken
/// conditions, the constant fold and the arm merge, which all read this term)
/// are made at the type's width, where the case values live.
fn switch_discriminant_at_type_width(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    discr: &Operand,
    discr_expr: Expr,
) -> Expr {
    use rustc_public::ty::{RigidTy, TyKind};
    let Some(term_width) = discr_expr.sort().bitvec_width() else {
        return discr_expr;
    };
    let Ok(ty) = discr.ty(walk_ctx.locals) else {
        return discr_expr;
    };
    let ty = ctx.resolve_body_ty(ty);
    let type_width = match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Char) => {
            crate::codegen_ay::types::ty_to_bv_width(ty)
        }
        _ => None,
    };
    match type_width {
        Some(type_width) if type_width > 0 && type_width < term_width => {
            debug!(
                term_width,
                type_width, "virtual body: SwitchInt discriminant compared at its type's width"
            );
            discr_expr.extract(type_width - 1, 0)
        }
        _ => discr_expr,
    }
}

/// The explicit value a folded discriminant selected `taken` by (`None`: the
/// `otherwise` arm).
fn folded_value(branches: &[(u128, usize)], taken: usize, otherwise_bb: usize) -> Option<u128> {
    if taken == otherwise_bb && branches.iter().all(|&(_, bb)| bb != taken) {
        return None;
    }
    branches.iter().find(|&&(_, bb)| bb == taken).map(|&(value, _)| value)
}

/// Translate a SwitchInt terminator into nested ITE expressions.
///
/// Part of #3188: SwitchInt support for inline translators.
pub(in crate::codegen_ay::chc) fn translate_switchint_ite<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    discr: &Operand,
    targets: &rustc_public::mir::SwitchTargets,
    local_exprs: HashMap<usize, Expr>,
    inline_vtable_ids: HashMap<usize, Expr>,
    inline_alloc_ids: HashMap<usize, u32>,
    modified_locals: HashSet<usize>,
    assume_guards: Vec<Expr>,
    assert_guards: Vec<Expr>,
    deferred_checks: Vec<DeferredInlineCheck>,
    memory_written_args: HashSet<usize>,
    switchint_bb: usize,
    switchint_depth: usize,
    inline_depth: usize,
) -> Option<InlineReturn> {
    if switchint_depth >= walk_ctx.switchint_depth_limit(MAX_SWITCHINT_DEPTH) {
        debug!(switchint_bb, switchint_depth, "virtual body: SwitchInt depth limit reached");
        return None;
    }
    // P5.3 (fail-closed): per-harness walk-node budget. Depth bounds one
    // chain, but forked sub-walks multiply across nesting, loop replay, and
    // call sites — unbounded, they burn the driver watchdog to a hard kill.
    // Take the SAME sound-overapprox bail path as depth exhaustion (callers
    // substitute an unconstrained branch result or havoc the inline), and
    // book a FailClose fallback so any resulting verdict is an honest
    // Demoted UNDETERMINED — a fast demotion instead of an ~80s hard kill.
    if ctx.switchint_walk_nodes_spent >= switchint_walk_node_budget() {
        ctx.record_sound_fallback_reason("walker_node_budget_exhausted");
        debug!(
            switchint_bb,
            nodes_spent = ctx.switchint_walk_nodes_spent,
            "virtual body: SwitchInt walk-node budget exhausted (P5.3), bailing fail-closed"
        );
        return None;
    }
    // Assert-guard side-channel: entries recorded BEFORE this SwitchInt are
    // path-independent of the branch guards. They are held aside here (branch
    // walk states start with an EMPTY side-channel) and re-attached to the
    // merged result unweakened; per-branch entries get their branch guard
    // composed in the merge fold below.
    let mut pre_switch_checks = deferred_checks;

    let resolver = walk_ctx.resolver;
    let discr_expr = inline_operand_to_expr(ctx, discr, &local_exprs, &resolver, walk_ctx.locals)?;
    let discr_expr = switch_discriminant_at_type_width(ctx, walk_ctx, discr, discr_expr);

    // Part of #3936 D3: Capture all aliasable arg-local values at entry.
    // When some branches modify an arg and others don't, the unmodified
    // side of the ITE merge must use the original value (not dropped).
    let alias_at_entry: HashMap<usize, Expr> = local_exprs.clone();

    let branches: Vec<(u128, usize)> = targets.branches().collect();
    let otherwise_bb = targets.otherwise();

    // Part of #3889/#4050: Dead-branch detection — skip branches whose target
    // is Unreachable (e.g., otherwise arm of a 2-variant enum) OR diverging
    // (panic/abort path, e.g., None arm of Option::unwrap). This prevents
    // Option unwrap SwitchInts from consuming depth unnecessarily.
    let otherwise_is_dead = is_dead_branch_target(ctx, walk_ctx, otherwise_bb);
    // Whether an `Unreachable` `otherwise` arm here is dead code or an
    // obligation (`unreachable_arm_is_obligation`).
    let otherwise_invalid_only =
        crate::codegen_ay::obligation_free_walk::switch_otherwise_is_invalid_only(
            walk_ctx.body,
            discr,
            targets,
        );

    let mut local_exprs = Some(local_exprs);
    let mut inline_vtable_ids = Some(inline_vtable_ids);
    let mut inline_alloc_ids = Some(inline_alloc_ids);
    let mut modified_locals = Some(modified_locals);
    let mut assume_guards = Some(assume_guards);
    let mut assert_guards = Some(assert_guards);

    // Part of #4050 D1: Collect live explicit branches, then deduplicate by
    // unique target block. Walk each unique target once; reuse the result for
    // every case value that points at the same block. This reduces duplicate
    // walks and overapprox variables from O(case_values) to O(unique_targets).
    let live_explicit: Vec<(u128, usize)> = branches
        .iter()
        .rev()
        .filter(|(_, bb)| !is_dead_branch_target(ctx, walk_ctx, *bb))
        .copied()
        .collect();

    // Part of #55 piece 2: EXACT constant discriminant — walk ONLY the taken
    // arm. Match semantics mirror the guard construction in the merge fold
    // below byte-for-byte: bool via `value != 0`; bitvec via raw-bits equality
    // at the discriminant's width, normalized through the SAME
    // `Expr::bitvec_const(value, width)` constructor the guard uses (no
    // hand-rolled masking — a width/signedness mismatch here would prune the
    // WRONG arm and false-prove). An undecidable fold leaves the full ITE
    // walk untouched. This is what lets concrete recursion (fib(6), fac(5),
    // hanoi) unroll one arm per level instead of exploding both arms.
    let folded_target: Option<usize> =
        const_fold_switch_target(&discr_expr, &branches, otherwise_bb);
    let (live_explicit, otherwise_is_dead) = match folded_target {
        Some(taken) if taken == otherwise_bb => (Vec::new(), otherwise_is_dead),
        Some(taken) => (live_explicit.into_iter().filter(|(_, bb)| *bb == taken).collect(), true),
        None => (live_explicit, otherwise_is_dead),
    };
    if let Some(taken) = folded_target {
        debug!(
            switchint_bb,
            ?folded_target,
            "virtual body: SwitchInt discriminant folded to a constant — single-arm walk"
        );
        // A concrete iteration of a walked loop does not spend its fuel
        // (`InlineWalkCtx::refund_concrete_loop_iteration`).
        let refunded = walk_ctx.refund_concrete_loop_iteration(switchint_bb, targets, taken);
        if !refunded.is_empty() {
            debug!(switchint_bb, ?refunded, "virtual body: concrete loop iteration refunded");
        }
    }
    // Every arm walk starts from the loop-replay state here, after the refund.
    let entry_loop_fuel = walk_ctx.snapshot_loop_replay();

    // The walker's path condition at this SwitchInt (its assume guards).
    let entry_path_guard = assume_guards
        .as_ref()
        .expect("invariant: not yet consumed")
        .iter()
        .cloned()
        .reduce(|a, b| a.and(b));

    // A discriminant that folds onto a filtered diverging arm (a panic, or
    // `unreachable_unchecked`) proves that arm TAKEN on this path: reaching it
    // is the failure, exactly (`path → false`). This used to bail ("all
    // branches dead"), and the bail became the enclosing arm's blessed havoc,
    // which dropped the certain failure with it.
    if let Some(taken) = folded_target
        && let Some((kind, message)) = diverging_arm_obligation(
            ctx,
            walk_ctx,
            folded_value(&branches, taken, otherwise_bb),
            taken,
            otherwise_invalid_only,
        )
    {
        let check = entry_path_guard.clone().map_or(Expr::bool_const(false), |guard| guard.not());
        debug!(
            switchint_bb,
            taken,
            %message,
            "virtual body: SwitchInt folds onto a diverging arm — it is reached on this path"
        );
        pre_switch_checks.push(DeferredInlineCheck {
            check,
            kind,
            message: Some(message),
            write_mark: ctx.heap_state.write_mark(),
            merge_key: None,
        });
        let mut reached = super::virtual_panic_fallback(ctx, walk_ctx)?;
        reached.deferred_checks = pre_switch_checks;
        walk_ctx.restore_loop_replay(&entry_loop_fuel);
        return Some(reached);
    }

    // A filtered PANIC arm is an obligation, not dead code (`is_panic_arm`);
    // so is an `unreachable_unchecked` arm (`is_ub_unreachable_arm`, Kani's
    // "unreachable code"). With the discriminant unfolded, "the arm is not
    // taken" must hold on this path exactly as a MIR `Assert` would: record it
    // on BOTH check channels — the side-channel entry the host emits as a
    // per-property error rule, and the value-channel guard `finish_return`
    // folds into the `__assert_fail_inline` ITE (the lane `codegen_drop`
    // reads). An exact fold to a live arm proves every such arm untaken, so
    // nothing is recorded; a fold onto one is handled above.
    if folded_target.is_none() {
        type ArmPredicate<'p> =
            &'p dyn Fn(&ChcCtx<'_, '_>, &InlineWalkCtx<'_>, Option<u128>, usize) -> bool;
        let is_panic = |ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, _: Option<u128>, bb| {
            is_panic_arm(ctx, walk_ctx, bb)
        };
        let is_unreachable =
            |ctx: &ChcCtx<'_, '_>, walk_ctx: &InlineWalkCtx<'_>, value: Option<u128>, bb| {
                is_ub_unreachable_arm(ctx, walk_ctx, bb)
                    || unreachable_arm_is_obligation(walk_ctx, value, bb, otherwise_invalid_only)
            };
        let arm_kinds: [(ArmPredicate<'_>, PropertyKind); 2] =
            [(&is_panic, PropertyKind::Assertion), (&is_unreachable, PropertyKind::Unreachable)];
        for (is_arm, kind) in arm_kinds {
            let arms: Vec<(Option<u128>, usize)> = branches
                .iter()
                .filter(|&&(value, bb)| is_arm(ctx, walk_ctx, Some(value), bb))
                .map(|&(value, bb)| (Some(value), bb))
                .chain(is_arm(ctx, walk_ctx, None, otherwise_bb).then_some((None, otherwise_bb)))
                .collect();
            if arms.is_empty() {
                continue;
            }
            let Some(not_taken) = panic_arms_not_taken(&discr_expr, &branches, otherwise_bb, &arms)
            else {
                debug!(
                    switchint_bb,
                    discr_sort = ?discr_expr.sort(),
                    "virtual body: SwitchInt diverging arm on a discriminant without equality, bailing"
                );
                return None;
            };
            // The obligation is recorded WHATEVER the discriminant is made of.
            // Where the walker gave up on the call that computes the condition,
            // the discriminant is a fresh unconstrained symbol it minted
            // (`discriminant_is_wholly_overapproximated`) and the obligation
            // cannot be discharged — that is the honest answer, not a reason to
            // drop it. Skipping it instead was measured and rejected: the
            // condition gates a CHECK, so dropping it removes exactly one
            // behaviour, the failing one (the argument `terminator_exec.rs`
            // makes for `nested_call_dropped_obligation`). A counterexample
            // that depends on the invented symbol is demoted downstream by
            // `classify_ctrex`; the gap reason below is what names it.
            if discriminant_is_wholly_overapproximated(&discr_expr) {
                ctx.note_gap_reason("switchint_panic_arm_on_overapprox");
            }
            let check = match entry_path_guard.clone() {
                Some(path_guard) => path_guard.not().or(not_taken),
                None => not_taken,
            };
            let message = arms
                .iter()
                .filter_map(|&(value, bb)| {
                    diverging_arm_obligation(ctx, walk_ctx, value, bb, otherwise_invalid_only)
                })
                .map(|(_, message)| message)
                .collect::<Vec<_>>()
                .join("; ");
            debug!(
                switchint_bb,
                ?arms,
                %message,
                "virtual body: SwitchInt diverging arm filtered — its not-taken condition is an obligation"
            );
            pre_switch_checks.push(DeferredInlineCheck {
                check: check.clone(),
                kind,
                message: Some(message),
                write_mark: ctx.heap_state.write_mark(),
                merge_key: None,
            });
            assert_guards.as_mut().expect("invariant: not yet consumed").push(check);
        }
    }

    // Build unique target list preserving first-seen order.
    let mut unique_targets: Vec<usize> = Vec::new();
    {
        let mut seen = HashSet::new();
        if !otherwise_is_dead {
            seen.insert(otherwise_bb);
            unique_targets.push(otherwise_bb);
        }
        for &(_, tbb) in &live_explicit {
            if seen.insert(tbb) {
                unique_targets.push(tbb);
            }
        }
    }
    let total_walks = unique_targets.len();
    let mut walk_num = 0usize;

    // Part of #4050 D3: Don't consume SwitchInt depth budget for
    // single-target SwitchInts (dead-branch filtering leaves one live arm):
    // no ITE branching, structurally sequential (e.g., unwrap() patterns).
    //
    // Part of #4145: Loop-fuel-bearing bodies must STILL increment depth.
    // The previous exemption (`has_loop_fuel → no depth increment`) caused
    // infinite recursion when nested inlined calls (e.g., scale → mul →
    // reduce → gcd) each had their own while-loop SwitchInts — depth
    // never increased, bypassing MAX_SWITCHINT_DEPTH entirely.
    let walk_depth = if total_walks <= 1 { switchint_depth } else { switchint_depth + 1 };

    // The subslice side tables (`ref_resolution.subslice_len` /
    // `subslice_offset`) are keyed by local and shared by the whole walk, but
    // each arm below is walked to the body's return on a path of its own. An
    // entry one arm records (an array's slice view,
    // `statement_metadata::seed_inline_array_view_len`) described a local on
    // THAT path; read by the next arm, where the local holds another slice, it
    // gave `s.len()` the array's length (walker fail-closed review 6, finding
    // 1). Every arm starts from the tables as they were at the SwitchInt, and
    // they are restored when the last arm is done: nothing after the arms
    // walks this body.
    let entry_subslice =
        (ctx.ref_resolution.subslice_len.clone(), ctx.ref_resolution.subslice_offset.clone());
    let restore_entry_subslice = |ctx: &mut ChcCtx<'tcx, 'body>| {
        ctx.ref_resolution.subslice_len = entry_subslice.0.clone();
        ctx.ref_resolution.subslice_offset = entry_subslice.1.clone();
    };

    // Walk each unique target block once and cache the result.
    let mut target_results: HashMap<usize, InlineReturn> =
        HashMap::with_capacity(unique_targets.len());
    for &tbb in &unique_targets {
        // P5.3: one walk node per sub-walk fork (survives speculative
        // rollback, like const_recursion_nodes_spent — the WORK was done
        // even when a branch walk bails).
        ctx.switchint_walk_nodes_spent += 1;
        walk_ctx.restore_loop_replay(&entry_loop_fuel);
        restore_entry_subslice(ctx);
        walk_num += 1;
        let mut state = if walk_num == total_walks {
            InlineExecutionState::new(
                local_exprs.take().expect("invariant: consumed only once"),
                inline_vtable_ids.take().expect("invariant: consumed only once"),
                modified_locals.take().expect("invariant: consumed only once"),
            )
        } else {
            InlineExecutionState::new(
                local_exprs.as_ref().expect("invariant: not yet consumed").clone(),
                inline_vtable_ids.as_ref().expect("invariant: not yet consumed").clone(),
                modified_locals.as_ref().expect("invariant: not yet consumed").clone(),
            )
        };
        state.inline_alloc_ids = if walk_num == total_walks {
            inline_alloc_ids.take().expect("invariant: consumed only once")
        } else {
            inline_alloc_ids.as_ref().expect("invariant: not yet consumed").clone()
        };
        state.assume_guards = if walk_num == total_walks {
            assume_guards.take().expect("invariant: consumed only once")
        } else {
            assume_guards.as_ref().expect("invariant: not yet consumed").clone()
        };
        state.assert_guards = if walk_num == total_walks {
            assert_guards.take().expect("invariant: consumed only once")
        } else {
            assert_guards.as_ref().expect("invariant: not yet consumed").clone()
        };
        state.memory_written_args = memory_written_args.clone();
        // Part of #4185: Snapshot heap state before each branch walk.
        // If the walk bails, partial heap mutations (stores, pending_updates)
        // from branch N must not contaminate branch N+1.
        let heap_snapshot = ctx.heap_state.snapshot_transient_rule_state();
        // Part of #4185 Fix 4: Snapshot modified_state_indices alongside heap.
        let modified_snapshot = ctx.encode.modified_state_indices.clone();
        let effects_before = ctx.heap_state.effect_mark();
        // A deep replay (a long constant loop is one nested walk per
        // iteration) grows the stack on demand.
        let walk_result = stacker::maybe_grow(WALK_STACK_RED_ZONE, WALK_STACK_SEGMENT, || {
            walk_blocks_to_return(
                ctx,
                walk_ctx,
                tbb,
                Some(switchint_bb),
                state,
                walk_depth,
                inline_depth,
            )
        });
        let result = match walk_result {
            Some(r) => {
                // The branch-arm rule (inline_walk_guard.rs): with several
                // live targets, a memory effect this arm made is kept and
                // applied by the host unguarded, and the next arm is walked
                // against it.
                if total_walks > 1 {
                    ctx.note_inline_branch_arm_effects(effects_before);
                }
                r
            }
            None => {
                // Part of #4185: Restore heap state after failed branch walk.
                ctx.heap_state.restore_transient_rule_state(&heap_snapshot);
                // Part of #4185 Fix 4: Restore modified_state_indices on bail-out.
                ctx.encode.modified_state_indices = modified_snapshot;
                debug!(
                    switchint_bb,
                    target_bb = tbb,
                    "virtual body: SwitchInt branch walk failed, using overapprox (#4031/#4050)"
                );
                switchint_branch_fallback(
                    ctx,
                    walk_ctx,
                    switchint_bb,
                    tbb,
                    &alias_at_entry,
                    entry_path_guard.as_ref(),
                )?
            }
        };
        target_results.insert(tbb, result);
    }
    restore_entry_subslice(ctx);

    // Part of #4050: If only one unique live target exists (all live arms go
    // to the same block, or single-arm after dead-branch filtering), skip ITE
    // construction entirely — just return the single walk result.
    if unique_targets.len() == 1 {
        let mut sole_result = target_results.into_values().next().expect("invariant: 1 target");
        // Re-attach the pre-switch side-channel entries (no branch condition
        // applies: the single live arm is taken unconditionally).
        sole_result.deferred_checks.extend(pre_switch_checks);
        walk_ctx.restore_loop_replay(&entry_loop_fuel);
        debug!(
            switchint_bb,
            sole_target = unique_targets[0],
            "virtual body: SwitchInt single live target, skipping ITE (#4050)"
        );
        return Some(sole_result);
    }

    // Map otherwise and explicit branches to their pre-walked results.
    let otherwise_result = if otherwise_is_dead {
        debug!(
            switchint_bb,
            otherwise_bb, "virtual body: SwitchInt otherwise is dead, skipping (#3889/#4050)"
        );
        None
    } else {
        Some(target_results.get(&otherwise_bb).expect("invariant: walked").clone())
    };

    let mut branch_results: Vec<(u128, InlineReturn)> = Vec::with_capacity(live_explicit.len());
    for &(value, tbb) in &live_explicit {
        let result = target_results.get(&tbb).expect("invariant: walked").clone();
        branch_results.push((value, result));
    }
    walk_ctx.restore_loop_replay(&entry_loop_fuel);

    // Merge: start with otherwise_result as accumulator, or first explicit branch if dead.
    if otherwise_result.is_none() && branch_results.is_empty() {
        debug!(switchint_bb, "virtual body: SwitchInt all branches dead, bailing");
        return None;
    }
    let mut result = if let Some(r) = otherwise_result { r } else { branch_results.remove(0).1 };

    for (value, mut branch_result) in branch_results {
        let guard = if discr_expr.sort().is_bool() {
            if value != 0 { discr_expr.clone() } else { discr_expr.clone().not() }
        } else if let Some(width) = discr_expr.sort().bitvec_width() {
            discr_expr.clone().eq(Expr::bitvec_const(value, width))
        } else if discr_expr.sort().is_int() {
            discr_expr.clone().eq(Expr::int_const(value))
        } else {
            return None;
        };

        if branch_result.value.sort() != result.value.sort() {
            debug!(
                switchint_bb,
                branch_result = ?branch_result.value,
                result = ?result.value,
                "virtual body: SwitchInt branch sort mismatch, coercing (#4031)"
            );
            // Part of #4031: Instead of bailing on sort mismatch, replace the
            // mismatched side with a fresh symbolic of the other side's sort.
            // Sound over-approximation: the coerced branch is unconstrained.
            // The side-channel entries survive the coercion — the branch WAS
            // walked, so its checks are real; only the VALUE is havocked.
            // (Pre-side-channel, the coercion silently dropped any assert ITE
            // riding the replaced value — one of the documented check-loss
            // shapes this side-channel exists to close.)
            let target_sort = result.value.sort().clone();
            let coerced = Havoc::mint(
                ctx,
                sound_havoc::UNTRACKED_SORT_MISMATCH_VALUE,
                chc_fresh_name("__switchint_sort_coerce"),
                target_sort,
            );
            let branch_checks = std::mem::take(&mut branch_result.deferred_checks);
            branch_result = InlineReturn::value_only(coerced);
            branch_result.deferred_checks = branch_checks;
        }
        let vtable = match (branch_result.vtable, result.vtable) {
            (Some(branch_vtable), Some(result_vtable)) => {
                if branch_vtable.sort() != result_vtable.sort() {
                    debug!(
                        switchint_bb,
                        branch_vtable = ?branch_vtable,
                        result_vtable = ?result_vtable,
                        "virtual body: SwitchInt vtable sort mismatch, bailing"
                    );
                    return None;
                }
                Some(Expr::ite(guard.clone(), branch_vtable, result_vtable))
            }
            _ => None,
        };
        // Part of #3936 D3: Merge alias_updates per-key across SwitchInt branches.
        let alias_updates = merge_alias_updates_ite(
            ctx,
            &guard,
            branch_result.alias_updates,
            result.alias_updates,
            &alias_at_entry,
            switchint_bb,
        );
        // Assert-guard side-channel: `ite(guard, branch, result)` means the
        // branch's checks apply when `guard` holds and the accumulator's when
        // it doesn't. Explicit case guards test the SAME discriminant against
        // DISTINCT values, so weakening each branch entry by only its own
        // guard is exact; accumulator entries pick up `guard ∨ check` per fold
        // step, matching the nested-ITE path condition exactly.
        //
        // Checks with a merge key (one abandoned arm reached on many paths)
        // join into one `ite(guard, branch, rest)` check instead
        // (`merge_keyed_arm_checks`), the same conjunction.
        let deferred_checks = super::super::inline_body::merge_keyed_arm_checks(
            &guard,
            branch_result.deferred_checks,
            result.deferred_checks,
        );
        result = InlineReturn {
            value: Expr::ite(guard, branch_result.value, result.value),
            vtable,
            alloc_id: None,
            alias_updates,
            deferred_checks,
        };
    }
    // Re-attach pre-switch side-channel entries unweakened (recorded before
    // any branch guard applied).
    result.deferred_checks.extend(pre_switch_checks);

    debug!(
        switchint_bb,
        num_branches = branches.len(),
        switchint_depth,
        "virtual body: translated SwitchInt to ITE chain (#3188)"
    );

    Some(result)
}

/// Merge two `alias_updates` maps across an ITE branch.
///
/// For each key present in either side:
/// - Both present with same sort: `ite(guard, branch, result)`
/// - Only one present: use entry-state original for the missing side if sorts match
/// - Sort mismatch: drop that key (sound — over-approximation)
///
/// Part of #3936 D3: generalizes the former single-key receiver_update merge.
fn merge_alias_updates_ite(
    ctx: &ChcCtx<'_, '_>,
    guard: &Expr,
    branch: BTreeMap<usize, Expr>,
    result: BTreeMap<usize, Expr>,
    at_entry: &HashMap<usize, Expr>,
    switchint_bb: usize,
) -> BTreeMap<usize, Expr> {
    // F5 (docs/chc-hole-fix-designs-2026-09-24.md section 2): an update whose
    // sides disagree in sort used to be DROPPED (two arms) or taken on BOTH
    // paths (one arm). Either loses a path's value. It is now a fresh value of
    // the updating side's sort, and the harness fails closed.
    let mismatch = |key: usize, sort: &ay_bindings::Sort| -> Expr {
        debug!(switchint_bb, key, "SwitchInt alias-update sort mismatch for key {key}, havocking");
        let booked = ctx.record_sound_fallback_reason(
            super::super::inline_walk_guard::DYN_DISPATCH_ALIAS_UPDATE_SORT_MISMATCH,
        );
        Havoc::booked(
            booked,
            chc_fresh_name(&format!("__switchint_alias_mismatch_{key}")),
            sort.clone(),
        )
    };
    let all_keys: HashSet<usize> = branch.keys().chain(result.keys()).copied().collect();
    let mut merged = BTreeMap::new();
    for key in all_keys {
        let merged_expr = match (branch.get(&key), result.get(&key)) {
            (Some(b), Some(r)) => {
                if b.sort() != r.sort() {
                    mismatch(key, r.sort())
                } else {
                    Expr::ite(guard.clone(), b.clone(), r.clone())
                }
            }
            (Some(b), None) => match at_entry.get(&key) {
                Some(original) if b.sort() == original.sort() => {
                    Expr::ite(guard.clone(), b.clone(), original.clone())
                }
                _ => mismatch(key, b.sort()),
            },
            (None, Some(r)) => match at_entry.get(&key) {
                Some(original) if r.sort() == original.sort() => {
                    Expr::ite(guard.clone(), original.clone(), r.clone())
                }
                _ => mismatch(key, r.sort()),
            },
            (None, None) => unreachable!("key came from one of the maps"),
        };
        merged.insert(key, merged_expr);
    }
    merged
}

/// Part of #55 piece 2: decide the taken SwitchInt target when the
/// discriminant evaluates to an exact constant.
///
/// MUST mirror the runtime guard semantics built in the merge fold of
/// `translate_switchint_ite`: bool discriminants match a branch when
/// `(value != 0) == discr`; bitvec discriminants match on raw-bits equality
/// after normalizing the branch's `u128` through `Expr::bitvec_const(value,
/// width)` — exactly the numeral the guard compares against. Returns `None`
/// (full ITE walk) for any sort or expression the evaluator cannot decide.
fn const_fold_switch_target(
    discr_expr: &Expr,
    branches: &[(u128, usize)],
    otherwise_bb: usize,
) -> Option<usize> {
    use trust_mc_core::chc_const_prop::eval::{try_eval_to_bool, try_eval_to_const};
    if discr_expr.sort().is_bool() {
        let b = try_eval_to_bool(discr_expr)?;
        return Some(
            branches.iter().find(|(v, _)| (*v != 0) == b).map(|(_, t)| *t).unwrap_or(otherwise_bb),
        );
    }
    let width = discr_expr.sort().bitvec_width()?;
    let folded = try_eval_to_const(discr_expr)?;
    let ay_bindings::ExprValue::BitVecConst { value: dv, .. } = folded.value() else {
        return None;
    };
    Some(
        branches
            .iter()
            .find(|(v, _)| {
                let guard_numeral = Expr::bitvec_const(*v, width);
                matches!(
                    guard_numeral.value(),
                    ay_bindings::ExprValue::BitVecConst { value: gv, .. } if gv == dv
                )
            })
            .map(|(_, t)| *t)
            .unwrap_or(otherwise_bb),
    )
}

#[cfg(test)]
mod tests {
    use super::discriminant_is_wholly_overapproximated;
    use ay_bindings::{Expr, Sort};

    fn var(name: &str, sort: Sort) -> Expr {
        Expr::var(name, sort)
    }

    /// The exact shape measured on `probe_check_thin_ptr_harness`: the panic
    /// arm's discriminant is `¬¬__nested_call_overapprox_0`, a symbol the
    /// walker minted where it gave up on a nested call. The obligation riding
    /// it is real but cannot be discharged, so the residual gets named.
    #[test]
    fn overapprox_only_discriminant_is_recognised() {
        let havoc = var("__nested_call_overapprox_0", Sort::bool());
        assert!(discriminant_is_wholly_overapproximated(&havoc.clone().not().not()));
        assert!(discriminant_is_wholly_overapproximated(&var(
            "__switchint_branch_overapprox_7",
            Sort::bool()
        )));
    }

    /// A program term's obligation is discharged on its own merits, so it must
    /// never be reported as an over-approximated residual.
    #[test]
    fn program_discriminant_is_not_overapproximated() {
        let state = var("_probe_cleanup_branchy_drop_assert_2", Sort::bool());
        assert!(!discriminant_is_wholly_overapproximated(&state));
        // A havoc MIXED with a program term still carries program meaning.
        let havoc = var("__nested_call_overapprox_1", Sort::bool());
        assert!(!discriminant_is_wholly_overapproximated(&state.and(havoc)));
    }

    /// A literal is a decided condition, not an invented one.
    #[test]
    fn constant_discriminant_is_not_overapproximated() {
        assert!(!discriminant_is_wholly_overapproximated(&Expr::bool_const(true)));
    }
}

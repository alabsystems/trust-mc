// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Obligations the inline walker reaches but cannot state.
//!
//! Where the walk meets an obligation whose condition it cannot translate (an
//! `Assert` or a `kani::assert` hook call reading a local it skipped, a
//! diverging call it does not model, the checks of a SwitchInt arm it could
//! not finish), the strongest honest
//! encoding is that the obligation FAILS WHEREVER IT IS REACHED. That is a
//! side-channel check whose condition is a fresh boolean `t` that nothing else
//! reads. The walker adds its path condition as for any check (assume guards at
//! record time, SwitchInt guards at the merges), and `t` can always be false,
//! so the host's error rule fires on exactly the paths that reach the record
//! point.
//!
//! * A PROOF requires every such path to be infeasible, and then the lost
//!   obligation is unreachable too: the check never lets a harness verify
//!   while the obligation it stands for can be reached.
//! * A FAILURE of it is not the program failing: the violated check reads `t`,
//!   which is recorded as this event's freed variable, so the driver never
//!   certifies it Genuine (`recertify_overapprox_ctrex`); a counterexample that
//!   violates another check without reading `t` can still be certified.
//!
//! The reasons are blessed (`codegen_ctx::fallback_soundness`) for exactly this
//! argument: the record accounts for a check, it frees no program value, and a
//! proof over it is a proof of the program. A demoting booking would demote
//! every harness whose walk merely explored such a path, feasible or not.
//! (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed".)

use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::mono_ty;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, LocalDecl, Operand, Place, TerminatorKind};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::chc_fresh_name;
use crate::codegen_ay::chc::codegen_ctx::Havoc;
use crate::codegen_ay::obligation_free_walk::{
    StubMap, Verdict, instance_obligation_verdict, statement_verdict,
};

/// Mechanism E: an `Assert` terminator (`terminator_exec.rs`
/// `execute_inline_assert`) or a `kani::assert` hook call (`kani_inline.rs`
/// `handle_inline_kani_assert_call`, what trust-mc's std lowers `assert!` to)
/// whose condition the walker cannot translate.
pub(in crate::codegen_ay::chc) const WALKER_UNTRANSLATABLE_ASSERT: &str =
    "walker_untranslatable_assert_uncertified";

/// A diverging call the walker does not model whose callee can carry an
/// obligation (`terminator_exec.rs` `execute_diverging_call`).
pub(in crate::codegen_ay::chc) const WALKER_UNMODELLED_DIVERGING_CALL: &str =
    "walker_diverging_call_uncertified";

/// Mechanism C: a SwitchInt arm the walker could not finish, whose abandoned
/// region can carry an obligation (`switchint.rs` `switchint_branch_fallback`).
pub(in crate::codegen_ay::chc) const WALKER_BAILED_ARM_OBLIGATION: &str =
    "walker_bailed_arm_obligation_uncertified";

/// An iterator reduction the statement path models (`Iterator::fold`,
/// `try_fold`, `sum`: `codegen_call_iterator_adapter/reduce.rs`) whose step
/// can carry an obligation, where the step is not replayed: past the replay
/// bound, or when the step's closure could not be walked or is never walked.
/// The check is `t` under that condition (reachable exactly when an unreplayed
/// step can run), recorded like the walker's.
pub(in crate::codegen_ay::chc) const ITER_REDUCE_STEP_UNCERTIFIED: &str =
    "iter_reduce_step_uncertified";

/// Kani's unwinding assertion on the std loop of an iterator reduction the
/// statement path models (`codegen_call_iterator_adapter/reduce.rs`), under
/// a declared unwind bound, where the model cannot state it exactly: an
/// iterator shape whose loop was not measured, or an unknown element count.
pub(in crate::codegen_ay::chc) const ITER_REDUCE_UNWIND_UNCERTIFIED: &str =
    "iter_reduce_unwind_uncertified";

/// A closure a `Vec` / slice method runs on the elements (`retain`,
/// `dedup_by(_key)`, `sort_by(_key)`: `codegen_call_vec.rs`) that can carry an
/// obligation: the models never walk it. The check is `t` wherever the call is
/// reached.
pub(in crate::codegen_ay::chc) const VEC_CLOSURE_STEP_UNCERTIFIED: &str =
    "vec_closure_step_uncertified";

/// A call the statement path handles with a MODEL (a stub, a pre-inline
/// dispatcher, a value havoc: anything but replaying the callee's body)
/// whose callee may run a loop Kani unwinds, under a declared unwind bound
/// with unwinding assertions on (`codegen_call.rs`,
/// `model_call_unwinding_check`). The model states nothing about the loop,
/// so Kani's unwinding assertion on it is lost. The check is `t` wherever the
/// call is reached.
pub(in crate::codegen_ay::chc) const MODEL_CALL_LOOP_UNWIND_UNCERTIFIED: &str =
    "model_call_loop_unwind_uncertified";

/// Can the callee of `func` (an operand of the body `locals` belongs to,
/// resolved through the unit's stub map) run a loop Kani unwinds
/// (`obligation_free_walk::instance_may_loop`)? `true` where it cannot be
/// resolved.
pub(in crate::codegen_ay::chc) fn call_may_loop(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let stubs = crate::kani_middle::transform::walker_stub_map();
    match super::terminator_exec::resolve_check_scan_instance(ctx, func, locals, &stubs) {
        Some(instance) => instance_may_loop_cached(ctx, instance, &stubs),
        None => true,
    }
}

/// The fresh boolean `t` of an uncertified reach check, recorded as the freed
/// variable of `reason` (see the module docs). The caller records it as the
/// check's condition, with the walk's path condition.
pub(in crate::codegen_ay::chc) fn uncertified_reach_check(
    ctx: &mut ChcCtx<'_, '_>,
    reason: &'static str,
) -> Expr {
    let name = chc_fresh_name("__walker_uncertified_reach");
    // Rule E: the check is a fresh value standing on its own booking (the
    // reason, with the value's identity).
    let booked = ctx.record_sound_fallback_reason_identified(reason, Some(&name));
    Havoc::booked(booked, name, Sort::bool())
}

/// Can the blocks reachable from `start` in `body` carry an obligation Kani
/// checks? The region a SwitchInt arm abandons when the walker cannot finish
/// it: everything the arm's walk would have walked, to the body's return.
///
/// An obligation site is what the walker, or the callee it walks, would have
/// checked: a statement the obligation walk SIGHTS
/// (`obligation_free_walk::statement_verdict`: an unchecked or dividing
/// BinOp, a pointer offset, a raw-pointer access, an index, a signed
/// negation, `assume`, `copy_nonoverlapping`), an `Assert`, inline asm, a
/// diverging call, an `Unreachable` terminator, or a call or drop whose
/// callee can carry one ([`callee_may_carry_obligation`]). A statement the
/// walk cannot vouch for but does not sight (a float operation, a transmute)
/// is not counted: the walker records no check for it when it does finish a
/// body.
///
/// `Unreachable` is Kani's "unreachable code" check, and the walker records
/// it where it reaches one (`core::intrinsics::unreachable` lowers to it,
/// `c3_region_unreachable_intrinsic_bug`). The one exception is an
/// `Unreachable` reached only as the invalid-only `otherwise` arm
/// (`obligation_free_walk::enum_exhaustive_unreachable_blocks`): the
/// `otherwise` rustc adds to an exhaustive `match` on a data-carrying enum,
/// which no term of its datatype sort selects; the walker filters those arms
/// as dead. A fieldless enum's `otherwise` is a site (its bitvector can hold
/// bits written through memory).
pub(super) fn region_may_carry_obligation(ctx: &ChcCtx<'_, '_>, body: &Body, start: usize) -> bool {
    let locals = body.locals();
    let stubs = crate::kani_middle::transform::walker_stub_map();
    let exempt_unreachable =
        crate::codegen_ay::obligation_free_walk::enum_exhaustive_unreachable_blocks(body);
    // Sites that provably hold are not obligations (`region_intervals.rs`):
    // a bounds check on an index the body reduced modulo the length, an
    // overflow check that cannot overflow.
    let intervals =
        super::region_intervals::BodyIntervals::analyse(body, |ty| ctx.resolve_body_ty(ty));
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(bb) = stack.pop() {
        if !seen.insert(bb) {
            continue;
        }
        let Some(block) = body.blocks.get(bb) else {
            continue;
        };
        if block.statements.iter().any(|stmt| {
            statement_verdict(stmt, body) == Verdict::HasObligation
                && !intervals.statement_obligations_discharged(stmt)
        }) {
            return true;
        }
        // Normal-path successors only: the walker never walks an unwind
        // cleanup block (a panic is an error, not a path Kani continues).
        match &block.terminator.kind {
            TerminatorKind::Assert { cond, expected, target, .. } => {
                if !intervals.assert_holds(cond, *expected) {
                    return true;
                }
                stack.push(*target);
            }
            TerminatorKind::InlineAsm { .. } => return true,
            TerminatorKind::Unreachable => {
                if !exempt_unreachable.contains(&bb) {
                    return true;
                }
            }
            TerminatorKind::Call { func, target, .. } => {
                if callee_may_carry_obligation(ctx, func, locals, &stubs) {
                    return true;
                }
                stack.extend(*target);
            }
            TerminatorKind::Drop { place, target, .. } => {
                if drop_may_carry_obligation(ctx, place, locals, &stubs) {
                    return true;
                }
                stack.push(*target);
            }
            TerminatorKind::Goto { target } => stack.push(*target),
            TerminatorKind::SwitchInt { targets, .. } => {
                stack.extend(targets.branches().map(|(_, bb)| bb));
                stack.push(targets.otherwise());
            }
            _ => {}
        }
    }
    false
}

/// Can the blocks reachable from `start` in `body` fail Kani's UNWINDING
/// assertion? Only under a declared unwind bound (`#[kani::unwind(U)]`,
/// `--default-unwind`) with unwinding assertions on: Kani then passes every
/// loop header at most `U` times per entry, and a path that needs one more
/// pass fails. Yes when the region holds a loop (a cycle among its blocks,
/// normal edges only) or reaches a callee that may hold one
/// (`obligation_free_walk::instance_may_loop`, fail-closed where it cannot
/// tell).
///
/// The region a SwitchInt arm abandons (`switchint.rs`
/// `switchint_branch_fallback`) is exactly where the walker stopped
/// replaying: at its SwitchInt depth limit (16 nested branches, so the 17th
/// pass of a `while`, sooner with branches in the body) or past its replay
/// fuel (16 passes under a declared bound, the ceiling). The walker records
/// the unwinding assertion exactly only where it replays the pass that
/// exceeds the bound (`walker.rs`, `LoopHeaderVisit::UnwindExceeded`); an
/// abandoned loop takes the pass, and with it the failure, along. The region
/// scan counts only checks the walker would have recorded, and an
/// obligation-free loop body has none, so the arm was the value havoc and
/// the harness verified clean where Kani fails `unwinding assertion loop 0`
/// (walker fail-closed review 6, finding 4: unwind 6, 17, 19 and 20).
///
/// The cost is where a loop that stays within the bound outruns the walker's
/// replay: the arm fails closed (a reach check) where Kani proves. Measured
/// in docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: repair
/// round 1".
pub(super) fn region_may_fail_unwinding_assertion(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &super::loop_replay::InlineWalkCtx<'_>,
    start: usize,
) -> bool {
    if walk_ctx.declared_unwind().is_none() || !ctx.unwinding_assertions {
        return false;
    }
    let body = walk_ctx.body;
    let locals = body.locals();
    let stubs = crate::kani_middle::transform::walker_stub_map();
    let successors = |bb: usize| -> Vec<usize> {
        match body.blocks.get(bb).map(|block| &block.terminator.kind) {
            Some(TerminatorKind::Goto { target })
            | Some(TerminatorKind::Assert { target, .. })
            | Some(TerminatorKind::Drop { target, .. }) => vec![*target],
            Some(TerminatorKind::Call { target, .. }) => target.iter().copied().collect(),
            Some(TerminatorKind::SwitchInt { targets, .. }) => targets
                .branches()
                .map(|(_, bb)| bb)
                .chain(std::iter::once(targets.otherwise()))
                .collect(),
            Some(TerminatorKind::InlineAsm { destination, .. }) => {
                destination.iter().copied().collect()
            }
            _ => Vec::new(),
        }
    };
    // Depth-first over the region: an edge onto a block still on the DFS
    // path closes a cycle.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        OnPath,
        Done,
    }
    let mut marks: HashMap<usize, Mark> = HashMap::new();
    let mut stack: Vec<(usize, Vec<usize>)> = vec![(start, successors(start))];
    marks.insert(start, Mark::OnPath);
    let mut region: Vec<usize> = vec![start];
    while let Some((_, pending)) = stack.last_mut() {
        match pending.pop() {
            Some(next) => match marks.get(&next) {
                Some(Mark::OnPath) => return true,
                Some(Mark::Done) => {}
                None => {
                    marks.insert(next, Mark::OnPath);
                    region.push(next);
                    let next_successors = successors(next);
                    stack.push((next, next_successors));
                }
            },
            None => {
                let (done, _) = stack.pop().expect("invariant: non-empty");
                marks.insert(done, Mark::Done);
            }
        }
    }
    region.into_iter().any(|bb| match body.blocks.get(bb).map(|block| &block.terminator.kind) {
        Some(TerminatorKind::Call { func, target: Some(_), .. }) => {
            match super::terminator_exec::resolve_check_scan_instance(ctx, func, locals, &stubs) {
                Some(instance) => instance_may_loop_cached(ctx, instance, &stubs),
                None => true,
            }
        }
        Some(TerminatorKind::Drop { place, .. }) => match place.ty(locals) {
            Ok(ty) => match mono_ty::drop_in_place(ctx.resolve_body_ty(ty)) {
                None => true,
                Some(glue) => !glue.is_empty_shim() && instance_may_loop_cached(ctx, glue, &stubs),
            },
            Err(_) => true,
        },
        _ => false,
    })
}

/// `obligation_free_walk::instance_may_loop`, cached per instance and stub
/// map for the compilation, as [`instance_may_carry_obligation`] is.
pub(in crate::codegen_ay::chc) fn instance_may_loop_cached(
    ctx: &ChcCtx<'_, '_>,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    thread_local! {
        static LOOPS: RefCell<HashMap<(String, String), bool>> = RefCell::new(HashMap::new());
    }
    let key = (instance.mangled_name(), stub_map_fingerprint(stubs));
    if let Some(cached) = LOOPS.with(|loops| loops.borrow().get(&key).copied()) {
        return cached;
    }
    let may_loop =
        crate::codegen_ay::obligation_free_walk::instance_may_loop(ctx.tcx, instance, stubs);
    LOOPS.with(|loops| loops.borrow_mut().insert(key, may_loop));
    may_loop
}

/// Can the callee of `func` carry an obligation? `true` unless it resolves
/// (through the unit's stub map, `stubs`) and the obligation walk proves its
/// body, and everything it reaches in any crate, free of one: a function
/// pointer, a `dyn` method, an unresolvable or body-less callee may.
pub(super) fn callee_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
    stubs: &StubMap,
) -> bool {
    match super::terminator_exec::resolve_check_scan_instance(ctx, func, locals, stubs) {
        Some(instance) => instance_may_carry_obligation(ctx, instance, stubs),
        None => true,
    }
}

fn drop_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    place: &Place,
    locals: &[LocalDecl],
    stubs: &StubMap,
) -> bool {
    let Ok(ty) = place.ty(locals) else {
        return true;
    };
    match mono_ty::drop_in_place(ctx.resolve_body_ty(ty)) {
        None => true,
        Some(glue) => !glue.is_empty_shim() && instance_may_carry_obligation(ctx, glue, stubs),
    }
}

/// [`instance_obligation_verdict`] is not `Free`, cached per instance and stub
/// map for the compilation: the scan runs for every arm the walker abandons,
/// and those reach the same callees again and again. The stub map is part of
/// the key because it decides which bodies the walk reads, and harnesses of
/// one compilation stub differently.
fn instance_may_carry_obligation(
    ctx: &ChcCtx<'_, '_>,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    thread_local! {
        static VERDICTS: RefCell<HashMap<(String, String), Verdict>> = RefCell::new(HashMap::new());
    }
    let key = (instance.mangled_name(), stub_map_fingerprint(stubs));
    let cached = VERDICTS.with(|verdicts| verdicts.borrow().get(&key).copied());
    let verdict = cached.unwrap_or_else(|| {
        let verdict = instance_obligation_verdict(ctx.tcx, instance, stubs);
        VERDICTS.with(|verdicts| verdicts.borrow_mut().insert(key, verdict));
        verdict
    });
    verdict != Verdict::Free
}

/// A stable identity for a stub map (empty for none).
fn stub_map_fingerprint(stubs: &StubMap) -> String {
    let mut pairs: Vec<String> =
        stubs.iter().map(|(from, to)| format!("{:?}->{:?}", from.def_id(), to.def_id())).collect();
    pairs.sort();
    pairs.join(",")
}

/// Does the callee of `func` write nothing, in its body and everything it
/// reaches? `false` unless the walk reads every body to the end: an
/// assignment or `SetDiscriminant` through a pointer, `copy_nonoverlapping`,
/// inline asm, a drop, an indirect or unresolvable call, a body-less callee
/// that is not a pure intrinsic, or the budget, each answers "may write". A
/// call that never returns (a panic) writes nothing any continuing path sees.
///
/// For the nested-call fallback's `inline_nested_call_writes_through_pointer`
/// record, which keyed on the argument TYPES alone: `ptr::add(self, count)`
/// takes a raw pointer and writes nothing.
pub(super) fn callee_is_write_free(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let stubs = crate::kani_middle::transform::walker_stub_map();
    let Some(instance) =
        super::terminator_exec::resolve_check_scan_instance(ctx, func, locals, &stubs)
    else {
        return false;
    };
    let mut seen = HashSet::new();
    let mut budget = WRITE_FREE_WALK_BODIES;
    instance_is_write_free(ctx, instance, &stubs, &mut seen, &mut budget)
}

/// Bodies the write-freedom walk may read.
const WRITE_FREE_WALK_BODIES: usize = 64;

/// Intrinsics that read their operands and write nothing.
fn is_pure_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "offset"
            | "arith_offset"
            | "ptr_offset_from"
            | "ptr_offset_from_unsigned"
            | "size_of_val"
            | "align_of_val"
            | "vtable_size"
            | "vtable_align"
            | "ub_checks"
            | "contract_checks"
            | "overflow_checks"
            | "assume"
            | "likely"
            | "unlikely"
            | "cold_path"
            | "black_box"
            | "ptr_guaranteed_cmp"
            | "ctpop"
            | "ctlz"
            | "cttz"
            | "bswap"
            | "bitreverse"
            | "rotate_left"
            | "rotate_right"
            | "saturating_add"
            | "saturating_sub"
            | "wrapping_add"
            | "wrapping_sub"
            | "wrapping_mul"
            | "add_with_overflow"
            | "sub_with_overflow"
            | "mul_with_overflow"
            | "unchecked_add"
            | "unchecked_sub"
            | "unchecked_mul"
            | "unchecked_div"
            | "unchecked_rem"
            | "unchecked_shl"
            | "unchecked_shr"
            | "exact_div"
            | "three_way_compare"
            | "discriminant_value"
            | "ptr_metadata"
            | "aggregate_raw_ptr"
    )
}

fn instance_is_write_free(
    ctx: &ChcCtx<'_, '_>,
    instance: Instance,
    stubs: &StubMap,
    seen: &mut HashSet<String>,
    budget: &mut usize,
) -> bool {
    use rustc_public::mir::{NonDivergingIntrinsic, StatementKind};
    if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. }) {
        return false;
    }
    if !seen.insert(instance.mangled_name()) {
        return true;
    }
    if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Intrinsic) {
        return instance.intrinsic_name().is_some_and(|name| is_pure_intrinsic(name.as_str()));
    }
    if instance.is_empty_shim() {
        return true;
    }
    let Some(body) = crate::kani_middle::transform::walker_transformed_body(ctx.tcx, instance)
        .or_else(|| instance.callee_body())
    else {
        return false;
    };
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    let through_deref = |place: &Place| {
        place.projection.iter().any(|p| matches!(p, rustc_public::mir::ProjectionElem::Deref))
    };
    for block in &body.blocks {
        for stmt in &block.statements {
            let writes = match &stmt.kind {
                StatementKind::Assign(place, _) | StatementKind::SetDiscriminant { place, .. } => {
                    through_deref(place)
                }
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => true,
                _ => false,
            };
            if writes {
                return false;
            }
        }
        match &block.terminator.kind {
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Drop { .. } => return false,
            TerminatorKind::Call { target: None, .. } => {}
            TerminatorKind::Call { func, destination, .. } => {
                if through_deref(destination) {
                    return false;
                }
                let Some(callee) = super::terminator_exec::resolve_check_scan_instance(
                    ctx,
                    func,
                    body.locals(),
                    stubs,
                ) else {
                    return false;
                };
                if !instance_is_write_free(ctx, callee, stubs, seen, budget) {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

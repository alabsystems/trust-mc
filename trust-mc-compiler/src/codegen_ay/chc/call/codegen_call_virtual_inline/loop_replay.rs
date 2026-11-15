// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bounded loop replay for the CHC inline walker.
//!
//! Contains `InlineWalkCtx` (shared walker context), loop classification,
//! and fuel-based replay for small while-loops in inline method bodies.
//!
//! Part of #3853: CHC inline walker drops bounded helper loops.

use ay_bindings::Expr;
use rustc_public::mir::LocalDecl;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::super::inline_shared::PlaceResolver;
use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers, natural_loop_blocks};
/// Maximum number of loop-header processings during bounded inline replay.
/// With fuel = MAX_INLINE_LOOP_REPLAYS + 1 (includes initial entry), a loop
/// iterating at most MAX_INLINE_LOOP_REPLAYS + 1 times fully unrolls: the visit
/// that finds the fuel spent is the loop's LAST pass, where its exit test is
/// evaluated like any other branch. A path that comes back to the header after
/// that pass needs more iterations than the walker replays; the walk of that
/// path fails, and the SwitchInt arm it belongs to takes the bailed-arm
/// fallback (`switchint.rs`), which owns what the walk abandoned.
pub(in crate::codegen_ay::chc) const MAX_INLINE_LOOP_REPLAYS: usize = 4;

/// Extra header visits a loop earns, per header and walk, for iterations whose
/// exit test folds to a constant that continues the loop. Such an iteration
/// adds no branch to the replay, only straight-line terms, so it is not what
/// the fuel exists to bound: a constant-bound `while i < 10` replays exactly
/// instead of running out after five iterations (walker_loop_replay_dual.rs).
/// Bounded, because each replayed iteration is a nested walk. 64 (was 32 on
/// the first cut) covers `while i < 50` (`l_const50_last_bug`, Genuine on
/// the base, which replayed concrete loops without a bound, and uncertified
/// with 32); a longer constant loop outruns the replay and takes the
/// bailed-arm fallback, which fails closed where the rest of the loop can
/// carry a check.
const MAX_INLINE_CONCRETE_LOOP_REFUNDS: usize = 64;

/// The adaptive part of the concrete-iteration refund (package round 2 item
/// b): a header whose natural loop has `B` blocks may be refunded up to
/// `MAX_INLINE_CONCRETE_REPLAY_BLOCKS / B` iterations (never fewer than
/// [`MAX_INLINE_CONCRETE_LOOP_REFUNDS`], never more than
/// [`MAX_INLINE_CONCRETE_LOOP_REFUNDS_CAP`]), so a small constant loop
/// replays exactly well past 69 iterations while a large body still stops
/// early. Each refunded iteration is straight-line terms and one nested walk,
/// which grows the stack on demand (`switchint.rs`).
const MAX_INLINE_CONCRETE_REPLAY_BLOCKS: usize = 2048;

/// Ceiling on the adaptive refund of one header. Measured 2026-09-27 on a
/// one-accumulator loop with an assertion in its last iteration (ay
/// 22db3bcc1): 300 iterations verify in about 3 s, 400 in 4 s, 450 in 17 s,
/// and 500 did not finish in 400 s, the solver on the replayed chain, not the
/// walk. 256 keeps the replay well inside that; a longer loop takes the
/// bailed-arm fallback, which fails closed where the rest can carry a check.
const MAX_INLINE_CONCRETE_LOOP_REFUNDS_CAP: usize = 256;

/// Maximum number of natural loop headers admitted by the inline walker.
/// Part of #4050: `ArraySolver::remove_assignment` lowers to two natural loops
/// (search + tail-shift). Supporting that shape keeps the restore path precise
/// without reopening broad multi-loop bodies.
const MAX_INLINE_LOOP_HEADERS: usize = 2;

/// Ceiling on the per-header fuel a DECLARED unwind bound may buy. Replay is
/// a nested-ITE encoding, so an unbounded `#[kani::unwind(1000)]` would make
/// the walker emit an unusable term; past this the walker stops replaying and
/// the abandoned-arm fallback takes over, which under a declared bound counts
/// the loop's unwinding assertion as an obligation (`switchint.rs`), and the
/// top-level walk's written-out size is capped as well
/// (`walker.rs`, `MAX_DECLARED_REPLAY_TREE_NODES`). Raised from 16 to 32 in
/// walker fail-closed repair round 5: at 16 a loop needing 19 or 26 of the
/// 19 or 30 passes Kani unwinds failed closed where main and Kani prove it
/// (`rc_unwind.rs` `d4_unwind19_within_safe`, `d3_unwind30_within_safe`);
/// measured in docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed:
/// repair round 5".
const MAX_INLINE_DECLARED_UNWIND_FUEL: usize = 32;

/// Ceiling on the per-header fuel a caller's ASSUMED bound may buy without a
/// declared unwind (`InlineWalkCtx::raise_loop_fuel`). Kept at 16: the raise
/// replays every loop of every candidate the caller dispatches to
/// (`rg_region.rs`, walker fail-closed review 6 round 2, finding 7).
const MAX_INLINE_RAISED_FUEL: usize = 16;

/// Shared context for inline body walking (immutable across recursive calls).
pub(in crate::codegen_ay::chc) struct InlineWalkCtx<'a> {
    pub(in crate::codegen_ay::chc) body: &'a rustc_public::mir::Body,
    pub(in crate::codegen_ay::chc) locals: &'a [LocalDecl],
    pub(in crate::codegen_ay::chc) resolver: PlaceResolver<'a>,
    pub(in crate::codegen_ay::chc) effective_blocks: usize,
    pub(in crate::codegen_ay::chc) bb_idx: usize,
    /// Per-header fuel for bounded loop replay (#3853).
    pub(in crate::codegen_ay::chc) loop_header_fuel: RefCell<HashMap<usize, usize>>,
    /// The natural loop (header included) of every fuelled header.
    loop_blocks: HashMap<usize, HashSet<usize>>,
    /// Fuelled headers whose last pass this path has begun: the fuel was spent
    /// when the walk reached them. Coming back to one ends the path's walk.
    exhausted_loop_headers: RefCell<HashSet<usize>>,
    /// Concrete-iteration refunds left per fuelled header
    /// ([`MAX_INLINE_CONCRETE_LOOP_REFUNDS`]).
    loop_concrete_refunds: RefCell<HashMap<usize, usize>>,
    /// The harness's DECLARED unwind bound (`#[kani::unwind(U)]`,
    /// `--unwind`, `--default-unwind`), `0` when none. Under a declared bound
    /// the replay follows Kani's unwinding exactly (see
    /// [`Self::visit_loop_header`]): a loop's header may be passed `U` times
    /// per entry, and a path that needs pass `U + 1` is an unwinding-assertion
    /// failure, not a path the walker gave up on.
    declared_unwind: usize,
    /// Header passes of the current loop entry, per fuelled header (declared
    /// unwind only).
    loop_passes: RefCell<HashMap<usize, usize>>,
    /// Each fuelled header's initial fuel and refunds, restored when the loop
    /// is entered afresh (declared unwind only: Kani counts per entry).
    initial_fuel: HashMap<usize, usize>,
    initial_refunds: HashMap<usize, usize>,
    /// Part of #4050: Cache for SwitchInt branch overapprox variables.
    /// Key: (switchint_bb, target_bb). Prevents duplication across loop
    /// unrollings — the same failing edge reuses the same symbolic variable.
    pub(in crate::codegen_ay::chc) switchint_overapprox_cache:
        RefCell<HashMap<(usize, usize), Expr>>,
    /// The freed reach variable and the assume-pruned value of each
    /// abandoned edge whose region can carry an obligation, per
    /// `(switchint_bb, target_bb)` (`switchint.rs`
    /// `switchint_branch_fallback`), shared by every path that reaches it.
    pub(in crate::codegen_ay::chc) bailed_arm_reach_cache: RefCell<HashMap<(usize, usize), Expr>>,
    pub(in crate::codegen_ay::chc) bailed_arm_pruned_cache: RefCell<HashMap<(usize, usize), Expr>>,
}

impl<'a> InlineWalkCtx<'a> {
    pub(in crate::codegen_ay::chc) fn new_with_loop_fuel_override(
        body: &'a rustc_public::mir::Body,
        resolver: PlaceResolver<'a>,
        effective_blocks: usize,
        bb_idx: usize,
        loop_fuel_override: Option<usize>,
    ) -> Self {
        Self::new_with_loop_policy(body, resolver, effective_blocks, bb_idx, loop_fuel_override, 0)
    }

    /// Like [`Self::new_with_loop_fuel_override`], but honours a harness's
    /// DECLARED unwind bound (`--default-unwind N` / `#[kani::unwind(N)]`).
    ///
    /// The declared bound RAISES the per-header fuel; it never lowers it. Kani
    /// semantics are "unroll N times", so a harness that asks for 12 and gets
    /// the built-in 5 silently loses every constraint the later iterations
    /// carry — an `assume` accumulated past the bound is simply dropped and the
    /// loop's residual becomes a free variable, which is how a fully-constrained
    /// harness ends up with a refutable assertion. `loop_fuel_override` (the
    /// spawn-scheduler model) still clamps DOWNWARD, which is a deliberate
    /// narrowing of a known-shaped runtime loop, not a bound the user declared.
    pub(in crate::codegen_ay::chc) fn new_with_loop_policy(
        body: &'a rustc_public::mir::Body,
        resolver: PlaceResolver<'a>,
        effective_blocks: usize,
        bb_idx: usize,
        loop_fuel_override: Option<usize>,
        declared_unwind: usize,
    ) -> Self {
        let (fuel, loop_blocks) = build_inline_loop_policy(body, declared_unwind);
        // The spawn scheduler's clamp is a deliberate narrowing of a
        // known-shaped runtime loop: no refunds there. Elsewhere a constant
        // iteration is refunded up to the adaptive budget.
        let loop_concrete_refunds: HashMap<usize, usize> = fuel
            .keys()
            .map(|&header| {
                let refunds = if loop_fuel_override.is_some() {
                    0
                } else {
                    let blocks = loop_blocks.get(&header).map_or(1, HashSet::len).max(1);
                    (MAX_INLINE_CONCRETE_REPLAY_BLOCKS / blocks).clamp(
                        MAX_INLINE_CONCRETE_LOOP_REFUNDS,
                        MAX_INLINE_CONCRETE_LOOP_REFUNDS_CAP,
                    )
                };
                (header, refunds)
            })
            .collect();
        let loop_policy = apply_loop_fuel_override(fuel, loop_fuel_override);
        Self {
            body,
            locals: body.locals(),
            resolver,
            effective_blocks,
            bb_idx,
            initial_fuel: loop_policy.clone(),
            initial_refunds: loop_concrete_refunds.clone(),
            loop_header_fuel: RefCell::new(loop_policy),
            loop_blocks,
            exhausted_loop_headers: RefCell::new(HashSet::new()),
            loop_concrete_refunds: RefCell::new(loop_concrete_refunds),
            declared_unwind,
            loop_passes: RefCell::new(HashMap::new()),
            switchint_overapprox_cache: RefCell::new(HashMap::new()),
            bailed_arm_reach_cache: RefCell::new(HashMap::new()),
            bailed_arm_pruned_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Can a replay raised for an assumed bound `bound` (`walker.rs`,
    /// `raise_loop_fuel(bound + 1)`) pass a loop bounded by it to its exit,
    /// within the declared-unwind ceiling? Past the ceiling the raised walk
    /// still abandons the loop, and its arm keeps the reach check the raise
    /// exists to make infeasible.
    pub(in crate::codegen_ay::chc) fn raise_covers(bound: usize) -> bool {
        bound.saturating_add(1) <= MAX_INLINE_RAISED_FUEL
    }

    /// Raise every fuelled header's fuel to at least `fuel`, up to the
    /// raise ceiling ([`MAX_INLINE_RAISED_FUEL`]): more replay, never less
    /// (the caller's assumed bound, `walker.rs`).
    pub(in crate::codegen_ay::chc) fn raise_loop_fuel(&mut self, fuel: usize) {
        let fuel = fuel.min(MAX_INLINE_RAISED_FUEL);
        for (header, initial) in &mut self.initial_fuel {
            if *initial < fuel {
                *initial = fuel;
                self.loop_header_fuel.get_mut().insert(*header, fuel);
            }
        }
    }

    /// The headers of the loops the replay fuels.
    pub(in crate::codegen_ay::chc) fn fuelled_headers(&self) -> impl Iterator<Item = usize> + '_ {
        self.initial_fuel.keys().copied()
    }

    /// The SwitchInt nesting this walk may reach (`switchint.rs`): `base`
    /// (`MAX_SWITCHINT_DEPTH`), or under a declared unwind bound `U` one more
    /// than the passes the declared fuel replays, `min(U, ceiling + 1) + 1`,
    /// when that is deeper. A `while` takes one level per pass, so at `base`
    /// the 17th pass was cut by depth whatever the fuel (walker fail-closed
    /// repair round 5, `rc_unwind.rs` `d3`, `d4`). The walk-node budget
    /// still bounds a branching body (`switchint_walk_node_budget`).
    pub(in crate::codegen_ay::chc) fn switchint_depth_limit(&self, base: usize) -> usize {
        if self.declared_unwind == 0 {
            return base;
        }
        base.max(self.declared_unwind.min(MAX_INLINE_DECLARED_UNWIND_FUEL + 1) + 1)
    }

    /// The declared unwind bound the replay follows exactly, `None` without
    /// one (see [`Self::visit_loop_header`]).
    pub(in crate::codegen_ay::chc) fn declared_unwind(&self) -> Option<usize> {
        (self.declared_unwind > 0).then_some(self.declared_unwind)
    }

    pub(in crate::codegen_ay::chc) fn snapshot_loop_header_fuel(&self) -> HashMap<usize, usize> {
        self.loop_header_fuel.borrow().clone()
    }

    /// The whole loop-replay state of the current path, which every SwitchInt
    /// arm walk starts from.
    pub(in crate::codegen_ay::chc) fn snapshot_loop_replay(&self) -> LoopReplaySnapshot {
        LoopReplaySnapshot {
            fuel: self.loop_header_fuel.borrow().clone(),
            exhausted: self.exhausted_loop_headers.borrow().clone(),
            refunds: self.loop_concrete_refunds.borrow().clone(),
            passes: self.loop_passes.borrow().clone(),
        }
    }

    pub(in crate::codegen_ay::chc) fn restore_loop_replay(&self, snapshot: &LoopReplaySnapshot) {
        *self.loop_header_fuel.borrow_mut() = snapshot.fuel.clone();
        *self.exhausted_loop_headers.borrow_mut() = snapshot.exhausted.clone();
        *self.loop_concrete_refunds.borrow_mut() = snapshot.refunds.clone();
        *self.loop_passes.borrow_mut() = snapshot.passes.clone();
    }

    /// Account one visit of `bb` against its loop's fuel.
    ///
    /// Not a fuelled header, or fuel left: [`LoopHeaderVisit::Continue`] (the
    /// fuel is spent). Fuel spent: the first such visit on a path is the loop's
    /// last pass ([`LoopHeaderVisit::LastPass`]); the walk goes on and the exit
    /// test decides, exactly. A later one means the path needs more iterations
    /// than the walker replays ([`LoopHeaderVisit::Outrun`]).
    ///
    /// Before 2026-09-26 a spent header made the walk jump to its SwitchInt's
    /// `otherwise` target without evaluating the exit test. For `while c {..}`
    /// that target is the loop BODY (MIR switches on `c` as `[0: exit,
    /// otherwise: body]`), so the walk ran one more iteration than the program
    /// on paths where `c` was false; for `if c { break }` it is the exit, and
    /// the walk left the loop with the state of the last replayed iteration,
    /// dropping every later iteration's checks and effects.
    ///
    /// Under a DECLARED unwind bound `U` (package round 2 item b), the replay
    /// follows Kani, which unwinds every loop `U` times per entry: the header
    /// may be passed `U` times, the `U`-th pass must leave the loop, and a
    /// path that needs pass `U + 1` fails Kani's unwinding assertion (or,
    /// with unwinding assertions off, is cut). Measured with the corpus-rev
    /// Kani on `while`, `loop { if .. break }` and `for` loops: two
    /// iterations pass under `unwind(3)` and fail under `unwind(2)`. Such a
    /// pass is [`LoopHeaderVisit::UnwindExceeded`], which the walk records as
    /// that failure exactly: it is certifiable, and it is no longer the
    /// bailed-arm havoc whose freed value kept every counterexample of the
    /// harness uncertified (`l_break_nested_call_bug`, walker fail-closed
    /// review finding 7b). The passes are counted per ENTRY: `from` is the
    /// block the walk comes from, and entering the loop from outside it (a
    /// nested loop's next outer iteration) restarts its count, fuel and
    /// refunds, as Kani's unwinding does. The fuel then only bounds how many
    /// symbolic passes the walker replays. A path the walker abandons before
    /// it reaches pass `U + 1` (past the fuel ceiling, or at the SwitchInt
    /// depth limit) records no unwinding failure here; the abandoned arm's
    /// region holds the loop, which counts as an obligation under a declared
    /// bound (`uncertified_check::region_may_fail_unwinding_assertion`), so it
    /// fails closed. Until repair round 1 it did not: an obligation-free loop
    /// body made the arm the value havoc, and Kani's unwinding failure was
    /// lost (walker fail-closed review 6, finding 4).
    pub(in crate::codegen_ay::chc) fn visit_loop_header(
        &self,
        bb: usize,
        from: Option<usize>,
    ) -> LoopHeaderVisit {
        if self.declared_unwind > 0 && self.initial_fuel.contains_key(&bb) {
            let entered = from.is_none_or(|pred| {
                self.loop_blocks.get(&bb).is_none_or(|blocks| !blocks.contains(&pred))
            });
            let mut passes = self.loop_passes.borrow_mut();
            if entered {
                passes.insert(bb, 0);
                self.loop_header_fuel.borrow_mut().insert(bb, self.initial_fuel[&bb]);
                self.exhausted_loop_headers.borrow_mut().remove(&bb);
                if let Some(&refunds) = self.initial_refunds.get(&bb) {
                    self.loop_concrete_refunds.borrow_mut().insert(bb, refunds);
                }
            }
            let pass = passes.entry(bb).or_insert(0);
            *pass += 1;
            if *pass > self.declared_unwind {
                return LoopHeaderVisit::UnwindExceeded;
            }
        }
        let mut fuel = self.loop_header_fuel.borrow_mut();
        let Some(left) = fuel.get_mut(&bb) else {
            return LoopHeaderVisit::Continue;
        };
        if *left > 0 {
            *left -= 1;
            return LoopHeaderVisit::Continue;
        }
        if self.exhausted_loop_headers.borrow_mut().insert(bb) {
            LoopHeaderVisit::LastPass
        } else {
            LoopHeaderVisit::Outrun
        }
    }

    /// A SwitchInt at `switchint_bb` whose discriminant folded to a constant
    /// selecting `taken`: when it is the exit test of a fuelled loop (a target
    /// leaves the loop) and `taken` stays in the loop, this concrete iteration
    /// is refunded its header visit, up to [`MAX_INLINE_CONCRETE_LOOP_REFUNDS`].
    /// Returns the headers refunded.
    ///
    /// The exit test is the header's own: the first branch the loop reaches
    /// from its header ([`Self::header_exit_test`]). A later test with an edge
    /// out of the loop (an early `return` or `break` inside the body) folding
    /// to "stay" says nothing about the loop's trip count: `iter().any(|_|
    /// false)` folded the closure's `if f(x) { return true }` every pass
    /// while `next()`'s test stayed symbolic, so every pass was refunded, the
    /// replay ran to the SwitchInt depth limit instead of its fuel, and the
    /// terms it built did not compile in 600 s (walker fail-closed review 6
    /// round 3, `q6_closure_helpers.rs`, `q10_any_shapes.rs`).
    pub(in crate::codegen_ay::chc) fn refund_concrete_loop_iteration(
        &self,
        switchint_bb: usize,
        targets: &rustc_public::mir::SwitchTargets,
        taken: usize,
    ) -> Vec<usize> {
        let mut refunded = Vec::new();
        for (&header, blocks) in &self.loop_blocks {
            if !blocks.contains(&switchint_bb) || !blocks.contains(&taken) {
                continue;
            }
            let leaves_loop = targets
                .branches()
                .map(|(_, bb)| bb)
                .chain(std::iter::once(targets.otherwise()))
                .any(|bb| !blocks.contains(&bb));
            if !leaves_loop || self.header_exit_test(header, blocks) != Some(switchint_bb) {
                continue;
            }
            let mut refunds = self.loop_concrete_refunds.borrow_mut();
            let Some(left) = refunds.get_mut(&header).filter(|left| **left > 0) else {
                continue;
            };
            *left -= 1;
            #[cfg(test)]
            CONCRETE_LOOP_REFUNDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            *self.loop_header_fuel.borrow_mut().entry(header).or_insert(0) += 1;
            self.exhausted_loop_headers.borrow_mut().remove(&header);
            refunded.push(header);
        }
        refunded
    }

    /// The first branch of the loop at `header` (whose blocks are `blocks`):
    /// the SwitchInt reached from the header along its single successors
    /// (gotos, returning calls, asserts, drops), all inside the loop. `None`
    /// when that chain ends any other way.
    fn header_exit_test(&self, header: usize, blocks: &HashSet<usize>) -> Option<usize> {
        use rustc_public::mir::TerminatorKind;
        let mut bb = header;
        for _ in 0..=blocks.len() {
            let next = match &self.body.blocks.get(bb)?.terminator.kind {
                TerminatorKind::SwitchInt { .. } => return Some(bb),
                TerminatorKind::Goto { target } => *target,
                TerminatorKind::Call { target: Some(target), .. } => *target,
                TerminatorKind::Assert { target, .. } => *target,
                TerminatorKind::Drop { target, .. } => *target,
                _ => return None,
            };
            if !blocks.contains(&next) || next == header {
                return None;
            }
            bb = next;
        }
        None
    }
}

/// Concrete loop iterations refunded so far (`refund_concrete_loop_iteration`),
/// for tests.
#[cfg(test)]
pub(in crate::codegen_ay::chc) static CONCRETE_LOOP_REFUNDS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// See [`InlineWalkCtx::snapshot_loop_replay`].
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct LoopReplaySnapshot {
    fuel: HashMap<usize, usize>,
    exhausted: HashSet<usize>,
    refunds: HashMap<usize, usize>,
    passes: HashMap<usize, usize>,
}

/// See [`InlineWalkCtx::visit_loop_header`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum LoopHeaderVisit {
    Continue,
    LastPass,
    Outrun,
    /// A pass past the DECLARED unwind bound: Kani's unwinding assertion
    /// fails on this path (see [`InlineWalkCtx::visit_loop_header`]).
    UnwindExceeded,
}

fn apply_loop_fuel_override(
    mut fuel: HashMap<usize, usize>,
    loop_fuel_override: Option<usize>,
) -> HashMap<usize, usize> {
    let Some(loop_fuel_override) = loop_fuel_override else {
        return fuel;
    };
    let loop_fuel_override = loop_fuel_override.max(1);
    for fuel_value in fuel.values_mut() {
        *fuel_value = (*fuel_value).min(loop_fuel_override);
    }
    fuel
}

/// Build the per-header fuel map for bounded inline loop replay, with each
/// fuelled header's natural loop.
///
/// Both are empty for acyclic bodies, irreducible cycles, or bodies with more
/// than `MAX_INLINE_LOOP_HEADERS` natural loop headers.
fn build_inline_loop_policy(
    body: &rustc_public::mir::Body,
    declared_unwind: usize,
) -> (HashMap<usize, usize>, HashMap<usize, HashSet<usize>>) {
    let cfg = Cfg::from_body(body);
    if cfg.is_acyclic() {
        return (HashMap::new(), HashMap::new());
    }
    let headers = match find_loop_headers(&cfg) {
        Ok(h) => h,
        Err(_) => return (HashMap::new(), HashMap::new()),
    };
    if headers.len() > MAX_INLINE_LOOP_HEADERS {
        debug!(
            header_count = headers.len(),
            max_headers = MAX_INLINE_LOOP_HEADERS,
            "inline loop policy: skipping body with too many loop headers (#3853, #4050)"
        );
        return (HashMap::new(), HashMap::new());
    }
    // A declared unwind bound `U` sets the fuel: Kani passes a header `U`
    // times per entry, and the pass that finds the fuel spent is the last
    // (`InlineWalkCtx::visit_loop_header`), so `U - 1` fuel replays exactly
    // Kani's passes, up to the ceiling. Without one the built-in replay count
    // applies.
    let fuel_each = if declared_unwind > 0 {
        declared_unwind.saturating_sub(1).min(MAX_INLINE_DECLARED_UNWIND_FUEL)
    } else {
        MAX_INLINE_LOOP_REPLAYS + 1
    };
    let mut fuel = HashMap::new();
    let mut loop_blocks = HashMap::new();
    for (&header, latches) in &headers {
        fuel.insert(header, fuel_each);
        loop_blocks.insert(header, natural_loop_blocks(&cfg, header, latches));
    }
    debug!(
        header_count = fuel.len(),
        fuel_each, declared_unwind, "inline loop policy: admitted multi-header body (#3853, #4050)"
    );
    (fuel, loop_blocks)
}

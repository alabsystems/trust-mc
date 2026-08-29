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
use rustc_public::ty::{RigidTy, TyKind};
use std::cell::RefCell;
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::PlaceResolver;
use super::InlineReturn;
use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers};
/// Maximum number of loop-header processings during bounded inline replay.
/// With fuel = MAX_INLINE_LOOP_REPLAYS + 1 (includes initial entry), a loop
/// iterating at most MAX_INLINE_LOOP_REPLAYS times fully unrolls. Beyond that,
/// a fresh symbolic over-approximation is returned (sound).
pub(in crate::codegen_ay::chc) const MAX_INLINE_LOOP_REPLAYS: usize = 4;

/// Maximum number of natural loop headers admitted by the inline walker.
/// Part of #4050: `ArraySolver::remove_assignment` lowers to two natural loops
/// (search + tail-shift). Supporting that shape keeps the restore path precise
/// without reopening broad multi-loop bodies.
const MAX_INLINE_LOOP_HEADERS: usize = 2;

/// Ceiling on the per-header fuel a DECLARED unwind bound may buy. Replay is
/// a nested-ITE encoding, so an unbounded `#[kani::unwind(1000)]` would make
/// the walker emit an unusable term; past this the walker stops replaying and
/// the existing bounded-replay fallbacks take over.
const MAX_INLINE_DECLARED_UNWIND_FUEL: usize = 16;

/// Shared context for inline body walking (immutable across recursive calls).
pub(in crate::codegen_ay::chc) struct InlineWalkCtx<'a> {
    pub(in crate::codegen_ay::chc) body: &'a rustc_public::mir::Body,
    pub(in crate::codegen_ay::chc) locals: &'a [LocalDecl],
    pub(in crate::codegen_ay::chc) resolver: PlaceResolver<'a>,
    pub(in crate::codegen_ay::chc) effective_blocks: usize,
    pub(in crate::codegen_ay::chc) bb_idx: usize,
    /// Per-header fuel for bounded loop replay (#3853).
    pub(in crate::codegen_ay::chc) loop_header_fuel: RefCell<HashMap<usize, usize>>,
    /// Part of #4050: Cache for SwitchInt branch overapprox variables.
    /// Key: (switchint_bb, target_bb). Prevents duplication across loop
    /// unrollings — the same failing edge reuses the same symbolic variable.
    pub(in crate::codegen_ay::chc) switchint_overapprox_cache:
        RefCell<HashMap<(usize, usize), Expr>>,
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
        let loop_policy = apply_loop_fuel_override(
            build_inline_loop_policy(body, declared_unwind),
            loop_fuel_override,
        );
        Self {
            body,
            locals: body.locals(),
            resolver,
            effective_blocks,
            bb_idx,
            loop_header_fuel: RefCell::new(loop_policy),
            switchint_overapprox_cache: RefCell::new(HashMap::new()),
        }
    }

    pub(in crate::codegen_ay::chc) fn snapshot_loop_header_fuel(&self) -> HashMap<usize, usize> {
        self.loop_header_fuel.borrow().clone()
    }

    pub(in crate::codegen_ay::chc) fn restore_loop_header_fuel(
        &self,
        fuel: &HashMap<usize, usize>,
    ) {
        *self.loop_header_fuel.borrow_mut() = fuel.clone();
    }
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

/// Build per-header fuel map for bounded inline loop replay.
///
/// Returns empty map for acyclic bodies, irreducible cycles, or bodies with
/// more than `MAX_INLINE_LOOP_HEADERS` natural loop headers.
fn build_inline_loop_policy(
    body: &rustc_public::mir::Body,
    declared_unwind: usize,
) -> HashMap<usize, usize> {
    let cfg = Cfg::from_body(body);
    if cfg.is_acyclic() {
        return HashMap::new();
    }
    let headers = match find_loop_headers(&cfg) {
        Ok(h) => h,
        Err(_) => return HashMap::new(),
    };
    if headers.len() > MAX_INLINE_LOOP_HEADERS {
        debug!(
            header_count = headers.len(),
            max_headers = MAX_INLINE_LOOP_HEADERS,
            "inline loop policy: skipping body with too many loop headers (#3853, #4050)"
        );
        return HashMap::new();
    }
    // A declared unwind bound RAISES the fuel (Kani `unwind(N)` = unroll N
    // times); the built-in replay count is the FLOOR, never the ceiling.
    let fuel_each = (MAX_INLINE_LOOP_REPLAYS + 1)
        .max(declared_unwind.min(MAX_INLINE_DECLARED_UNWIND_FUEL).saturating_add(1));
    let mut fuel = HashMap::new();
    for &header in headers.keys() {
        fuel.insert(header, fuel_each);
    }
    debug!(
        header_count = fuel.len(),
        fuel_each, declared_unwind, "inline loop policy: admitted multi-header body (#3853, #4050)"
    );
    fuel
}

/// Return a fresh symbolic over-approximation when loop replay fuel is
/// exhausted. Sound: the result is nondeterministic.
pub(in crate::codegen_ay::chc) fn loop_exhaustion_fallback<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
) -> Option<InlineReturn> {
    // Part of #3955: resolve return local through body-local normalization.
    let ret_ty = ctx.resolve_inline_local_ty(walk_ctx.body, 0).unwrap_or(walk_ctx.locals[0].ty);
    let ret_sort = match ret_ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
            Expr::bool_const(true).sort().clone()
        }
        _ => ChcCtx::translate_ty(ret_ty)?,
    };
    debug!(
        bb_idx = walk_ctx.bb_idx,
        "virtual body: loop replay fuel exhausted, over-approximating (#3853)"
    );
    let name = super::super::chc_fresh_name("__loop_exhaust_inline");
    // Route through the per-fn reason map WITH the freed variable's identity.
    // Bumping `place_translation_drop` directly (the previous code) kept the
    // fail-closed proof behaviour but left the approximation UNACCOUNTED, so
    // the driver could never tell whether a counterexample actually read this
    // value — it had to leave every one of them certified Genuine.
    ctx.record_sound_fallback_reason_identified("inline_loop_replay_exhausted", Some(&name));
    Some(InlineReturn::value_only(super::super::declare_pending_var(name, ret_sort)))
}

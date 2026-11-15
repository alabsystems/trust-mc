// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A write through a NON-ARGUMENT pointer local inside an inline walk
//! (review finding M1 of design 2 Phase 0, `docs/chc-hole-fix-designs-2026-09-24.md`).
//!
//! The walker models references transparently: `let p = &mut x` binds `p` to
//! `x`'s TERM, and `*p = v` takes the functional lane, which rebinds `p` to the
//! updated pointee and nothing else. `x` keeps its old term, and a later read
//! of `x` has no `Deref`, so F1 never sees it: the read returns the value from
//! before the write. An argument's rebind reaches the caller as an alias
//! update; a non-argument local's reaches nothing.
//!
//! The walked body usually names the referent: `p = &mut x`,
//! `p = &mut (*q).f`, `p = &raw mut arr[i]`, `p = copy q`, `p = q as *mut T`.
//! When every definition of `p` names the same place, and every local that
//! place reads (an `Index` operand, the root of a leading `Deref`) has no other
//! definition, the write is applied to that place as well, through the
//! ordinary lanes, so the referent holds the written value (and, through an
//! argument, the caller does). Otherwise the write is recorded as lost
//! (`walker_deref_write_rebind_lost`), which fails closed.

use ay_bindings::Expr;
use rustc_public::mir::{
    Body, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_walk_guard::WALKER_DEREF_WRITE_REBIND_LOST;
use super::execution_state::InlineExecutionState;
use super::loop_replay::InlineWalkCtx;
use super::statement_exec::{note_projected_write_effects, write_inline_projected_value};

/// How many referent hops one write follows (`p = &mut *q`, `q = &mut x`, ...).
const REFERENT_HOPS: usize = 8;

/// Whether `local` is an argument of `body` (MIR numbers them `1..=n`).
fn is_arg_local(body: &Body, local: usize) -> bool {
    (1..=body.arg_locals().len()).contains(&local)
}

/// How many statements and terminators of `body` can change `local`'s value:
/// assignments to it or to a part of it (not a write THROUGH it, which starts
/// with a `Deref`), `SetDiscriminant`s, and call destinations. `usize::MAX`
/// when the body has inline assembly, whose outputs are not tracked here.
fn value_definitions(body: &Body, local: usize) -> usize {
    let through_pointer =
        |place: &Place| matches!(place.projection.first(), Some(ProjectionElem::Deref));
    let mut count = 0usize;
    for block in &body.blocks {
        for stmt in &block.statements {
            let place = match &stmt.kind {
                StatementKind::Assign(place, _) | StatementKind::SetDiscriminant { place, .. } => {
                    place
                }
                _ => continue,
            };
            if place.local == local && !through_pointer(place) {
                count += 1;
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => count += 1,
            TerminatorKind::InlineAsm { .. } => return usize::MAX,
            _ => {}
        }
    }
    count
}

/// Whether `local` holds, at every point after its definition, the value it
/// was defined with: an argument the body never reassigns, or a local with at
/// most one definition.
fn holds_one_value(body: &Body, local: usize) -> bool {
    let defs = value_definitions(body, local);
    if is_arg_local(body, local) { defs == 0 } else { defs <= 1 }
}

/// The place the non-argument pointer local `local` points at, as `body` names
/// it, or `None` when it does not name exactly one.
///
/// Every whole-local definition of `local` must be `&place`, `&raw place`, or a
/// copy, move or cast of another pointer local `q` (whose referent is `*q`),
/// and all of them must name the same place; a call destination defines it
/// with a place the body does not name. The place is read when it is
/// borrowed, so every local it reads (an `Index` operand, the root of a leading
/// `Deref`) must hold one value throughout, or the place named now could be a
/// different one than the place borrowed then. Its root local needs no such
/// condition: a local's address does not change when it is reassigned.
pub(super) fn resolve_nonarg_pointer_referent(body: &Body, local: usize) -> Option<Place> {
    if is_arg_local(body, local) {
        return None;
    }
    let mut referent: Option<Place> = None;
    for block in &body.blocks {
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => return None,
            TerminatorKind::InlineAsm { .. } => return None,
            _ => {}
        }
        for stmt in &block.statements {
            let (lhs, rvalue) = match &stmt.kind {
                StatementKind::Assign(lhs, rvalue) => (lhs, rvalue),
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return None;
                }
                _ => continue,
            };
            if lhs.local != local {
                continue;
            }
            if !lhs.projection.is_empty() {
                // A write THROUGH the pointer (`*p = v`) does not redefine it.
                if matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
                    continue;
                }
                return None;
            }
            let candidate = match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => place.clone(),
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                | Rvalue::CopyForDeref(src)
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() =>
                {
                    Place { local: src.local, projection: vec![ProjectionElem::Deref] }
                }
                _ => return None,
            };
            match &referent {
                Some(existing) if *existing != candidate => return None,
                _ => referent = Some(candidate),
            }
        }
    }
    let referent = referent?;
    for (position, proj) in referent.projection.iter().enumerate() {
        let stable = match proj {
            ProjectionElem::Deref if position == 0 => holds_one_value(body, referent.local),
            // Runtime MIR puts a `Deref` first; any other position is not a
            // place this module composes.
            ProjectionElem::Deref => false,
            ProjectionElem::Index(index) => holds_one_value(body, *index),
            ProjectionElem::Field(..)
            | ProjectionElem::Downcast(_)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. } => true,
            #[allow(unreachable_patterns)]
            _ => false,
        };
        if !stable {
            return None;
        }
    }
    Some(referent)
}

/// `referent` followed by the projections of a write that came after its
/// leading `Deref` (`(*p).f` through `p = &mut x` is `x.f`).
fn compose_referent_place(referent: Place, rest: &[ProjectionElem]) -> Place {
    let mut projection = referent.projection;
    projection.extend(rest.iter().cloned());
    Place { local: referent.local, projection }
}

/// M1: the functional lane rebound the non-argument pointer local
/// `place.local` (whose term was its referent's VALUE, not a memory address)
/// to the updated pointee. Apply the same write to the referent the walked
/// body names, through the ordinary projected-write lanes, so the referent
/// (and, through an argument, the caller) holds the written value too.
/// Record the write as lost when the referent is not named or cannot take it.
///
/// Other reference locals whose terms still hold the old value (`q` after
/// `p = &mut *q`) are read through a `Deref`, which F1 fails closed after this
/// write.
#[allow(clippy::too_many_arguments)]
pub(super) fn write_through_nonarg_referent(
    ctx: &mut ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    place: &Place,
    rhs: &Expr,
    rhs_vtable: Option<Expr>,
    hops: usize,
) {
    let target = if hops < REFERENT_HOPS {
        resolve_nonarg_pointer_referent(walk_ctx.body, place.local)
            .map(|referent| compose_referent_place(referent, &place.projection[1..]))
    } else {
        None
    };
    let Some(target) = target else {
        debug!(
            bb_idx = walk_ctx.bb_idx,
            local = place.local,
            hops,
            "walker: deref write rebinds a non-argument pointer local whose referent is not named — write lost"
        );
        ctx.record_sound_fallback_reason(WALKER_DEREF_WRITE_REBIND_LOST);
        return;
    };
    let effects_before = ctx.heap_state.effect_mark();
    match write_inline_projected_value(
        ctx,
        walk_ctx,
        state,
        &target,
        rhs.clone(),
        rhs_vtable,
        hops + 1,
    ) {
        Some(lane) => {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                local = place.local,
                target_local = target.local,
                target_projection = ?target.projection,
                ?lane,
                "walker: deref write through a non-argument pointer local applied to its referent"
            );
            note_projected_write_effects(ctx, walk_ctx, state, &target, lane, effects_before);
        }
        None => {
            debug!(
                bb_idx = walk_ctx.bb_idx,
                local = place.local,
                target_local = target.local,
                "walker: the referent of a non-argument pointer local could not take the write — write lost"
            );
            ctx.record_sound_fallback_reason(WALKER_DEREF_WRITE_REBIND_LOST);
        }
    }
}

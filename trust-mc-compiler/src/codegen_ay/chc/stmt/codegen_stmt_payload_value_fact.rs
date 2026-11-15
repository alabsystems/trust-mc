// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A payload VALUE fact that every producer agrees on.
//!
//! The slice `Iterator::next` stub stores the ELEMENT, not an address, in the
//! payload slot of its `Option<&T>` destination, and records that slot's input
//! state variable in `const_ref_values`, so `*payload` reads the slot.
//! `propagate_ref_metadata` copies path-insensitive facts only between locals
//! with one producer each. Loop unwinding duplicates the `next` call and the
//! payload copy `_42 = copy ((_39 as Some).0)` into every unwound body, so the
//! fact was dropped and the deref failed closed (`deref_value_fact_dropped`):
//! kani/SwitchInt/main.rs went from a 3.4 s encoding_gap to a 49 s unknown.
//!
//! [`ChcCtx::keep_agreeing_payload_value_fact`] keeps the fact only when it
//! holds on every path; otherwise the fail-closed guard stays:
//!
//! 1. The source's fact is the slot convention itself: the input state variable
//!    of the source's own payload slot. That term names the source's current
//!    payload whichever producer ran.
//! 2. Every whole definition of the destination is the same statement
//!    `dest = copy ((src as V).0)`: no call, no partial write, no other source.
//! 3. The source is written only by `Call` terminators to one callee, never by
//!    a statement; neither local's own storage is ever borrowed; neither is an
//!    argument. No write can escape the producer list.
//! 4. At every source producer, and at every `StorageDead` of the source, the
//!    copied payload is not READABLE. Two halves: a forward may-analysis of "a
//!    payload copy was made on this path" (a whole assignment of the
//!    destination gens; nothing kills, because the fact can be handed to
//!    another local and outlive the destination's storage), and a backward
//!    may-liveness of the fact's CARRIERS — the destination plus every local a
//!    whole-local copy or a reborrow could hand `const_ref_values` to
//!    (`codegen_stmt_payload_value_liveness`). A readable copy whose source can
//!    be rewritten under it would read the NEW payload through the kept term,
//!    so it fails closed. Liveness rather than storage markers because rustc
//!    brackets `for e in a`'s binding and not `for &e in a`'s payload temp, and
//!    the program is the same either way.
//! 5. After translation, every source producer block must be one where the stub
//!    actually recorded the slot fact, or one the Small-mode transition loop
//!    skipped (no block relation, or unreachable from `bb0`), from which no rule
//!    leaves ([`ChcCtx::verify_kept_payload_value_facts`]). Unwinding leaves the
//!    last copy's `next` call in such a block (kani/SwitchInt/main.rs bb136). A
//!    producer the stub did not handle could have left anything in the slot;
//!    the harness then records the FAIL-CLOSED `payload_value_fact_unverified`.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_stmt_payload_value_liveness::CarrierLiveness;

/// Whether `place` is storage of `local` itself (no `Deref`): a borrow of it can
/// write the local outside the producer list.
fn place_is_storage_of(place: &Place, local: usize) -> bool {
    place.local == local && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether a STATEMENT writes `local`'s payload: a partial write, a
    /// `SetDiscriminant`, a whole copy, or an aggregate of a variant with
    /// fields. Only a fieldless aggregate (`None`) leaves the payload to the
    /// call producers.
    pub(in crate::codegen_ay::chc) fn local_has_statement_payload_producer(
        &self,
        local: usize,
    ) -> bool {
        self.body.blocks.iter().flat_map(|block| block.statements.iter()).any(|stmt| {
            match &stmt.kind {
                StatementKind::Assign(lhs, rhs) if lhs.local == local => {
                    !(lhs.projection.is_empty()
                        && matches!(rhs, Rvalue::Aggregate(_, operands) if operands.is_empty()))
                }
                StatementKind::SetDiscriminant { place, .. } => place.local == local,
                _ => false,
            }
        })
    }

    /// The value fact `dest` may keep when it copies `source`'s payload and has
    /// several producers, or `None` when any condition of the module doc fails.
    /// A kept fact is registered for [`Self::verify_kept_payload_value_facts`].
    pub(in crate::codegen_ay::chc) fn keep_agreeing_payload_value_fact(
        &mut self,
        source_local: usize,
        dest_local: usize,
    ) -> Option<Expr> {
        let fact = self.source_payload_slot_fact(source_local)?;
        if !self.whole_definitions_all_same_payload_copy_of(dest_local, source_local) {
            return None;
        }
        let producer_sites = self.source_call_producer_sites(source_local, dest_local)?;
        if self.payload_copy_may_outlive_source(source_local, dest_local, &producer_sites) {
            debug!(
                source_local,
                dest_local, "payload value fact: the source can change under the copy; dropped"
            );
            return None;
        }
        debug!(
            source_local,
            dest_local,
            producers = producer_sites.len(),
            "payload value fact: every producer agrees; kept"
        );
        self.ref_resolution.kept_payload_value_facts.insert((source_local, dest_local), producer_sites);
        Some(fact)
    }

    /// Condition 1: `source`'s value fact is the input state variable of its own
    /// payload slot (state index + 1, the slot the `next` stub writes).
    pub(in crate::codegen_ay::chc) fn source_payload_slot_fact(
        &self,
        source_local: usize,
    ) -> Option<Expr> {
        if self.ref_resolution.const_ref_slice_views.contains_key(&source_local) {
            return None;
        }
        let fact = self.ref_resolution.const_ref_values.get(&source_local)?;
        let ExprValue::Var { name } = fact.value() else {
            return None;
        };
        let base = self.try_state_idx_for_local(source_local)?;
        let (payload_name, _) = self.state_var_mgr.state_vars.get(base + 1)?;
        (name.as_str() == &**payload_name).then(|| fact.clone())
    }

    /// Condition 2: every whole definition of `dest` is the same statement
    /// `dest = copy|move ((src as V).0)`, and nothing else writes `dest`.
    pub(in crate::codegen_ay::chc) fn whole_definitions_all_same_payload_copy_of(
        &self,
        dest: usize,
        src: usize,
    ) -> bool {
        if dest == src {
            return false;
        }
        let call_defines = self.body.blocks.iter().any(|block| {
            matches!(
                &block.terminator.kind,
                TerminatorKind::Call { destination, .. } if destination.local == dest
            )
        });
        if call_defines {
            return false;
        }
        let mut first: Option<String> = None;
        for stmt in self.body.blocks.iter().flat_map(|block| &block.statements) {
            let (lhs, rhs) = match &stmt.kind {
                StatementKind::Assign(lhs, rhs) if lhs.local == dest => (lhs, rhs),
                StatementKind::SetDiscriminant { place, .. } if place.local == dest => {
                    return false;
                }
                _ => continue,
            };
            if !lhs.projection.is_empty() {
                return false;
            }
            let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs else {
                return false;
            };
            if place.local != src
                || !matches!(
                    place.projection.as_slice(),
                    [ProjectionElem::Downcast(_), ProjectionElem::Field(0, _)]
                )
            {
                return false;
            }
            let rendered = format!("{rhs:?}");
            match &first {
                None => first = Some(rendered),
                Some(existing) if *existing == rendered => {}
                Some(_) => return false,
            }
        }
        first.is_some()
    }

    /// Condition 3: the blocks whose `Call` writes `src`, when every write of
    /// `src` is such a call to one callee, neither local's own storage is
    /// borrowed, and neither is an argument.
    pub(in crate::codegen_ay::chc) fn source_call_producer_sites(
        &self,
        src: usize,
        dest: usize,
    ) -> Option<Vec<usize>> {
        let arg_count = self.body.arg_locals().len();
        if (1..=arg_count).contains(&src) || (1..=arg_count).contains(&dest) {
            return None;
        }
        for stmt in self.body.blocks.iter().flat_map(|block| &block.statements) {
            match &stmt.kind {
                StatementKind::Assign(lhs, _) if lhs.local == src => return None,
                StatementKind::SetDiscriminant { place, .. } if place.local == src => return None,
                StatementKind::Assign(_, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place))
                    if place_is_storage_of(place, src) || place_is_storage_of(place, dest) =>
                {
                    return None;
                }
                _ => {}
            }
        }
        let locals = self.body.locals();
        let mut callee = None;
        let mut sites = Vec::new();
        for (bb, block) in self.body.blocks.iter().enumerate() {
            match &block.terminator.kind {
                TerminatorKind::InlineAsm { .. } => return None,
                TerminatorKind::Call { func, destination, .. } if destination.local == src => {
                    if !destination.projection.is_empty() {
                        return None;
                    }
                    let ty = func.ty(locals).ok()?;
                    match callee {
                        None => callee = Some(ty),
                        Some(existing) if existing == ty => {}
                        Some(_) => return None,
                    }
                    sites.push(bb);
                }
                _ => {}
            }
        }
        (!sites.is_empty()).then_some(sites)
    }

    /// Condition 4: whether a producer or a `StorageDead` of `src` can run while
    /// a payload copied from an earlier value of `src` is still READABLE — the
    /// forward analysis says `dest` may hold one AND some carrier of the fact is
    /// live there ([`CarrierLiveness`], `codegen_stmt_payload_value_liveness`).
    ///
    /// The liveness half is what makes `for &e in a` work: its payload copy is a
    /// temp rustc never brackets, so the storage markers this once relied on
    /// killed nothing and the loop backedge carried the copy into the next
    /// `next` call. A copy no path reads again cannot be misread.
    pub(in crate::codegen_ay::chc) fn payload_copy_may_outlive_source(
        &self,
        src: usize,
        dest: usize,
        producer_sites: &[usize],
    ) -> bool {
        // (a payload copy was made on this path, the statement kills `src` while
        // one was). GEN ONLY: the destination's own `StorageLive`/`StorageDead`
        // must NOT reset this. The fact can be handed to another local before
        // the copy's storage dies — `kept = q` lowers to `_9 = &(*_8)`,
        // `_3 = move _9`, `StorageDead(_8)` — and the fact then lives in `_3`,
        // so a kill here would call the copy gone while it is still readable.
        // Whether anything can still READ it is the liveness half's question.
        let step = |assigned: bool, kind: &StatementKind| -> (bool, bool) {
            match kind {
                StatementKind::Assign(lhs, _) if lhs.local == dest => (true, false),
                StatementKind::StorageDead(local) if *local == src => (assigned, assigned),
                _ => (assigned, false),
            }
        };
        let blocks = &self.body.blocks;
        let mut entry = vec![false; blocks.len()];
        let mut changed = true;
        while changed {
            changed = false;
            for (bb, block) in blocks.iter().enumerate() {
                let assigned =
                    block.statements.iter().fold(entry[bb], |state, stmt| step(state, &stmt.kind).0);
                if !assigned {
                    continue;
                }
                for succ in block.terminator.successors() {
                    if let Some(slot) = entry.get_mut(succ)
                        && !*slot
                    {
                        *slot = true;
                        changed = true;
                    }
                }
            }
        }
        let carriers = self.payload_fact_carriers(dest);
        let liveness = self.carrier_liveness(&carriers);
        let sites: HashSet<usize> = producer_sites.iter().copied().collect();
        for (bb, block) in blocks.iter().enumerate() {
            let mut assigned = entry[bb];
            for (idx, stmt) in block.statements.iter().enumerate() {
                let (next, kills_source) = step(assigned, &stmt.kind);
                if kills_source && liveness.any_live_after_statement(self.body, bb, idx) {
                    return true;
                }
                assigned = next;
            }
            if assigned && sites.contains(&bb) && liveness.any_live_at_terminator(self.body, bb) {
                return true;
            }
        }
        false
    }

    /// Condition 5, checked once every block is translated: each producer of a
    /// kept fact's source is a block where the `next` stub recorded the slot
    /// fact, or a block the transition loop skipped. Otherwise record the
    /// fail-closed `payload_value_fact_unverified`, so no proof and no certified
    /// counterexample rests on the kept fact.
    pub(in crate::codegen_ay::chc) fn verify_kept_payload_value_facts(&self) {
        let mut kept: Vec<_> = self.ref_resolution.kept_payload_value_facts.iter().collect();
        kept.sort_by_key(|(key, _)| **key);
        for ((src, dest), sites) in kept {
            let recorded = self.ref_resolution.payload_slot_fact_sites.get(src);
            let unverified: Vec<usize> = sites
                .iter()
                .copied()
                .filter(|bb| {
                    !recorded.is_some_and(|blocks| blocks.contains(bb))
                        && !self.ref_resolution.untranslated_transition_blocks.contains(bb)
                })
                .collect();
            if !unverified.is_empty() {
                debug!(
                    src,
                    dest,
                    ?unverified,
                    "payload value fact: a source producer did not record the slot fact"
                );
                self.record_sound_fallback_reason("payload_value_fact_unverified");
            }
        }
    }
}

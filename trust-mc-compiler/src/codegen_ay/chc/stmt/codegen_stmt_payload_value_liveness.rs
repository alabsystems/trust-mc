// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Is a kept payload value fact still READABLE when a producer runs?
//!
//! Condition 4 of [`super::codegen_stmt_payload_value_fact`] has to decide
//! whether a producer of the source can run while the copy still holds a
//! payload some path can read. Its first form answered that with
//! `StorageLive`/`StorageDead` of the copy — and rustc does not bracket every
//! temp. `for &e in a` lowers the pattern binding to a read THROUGH a bare
//! temp:
//!
//! ```text
//! bb5: _10 = copy ((_5 as Some).0: &i32);   // the payload copy
//!      _8  = copy (*_10);                   // the `&e` binding reads it
//! ```
//!
//! `_10` carries no storage marker anywhere in the body, so nothing killed the
//! copy, the loop backedge carried it into the `next` call again, and the fact
//! was dropped — although every unwound copy reads its own payload before the
//! next call runs. `for e in a`, whose binding IS the copy and IS bracketed,
//! kept it. The guard was keyed on a debug-info artifact instead of on the
//! program.
//!
//! LIVENESS is the property that matters: a copy no path reads again cannot be
//! misread, bracketed or not. [`CarrierLiveness`] is a backward may-liveness
//! over the copy and over every local the fact can REACH from it — a whole-local
//! copy hands `const_ref_values` on (`propagate_ref_metadata`), and so does a
//! REBORROW `dest = &(*src)` (`propagate_subslice_metadata`) — so the copy going
//! dead is not enough on its own. Anything unproven still fails closed:
//! an unhandled rvalue that merely mentions a carrier makes its destination a
//! carrier too, and a carrier live at a producer refuses the fact.

use std::collections::{HashMap, HashSet};

use rustc_public::mir::{Body, Operand, Place, Rvalue, StatementKind, TerminatorKind};

use super::ChcCtx;

/// Whether `place` names `local` with NO projection: the whole value, which is
/// what a value fact can be handed along.
fn place_is_whole(place: &Place, local: usize) -> bool {
    place.local == local && place.projection.is_empty()
}

fn operand_is_whole_carrier(operand: &Operand, carriers: &HashSet<usize>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            carriers.iter().any(|&local| place_is_whole(place, local))
        }
        _ => false,
    }
}

/// Whether `rv` names a carrier as a WHOLE place, so its destination may
/// inherit the fact. An rvalue kind this does not spell out falls back to "does
/// it mention a carrier at all" — fail-closed, never silently `false`.
fn rvalue_hands_on_a_carrier(rv: &Rvalue, carriers: &HashSet<usize>) -> bool {
    let whole = |place: &Place| carriers.iter().any(|&local| place_is_whole(place, local));
    match rv {
        Rvalue::Use(operand, ..) | Rvalue::Cast(_, operand, _) | Rvalue::UnaryOp(_, operand) => {
            operand_is_whole_carrier(operand, carriers)
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_is_whole_carrier(lhs, carriers) || operand_is_whole_carrier(rhs, carriers)
        }
        // A borrow or REBORROW of a carrier hands the fact on, so the BASE
        // local decides, not whether the place is whole:
        // `propagate_subslice_metadata` copies `const_ref_values` from the
        // source local to the destination of `dest = &(*src)` (projection
        // `[Deref]`), of a custom-DST tail field reborrow, and of a subslice
        // reborrow. `for &e in a`'s own `kept = q` lowers to exactly that
        // shape (`_9 = &(*_8)`), which an earlier form of this closure missed.
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) | Rvalue::CopyForDeref(place) => {
            carriers.contains(&place.local)
        }
        other => {
            let mut used = HashSet::new();
            ChcCtx::collect_rvalue_used_locals(other, &mut used);
            used.iter().any(|local| carriers.contains(local))
        }
    }
}

/// Backward may-liveness of a set of locals, per block entry.
pub(in crate::codegen_ay::chc) struct CarrierLiveness {
    /// Carrier local -> its bit position.
    index: HashMap<usize, usize>,
    /// Which carriers may be live at each block's ENTRY.
    entry: Vec<Vec<bool>>,
}

impl CarrierLiveness {
    /// Which carriers may be live on the way OUT of `bb` (the union over its
    /// successors' entry states).
    fn out_state(&self, body: &Body, bb: usize) -> Vec<bool> {
        let mut state = vec![false; self.index.len()];
        if let Some(block) = body.blocks.get(bb) {
            for succ in block.terminator.successors() {
                if let Some(entry) = self.entry.get(succ) {
                    for (slot, live) in state.iter_mut().zip(entry) {
                        *slot |= *live;
                    }
                }
            }
        }
        state
    }

    /// Whether any carrier may be live AT `bb`'s terminator: read by it, or read
    /// on some path out of it without being written first.
    pub(in crate::codegen_ay::chc) fn any_live_at_terminator(
        &self,
        body: &Body,
        bb: usize,
    ) -> bool {
        let Some(block) = body.blocks.get(bb) else {
            return false;
        };
        let mut state = self.out_state(body, bb);
        self.apply_terminator(&block.terminator.kind, &mut state);
        state.iter().any(|live| *live)
    }

    /// Whether any carrier may be live immediately AFTER statement `idx` of `bb`.
    pub(in crate::codegen_ay::chc) fn any_live_after_statement(
        &self,
        body: &Body,
        bb: usize,
        idx: usize,
    ) -> bool {
        let Some(block) = body.blocks.get(bb) else {
            return false;
        };
        let mut state = self.out_state(body, bb);
        self.apply_terminator(&block.terminator.kind, &mut state);
        for stmt in block.statements.iter().skip(idx + 1).rev() {
            self.apply_statement(&stmt.kind, &mut state);
        }
        state.iter().any(|live| *live)
    }

    fn gen_local(&self, local: usize, state: &mut [bool]) {
        if let Some(&bit) = self.index.get(&local) {
            state[bit] = true;
        }
    }

    fn kill_local(&self, local: usize, state: &mut [bool]) {
        if let Some(&bit) = self.index.get(&local) {
            state[bit] = false;
        }
    }

    /// Backward transfer of one terminator: a `Call` whose destination is a
    /// whole carrier kills it; every local it reads is live before it.
    fn apply_terminator(&self, kind: &TerminatorKind, state: &mut [bool]) {
        if let TerminatorKind::Call { destination, .. } = kind
            && destination.projection.is_empty()
        {
            self.kill_local(destination.local, state);
        }
        let mut used = HashSet::new();
        ChcCtx::collect_terminator_used_locals(kind, &mut used);
        if let TerminatorKind::Call { destination, .. } = kind
            && !destination.projection.is_empty()
        {
            // A projected write keeps the rest of the local: it reads it.
            used.insert(destination.local);
        }
        for local in used {
            self.gen_local(local, state);
        }
    }

    /// Backward transfer of one statement. A whole assignment or either storage
    /// marker ends the value the fact described; a projected write keeps the
    /// rest of the local, so it READS it.
    fn apply_statement(&self, kind: &StatementKind, state: &mut [bool]) {
        match kind {
            StatementKind::Assign(place, _) if place.projection.is_empty() => {
                self.kill_local(place.local, state);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.kill_local(*local, state);
            }
            _ => {}
        }
        let mut used = HashSet::new();
        ChcCtx::collect_statement_used_locals(kind, &mut used);
        match kind {
            StatementKind::Assign(place, _) if !place.projection.is_empty() => {
                used.insert(place.local);
            }
            StatementKind::SetDiscriminant { place, .. } => {
                used.insert(place.local);
            }
            _ => {}
        }
        for local in used {
            self.gen_local(local, state);
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Every local that may CARRY `dest`'s payload value fact: `dest` itself,
    /// and the destination of any assignment that hands a carrier's whole value
    /// on. `propagate_ref_metadata` copies `const_ref_values` across such an
    /// assignment, so a deref through the copy would read the fact just as
    /// `*dest` would; the copy going dead is not enough on its own.
    pub(in crate::codegen_ay::chc) fn payload_fact_carriers(&self, dest: usize) -> Vec<usize> {
        let mut carriers: HashSet<usize> = HashSet::new();
        carriers.insert(dest);
        loop {
            let mut grew = false;
            for stmt in self.body.blocks.iter().flat_map(|block| &block.statements) {
                if let StatementKind::Assign(lhs, rv) = &stmt.kind
                    && rvalue_hands_on_a_carrier(rv, &carriers)
                    && carriers.insert(lhs.local)
                {
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        let mut carriers: Vec<usize> = carriers.into_iter().collect();
        carriers.sort_unstable();
        carriers
    }

    /// Backward may-liveness of `carriers` over this body, to a fixpoint.
    pub(in crate::codegen_ay::chc) fn carrier_liveness(&self, carriers: &[usize]) -> CarrierLiveness {
        let index: HashMap<usize, usize> =
            carriers.iter().copied().enumerate().map(|(bit, local)| (local, bit)).collect();
        let mut liveness = CarrierLiveness {
            index,
            entry: vec![vec![false; carriers.len()]; self.body.blocks.len()],
        };
        let mut changed = true;
        while changed {
            changed = false;
            for bb in (0..self.body.blocks.len()).rev() {
                let block = &self.body.blocks[bb];
                let mut state = liveness.out_state(self.body, bb);
                liveness.apply_terminator(&block.terminator.kind, &mut state);
                for stmt in block.statements.iter().rev() {
                    liveness.apply_statement(&stmt.kind, &mut state);
                }
                if state != liveness.entry[bb] {
                    liveness.entry[bb] = state;
                    changed = true;
                }
            }
        }
        liveness
    }
}

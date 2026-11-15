// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Conservative stack lifetime evidence. Static object IDs cannot distinguish
//! separate activations of one MIR local; never use them to certify re-entry.

use super::ChcCtx;
use rustc_public::mir::{Body, ProjectionElem, Rvalue, StatementKind};
use std::collections::{HashMap, HashSet};

const MAX_LIFETIME_WORK: usize = 262_144;

/// Shared MIR storage analysis. The first component is definitely dead; the
/// second is possibly dead. Callers must install each block's two sets and
/// apply StorageLive/StorageDead in statement order before asking about liveness.
pub(in crate::codegen_ay) fn stack_storage_liveness_at_entry(
    body: &Body,
) -> (Vec<HashSet<usize>>, Vec<HashSet<usize>>) {
    (
        ChcCtx::compute_dead_locals_at_block_entry(body),
        ChcCtx::compute_maybe_dead_locals_at_block_entry(body),
    )
}

fn spend(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}

/// Uses all successor edges, including cleanup. Multiple reachable activation
/// sites also refuse an acyclic unrolled body, which retains the original locals.
pub(in crate::codegen_ay) fn reused_address_taken_locals(body: &Body) -> Option<HashSet<usize>> {
    let mut work = MAX_LIFETIME_WORK;
    spend(&mut work, body.blocks.len())?;
    let mut reachable = HashSet::new();
    let mut pending = vec![0];
    while let Some(index) = pending.pop() {
        spend(&mut work, 1)?;
        if !reachable.insert(index) {
            continue;
        }
        let block = body.blocks.get(index)?;
        let successors = block.terminator.successors();
        spend(&mut work, successors.len())?;
        pending.extend(successors);
    }
    let mut taken = HashSet::new();
    let mut starts: HashMap<usize, Vec<usize>> = HashMap::new();
    for index in reachable.iter().copied() {
        for statement in &body.blocks[index].statements {
            spend(&mut work, 1)?;
            match &statement.kind {
                StatementKind::StorageLive(local) => {
                    starts.entry(*local).or_default().push(index);
                }
                StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                ) => {
                    spend(&mut work, place.projection.len())?;
                    if !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                        taken.insert(place.local);
                    }
                }
                _ => {}
            }
        }
    }
    let mut reused = HashSet::new();
    for local in taken {
        let Some(sites) = starts.get(&local) else { continue };
        if sites.len() > 1 {
            reused.insert(local);
            continue;
        }
        let site = sites[0];
        let mut pending = body.blocks.get(site)?.terminator.successors();
        let mut visited = HashSet::new();
        while let Some(next) = pending.pop() {
            spend(&mut work, 1)?;
            if next == site {
                reused.insert(local);
                break;
            }
            if visited.insert(next) {
                let successors = body.blocks.get(next)?.terminator.successors();
                spend(&mut work, successors.len())?;
                pending.extend(successors);
            }
        }
    }
    Some(reused)
}

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn stack_local_is_live(&self, local: usize) -> Option<bool> {
        if local >= self.body.locals().len()
            || self.current_encode_bb >= self.liveness.dead_locals_at_entry.len()
            || self.current_encode_bb >= self.liveness.maybe_dead_locals_at_entry.len()
        {
            return None;
        }
        if self.liveness.dead_locals.contains(&local) {
            return Some(false);
        }
        if self.liveness.maybe_dead_locals.contains(&local) {
            return None;
        }
        let reused = self
            .liveness
            .reused_stack_locals
            .get_or_init(|| reused_address_taken_locals(self.body))
            .as_ref()?;
        if reused.contains(&local) { None } else { Some(true) }
    }
}

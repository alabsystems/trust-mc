// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `subslice_len` entries that cannot be replayed in the block being encoded.
//!
//! `subslice_len` is a path-insensitive side table keyed by local: when
//! `&source[start..end]` is encoded, the length is cached as an expression over
//! the RANGE local's state columns (`_129_fld1 - _129_fld0`) and replayed by
//! every later `PtrMetadata` / `len()` / slice-construction read of the slice
//! local. Relation frames are fixed at declaration time, so in a block whose
//! frame no longer carries the range local (liveness pruned it once the slice
//! was built) that replay reads a column no relation atom binds: a universally
//! quantified free variable, i.e. an unconstrained length.
//! tests/expected/loop-contract/for_loop_for_slice.rs replayed the
//! `any_slice_of_array` length that way in bb2 and bb72, the length became
//! unbounded, and `kani::index as u32 * u8::MAX as u32` refuted.
//!
//! The slice local itself carries its length (the high half of its BV128 fat
//! pointer, or the flattened metadata field), and it is in the frame wherever
//! it is read. So for the duration of one block (its statements AND its
//! terminator) the entries whose cached expression reads an out-of-frame
//! MIR-local column are withheld, and every read falls through to the slice
//! local's own metadata. The entries come back when the next block starts,
//! unless that block wrote the local (a new producer decides its metadata).
//! `ChcCtx::local_columns_read_outside_rule_frames` stays the fallback for the
//! other side tables: it demotes a counterexample through such a read.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{StatementKind, TerminatorKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Restore what the previous block withheld, then withhold the entries whose
    /// cached length reads a MIR-local column outside `bb_idx`'s frame.
    pub(in crate::codegen_ay::chc) fn refresh_subslice_len_frame(&mut self, bb_idx: usize) {
        self.restore_hidden_subslice_lens();
        if self.ref_resolution.subslice_len.is_empty() {
            return;
        }
        let Some(frame) = self.state_var_mgr.live_state_indices.get(bb_idx) else {
            return;
        };
        let frame: HashSet<usize> = frame.iter().copied().collect();
        let local_backed = self.mir_local_backed_state_indices();
        let stale: Vec<usize> = self
            .ref_resolution
            .subslice_len
            .iter()
            .filter(|(_, len)| self.reads_unframed_local_column(len, &frame, &local_backed))
            .map(|(&local, _)| local)
            .collect();
        if stale.is_empty() {
            return;
        }
        let mut hidden = Vec::with_capacity(stale.len());
        for local in stale {
            if let Some(len) = self.ref_resolution.subslice_len.remove(&local) {
                debug!(
                    bb_idx,
                    local,
                    "subslice_len: cached length reads a column outside this block's frame; \
                     reading the slice's own metadata instead"
                );
                hidden.push((local, len));
            }
        }
        self.subslice_len_hidden = Some((bb_idx, hidden));
    }

    /// Put back the entries withheld for the block that was encoded last. An
    /// entry whose local that block re-assigned, or re-recorded, stays as the
    /// block left it.
    pub(in crate::codegen_ay::chc) fn restore_hidden_subslice_lens(&mut self) {
        let Some((bb_idx, hidden)) = self.subslice_len_hidden.take() else {
            return;
        };
        for (local, len) in hidden {
            if self.ref_resolution.subslice_len.contains_key(&local)
                || self.block_writes_local(bb_idx, local)
            {
                continue;
            }
            self.ref_resolution.subslice_len.insert(local, len);
        }
    }

    /// Whether `expr` reads only MIR-local columns that the relation frame of the
    /// block being encoded carries. True when no frame is computed (unit-test
    /// contexts that never declared relations).
    pub(in crate::codegen_ay::chc) fn reads_only_framed_local_columns(&self, expr: &Expr) -> bool {
        let Some(frame) = self.state_var_mgr.live_state_indices.get(self.current_encode_bb) else {
            return true;
        };
        let frame: HashSet<usize> = frame.iter().copied().collect();
        !self.reads_unframed_local_column(expr, &frame, &self.mir_local_backed_state_indices())
    }

    /// State indices of the columns that back a MIR local (every field of a
    /// flattened local). Ambient columns (type arrays, heap metadata, statics)
    /// have no local and are legitimately unframed.
    pub(in crate::codegen_ay::chc) fn mir_local_backed_state_indices(&self) -> HashSet<usize> {
        let mut backed = HashSet::new();
        for (&local, &base) in &self.state_var_mgr.local_to_state_idx {
            let n = if self.flatten.flattened_tuple_locals.contains(&local) {
                self.flattened_field_count(local)
            } else {
                1
            };
            backed.extend(base..base + n.max(1));
        }
        backed
    }

    /// Does `expr` read the bare input name of a MIR-local column outside `frame`?
    /// `X__out` and `X__mid_bbN` are defined by the rule that mentions them, and
    /// `__pad_*` slots are anonymous by design.
    fn reads_unframed_local_column(
        &self,
        expr: &Expr,
        frame: &HashSet<usize>,
        local_backed: &HashSet<usize>,
    ) -> bool {
        let mut stack = vec![expr.clone()];
        while let Some(node) = stack.pop() {
            if let ExprValue::Var { name } = node.value() {
                if name.ends_with("__out") || name.contains("__mid_bb") || name.starts_with("__pad_")
                {
                    continue;
                }
                if self
                    .state_var_mgr
                    .state_var_index_by_name(name)
                    .is_some_and(|idx| local_backed.contains(&idx) && !frame.contains(&idx))
                {
                    return true;
                }
                continue;
            }
            stack.extend(node.children().cloned());
        }
        false
    }

    fn block_writes_local(&self, bb_idx: usize, local: usize) -> bool {
        let Some(block) = self.body.blocks.get(bb_idx) else {
            return false;
        };
        block.statements.iter().any(
            |stmt| matches!(&stmt.kind, StatementKind::Assign(place, _) if place.local == local),
        ) || matches!(
            &block.terminator.kind,
            TerminatorKind::Call { destination, .. } if destination.local == local
        )
    }
}

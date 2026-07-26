// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dead local analysis for CHC encoding.
//!
//! Forward must-analysis over StorageLive/StorageDead to compute which
//! locals are definitely dead at each basic block entry.
//!
//! Extracted from codegen_ctx.rs per #2246 decomposition.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::{HashSet, VecDeque};

use rustc_public::mir::{Body, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Applies StorageLive/StorageDead transfer for one block, writing into `out`.
    /// REQUIRES: `out.len() == dead_in.len()`
    pub(super) fn apply_dead_local_transfer_into(
        body: &Body,
        bb_idx: usize,
        dead_in: &[bool],
        out: &mut Vec<bool>,
    ) {
        out.clear();
        out.extend_from_slice(dead_in);
        let Some(block) = body.blocks.get(bb_idx) else {
            return;
        };
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::StorageLive(local) => {
                    out[*local] = false;
                }
                StatementKind::StorageDead(local) => {
                    out[*local] = true;
                }
                _ => {} // external enum: StatementKind
            }
        }
    }

    /// Computes dead locals at each block entry using forward must-analysis.
    pub(super) fn compute_dead_locals_at_block_entry(body: &Body) -> Vec<HashSet<usize>> {
        let block_count = body.blocks.len();
        if block_count == 0 {
            return Vec::new();
        }

        let local_count = body.local_decls().count();
        let mut successors: Vec<Vec<usize>> = vec![Vec::new(); block_count];
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            successors[bb_idx] = Self::block_successors(&block.terminator.kind);
        }

        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); block_count];
        for (src, succs) in successors.iter().enumerate() {
            for &dst in succs {
                predecessors[dst].push(src);
            }
        }

        // Restrict analysis to blocks reachable from entry.
        let mut reachable = vec![false; block_count];
        let mut queue: VecDeque<usize> = VecDeque::new();
        reachable[0] = true;
        queue.push_back(0);
        while let Some(bb) = queue.pop_front() {
            for &succ in &successors[bb] {
                if !reachable[succ] {
                    reachable[succ] = true;
                    queue.push_back(succ);
                }
            }
        }

        // Must analysis domain:
        // - entry starts with no dead locals,
        // - all other reachable blocks start at top (all dead) then monotonically decrease.
        let mut dead_in = vec![vec![true; local_count]; block_count];
        dead_in[0] = vec![false; local_count];
        for bb in 0..block_count {
            if !reachable[bb] {
                dead_in[bb] = vec![false; local_count];
            }
        }

        // Pre-compute dead_out for each reachable block, updated each iteration.
        // This avoids cloning dead_in[pred] for every predecessor edge (#2286 HIGH).
        let mut dead_out: Vec<Vec<bool>> = vec![Vec::new(); block_count];
        let mut transfer_buf: Vec<bool> = Vec::with_capacity(local_count);
        let mut new_in: Vec<bool> = vec![true; local_count];

        let mut changed = true;
        while changed {
            changed = false;

            // Compute dead_out once per reachable block per iteration.
            for bb in 0..block_count {
                if !reachable[bb] {
                    continue;
                }
                Self::apply_dead_local_transfer_into(body, bb, &dead_in[bb], &mut transfer_buf);
                if dead_out[bb] != transfer_buf {
                    dead_out[bb].clear();
                    dead_out[bb].extend_from_slice(&transfer_buf);
                }
            }

            for bb in 1..block_count {
                if !reachable[bb] {
                    continue;
                }

                let mut has_reachable_pred = false;
                new_in.fill(true);

                for &pred in &predecessors[bb] {
                    if !reachable[pred] {
                        continue;
                    }
                    has_reachable_pred = true;
                    for local in 0..local_count {
                        new_in[local] &= dead_out[pred][local];
                    }
                }

                if !has_reachable_pred {
                    new_in.fill(false);
                }

                if new_in != dead_in[bb] {
                    dead_in[bb].copy_from_slice(&new_in);
                    changed = true;
                }
            }
        }

        dead_in
            .into_iter()
            .map(|bits| {
                bits.into_iter()
                    .enumerate()
                    .filter_map(|(idx, is_dead)| if is_dead { Some(idx) } else { None })
                    .collect()
            })
            .collect()
    }

    /// Computes which MIR locals are used (read) in each block's statements and terminator.
    ///
    /// Part of #112: StorageLive/StorageDead tracks allocation scope, not value liveness.
    /// A local can be "storage-dead" at block entry but still read as a source operand.
    /// If the dead-locals analysis excludes it from the CHC relation signature, the local
    /// becomes a universally-quantified free variable, making constraints trivially
    /// satisfiable and producing spurious counterexamples.
    ///
    /// This function scans statements and terminators for source-operand locals so
    /// `compute_live_state_indices` can keep used-but-storage-dead locals in the relation.
    pub(super) fn compute_used_locals_per_block(body: &Body) -> Vec<HashSet<usize>> {
        let block_count = body.blocks.len();
        let mut result = Vec::with_capacity(block_count);

        for block in &body.blocks {
            let mut used = HashSet::new();

            // Scan statements for source operand locals.
            for stmt in &block.statements {
                Self::collect_statement_used_locals(&stmt.kind, &mut used);
            }

            // Scan terminator for source operand locals.
            Self::collect_terminator_used_locals(&block.terminator.kind, &mut used);

            result.push(used);
        }

        result
    }

    /// Collect locals used as source operands in a statement.
    fn collect_statement_used_locals(kind: &StatementKind, used: &mut HashSet<usize>) {
        match kind {
            StatementKind::Assign(place, rvalue) => {
                // RHS locals are source operands.
                Self::collect_rvalue_used_locals(rvalue, used);
                // LHS projections (e.g., Index) can also read locals.
                Self::collect_place_index_locals(place, used);
            }
            StatementKind::SetDiscriminant { place, .. } => {
                Self::collect_place_index_locals(place, used);
            }
            StatementKind::Intrinsic(intrinsic) => {
                // Intrinsic statements generate constraints from their operands
                // (codegen_stmt.rs:113-153). Without scanning these, storage-dead
                // locals referenced by Assume or CopyNonOverlapping become free
                // variables in CHC rules — making constraints vacuously satisfiable.
                match intrinsic {
                    rustc_public::mir::NonDivergingIntrinsic::Assume(op) => {
                        Self::collect_operand_local(op, used);
                    }
                    rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                        Self::collect_operand_local(&copy.src, used);
                        Self::collect_operand_local(&copy.dst, used);
                        Self::collect_operand_local(&copy.count, used);
                    }
                }
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            _ => {} // external enum: StatementKind
        }
    }

    /// Collect locals used as source operands in a terminator.
    fn collect_terminator_used_locals(kind: &TerminatorKind, used: &mut HashSet<usize>) {
        match kind {
            TerminatorKind::SwitchInt { discr, .. } => {
                Self::collect_operand_local(discr, used);
            }
            TerminatorKind::Return => {
                // _0 is implicitly read on return.
                used.insert(0);
            }
            TerminatorKind::Call { func, args, destination, .. } => {
                Self::collect_operand_local(func, used);
                for arg in args {
                    Self::collect_operand_local(arg, used);
                }
                // destination place projections can read locals.
                Self::collect_place_index_locals(destination, used);
            }
            TerminatorKind::Assert { cond, msg, .. } => {
                Self::collect_operand_local(cond, used);
                Self::collect_assert_message_locals(msg, used);
            }
            TerminatorKind::Drop { place, .. } => {
                used.insert(place.local);
                Self::collect_place_index_locals(place, used);
            }
            TerminatorKind::Goto { .. } | TerminatorKind::Resume | TerminatorKind::Unreachable => {}
            _ => {} // external enum: TerminatorKind
        }
    }

    /// Extract the local from a Copy or Move operand.
    fn collect_operand_local(operand: &Operand, used: &mut HashSet<usize>) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                used.insert(place.local);
                Self::collect_place_index_locals(place, used);
            }
            Operand::Constant(_) => {}
        }
    }

    /// Extract locals from Index projections on a place.
    fn collect_place_index_locals(place: &rustc_public::mir::Place, used: &mut HashSet<usize>) {
        for proj in &place.projection {
            if let ProjectionElem::Index(local) = proj {
                used.insert(*local);
            }
        }
    }

    /// Extract locals from Rvalue source operands.
    fn collect_rvalue_used_locals(rvalue: &Rvalue, used: &mut HashSet<usize>) {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::Repeat(op, _)
            | Rvalue::Cast(_, op, _)
            | Rvalue::UnaryOp(_, op) => {
                Self::collect_operand_local(op, used);
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                Self::collect_operand_local(lhs, used);
                Self::collect_operand_local(rhs, used);
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                used.insert(place.local);
                Self::collect_place_index_locals(place, used);
            }
            Rvalue::Len(place) | Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => {
                used.insert(place.local);
                Self::collect_place_index_locals(place, used);
            }
            Rvalue::Aggregate(_, operands) => {
                for op in operands {
                    Self::collect_operand_local(op, used);
                }
            }
            Rvalue::ShallowInitBox(op, _) => {
                Self::collect_operand_local(op, used);
            }
            Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => {}
        }
    }

    /// Extract locals from AssertMessage operands.
    fn collect_assert_message_locals(
        msg: &rustc_public::mir::AssertMessage,
        used: &mut HashSet<usize>,
    ) {
        // AssertMessage variants may contain operands (e.g., BoundsCheck { len, index }).
        // We use the operands() method if available, otherwise match known variants.
        use rustc_public::mir::AssertMessage;
        match msg {
            AssertMessage::BoundsCheck { len, index } => {
                Self::collect_operand_local(len, used);
                Self::collect_operand_local(index, used);
            }
            AssertMessage::Overflow(_, lhs, rhs) => {
                Self::collect_operand_local(lhs, used);
                Self::collect_operand_local(rhs, used);
            }
            AssertMessage::OverflowNeg(op)
            | AssertMessage::DivisionByZero(op)
            | AssertMessage::RemainderByZero(op) => {
                Self::collect_operand_local(op, used);
            }
            AssertMessage::ResumedAfterReturn(_)
            | AssertMessage::ResumedAfterPanic(_)
            | AssertMessage::MisalignedPointerDereference { .. } => {}
            _ => {} // external enum: AssertMessage
        }
    }
}

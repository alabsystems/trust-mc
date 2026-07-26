// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CFG construction and topological sorting for loop unrolling.

use rustc_public::mir::{Body, TerminatorKind};
use std::collections::VecDeque;

#[derive(Debug)]
pub(in crate::codegen_ay) struct Cfg {
    pub(in crate::codegen_ay) successors: Vec<Vec<usize>>,
    pub(in crate::codegen_ay) predecessors: Vec<Vec<usize>>,
    pub(in crate::codegen_ay) reachable: Vec<bool>,
    pub(in crate::codegen_ay) topo_order: Vec<usize>,
}

impl Cfg {
    pub(in crate::codegen_ay) fn from_body(body: &Body) -> Self {
        let block_count = body.blocks.len();
        let mut successors: Vec<Vec<usize>> = vec![Vec::new(); block_count];

        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let mut succs = match &block.terminator.kind {
                TerminatorKind::Goto { target } => vec![*target],
                TerminatorKind::SwitchInt { targets, .. } => {
                    let mut succs: Vec<usize> =
                        targets.branches().map(|(_case_val, target)| target).collect();
                    succs.push(targets.otherwise());
                    succs
                }
                TerminatorKind::Drop { target, .. } => vec![*target],
                TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
                TerminatorKind::Assert { target, .. } => vec![*target],
                TerminatorKind::Return | TerminatorKind::Unreachable => vec![],
                TerminatorKind::Resume | TerminatorKind::Abort => vec![],
                TerminatorKind::InlineAsm { destination, .. } => {
                    destination.iter().copied().collect()
                }
            };
            succs.sort_unstable();
            succs.dedup();
            successors[bb_idx] = succs;
        }

        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); block_count];
        for (src, succs) in successors.iter().enumerate() {
            for &dst in succs {
                if dst < block_count {
                    predecessors[dst].push(src);
                }
            }
        }
        for preds in &mut predecessors {
            preds.sort_unstable();
            preds.dedup();
        }

        // Reachable from entry (bb0).
        let mut reachable = vec![false; block_count];
        let mut q: VecDeque<usize> = VecDeque::new();
        reachable[0] = true;
        q.push_back(0);
        while let Some(bb) = q.pop_front() {
            for &succ in &successors[bb] {
                if !reachable[succ] {
                    reachable[succ] = true;
                    q.push_back(succ);
                }
            }
        }

        let topo_order = topo_sort(&successors, &reachable);

        Self { successors, predecessors, reachable, topo_order }
    }

    pub(in crate::codegen_ay) fn reachable_count(&self) -> usize {
        self.reachable.iter().filter(|&&b| b).count()
    }

    pub(in crate::codegen_ay) fn is_acyclic(&self) -> bool {
        self.topo_order.len() == self.reachable_count()
    }
}

pub(in crate::codegen_ay) fn topo_sort(
    successors: &[Vec<usize>],
    reachable: &[bool],
) -> Vec<usize> {
    let n = successors.len();
    let mut indegree = vec![0usize; n];
    for bb in 0..n {
        if !reachable[bb] {
            continue;
        }
        for &succ in &successors[bb] {
            if reachable[succ] {
                indegree[succ] += 1;
            }
        }
    }

    let mut q: VecDeque<usize> = VecDeque::new();
    for bb in 0..n {
        if reachable[bb] && indegree[bb] == 0 {
            q.push_back(bb);
        }
    }

    let mut order = Vec::with_capacity(n);
    while let Some(bb) = q.pop_front() {
        order.push(bb);
        for &succ in &successors[bb] {
            if !reachable[succ] {
                continue;
            }
            indegree[succ] -= 1;
            if indegree[succ] == 0 {
                q.push_back(succ);
            }
        }
    }
    order
}

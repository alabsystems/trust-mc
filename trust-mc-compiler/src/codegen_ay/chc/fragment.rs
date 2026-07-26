// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CFG fragment analysis for large-step CHC encoding.
//!
//! Identifies cut points (loop headers, function entry/exit) and partitions
//! the CFG into loop-free fragments between them. Each fragment's blocks
//! form a DAG — no back-edges exist within a fragment.
//!
//! Part of #112: large-step CHC encoding for loop PROOF scalability.

use rustc_public::mir::TerminatorKind;
use std::collections::{HashSet, VecDeque};
use tracing::warn;

use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers, topo_sort};

use super::ChcCtx;

/// A cut point in the CFG (loop header, entry, or exit).
///
/// Variants used in Step 5 (#112) for fragment constraint composition dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::codegen_ay) enum CutPointKind {
    /// Function entry (bb0).
    Entry,
    /// Loop header (back-edge target that dominates its source).
    LoopHeader,
    /// Function exit (Return terminator block).
    Exit,
}

/// Identified cut point in the CFG.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay) struct CutPoint {
    pub(in crate::codegen_ay) bb_idx: usize,
    pub(in crate::codegen_ay) kind: CutPointKind,
}

/// A loop-free fragment between cut points.
///
/// The fragment's blocks form a DAG (no back-edges within the fragment).
/// All paths through the fragment start at `entry_bb` (a cut point) and
/// end at one or more successor cut points.
#[derive(Debug)]
pub(in crate::codegen_ay) struct Fragment {
    /// The entry cut point (where this fragment starts).
    pub(in crate::codegen_ay) entry_bb: usize,
    /// Basic blocks in this fragment, topologically sorted.
    pub(in crate::codegen_ay) blocks: Vec<usize>,
    /// Exit edges: (last_bb_in_fragment, target_cut_point_bb).
    pub(in crate::codegen_ay) exits: Vec<(usize, usize)>,
}

/// Result of CFG analysis for large-step encoding.
#[derive(Debug)]
pub(in crate::codegen_ay) struct FragmentAnalysis {
    /// All identified cut points.
    pub(in crate::codegen_ay) cut_points: Vec<CutPoint>,
    /// Set of cut point block indices (for O(1) lookup).
    pub(in crate::codegen_ay) cut_point_set: HashSet<usize>,
    /// Fragments partitioning the CFG.
    pub(in crate::codegen_ay) fragments: Vec<Fragment>,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Analyze the CFG to identify cut points and partition into fragments.
    ///
    /// Cut points are: function entry (bb0), loop headers (back-edge targets),
    /// and function exits (Return blocks). Fragments are the loop-free regions
    /// between cut points.
    ///
    /// Used in `ChcStepMode::Large` to emit one CHC rule per fragment instead
    /// of one per basic block.
    pub(super) fn analyze_fragments(&self) -> FragmentAnalysis {
        let cfg = Cfg::from_body(self.body);
        let headers = find_loop_headers(&cfg).unwrap_or_else(|e| {
            warn!(
                "fragment analysis: find_loop_headers failed ({e:?}); \
                 proceeding with no loop headers — entire function body \
                 may be treated as one fragment"
            );
            Default::default()
        });

        // 1. Identify all cut points.
        let mut cut_points = vec![CutPoint { bb_idx: 0, kind: CutPointKind::Entry }];
        for &header_bb in headers.keys() {
            cut_points.push(CutPoint { bb_idx: header_bb, kind: CutPointKind::LoopHeader });
        }
        for (bb_idx, block) in self.body.blocks.iter().enumerate() {
            if matches!(block.terminator.kind, TerminatorKind::Return) {
                cut_points.push(CutPoint { bb_idx, kind: CutPointKind::Exit });
            }
        }

        let cut_point_set: HashSet<usize> = cut_points.iter().map(|cp| cp.bb_idx).collect();

        // 2. Partition blocks into fragments via BFS from each cut point,
        //    stopping at other cut points.
        let fragments = build_fragments(&cfg, &cut_point_set);

        FragmentAnalysis { cut_points, cut_point_set, fragments }
    }
}

/// Partition CFG blocks into fragments by BFS from each cut point.
///
/// For each cut point, explores successor blocks, adding non-cut-point
/// blocks to the fragment and recording edges to other cut points as exits.
/// Fragment blocks are topologically sorted for correct composition order.
fn build_fragments(cfg: &Cfg, cut_point_set: &HashSet<usize>) -> Vec<Fragment> {
    let n = cfg.successors.len();
    let mut fragments = Vec::new();

    for &entry_bb in cut_point_set {
        if !cfg.reachable[entry_bb] {
            continue;
        }

        let mut fragment_blocks: HashSet<usize> = HashSet::new();
        let mut exits: Vec<(usize, usize)> = Vec::new();
        let mut queue: VecDeque<usize> = VecDeque::new();

        // The entry cut point is always part of its own fragment.
        fragment_blocks.insert(entry_bb);
        queue.push_back(entry_bb);

        while let Some(bb) = queue.pop_front() {
            for &succ in &cfg.successors[bb] {
                if !cfg.reachable[succ] {
                    continue;
                }
                if cut_point_set.contains(&succ) && succ != entry_bb {
                    // Successor is a different cut point — record as exit edge.
                    exits.push((bb, succ));
                } else if succ == entry_bb {
                    // Back-edge to own entry (loop header) — record as exit
                    // to self (the loop-back edge).
                    exits.push((bb, succ));
                } else if fragment_blocks.insert(succ) {
                    // New non-cut-point block — add to fragment and explore.
                    queue.push_back(succ);
                }
            }
        }

        // Topologically sort fragment blocks. We must exclude edges that
        // leave the fragment (to other cut points) and back-edges to the
        // fragment's own entry (loop-back edges), otherwise Kahn's algorithm
        // sees a cycle and drops nodes.
        let mut frag_reachable = vec![false; n];
        for &bb in &fragment_blocks {
            frag_reachable[bb] = true;
        }
        let mut frag_succs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &bb in &fragment_blocks {
            for &succ in &cfg.successors[bb] {
                if frag_reachable[succ] && succ != entry_bb {
                    frag_succs[bb].push(succ);
                }
            }
        }
        // entry_bb has indegree 0 in this filtered graph (all edges into
        // it are either external or back-edges, both excluded).
        let sorted_blocks = topo_sort(&frag_succs, &frag_reachable);

        exits.sort_unstable();
        exits.dedup();

        fragments.push(Fragment { entry_bb, blocks: sorted_blocks, exits });
    }

    // Sort fragments by entry block for deterministic output.
    fragments.sort_by_key(|f| f.entry_bb);
    fragments
}

#[cfg(test)]
#[allow(clippy::unwrap_used)] // Test code: unwrap is acceptable for assertions
mod tests {
    use super::*;

    /// Helper: build a Cfg from adjacency list.
    fn cfg_from_edges(n: usize, edges: &[(usize, usize)]) -> Cfg {
        let mut successors = vec![Vec::new(); n];
        let mut predecessors = vec![Vec::new(); n];
        for &(src, dst) in edges {
            successors[src].push(dst);
            predecessors[dst].push(src);
        }
        // BFS reachability from bb0.
        let mut reachable = vec![false; n];
        let mut q = VecDeque::new();
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
        Cfg { successors, predecessors, reachable, topo_order }
    }

    /// Linear CFG: bb0 → bb1 → bb2 (return).
    /// Cut points: bb0 (entry), bb2 (exit).
    /// Single fragment: {bb0, bb1, bb2} with no exits to other cut points
    /// (bb2 is exit/return, exits via return not via edge).
    #[test]
    fn test_linear_cfg() {
        let cfg = cfg_from_edges(3, &[(0, 1), (1, 2)]);
        let cut_point_set: HashSet<usize> = [0, 2].into_iter().collect();
        let fragments = build_fragments(&cfg, &cut_point_set);

        assert_eq!(fragments.len(), 2, "entry fragment + exit fragment");

        // Fragment starting at bb0.
        let f0 = fragments.iter().find(|f| f.entry_bb == 0).unwrap();
        assert!(f0.blocks.contains(&0));
        assert!(f0.blocks.contains(&1));
        // bb2 is a cut point, so bb0's fragment reaches it as an exit.
        assert!(f0.exits.contains(&(1, 2)));

        // Fragment starting at bb2 (exit cut point, single block).
        let f2 = fragments.iter().find(|f| f.entry_bb == 2).unwrap();
        assert_eq!(f2.blocks, vec![2]);
        assert!(f2.exits.is_empty());
    }

    /// Single loop: bb0 → bb1 → bb2, bb2 → bb1 (back-edge), bb2 → bb3 (exit).
    /// Cut points: bb0 (entry), bb1 (loop header), bb3 (exit).
    /// Fragments:
    ///   - {bb0}: entry to loop header
    ///   - {bb1, bb2}: loop body (bb2 → bb1 is exit-to-self, bb2 → bb3 is exit)
    ///   - {bb3}: exit
    #[test]
    fn test_single_loop_cfg() {
        let cfg = cfg_from_edges(4, &[(0, 1), (1, 2), (2, 1), (2, 3)]);
        let cut_point_set: HashSet<usize> = [0, 1, 3].into_iter().collect();
        let fragments = build_fragments(&cfg, &cut_point_set);

        assert_eq!(fragments.len(), 3);

        // Entry fragment.
        let f0 = fragments.iter().find(|f| f.entry_bb == 0).unwrap();
        assert_eq!(f0.blocks, vec![0]);
        assert!(f0.exits.contains(&(0, 1)));

        // Loop body fragment.
        let f1 = fragments.iter().find(|f| f.entry_bb == 1).unwrap();
        assert!(f1.blocks.contains(&1));
        assert!(f1.blocks.contains(&2));
        assert!(f1.exits.contains(&(2, 1)), "back-edge to loop header");
        assert!(f1.exits.contains(&(2, 3)), "exit to return block");

        // Exit fragment.
        let f3 = fragments.iter().find(|f| f.entry_bb == 3).unwrap();
        assert_eq!(f3.blocks, vec![3]);
        assert!(f3.exits.is_empty());
    }

    /// If-else: bb0 → bb1, bb0 → bb2, bb1 → bb3, bb2 → bb3, bb3 (return).
    /// Cut points: bb0 (entry), bb3 (exit).
    /// Single fragment (beyond exit): {bb0, bb1, bb2} with exit to bb3.
    #[test]
    fn test_if_else_cfg() {
        let cfg = cfg_from_edges(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        let cut_point_set: HashSet<usize> = [0, 3].into_iter().collect();
        let fragments = build_fragments(&cfg, &cut_point_set);

        assert_eq!(fragments.len(), 2);

        let f0 = fragments.iter().find(|f| f.entry_bb == 0).unwrap();
        assert!(f0.blocks.contains(&0));
        assert!(f0.blocks.contains(&1));
        assert!(f0.blocks.contains(&2));
        assert!(f0.exits.contains(&(1, 3)));
        assert!(f0.exits.contains(&(2, 3)));

        let f3 = fragments.iter().find(|f| f.entry_bb == 3).unwrap();
        assert_eq!(f3.blocks, vec![3]);
    }

    /// Nested loops:
    /// bb0 → bb1, bb1 → bb2, bb2 → bb3, bb3 → bb2 (inner back-edge),
    /// bb3 → bb4, bb4 → bb1 (outer back-edge), bb4 → bb5 (exit).
    /// Cut points: bb0 (entry), bb1 (outer loop header), bb2 (inner loop header), bb5 (exit).
    #[test]
    fn test_nested_loop_cfg() {
        let cfg = cfg_from_edges(6, &[(0, 1), (1, 2), (2, 3), (3, 2), (3, 4), (4, 1), (4, 5)]);
        let cut_point_set: HashSet<usize> = [0, 1, 2, 5].into_iter().collect();
        let fragments = build_fragments(&cfg, &cut_point_set);

        assert_eq!(fragments.len(), 4);

        // Entry fragment.
        let f0 = fragments.iter().find(|f| f.entry_bb == 0).unwrap();
        assert_eq!(f0.blocks, vec![0]);
        assert!(f0.exits.contains(&(0, 1)));

        // Outer loop body (bb1 → bb2 is exit to inner header).
        let f1 = fragments.iter().find(|f| f.entry_bb == 1).unwrap();
        assert!(f1.blocks.contains(&1));
        assert!(f1.exits.contains(&(1, 2)));

        // Inner loop body.
        let f2 = fragments.iter().find(|f| f.entry_bb == 2).unwrap();
        assert!(f2.blocks.contains(&2));
        assert!(f2.blocks.contains(&3));
        // Inner back-edge and exits to outer.
        assert!(f2.exits.contains(&(3, 2)), "inner back-edge");

        // Exit fragment.
        let f5 = fragments.iter().find(|f| f.entry_bb == 5).unwrap();
        assert_eq!(f5.blocks, vec![5]);
    }
}

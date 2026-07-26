// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// ===== Unit Tests (Part of #882) =====

#![allow(clippy::panic)] // Tests use panic! for assertion failures

use super::cfg::{Cfg, topo_sort};
use super::dominators::{
    compute_dom_matrix_from_idom, compute_dominators, compute_idom_lengauer_tarjan, dominates,
    find_loop_headers, validate_idom,
};
use super::unroll::{
    BlockMap, MAX_EXPANDED_BLOCKS, NaturalLoop, UnrollContext, check_single_entry,
    compute_effective_unwind_depth, natural_loop, remap_target, remap_unwind_action,
};
use super::{LoopUnrollError, unroll_cfg_loops};
use rustc_public::mir::{
    BasicBlock, Body, LocalDecl, Mutability, Terminator, TerminatorKind, UnwindAction,
};

/// Create dummy Span/Ty handles for unit tests that run without a rustc compiler session.
///
/// SAFETY: These are opaque handles (internally integer indices) that are never dereferenced
/// or passed back to the compiler. All-zeros is a valid bit pattern for these types in the
/// current rustc_public implementation. If rustc_public ever adds NonNull/&T/bool fields
/// to Span or Ty, this will need a proper test mock (#2062).
fn dummy_span() -> rustc_public::ty::Span {
    unsafe { std::mem::zeroed() }
}

fn dummy_ty() -> rustc_public::ty::Ty {
    unsafe { std::mem::zeroed() }
}

fn synthetic_body_with_unreachable_blocks(block_count: usize) -> Body {
    let span = dummy_span();
    let ty = dummy_ty();
    let block_template = BasicBlock {
        statements: Vec::new(),
        terminator: Terminator { kind: TerminatorKind::Unreachable, span },
    };
    let locals = vec![LocalDecl { ty, span, mutability: Mutability::Mut }];
    Body::new(vec![block_template; block_count], locals, 0, Vec::new(), None, span)
}

// Tests for topo_sort function

#[test]
fn test_topo_sort_empty() {
    // Empty graph should return empty order
    let successors: Vec<Vec<usize>> = vec![];
    let reachable: Vec<bool> = vec![];
    let order = topo_sort(&successors, &reachable);
    assert!(order.is_empty());
}

#[test]
fn test_topo_sort_single_node() {
    // Single reachable node with no successors
    let successors = vec![vec![]];
    let reachable = vec![true];
    let order = topo_sort(&successors, &reachable);
    assert_eq!(order, vec![0]);
}

#[test]
fn test_topo_sort_linear_chain() {
    // Linear chain: 0 -> 1 -> 2
    let successors = vec![vec![1], vec![2], vec![]];
    let reachable = vec![true, true, true];
    let order = topo_sort(&successors, &reachable);
    assert_eq!(order, vec![0, 1, 2]);
}

#[test]
fn test_topo_sort_diamond() {
    // Diamond graph: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
    let successors = vec![vec![1, 2], vec![3], vec![3], vec![]];
    let reachable = vec![true, true, true, true];
    let order = topo_sort(&successors, &reachable);
    // 0 must come first, 3 must come last, 1 and 2 can be in any order
    assert_eq!(order[0], 0);
    assert_eq!(order[3], 3);
    assert!(order[1] == 1 || order[1] == 2);
    assert!(order[2] == 1 || order[2] == 2);
}

#[test]
fn test_topo_sort_with_unreachable() {
    // Node 2 is unreachable
    let successors = vec![vec![1], vec![], vec![1]]; // 2 -> 1 but 2 is unreachable
    let reachable = vec![true, true, false];
    let order = topo_sort(&successors, &reachable);
    // Only nodes 0 and 1 should be in order
    assert_eq!(order.len(), 2);
    assert!(order.contains(&0));
    assert!(order.contains(&1));
    assert!(!order.contains(&2));
}

#[test]
fn test_topo_sort_cycle_incomplete() {
    // Graph with a cycle (0 -> 1 -> 0): topo_sort returns incomplete order
    let successors = vec![vec![1], vec![0]];
    let reachable = vec![true, true];
    let order = topo_sort(&successors, &reachable);
    // With a cycle, topo_sort will return fewer nodes than reachable
    // since neither node will reach 0 indegree
    assert!(order.is_empty(), "Cyclic graph should have no topo order");
}

#[test]
fn test_topo_sort_multiple_roots() {
    // Multiple entry points: 0 -> 2, 1 -> 2
    let successors = vec![vec![2], vec![2], vec![]];
    let reachable = vec![true, true, true];
    let order = topo_sort(&successors, &reachable);
    // Both 0 and 1 have indegree 0, so they come before 2
    assert_eq!(order.len(), 3);
    assert_eq!(order[2], 2); // 2 must be last
    assert!(order[0] == 0 || order[0] == 1);
    assert!(order[1] == 0 || order[1] == 1);
}

// Tests for Cfg struct helpers

#[test]
fn test_cfg_reachable_count_empty() {
    // Cfg with no reachable nodes
    let cfg = Cfg {
        successors: vec![vec![]],
        predecessors: vec![vec![]],
        reachable: vec![false],
        topo_order: vec![],
    };
    assert_eq!(cfg.reachable_count(), 0);
}

#[test]
fn test_cfg_reachable_count_partial() {
    // Cfg with some reachable nodes
    let cfg = Cfg {
        successors: vec![vec![], vec![], vec![]],
        predecessors: vec![vec![], vec![], vec![]],
        reachable: vec![true, false, true],
        topo_order: vec![0, 2],
    };
    assert_eq!(cfg.reachable_count(), 2);
}

#[test]
fn test_natural_loop_struct_creation() {
    // Test NaturalLoop struct construction
    let lp = NaturalLoop {
        header: 0,
        latches: vec![1],
        blocks: vec![0, 1],
        in_loop: vec![true, true, false],
    };
    assert_eq!(lp.header, 0);
    assert!(lp.in_loop[0]);
    assert!(lp.in_loop[1]);
    assert!(!lp.in_loop[2]);
}

#[test]
fn test_natural_loop_basic() {
    // Loop: 1 -> 2 -> 1 with exit 1 -> 3
    let cfg = Cfg {
        successors: vec![vec![1], vec![2, 3], vec![1], vec![]],
        predecessors: vec![vec![], vec![0, 2], vec![1], vec![1]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let lp = natural_loop(&cfg, 1, &[2]);
    assert_eq!(lp.header, 1);
    assert_eq!(lp.blocks, vec![1, 2]);
    assert!(lp.in_loop[1]);
    assert!(lp.in_loop[2]);
    assert!(!lp.in_loop[0]);
    assert!(!lp.in_loop[3]);
}

#[test]
fn test_check_single_entry_ok() {
    let cfg = Cfg {
        successors: vec![vec![1], vec![2, 3], vec![1], vec![]],
        predecessors: vec![vec![], vec![0, 2], vec![1], vec![1]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let lp = NaturalLoop {
        header: 1,
        latches: vec![2],
        blocks: vec![1, 2],
        in_loop: vec![false, true, true, false],
    };
    assert!(check_single_entry(&cfg, &lp).is_ok());
}

#[test]
fn test_check_single_entry_error() {
    let cfg = Cfg {
        successors: vec![vec![1], vec![2, 3], vec![1], vec![]],
        predecessors: vec![vec![], vec![0, 2], vec![0, 1], vec![1]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let lp = NaturalLoop {
        header: 1,
        latches: vec![2],
        blocks: vec![1, 2],
        in_loop: vec![false, true, true, false],
    };
    match check_single_entry(&cfg, &lp) {
        Err(LoopUnrollError::MultipleEntries { header, entry, pred }) => {
            assert_eq!(header, 1);
            assert_eq!(entry, 2);
            assert_eq!(pred, 0);
        }
        other => panic!("Expected MultipleEntries error, got {:?}", other),
    }
}

fn sample_loop_and_maps() -> (NaturalLoop, Vec<BlockMap>) {
    let lp = NaturalLoop {
        header: 1,
        latches: vec![2],
        blocks: vec![1, 2],
        in_loop: vec![false, true, true, false],
    };
    // Iteration 0: identity (no remaps).
    // Iteration 1: loop blocks remapped (1->11, 2->12); non-loop blocks identity.
    let maps =
        vec![BlockMap::identity(), BlockMap::with_remaps([(1, 11), (2, 12)].into_iter().collect())];
    (lp, maps)
}

#[test]
fn test_remap_target_outside_loop() {
    let (lp, maps) = sample_loop_and_maps();
    let ucx = UnrollContext::test_default(&lp, &maps);
    assert_eq!(remap_target(3, 0, 1, &ucx), 3);
}

#[test]
fn test_remap_target_internal_node() {
    let (lp, maps) = sample_loop_and_maps();
    let ucx = UnrollContext::test_default(&lp, &maps);
    assert_eq!(remap_target(2, 0, 1, &ucx), maps[0].get(2));
}

#[test]
fn test_remap_target_backedge_next_iter() {
    let (lp, maps) = sample_loop_and_maps();
    let ucx = UnrollContext::test_default(&lp, &maps);
    assert_eq!(remap_target(lp.header, 0, 2, &ucx), maps[1].get(lp.header));
}

#[test]
fn test_remap_target_final_iter_unwinding() {
    let (lp, maps) = sample_loop_and_maps();
    let ucx = UnrollContext::test_default(&lp, &maps);
    assert_eq!(remap_target(lp.header, 1, 2, &ucx), 99);
}

#[test]
fn test_remap_target_final_iter_silent_fail() {
    let (lp, maps) = sample_loop_and_maps();
    let mut ucx = UnrollContext::test_default(&lp, &maps);
    ucx.silent_fail_bb = 77;
    ucx.unwinding_assertions = false;
    // Part of #4175: with unwinding_assertions=false, exhausted back-edges
    // go to silent_fail_bb (Return block) instead of the loop exit.
    assert_eq!(remap_target(lp.header, 1, 2, &ucx), 77);
}

#[test]
fn test_remap_unwind_action_continue() {
    let map = BlockMap::with_remaps([(0, 10), (1, 11), (2, 12)].into_iter().collect());
    let action = remap_unwind_action(&UnwindAction::Continue, &map);
    assert!(matches!(action, UnwindAction::Continue));
}

#[test]
fn test_remap_unwind_action_unreachable_and_terminate() {
    let map = BlockMap::with_remaps([(0, 10), (1, 11), (2, 12)].into_iter().collect());
    let action = remap_unwind_action(&UnwindAction::Unreachable, &map);
    assert!(matches!(action, UnwindAction::Unreachable));
    let action = remap_unwind_action(&UnwindAction::Terminate, &map);
    assert!(matches!(action, UnwindAction::Terminate));
}

#[test]
fn test_remap_unwind_action_cleanup() {
    let map = BlockMap::with_remaps([(0, 10), (1, 11), (2, 12), (3, 42)].into_iter().collect());
    let action = remap_unwind_action(&UnwindAction::Cleanup(3), &map);
    match action {
        UnwindAction::Cleanup(bb) => assert_eq!(bb, 42),
        other => panic!("Expected Cleanup, got {:?}", other),
    }
}

// Tests for compute_dominators function

#[test]
fn test_dominators_single_node() {
    // Single node: dominates only itself
    let cfg = Cfg {
        successors: vec![vec![]],
        predecessors: vec![vec![]],
        reachable: vec![true],
        topo_order: vec![0],
    };
    let dom = compute_dominators(&cfg).expect("valid dominator tree");
    assert!(dom[0][0], "Node 0 should dominate itself");
}

#[test]
fn test_dominators_linear_chain() {
    // Linear: 0 -> 1 -> 2
    // Dominators: 0 dominates all, 1 dominates 1,2, 2 dominates 2
    let cfg = Cfg {
        successors: vec![vec![1], vec![2], vec![]],
        predecessors: vec![vec![], vec![0], vec![1]],
        reachable: vec![true, true, true],
        topo_order: vec![0, 1, 2],
    };
    let dom = compute_dominators(&cfg).expect("valid dominator tree");
    // Node 0 dominates all
    assert!(dom[0][0]);
    assert!(dom[1][0]);
    assert!(dom[2][0]);
    // Node 1 dominates 1, 2
    assert!(!dom[0][1]);
    assert!(dom[1][1]);
    assert!(dom[2][1]);
    // Node 2 dominates only itself
    assert!(!dom[0][2]);
    assert!(!dom[1][2]);
    assert!(dom[2][2]);
}

#[test]
fn test_dominators_with_unreachable_node() {
    // Graph: 0 -> 1 -> 2, node 3 unreachable
    let cfg = Cfg {
        successors: vec![vec![1], vec![2], vec![], vec![2]],
        predecessors: vec![vec![], vec![0], vec![1, 3], vec![]],
        reachable: vec![true, true, true, false],
        topo_order: vec![0, 1, 2],
    };
    let dom = compute_dominators(&cfg).expect("valid dominator tree");
    assert!(dom[0][0]);
    assert!(dom[1][0]);
    assert!(dom[2][0]);
    assert!(!dom[3][3], "Unreachable node should have no dominators recorded");
    assert!(dom[2][2]);
}

#[test]
fn test_dominators_diamond() {
    // Diamond: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
    // 0 dominates all, 1 and 2 only dominate themselves, 3 dominates itself
    let cfg = Cfg {
        successors: vec![vec![1, 2], vec![3], vec![3], vec![]],
        predecessors: vec![vec![], vec![0], vec![0], vec![1, 2]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let dom = compute_dominators(&cfg).expect("valid dominator tree");
    // Node 0 dominates all
    assert!(dom[0][0]);
    assert!(dom[1][0]);
    assert!(dom[2][0]);
    assert!(dom[3][0]);
    // Node 1 only dominates itself (not 3, because 3 is also reachable via 2)
    assert!(dom[1][1]);
    assert!(!dom[3][1]);
    // Node 2 only dominates itself
    assert!(dom[2][2]);
    assert!(!dom[3][2]);
    // Node 3 dominates only itself
    assert!(dom[3][3]);
}

#[test]
fn test_find_loop_headers_single_backedge() {
    // Loop: 0 -> 1 -> 2 -> 1 and 1 -> 3
    // Back-edge 2 -> 1 should identify header 1 with latch 2.
    let cfg = Cfg {
        successors: vec![vec![1], vec![2, 3], vec![1], vec![]],
        predecessors: vec![vec![], vec![0, 2], vec![1], vec![1]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let headers = find_loop_headers(&cfg).expect("valid idom tree");
    assert_eq!(headers.get(&1), Some(&vec![2]));
    assert_eq!(headers.len(), 1);
}

#[test]
fn test_validate_idom_cycle_two_node() {
    // Malformed idom cycle: 1 -> 2 -> 1
    let idom = vec![usize::MAX, 2, 1];
    let reachable = vec![true, true, true];
    let result = validate_idom(&idom, &reachable);
    assert!(result.is_err(), "Should detect two-node cycle");
    match result {
        Err(LoopUnrollError::IdomCycle { node: 1, revisited: 1, .. }) => (),
        other => panic!("Expected IdomCycle{{node:1, revisited:1}}, got {:?}", other),
    }
}

#[test]
fn test_validate_idom_valid_chain() {
    let idom = vec![usize::MAX, 0, 1, 2];
    let reachable = vec![true, true, true, true];
    assert!(validate_idom(&idom, &reachable).is_ok());
}

// Tests for idom cycle detection (issue #1291, #1293)

#[test]
fn test_idom_cycle_self_loop() {
    // Malformed idom: node 1 is its own immediate dominator (self-loop cycle)
    // idom[0] = MAX (entry), idom[1] = 1 (self-loop!), idom[2] = 1
    let idom = vec![usize::MAX, 1, 1];
    let reachable = vec![true, true, true];

    let result = compute_dom_matrix_from_idom(&idom, &reachable);
    assert!(result.is_err(), "Should detect idom self-loop cycle");
    match result {
        Err(LoopUnrollError::IdomCycle { node: 1, revisited: 1, .. }) => (),
        other => panic!("Expected IdomCycle for node 1, got {:?}", other),
    }
}

#[test]
fn test_idom_cycle_two_node() {
    // Malformed idom: nodes 1 and 2 form a cycle (1 -> 2 -> 1)
    // idom[0] = MAX (entry), idom[1] = 2, idom[2] = 1
    let idom = vec![usize::MAX, 2, 1];
    let reachable = vec![true, true, true];

    let result = compute_dom_matrix_from_idom(&idom, &reachable);
    assert!(result.is_err(), "Should detect idom two-node cycle");
    // Node 1 is first non-entry processed, walks idom chain 1->2->1, revisits 1
    match result {
        Err(LoopUnrollError::IdomCycle { node: 1, revisited: 1, .. }) => (),
        other => panic!("Expected IdomCycle{{node:1, revisited:1}}, got {:?}", other),
    }
}

#[test]
fn test_idom_valid_chain() {
    // Valid idom: linear chain 0 <- 1 <- 2
    // idom[0] = MAX (entry), idom[1] = 0, idom[2] = 1
    let idom = vec![usize::MAX, 0, 1];
    let reachable = vec![true, true, true];

    let result = compute_dom_matrix_from_idom(&idom, &reachable);
    assert!(result.is_ok(), "Valid idom should succeed");
    let dom = result.expect("valid dominator tree");
    // Node 0 dominates all
    assert!(dom[0][0]);
    assert!(dom[1][0]);
    assert!(dom[2][0]);
    // Node 1 dominates 1, 2
    assert!(!dom[0][1]);
    assert!(dom[1][1]);
    assert!(dom[2][1]);
    // Node 2 only dominates itself (not 0 or 1)
    assert!(!dom[0][2], "Node 2 should not dominate node 0");
    assert!(!dom[1][2], "Node 2 should not dominate node 1");
    assert!(dom[2][2]);
}

// Tests for compute_idom_lengauer_tarjan (Lengauer-Tarjan immediate dominators)

#[test]
fn test_idom_empty_graph() {
    let cfg =
        Cfg { successors: vec![], predecessors: vec![], reachable: vec![], topo_order: vec![] };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert!(idom.is_empty());
}

#[test]
fn test_idom_single_node() {
    // Single node has no immediate dominator (it's the entry)
    let cfg = Cfg {
        successors: vec![vec![]],
        predecessors: vec![vec![]],
        reachable: vec![true],
        topo_order: vec![0],
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX, "Entry node has no idom");
}

#[test]
fn test_idom_linear_chain() {
    // Linear: 0 -> 1 -> 2
    // idom[0] = MAX (entry), idom[1] = 0, idom[2] = 1
    let cfg = Cfg {
        successors: vec![vec![1], vec![2], vec![]],
        predecessors: vec![vec![], vec![0], vec![1]],
        reachable: vec![true, true, true],
        topo_order: vec![0, 1, 2],
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX, "Entry has no idom");
    assert_eq!(idom[1], 0, "idom[1] = 0");
    assert_eq!(idom[2], 1, "idom[2] = 1");
}

#[test]
fn test_idom_diamond() {
    // Diamond: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
    // idom[0] = MAX, idom[1] = 0, idom[2] = 0, idom[3] = 0
    let cfg = Cfg {
        successors: vec![vec![1, 2], vec![3], vec![3], vec![]],
        predecessors: vec![vec![], vec![0], vec![0], vec![1, 2]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3],
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX, "Entry has no idom");
    assert_eq!(idom[1], 0, "idom[1] = 0");
    assert_eq!(idom[2], 0, "idom[2] = 0");
    assert_eq!(idom[3], 0, "idom[3] = 0 (join point)");
}

#[test]
fn test_idom_with_loop() {
    // Graph with back edge: 0 -> 1 -> 2 -> 1 (loop), 1 -> 3
    // 2 has back edge to 1, but 1 still dominates 2
    // idom[0] = MAX, idom[1] = 0, idom[2] = 1, idom[3] = 1
    let cfg = Cfg {
        successors: vec![vec![1], vec![2, 3], vec![1], vec![]],
        predecessors: vec![vec![], vec![0, 2], vec![1], vec![1]],
        reachable: vec![true, true, true, true],
        topo_order: vec![0, 1, 2, 3], // Not a valid topo due to cycle, but we need reachability
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX, "Entry has no idom");
    assert_eq!(idom[1], 0, "idom[1] = 0");
    assert_eq!(idom[2], 1, "idom[2] = 1");
    assert_eq!(idom[3], 1, "idom[3] = 1");
}

#[test]
fn test_idom_deep_tree() {
    // Deep tree: 0 -> 1 -> 2 -> 3 -> 4
    // idom forms same chain
    let cfg = Cfg {
        successors: vec![vec![1], vec![2], vec![3], vec![4], vec![]],
        predecessors: vec![vec![], vec![0], vec![1], vec![2], vec![3]],
        reachable: vec![true, true, true, true, true],
        topo_order: vec![0, 1, 2, 3, 4],
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX);
    assert_eq!(idom[1], 0);
    assert_eq!(idom[2], 1);
    assert_eq!(idom[3], 2);
    assert_eq!(idom[4], 3);
}

#[test]
fn test_idom_with_unreachable_nodes() {
    // Graph: 0 -> 1 -> 2, with node 3 unreachable
    // Node 3 is not connected to entry, so it should have idom = MAX
    let cfg = Cfg {
        successors: vec![vec![1], vec![2], vec![], vec![2]], // 3 -> 2 but 3 unreachable
        predecessors: vec![vec![], vec![0], vec![1, 3], vec![]],
        reachable: vec![true, true, true, false],
        topo_order: vec![0, 1, 2],
    };
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert_eq!(idom[0], usize::MAX, "Entry has no idom");
    assert_eq!(idom[1], 0, "idom[1] = 0");
    assert_eq!(idom[2], 1, "idom[2] = 1 (3 is unreachable, doesn't affect dominator)");
    assert_eq!(idom[3], usize::MAX, "Unreachable node has no idom");
}

// Tests for LoopUnrollError

#[test]
fn test_loop_unroll_error_debug() {
    // Verify LoopUnrollError variants can be debug-printed
    let err = LoopUnrollError::IrreducibleCycle;
    assert!(format!("{:?}", err).contains("IrreducibleCycle"));

    let err = LoopUnrollError::MultipleEntries { header: 1, entry: 2, pred: 3 };
    let debug = format!("{:?}", err);
    assert!(debug.contains("MultipleEntries"));
    assert!(debug.contains('1'));

    let err = LoopUnrollError::TooManyIterations { iterations: 100 };
    let debug = format!("{:?}", err);
    assert!(debug.contains("TooManyIterations"));
    assert!(debug.contains("100"));

    let err = LoopUnrollError::IdomCycle { node: 5, revisited: 3, steps: 2 };
    let debug = format!("{:?}", err);
    assert!(debug.contains("IdomCycle"));
    assert!(debug.contains('5'));

    let err = LoopUnrollError::MaxBlocksExceeded { block_count: 100_001, limit: 100_000 };
    let debug = format!("{:?}", err);
    assert!(debug.contains("MaxBlocksExceeded"));
    assert!(debug.contains("100001"));
}

#[test]
fn test_loop_unroll_error_display() {
    // Verify Display implementations produce user-friendly messages (#1296)
    let err = LoopUnrollError::IrreducibleCycle;
    assert_eq!(format!("{}", err), "irreducible control flow (non-natural loop)");

    let err = LoopUnrollError::MultipleEntries { header: 1, entry: 2, pred: 3 };
    assert_eq!(format!("{}", err), "multiple loop entries: header=1, entry=2, pred=3");

    let err = LoopUnrollError::TooManyIterations { iterations: 100 };
    assert_eq!(format!("{}", err), "exceeded max unroll iterations (100)");

    let err = LoopUnrollError::IdomCycle { node: 5, revisited: 3, steps: 2 };
    assert_eq!(format!("{}", err), "dominator tree cycle: node 5 revisited 3 after 2 steps");

    let err = LoopUnrollError::MaxBlocksExceeded { block_count: 100_001, limit: 100_000 };
    assert_eq!(format!("{}", err), "total block count 100001 exceeds limit 100000");
}

#[test]
fn test_loop_unroll_error_is_std_error() {
    // Verify LoopUnrollError implements std::error::Error (#1296)
    fn assert_error<E: std::error::Error>(_: &E) {}

    let err = LoopUnrollError::IrreducibleCycle;
    assert_error(&err);
}

#[test]
fn test_loop_unroll_error_display_edge_cases() {
    // Verify Display works correctly at boundary values (#1296)
    // Zero values
    let err = LoopUnrollError::TooManyIterations { iterations: 0 };
    assert_eq!(format!("{}", err), "exceeded max unroll iterations (0)");

    let err = LoopUnrollError::IdomCycle { node: 0, revisited: 0, steps: 0 };
    assert_eq!(format!("{}", err), "dominator tree cycle: node 0 revisited 0 after 0 steps");

    // Large values (verify no panic)
    let err = LoopUnrollError::TooManyIterations { iterations: usize::MAX };
    let msg = format!("{}", err);
    assert!(msg.contains("exceeded max unroll iterations"));

    let err = LoopUnrollError::MaxBlocksExceeded { block_count: usize::MAX, limit: usize::MAX - 1 };
    let msg = format!("{}", err);
    assert!(msg.contains("total block count"));
}

#[test]
fn test_unroll_cfg_loops_max_blocks_guard_via_public_api() {
    // Exercise the global block-count guard through the public unroll entry point.
    let body = synthetic_body_with_unreachable_blocks(100_001);

    let err = unroll_cfg_loops(body, 1, false).expect_err("body over cap must fail");
    match err {
        LoopUnrollError::MaxBlocksExceeded { block_count, limit } => {
            assert_eq!(block_count, 100_001);
            assert_eq!(limit, 100_000);
        }
        other => panic!("Expected MaxBlocksExceeded, got {:?}", other),
    }
}

// Tests for compute_effective_unwind_depth (memory bounds heuristic)

#[test]
fn test_effective_depth_within_bounds() {
    // Small loop (10 blocks) with moderate depth (100): 10 * 100 = 1000 < 10_000
    let (depth, reduced) = compute_effective_unwind_depth(100, 10);
    assert_eq!(depth, 100);
    assert!(!reduced, "Should not be reduced when within bounds");
}

#[test]
fn test_effective_depth_at_boundary() {
    // Exactly at boundary: 1000 blocks * 10 depth = 10_000 = MAX_EXPANDED_BLOCKS
    let (depth, reduced) = compute_effective_unwind_depth(10, 1000);
    assert_eq!(depth, 10);
    assert!(!reduced, "Should not be reduced when exactly at boundary");
}

#[test]
fn test_effective_depth_exceeds_bounds() {
    // Large loop (2000 blocks) with depth 10: 2000 * 10 = 20_000 > 10_000
    // Expected: 10_000 / 2000 = 5
    let (depth, reduced) = compute_effective_unwind_depth(10, 2000);
    assert_eq!(depth, 5);
    assert!(reduced, "Should be reduced when exceeding bounds");
}

#[test]
fn test_effective_depth_minimum_of_one() {
    // Very large loop (20_000 blocks) with depth 100: would reduce to 0
    // But minimum is 1 to make progress
    let (depth, reduced) = compute_effective_unwind_depth(100, 20_000);
    assert_eq!(depth, 1, "Minimum depth should be 1");
    assert!(reduced);
}

#[test]
fn test_effective_depth_zero_blocks() {
    // Edge case: 0 blocks (shouldn't happen, but be defensive)
    let (depth, reduced) = compute_effective_unwind_depth(100, 0);
    assert_eq!(depth, 100);
    assert!(!reduced, "Zero blocks means zero expansion");
}

#[test]
fn test_effective_depth_nested_loop_scenario() {
    // Simulates nested loop: after inner loop unrolled, outer loop sees 500 blocks
    // With depth 100: 500 * 100 = 50_000 > 10_000
    // Expected: 10_000 / 500 = 20
    let (depth, reduced) = compute_effective_unwind_depth(100, 500);
    assert_eq!(depth, 20);
    assert!(reduced);
}

#[test]
fn test_effective_depth_overflow_protection() {
    // Defensive: huge depth with non-zero blocks should still reduce safely.
    let (depth, reduced) = compute_effective_unwind_depth(usize::MAX, 2);
    assert_eq!(depth, MAX_EXPANDED_BLOCKS / 2);
    assert!(reduced);
}

#[test]
fn test_effective_depth_single_block_max_depth() {
    // Edge case: loop_blocks=1 with depth=MAX_EXPANDED_BLOCKS
    // 1 * 10_000 = 10_000 = MAX, should be exactly at boundary
    let (depth, reduced) = compute_effective_unwind_depth(MAX_EXPANDED_BLOCKS, 1);
    assert_eq!(depth, MAX_EXPANDED_BLOCKS);
    assert!(!reduced, "Exactly at boundary should not be reduced");

    // Just over boundary: 1 * 10_001 > 10_000
    let (depth, reduced) = compute_effective_unwind_depth(MAX_EXPANDED_BLOCKS + 1, 1);
    assert_eq!(depth, MAX_EXPANDED_BLOCKS);
    assert!(reduced, "Over boundary should be reduced");
}

// ===== Stress tests for large synthetic CFGs (Part of #2040) =====

/// Build a Cfg directly (bypasses Body) for stress-testing internal algorithms.
fn synthetic_cfg_chain_with_backedge(chain_len: usize) -> Cfg {
    // Linear chain 0->1->2->...->( n-1) with back-edge (n-1)->0.
    let mut successors = Vec::with_capacity(chain_len);
    let mut predecessors = vec![Vec::new(); chain_len];
    for i in 0..chain_len {
        if i + 1 < chain_len {
            successors.push(vec![i + 1]);
            predecessors[i + 1].push(i);
        } else {
            // Back-edge to header
            successors.push(vec![0]);
            predecessors[0].push(i);
        }
    }
    let reachable = vec![true; chain_len];
    let topo_order = topo_sort(&successors, &reachable);
    Cfg { successors, predecessors, reachable, topo_order }
}

/// Build a Cfg with `num_loops` independent self-loops (block i -> i for i in 1..=num_loops,
/// plus entry block 0 that branches to all of them, plus an exit block).
#[allow(clippy::needless_range_loop)]
fn synthetic_cfg_many_self_loops(num_loops: usize) -> Cfg {
    let n = num_loops + 2; // block 0 = entry, 1..=num_loops = loop bodies, n-1 = exit
    let mut successors = vec![Vec::new(); n];
    let mut predecessors = vec![Vec::new(); n];

    // Entry fans out to all loop bodies
    for i in 1..=num_loops {
        successors[0].push(i);
        predecessors[i].push(0);
    }
    // Each loop body: self-loop + forward edge to exit
    let exit = n - 1;
    for i in 1..=num_loops {
        successors[i] = vec![i, exit]; // self-loop + exit
        predecessors[i].push(i);
        predecessors[exit].push(i);
    }
    let reachable = vec![true; n];
    let topo_order = topo_sort(&successors, &reachable);
    Cfg { successors, predecessors, reachable, topo_order }
}

/// Build a Cfg with `depth` nested loops: 0->1->2->...->depth, with back-edges
/// depth->(depth-1), (depth-1)->(depth-2), ..., 1->0.
fn synthetic_cfg_nested_loops(depth: usize) -> Cfg {
    // Blocks: 0, 1, ..., depth, (depth+1)=exit
    // Forward edges: i->i+1 for i in 0..=depth
    // Back-edges: i->(i-1) for i in 1..=depth (each block also loops back)
    let n = depth + 2;
    let mut successors = vec![Vec::new(); n];
    let mut predecessors = vec![Vec::new(); n];

    for i in 0..=depth {
        successors[i].push(i + 1); // forward
        predecessors[i + 1].push(i);
        if i > 0 {
            successors[i].push(i - 1); // back-edge
            predecessors[i - 1].push(i);
        }
    }
    let reachable = vec![true; n];
    let topo_order = topo_sort(&successors, &reachable);
    Cfg { successors, predecessors, reachable, topo_order }
}

/// Build a synthetic Body with a single loop for public API stress testing.
/// Chain: 0->1->2->...->( n-2)->(n-1), with back-edge (n-1)->1 forming a loop.
/// Block 0 is the entry, block (n-1) has the back-edge to block 1.
fn synthetic_body_with_loop(body_blocks: usize) -> Body {
    assert!(body_blocks >= 3, "need at least entry + 2 loop blocks");
    let span = dummy_span();
    let ty = dummy_ty();

    let mut blocks = Vec::with_capacity(body_blocks);
    for i in 0..body_blocks {
        let kind = if i + 1 < body_blocks {
            TerminatorKind::Goto { target: i + 1 }
        } else {
            // Last block: back-edge to block 1 (loop header)
            TerminatorKind::Goto { target: 1 }
        };
        blocks.push(BasicBlock { statements: Vec::new(), terminator: Terminator { kind, span } });
    }
    let locals = vec![LocalDecl { ty, span, mutability: Mutability::Mut }];
    Body::new(blocks, locals, 0, Vec::new(), None, span)
}

#[test]
fn test_stress_idom_deep_chain_1000() {
    // Deep linear chain with single back-edge: stresses idom walk depth.
    let cfg = synthetic_cfg_chain_with_backedge(1_000);
    let idom = compute_idom_lengauer_tarjan(&cfg);
    validate_idom(&idom, &cfg.reachable).expect("idom should be cycle-free");
    // Entry node should have no dominator
    assert_eq!(idom[0], usize::MAX);
    // Every other node should be dominated by its predecessor
    for (i, &dominator) in idom.iter().enumerate().skip(1).take(999) {
        assert_eq!(dominator, i - 1, "node {i} should be dominated by {}", i - 1);
    }
}

#[test]
fn test_stress_idom_deep_chain_10000() {
    // 10K chain: validates iterative compress doesn't stack overflow.
    let cfg = synthetic_cfg_chain_with_backedge(10_000);
    let idom = compute_idom_lengauer_tarjan(&cfg);
    validate_idom(&idom, &cfg.reachable).expect("idom should be cycle-free");
    assert_eq!(idom[0], usize::MAX);
    // Spot-check: every node dominated by its predecessor (same invariant as 1000-node test)
    for i in [1, 100, 999, 5_000, 9_999] {
        assert_eq!(idom[i], i - 1, "node {i} should be dominated by {}", i - 1);
    }
}

#[test]
fn test_stress_find_headers_many_loops_500() {
    // 500 independent self-loops: stresses header detection with many back-edges.
    let cfg = synthetic_cfg_many_self_loops(500);
    let headers = find_loop_headers(&cfg).expect("should find headers in valid reducible CFG");
    assert_eq!(headers.len(), 500, "each self-loop block should be detected as a loop header");
    for i in 1..=500 {
        assert!(headers.contains_key(&i), "block {i} should be a detected loop header");
    }
}

#[test]
fn test_stress_find_headers_many_loops_2000() {
    // 2000 independent self-loops: larger scale.
    let cfg = synthetic_cfg_many_self_loops(2_000);
    let headers = find_loop_headers(&cfg).expect("should find headers in valid reducible CFG");
    assert_eq!(headers.len(), 2_000);
    // Spot-check membership at boundaries and midpoint
    for i in [1, 500, 1_000, 1_500, 2_000] {
        assert!(headers.contains_key(&i), "block {i} should be a detected loop header");
    }
}

#[test]
fn test_stress_nested_loops_50() {
    // 50 nesting levels: stresses iterative unrolling loop count.
    let cfg = synthetic_cfg_nested_loops(50);
    let headers = find_loop_headers(&cfg).expect("should find headers in nested loop CFG");
    // Each nesting level contributes one header (blocks 0..depth-1 each get a back-edge).
    // Back-edge i->(i-1) makes block i-1 a header for i in 1..=50, giving exactly 50 headers.
    assert_eq!(
        headers.len(),
        50,
        "expected exactly 50 headers for 50 nesting levels, got {}",
        headers.len()
    );
    for i in 0..50 {
        assert!(
            headers.contains_key(&i),
            "block {i} should be a loop header (back-edge from {})",
            i + 1
        );
    }
}

#[test]
fn test_stress_nested_loops_200() {
    // 200 nesting levels
    let cfg = synthetic_cfg_nested_loops(200);
    let idom = compute_idom_lengauer_tarjan(&cfg);
    validate_idom(&idom, &cfg.reachable).expect("idom should be cycle-free");
    let headers = find_loop_headers(&cfg).expect("should find headers in deeply nested CFG");
    // Back-edge i->(i-1) makes block i-1 a header for i in 1..=200, giving exactly 200 headers.
    assert_eq!(
        headers.len(),
        200,
        "expected exactly 200 headers for 200 nesting levels, got {}",
        headers.len()
    );
    for i in 0..200 {
        assert!(
            headers.contains_key(&i),
            "block {i} should be a loop header (back-edge from {})",
            i + 1
        );
    }
}

#[test]
fn test_stress_unroll_public_api_small_loop() {
    // 20-block body with single back-edge: verifies unrolling terminates correctly.
    let body = synthetic_body_with_loop(20);
    let result = unroll_cfg_loops(body, 3, false);
    let body = result.expect("unrolling 20-block loop at depth 3 should succeed");
    // After unrolling, CFG should be acyclic
    let cfg = Cfg::from_body(&body);
    assert!(cfg.is_acyclic(), "unrolled body must be acyclic");
}

#[test]
fn test_stress_unroll_public_api_medium_loop() {
    // 200-block body with single back-edge and depth 2.
    // The memory heuristic should keep block count manageable.
    let body = synthetic_body_with_loop(200);
    let result = unroll_cfg_loops(body, 2, false);
    let body = result.expect("unrolling 200-block loop at depth 2 should succeed");
    let cfg = Cfg::from_body(&body);
    assert!(cfg.is_acyclic(), "unrolled body must be acyclic");
}

#[test]
fn test_stress_unroll_public_api_large_loop_depth_capped() {
    // 5000-block body with high unwind depth.
    // compute_effective_unwind_depth should cap: 5000 * 100 = 500_000 > 10_000
    // Effective depth = 10_000/5_000 = 2
    let body = synthetic_body_with_loop(5_000);
    let result = unroll_cfg_loops(body, 100, false);
    let body = result.expect("large loop with capped depth should succeed");
    let cfg = Cfg::from_body(&body);
    assert!(cfg.is_acyclic(), "unrolled body must be acyclic");
}

#[test]
fn test_stress_validate_idom_linear_10000() {
    // Direct validate_idom on a 10K-node linear chain idom array.
    let n = 10_000;
    let cfg = synthetic_cfg_chain_with_backedge(n);
    let idom = compute_idom_lengauer_tarjan(&cfg);
    // Should validate without hitting cycles
    validate_idom(&idom, &cfg.reachable).expect("linear idom should validate");
}

#[test]
fn test_stress_dominates_deep_query() {
    // 5000-node chain: verify dominates(0, 4999) walks the full depth.
    let cfg = synthetic_cfg_chain_with_backedge(5_000);
    let idom = compute_idom_lengauer_tarjan(&cfg);
    assert!(
        dominates(&idom, 0, 4_999, 5_000),
        "entry should dominate the last node in a linear chain"
    );
    assert!(!dominates(&idom, 4_999, 0, 5_000), "last node should not dominate entry");
}

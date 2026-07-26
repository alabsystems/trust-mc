// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A call graph mirroring `reachability::CallGraph`.
//
// The real type is:
//
//     pub(crate) struct CallGraph {
//         nodes: HashSet<Node>,                       // Node(MonoItem)
//         edges: HashMap<Node, Vec<CollectedNode>>,   // CollectedNode(CollectedItem)
//         back_edges: HashMap<Node, Vec<CollectedNode>>,
//     }
//
// where each `CollectedItem` carries a `CollectionReason`. We model the same
// shape over `Instance::name()` strings (`ItemPath`) and a reason that maps 1:1
// onto the subset of `CollectionReason` an edge can carry:
//
//     CollectionReason::DirectCall   -> EdgeReason::DirectCall
//     CollectionReason::IndirectCall -> EdgeReason::IndirectCall
//     CollectionReason::StaticDrop   -> EdgeReason::Drop   (the `Drop` terminator)
//     CollectionReason::VTableMethod -> EdgeReason::IndirectCall (dyn dispatch)
//
// We keep `back_edges` because the witness-path reconstruction is a reverse walk,
// exactly like the real `dump_reason()` reverse traversal.

use std::collections::{BTreeMap, BTreeSet};

/// A monomorphized item's identity: its `Instance::name()` / `def_path_str()`
/// string. Owned `String` here (the real `Node` owns a `MonoItem`).
pub type ItemPath = String;

/// Why an edge exists. Mirrors the edge-bearing subset of `CollectionReason`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EdgeReason {
    /// `TerminatorKind::Call` to a statically-known callee.
    DirectCall,
    /// fn-ptr / `dyn` dispatch (`CollectionReason::IndirectCall`/`VTableMethod`).
    IndirectCall,
    /// `TerminatorKind::Drop` -> `drop_in_place` glue
    /// (`CollectionReason::StaticDrop`). This is the architecturally-invisible
    /// edge: nothing at the source site names the callee.
    Drop,
}

impl EdgeReason {
    pub fn arrow(self) -> &'static str {
        match self {
            EdgeReason::DirectCall => " --call--> ",
            EdgeReason::IndirectCall => " --dyn--> ",
            EdgeReason::Drop => " --Drop--> ",
        }
    }
}

/// One directed edge: `from` calls/drops `to`, for `reason`.
#[derive(Clone, Debug)]
pub struct Edge {
    pub from: ItemPath,
    pub to: ItemPath,
    pub reason: EdgeReason,
}

impl Edge {
    pub fn call(from: &str, to: &str) -> Edge {
        Edge { from: from.into(), to: to.into(), reason: EdgeReason::DirectCall }
    }
    pub fn dynamic(from: &str, to: &str) -> Edge {
        Edge { from: from.into(), to: to.into(), reason: EdgeReason::IndirectCall }
    }
    pub fn drop(from: &str, to: &str) -> Edge {
        Edge { from: from.into(), to: to.into(), reason: EdgeReason::Drop }
    }
}

/// Forward adjacency `from -> [(to, reason)]`. `BTreeMap`/`BTreeSet` give the
/// same deterministic ordering trust-mc relies on for reproducible output.
#[derive(Debug, Default)]
pub struct CallGraph {
    nodes: BTreeSet<ItemPath>,
    edges: BTreeMap<ItemPath, Vec<(ItemPath, EdgeReason)>>,
}

impl CallGraph {
    pub fn from_edges(edges: impl IntoIterator<Item = Edge>) -> CallGraph {
        let mut g = CallGraph::default();
        for e in edges {
            g.nodes.insert(e.from.clone());
            g.nodes.insert(e.to.clone());
            g.edges.entry(e.from).or_default().push((e.to, e.reason));
        }
        g
    }

    pub fn nodes(&self) -> impl Iterator<Item = &ItemPath> {
        self.nodes.iter()
    }

    pub fn successors(&self, node: &str) -> &[(ItemPath, EdgeReason)] {
        self.edges.get(node).map(Vec::as_slice).unwrap_or(&[])
    }
}

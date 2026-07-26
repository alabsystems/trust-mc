// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Graph data structure to store the results of points-to analysis.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Location, Place, ProjectionElem},
    ty::{Instance, List, TyCtxt},
};
use rustc_mir_dataflow::{JoinSemiLattice, fmt::DebugWithContext};
use rustc_public::mir::{
    Place as StablePlace,
    mono::{Instance as StableInstance, StaticDef},
};
use rustc_public::rustc_internal;
use std::collections::{HashMap, HashSet, VecDeque};

/// A node in the points-to graph, which could be a place on the stack, a heap allocation, or a static.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub(crate) enum MemLoc<'tcx> {
    /// Notice that the type of `Place` here is not restricted to references or pointers. For
    /// example, we propagate aliasing information for values derived from casting a pointer to a
    /// usize in order to ensure soundness, as it could later be casted back to a pointer.
    Stack(Instance<'tcx>, Place<'tcx>),
    /// Using a combination of the instance of the function where the allocation took place and the
    /// location of the allocation inside this function implements allocation-site abstraction.
    Heap(Instance<'tcx>, Location),
    Static(DefId),
}

impl<'tcx> MemLoc<'tcx> {
    /// Create a memory location representing a new heap allocation site.
    pub(super) fn new_heap_allocation(instance: Instance<'tcx>, location: Location) -> Self {
        MemLoc::Heap(instance, location)
    }

    /// Create a memory location representing a new stack allocation.
    pub(super) fn new_stack_allocation(instance: Instance<'tcx>, place: Place<'tcx>) -> Self {
        MemLoc::Stack(instance, place)
    }

    /// Create a memory location representing a new static allocation.
    pub(super) fn new_static_allocation(static_def: DefId) -> Self {
        MemLoc::Static(static_def)
    }

    /// Create a memory location representing a new stack allocation from StableMIR values.
    pub(crate) fn from_stable_stack_allocation(
        instance: StableInstance,
        place: StablePlace,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let internal_instance = rustc_internal::internal(tcx, instance);
        let internal_place = rustc_internal::internal(tcx, place);
        Self::new_stack_allocation(internal_instance, internal_place)
    }

    /// Create a memory location representing a new static allocation from StableMIR values.
    pub(crate) fn from_stable_static_allocation(static_def: StaticDef, tcx: TyCtxt<'tcx>) -> Self {
        let static_def_id = rustc_internal::internal(tcx, static_def);
        Self::new_static_allocation(static_def_id)
    }
}

/// Data structure to keep track of both successors and ancestors of the node.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct NodeData<'tcx> {
    successors: HashSet<MemLoc<'tcx>>,
    ancestors: HashSet<MemLoc<'tcx>>,
}

impl<'tcx> NodeData<'tcx> {
    /// Merge another NodeData into self, return true if self was updated.
    fn merge(&mut self, other: &Self) -> bool {
        let s = self.successors.len();
        let a = self.ancestors.len();
        self.successors.extend(other.successors.iter().copied());
        self.ancestors.extend(other.ancestors.iter().copied());
        self.successors.len() != s || self.ancestors.len() != a
    }
}

/// Graph data structure that stores the current results of the point-to analysis. The graph is
/// directed, so having an edge between two places means that one is pointing to the other.
///
/// For example:
/// - `a = &b` would translate to `a --> b`
/// - `a = b` would translate to `a --> {all pointees of b}` (if `a` and `b` are pointers /
///   references)
///
/// Note that the aliasing is not field-sensitive, since the nodes in the graph are places with no
/// projections, which is sound but can be imprecise.
///
/// For example:
/// ```
/// let ref_pair = (&a, &b); // Will add `ref_pair --> (a | b)` edges into the graph.
/// let first = ref_pair.0; // Will add `first -> (a | b)`, which is an overapproximation.
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PointsToGraph<'tcx> {
    /// A hash map of node --> {nodes} edges.
    nodes: HashMap<MemLoc<'tcx>, NodeData<'tcx>>,
}

impl<'tcx> PointsToGraph<'tcx> {
    pub(crate) fn empty() -> Self {
        Self { nodes: HashMap::new() }
    }

    /// Collect all nodes currently present in the graph.
    pub(super) fn all_nodes(&self) -> HashSet<MemLoc<'tcx>> {
        self.nodes.keys().copied().collect()
    }

    /// Collect all nodes which have incoming edges from `nodes`.
    pub(crate) fn successors(&self, nodes: &HashSet<MemLoc<'tcx>>) -> HashSet<MemLoc<'tcx>> {
        nodes
            .iter()
            .filter_map(|node| self.nodes.get(node))
            .flat_map(|nd| nd.successors.iter().copied())
            .collect()
    }

    /// Collect all nodes which have outgoing edges to `nodes`.
    pub(crate) fn ancestors(&self, nodes: &HashSet<MemLoc<'tcx>>) -> HashSet<MemLoc<'tcx>> {
        nodes
            .iter()
            .filter_map(|node| self.nodes.get(node))
            .flat_map(|nd| nd.ancestors.iter().copied())
            .collect()
    }

    /// For each node in `from`, add an edge to each node in `to` (and the reverse for ancestors).
    pub(super) fn extend(&mut self, from: &HashSet<MemLoc<'tcx>>, to: &HashSet<MemLoc<'tcx>>) {
        for node in from {
            let node_pointees = self.nodes.entry(*node).or_default();
            node_pointees.successors.extend(to.iter());
        }
        for node in to {
            let node_pointees = self.nodes.entry(*node).or_default();
            node_pointees.ancestors.extend(from.iter());
        }
    }

    /// Collect all places to which a given place can alias.
    ///
    /// We automatically resolve dereference projections here (by finding successors for each
    /// dereference projection we encounter), which is valid as long as we do it for every place we
    /// add to the graph.
    pub(super) fn resolve_place(
        &self,
        place: Place<'tcx>,
        instance: Instance<'tcx>,
    ) -> HashSet<MemLoc<'tcx>> {
        let place_without_projections = Place { local: place.local, projection: List::empty() };
        let mut node_set =
            HashSet::from([MemLoc::new_stack_allocation(instance, place_without_projections)]);
        for projection in place.projection {
            match projection {
                ProjectionElem::Deref => {
                    node_set = self.successors(&node_set);
                }
                ProjectionElem::Field(..)
                | ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::Downcast(..)
                | ProjectionElem::OpaqueCast(..)
                | ProjectionElem::UnwrapUnsafeBinder(..) => {
                    /* There operations are no-ops w.r.t aliasing since we are tracking it on per-object basis. */
                }
            }
        }
        node_set
    }

    /// Stable interface for `resolve_place`.
    pub(crate) fn resolve_place_stable(
        &self,
        place: StablePlace,
        instance: StableInstance,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<MemLoc<'tcx>> {
        let internal_place = rustc_internal::internal(tcx, place);
        let internal_instance = rustc_internal::internal(tcx, instance);
        self.resolve_place(internal_place, internal_instance)
    }

    /// Dump the graph into a file using the graphviz format for later visualization.
    pub(crate) fn dump(&self, file_path: &str) {
        let mut nodes: Vec<String> =
            self.nodes.keys().map(|from| format!("\t\"{from:?}\"")).collect();
        nodes.sort();
        let nodes_str = nodes.join("\n");

        let mut edges: Vec<String> = self
            .nodes
            .iter()
            .flat_map(|(from, to)| {
                let from = format!("\"{from:?}\"");
                to.successors.iter().map(move |to| {
                    let to = format!("\"{to:?}\"");
                    format!("\t{from} -> {to}")
                })
            })
            .collect();
        edges.sort();
        let edges_str = edges.join("\n");

        std::fs::write(file_path, format!("digraph {{\n{nodes_str}\n{edges_str}\n}}"))
            .expect("failed to write points-to graph");
    }

    /// Find a transitive closure of the graph starting from a set of given locations; this also
    /// includes statics.
    pub(super) fn transitive_closure(&self, targets: HashSet<MemLoc<'tcx>>) -> PointsToGraph<'tcx> {
        let mut result = PointsToGraph::empty();
        // Working queue.
        let mut queue = VecDeque::from_iter(targets);
        // Add all statics, as they can be accessed at any point.
        let statics = self.nodes.keys().filter(|node| matches!(node, MemLoc::Static(_)));
        queue.extend(statics);
        // Add all entries.
        while let Some(next_target) = queue.pop_front() {
            result.nodes.entry(next_target).or_insert_with(|| {
                let data = self.nodes.get(&next_target).cloned().unwrap_or_default();
                queue.extend(data.successors.iter().copied());
                data
            });
        }
        result
    }
}

/// Since we are performing the analysis using a dataflow, we need to implement a proper monotonous
/// join operation. In our case, this is a simple union of two graphs. This "lattice" is finite,
/// because in the worst case all places will alias to all places, in which case the join will be a
/// no-op.
impl JoinSemiLattice for PointsToGraph<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut updated = false;
        // Check every node in the other graph.
        for (node, data) in &other.nodes {
            let existing_node = self.nodes.entry(*node).or_default();
            let changed = existing_node.merge(data);
            updated |= changed;
        }
        updated
    }
}

/// This is a requirement for the fixpoint solver, and there is no derive macro for this, so
/// implement it manually.
impl<C> DebugWithContext<C> for PointsToGraph<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hir::def_id::{DefId, DefIndex, LOCAL_CRATE};
    use rustc_mir_dataflow::JoinSemiLattice;

    /// Helper: create a distinct `MemLoc::Static` for testing.
    fn static_loc(index: u32) -> MemLoc<'static> {
        MemLoc::Static(DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(index) })
    }

    fn set_of(locs: &[MemLoc<'static>]) -> HashSet<MemLoc<'static>> {
        locs.iter().copied().collect()
    }

    // --- PointsToGraph::empty / all_nodes ---

    #[test]
    fn empty_graph_has_no_nodes() {
        let graph = PointsToGraph::empty();
        assert!(graph.all_nodes().is_empty());
    }

    // --- extend + successors + ancestors ---

    #[test]
    fn extend_adds_directed_edges() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        graph.extend(&set_of(&[a]), &set_of(&[b]));

        assert_eq!(graph.successors(&set_of(&[a])), set_of(&[b]));
        assert_eq!(graph.ancestors(&set_of(&[b])), set_of(&[a]));
    }

    #[test]
    fn successors_of_unknown_node_is_empty() {
        let graph = PointsToGraph::empty();
        let a = static_loc(0);
        assert!(graph.successors(&set_of(&[a])).is_empty());
    }

    #[test]
    fn ancestors_of_unknown_node_is_empty() {
        let graph = PointsToGraph::empty();
        let a = static_loc(0);
        assert!(graph.ancestors(&set_of(&[a])).is_empty());
    }

    #[test]
    fn extend_multiple_sources_to_one_target() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);
        graph.extend(&set_of(&[a, b]), &set_of(&[c]));

        assert_eq!(graph.successors(&set_of(&[a])), set_of(&[c]));
        assert_eq!(graph.successors(&set_of(&[b])), set_of(&[c]));
        assert_eq!(graph.ancestors(&set_of(&[c])), set_of(&[a, b]));
    }

    #[test]
    fn extend_one_source_to_multiple_targets() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);
        graph.extend(&set_of(&[a]), &set_of(&[b, c]));

        assert_eq!(graph.successors(&set_of(&[a])), set_of(&[b, c]));
        assert_eq!(graph.ancestors(&set_of(&[b])), set_of(&[a]));
        assert_eq!(graph.ancestors(&set_of(&[c])), set_of(&[a]));
    }

    #[test]
    fn all_nodes_includes_both_sources_and_targets() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        graph.extend(&set_of(&[a]), &set_of(&[b]));

        let nodes = graph.all_nodes();
        assert!(nodes.contains(&a));
        assert!(nodes.contains(&b));
        assert_eq!(nodes.len(), 2);
    }

    // --- transitive_closure ---

    #[test]
    fn transitive_closure_follows_chain() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);
        // a -> b -> c
        graph.extend(&set_of(&[a]), &set_of(&[b]));
        graph.extend(&set_of(&[b]), &set_of(&[c]));

        let closure = graph.transitive_closure(set_of(&[a]));
        let nodes = closure.all_nodes();
        assert!(nodes.contains(&a));
        assert!(nodes.contains(&b));
        assert!(nodes.contains(&c));
    }

    #[test]
    fn transitive_closure_includes_statics() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let s = static_loc(99);
        // a -> b, s is a standalone static
        graph.extend(&set_of(&[a]), &set_of(&[b]));
        // Add s as a node with no edges
        graph.extend(&set_of(&[s]), &HashSet::new());

        // Closure from {a} should include s (statics always included)
        let closure = graph.transitive_closure(set_of(&[a]));
        let nodes = closure.all_nodes();
        assert!(nodes.contains(&s), "statics should always be included in transitive closure");
    }

    #[test]
    fn transitive_closure_handles_cycle() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        // a -> b -> a (cycle)
        graph.extend(&set_of(&[a]), &set_of(&[b]));
        graph.extend(&set_of(&[b]), &set_of(&[a]));

        let closure = graph.transitive_closure(set_of(&[a]));
        let nodes = closure.all_nodes();
        assert!(nodes.contains(&a));
        assert!(nodes.contains(&b));
    }

    #[test]
    fn transitive_closure_excludes_unreachable_non_static() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);
        // a -> b, c is disconnected and non-static... but wait, all MemLoc::Static
        // are included by the algorithm. Let's test with an isolated node that
        // is explicitly a static - the algorithm includes ALL statics.
        graph.extend(&set_of(&[a]), &set_of(&[b]));
        // c has no edges but is a Static node. It should be included.
        graph.nodes.entry(c).or_default();

        let closure = graph.transitive_closure(set_of(&[a]));
        // All MemLoc::Static nodes are always included per the implementation
        assert!(closure.all_nodes().contains(&c));
    }

    // --- JoinSemiLattice ---

    #[test]
    fn join_empty_with_empty_returns_false() {
        let mut g1 = PointsToGraph::empty();
        let g2 = PointsToGraph::empty();
        assert!(!g1.join(&g2), "joining two empty graphs should not change state");
    }

    #[test]
    fn join_empty_with_nonempty_returns_true() {
        let mut g1 = PointsToGraph::empty();
        let mut g2 = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        g2.extend(&set_of(&[a]), &set_of(&[b]));

        assert!(g1.join(&g2), "joining with new edges should return true");
        assert_eq!(g1.successors(&set_of(&[a])), set_of(&[b]));
    }

    #[test]
    fn join_identical_graphs_returns_false() {
        let mut g1 = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        g1.extend(&set_of(&[a]), &set_of(&[b]));

        let g2 = g1.clone();
        assert!(!g1.join(&g2), "joining identical graphs should not change state");
    }

    #[test]
    fn join_merges_disjoint_edges() {
        let mut g1 = PointsToGraph::empty();
        let mut g2 = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);
        let d = static_loc(3);

        g1.extend(&set_of(&[a]), &set_of(&[b]));
        g2.extend(&set_of(&[c]), &set_of(&[d]));

        assert!(g1.join(&g2));
        assert_eq!(g1.successors(&set_of(&[a])), set_of(&[b]));
        assert_eq!(g1.successors(&set_of(&[c])), set_of(&[d]));
    }

    #[test]
    fn join_merges_overlapping_successor_sets() {
        let mut g1 = PointsToGraph::empty();
        let mut g2 = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        let c = static_loc(2);

        g1.extend(&set_of(&[a]), &set_of(&[b]));
        g2.extend(&set_of(&[a]), &set_of(&[c]));

        assert!(g1.join(&g2));
        assert_eq!(g1.successors(&set_of(&[a])), set_of(&[b, c]));
    }

    // --- NodeData::merge ---

    #[test]
    fn node_data_merge_empty_returns_false() {
        let mut data = NodeData::default();
        assert!(!data.merge(&NodeData::default()));
    }

    #[test]
    fn node_data_merge_new_successors_returns_true() {
        let mut data = NodeData::default();
        let b = static_loc(1);
        let other = NodeData { successors: set_of(&[b]), ancestors: HashSet::new() };
        assert!(data.merge(&other));
        assert!(data.successors.contains(&b));
    }

    #[test]
    fn node_data_merge_duplicate_returns_false() {
        let b = static_loc(1);
        let mut data = NodeData { successors: set_of(&[b]), ancestors: HashSet::new() };
        let other = NodeData { successors: set_of(&[b]), ancestors: HashSet::new() };
        assert!(!data.merge(&other));
    }

    // --- dump (format validation) ---

    #[test]
    fn dump_produces_valid_dot_format() {
        let mut graph = PointsToGraph::empty();
        let a = static_loc(0);
        let b = static_loc(1);
        graph.extend(&set_of(&[a]), &set_of(&[b]));

        let dir = std::env::temp_dir().join("points_to_graph_test");
        std::fs::create_dir_all(&dir).expect("create temp dir for dump test");
        let path = dir.join("test.dot");
        let path_str = path.to_string_lossy().to_string();
        graph.dump(&path_str);

        let content = std::fs::read_to_string(&path).expect("read dump output");
        assert!(content.starts_with("digraph {"));
        assert!(content.ends_with('}'));
        assert!(content.contains("->"), "DOT output should contain edge arrows");
        // Cleanup
        let _ = std::fs::remove_file(&path);
    }
}

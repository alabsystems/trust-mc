// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The analysis: a worklist BFS over the call graph, the same shape as
// `MonoItemsCollector::reachable_items`, but it records the witness PATH from a
// seed to the offending blocking leaf instead of collecting items for codegen.
//
// Seeding subtlety (the task's "EVERY Drop transitively triggered from those"):
// the SEED set is not just the named UI roots — it is their forward closure, and
// the forbidden leaves we care about are typically reached THROUGH `Drop` glue
// (`drop_in_place` chains) that the named root triggers. Because the BFS already
// follows `EdgeReason::Drop` edges, the Drop closure is handled for free: any
// destructor reachable from a seed is in the explored set, and a forbidden call
// inside it is reported with `via_drop = true`.

use crate::graph::{CallGraph, EdgeReason};
use crate::policy::Policy;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    /// A forbidden leaf reached through ordinary calls. Still a wedge, but at
    /// least the call site names the callee.
    Error,
    /// A forbidden leaf reached through `Drop` glue: invisible at the source
    /// site (the programmer wrote `}` or `drop(x)`). THIS is the aterm bug.
    ErrorViaDrop,
}

impl Severity {
    pub fn label(self) -> &'static str {
        match self {
            Severity::Error => "ERROR",
            Severity::ErrorViaDrop => "ERROR (blocking op reached through Drop glue)",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Finding {
    /// The UI/main-thread root the witness started from.
    pub seed: String,
    /// The full chain `seed --reason--> … --reason--> leaf`, as (node, reason)
    /// pairs *excluding* the seed (which is `self.seed`).
    pub witness: Vec<(String, EdgeReason)>,
    /// The forbidden blocking leaf.
    pub leaf: String,
    /// Why the leaf is forbidden.
    pub why: &'static str,
    pub severity: Severity,
}

impl Finding {
    /// Render the witness as `seed --call--> a --Drop--> b --call--> leaf`.
    pub fn render_path(&self) -> String {
        let mut s = self.seed.clone();
        for (node, reason) in &self.witness {
            s.push_str(reason.arrow());
            s.push_str(node);
        }
        s
    }
}

/// For each seed, BFS the call graph; the first (shortest) time we touch a
/// forbidden leaf on a branch, emit the witness. Per-seed `visited` so each seed
/// gets its own shortest witness. Deterministic via `BTree*` ordering in the
/// graph + sorted seed iteration, matching trust-mc's reproducible-output rule.
pub fn analyze(g: &CallGraph, policy: &Policy) -> Vec<Finding> {
    let mut seeds: Vec<&String> = g.nodes().filter(|n| policy.is_seed(n)).collect();
    seeds.sort();

    let mut findings = Vec::new();
    let mut reported: BTreeSet<(String, String)> = BTreeSet::new(); // (seed, leaf) dedup

    for seed in seeds {
        // Queue carries the path-so-far (excluding the seed node itself).
        let mut visited: BTreeSet<&str> = BTreeSet::new();
        let mut queue: std::collections::VecDeque<(&str, Vec<(String, EdgeReason)>)> =
            std::collections::VecDeque::new();
        visited.insert(seed.as_str());
        queue.push_back((seed.as_str(), Vec::new()));

        while let Some((node, path)) = queue.pop_front() {
            // A seed can itself be a leaf in pathological inputs; skip the seed
            // node, but classify every node we *arrive at*.
            if node != seed.as_str() {
                if let Some(why) = policy.classify_leaf(node) {
                    let via_drop = path.iter().any(|(_, r)| *r == EdgeReason::Drop);
                    let key = (seed.clone(), node.to_string());
                    if reported.insert(key) {
                        findings.push(Finding {
                            seed: seed.clone(),
                            witness: path.clone(),
                            leaf: node.to_string(),
                            why,
                            severity: if via_drop {
                                Severity::ErrorViaDrop
                            } else {
                                Severity::Error
                            },
                        });
                    }
                    // A forbidden leaf is terminal: do not descend through it.
                    continue;
                }
            }
            for (to, reason) in g.successors(node) {
                if visited.insert(to.as_str()) {
                    let mut next = path.clone();
                    next.push((to.clone(), *reason));
                    queue.push_back((to.as_str(), next));
                }
            }
        }
    }
    findings
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::Edge;

    #[test]
    fn flags_direct_blocking_call_without_drop() {
        let g = CallGraph::from_edges([
            Edge::call("app::main", "app::teardown"),
            Edge::call("app::teardown", "libc::waitpid"),
        ]);
        let f = analyze(&g, &Policy::aterm());
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].leaf, "libc::waitpid");
        assert_eq!(f[0].severity, Severity::Error);
    }

    #[test]
    fn unreachable_blocking_leaf_is_not_flagged() {
        // The blocking leaf exists but no seed reaches it.
        let g = CallGraph::from_edges([
            Edge::call("worker::{closure#0}", "libc::read"),
            Edge::call("app::main", "app::render"),
        ]);
        let f = analyze(&g, &Policy::aterm());
        assert!(f.is_empty(), "no seed reaches libc::read");
    }
}

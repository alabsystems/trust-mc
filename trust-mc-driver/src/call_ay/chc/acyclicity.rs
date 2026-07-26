// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Acyclicity detection for CHC predicate dependency graphs.
//!
//! Used by the BMC lane to determine if a CHC problem can be solved
//! soundly by bounded model checking without invariant synthesis.
//! Part of #4264.

use ay::chc::ChcProblem;

/// Check if the CHC problem's predicate dependency graph is acyclic.
///
/// Uses `ChcProblem::dependency_edges()` and DFS-based cycle detection.
/// O(V + E) where V = num_predicates, E = num_dependency_edges.
///
/// An acyclic dependency graph means every execution path through the CHC
/// system has bounded length, so BMC at depth = num_predicates is complete.
pub(super) fn is_acyclic_problem(problem: &ChcProblem) -> bool {
    let n = problem.predicates().len();
    if n == 0 {
        return true;
    }
    let edges = problem.dependency_edges();
    if n <= 1 {
        // Single-predicate: acyclic iff no self-referencing edge.
        return !edges.iter().any(|(from, to)| from == to);
    }
    // Build adjacency list from dependency edges.
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (from, to) in &edges {
        let from_idx = from.index();
        let to_idx = to.index();
        if from_idx < n && to_idx < n {
            adj[from_idx].push(to_idx);
        }
    }
    // DFS cycle detection using coloring: 0=unvisited, 1=in-stack, 2=done.
    let mut state = vec![0u8; n];
    for v in 0..n {
        if state[v] == 0 && has_cycle_dfs(v, &adj, &mut state) {
            return false;
        }
    }
    true
}

/// DFS helper: returns true if a cycle is found starting from vertex `v`.
fn has_cycle_dfs(v: usize, adj: &[Vec<usize>], state: &mut [u8]) -> bool {
    state[v] = 1; // Mark as in-stack
    for &w in &adj[v] {
        if state[w] == 1 {
            return true; // Back edge = cycle
        }
        if state[w] == 0 && has_cycle_dfs(w, adj, state) {
            return true;
        }
    }
    state[v] = 2; // Mark as done
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay::chc::{ChcParser, ChcProblem};

    /// Build a minimal CHC problem from SMT-LIB string for testing.
    fn parse_problem(smt: &str) -> ChcProblem {
        ChcParser::parse(smt).expect("test SMT should parse")
    }

    #[test]
    fn test_acyclic_linear_chain() {
        // A -> B -> error (acyclic chain)
        let smt = r#"
(declare-rel A (Int))
(declare-rel B (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (> x 0) (A x)))
(rule (=> (A x) (B x)))
(rule (=> (and (B x) (< x 0)) error))
(query error)
"#;
        let problem = parse_problem(smt);
        assert!(is_acyclic_problem(&problem), "linear chain should be acyclic");
    }

    #[test]
    fn test_cyclic_self_loop() {
        // A -> A (self-loop = cycle)
        let smt = r#"
(declare-rel A (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (> x 0) (A x)))
(rule (=> (A x) (A (- x 1))))
(rule (=> (and (A x) (< x 0)) error))
(query error)
"#;
        let problem = parse_problem(smt);
        assert!(!is_acyclic_problem(&problem), "self-loop should be cyclic");
    }

    #[test]
    fn test_acyclic_diamond_dag() {
        // A -> B, A -> C, B -> D, C -> D (diamond DAG, no cycle)
        let smt = r#"
(declare-rel A (Int))
(declare-rel B (Int))
(declare-rel C (Int))
(declare-rel D (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (> x 0) (A x)))
(rule (=> (A x) (B x)))
(rule (=> (A x) (C x)))
(rule (=> (B x) (D x)))
(rule (=> (C x) (D x)))
(rule (=> (and (D x) (< x 0)) error))
(query error)
"#;
        let problem = parse_problem(smt);
        assert!(is_acyclic_problem(&problem), "diamond DAG should be acyclic");
    }

    #[test]
    fn test_cyclic_two_pred_mutual() {
        // A -> B -> A (mutual recursion = cycle)
        let smt = r#"
(declare-rel A (Int))
(declare-rel B (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (> x 0) (A x)))
(rule (=> (A x) (B (- x 1))))
(rule (=> (B x) (A (- x 1))))
(rule (=> (and (A x) (< x 0)) error))
(query error)
"#;
        let problem = parse_problem(smt);
        assert!(!is_acyclic_problem(&problem), "mutual recursion should be cyclic");
    }

    #[test]
    fn test_empty_problem_is_acyclic() {
        // Empty problem with no predicates
        let smt = r#"
(declare-rel error ())
(query error)
"#;
        // This may or may not parse depending on ay's handling of empty problems.
        // If it parses, it should be acyclic.
        if let Ok(problem) = ChcParser::parse(smt) {
            assert!(is_acyclic_problem(&problem));
        }
    }
}

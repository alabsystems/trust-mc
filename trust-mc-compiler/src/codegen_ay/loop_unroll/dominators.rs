// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dominator computation (Lengauer-Tarjan) and loop header detection.

use super::LoopUnrollError;
use super::cfg::Cfg;
use std::collections::HashMap;

/// Lengauer-Tarjan algorithm for computing dominators in O(m*alpha(n)) time.
///
/// Returns immediate dominators as `idom[node]` where `idom[node]` is the immediate
/// dominator of `node`, or `usize::MAX` if the node is unreachable or is the entry.
///
/// Reference: Lengauer & Tarjan, "A Fast Algorithm for Finding Dominators in a Flowgraph",
/// ACM TOPLAS 1(1), 1979. https://doi.org/10.1145/357062.357071
#[allow(clippy::needless_range_loop)] // Index loops match original algorithm structure
pub(in crate::codegen_ay) fn compute_idom_lengauer_tarjan(cfg: &Cfg) -> Vec<usize> {
    let n = cfg.successors.len();
    if n == 0 {
        return vec![];
    }

    // DFS numbering
    let mut dfs_num = vec![usize::MAX; n]; // node -> DFS number
    let mut vertex = vec![usize::MAX; n]; // DFS number -> node
    let mut parent = vec![usize::MAX; n]; // DFS parent in DFS tree
    let mut dfs_count = 0;

    // DFS from entry (node 0)
    let mut discovered = vec![false; n];
    let mut stack = vec![0usize];
    discovered[0] = true;
    while let Some(v) = stack.pop() {
        if dfs_num[v] != usize::MAX {
            continue;
        }
        dfs_num[v] = dfs_count;
        vertex[dfs_count] = v;
        dfs_count += 1;

        for &w in &cfg.successors[v] {
            if w < n && !discovered[w] {
                discovered[w] = true;
                parent[w] = v;
                stack.push(w);
            }
        }
    }

    if dfs_count == 0 {
        return vec![usize::MAX; n];
    }

    // Semi-dominators and LINK-EVAL union-find structure
    let mut semi = (0..n).collect::<Vec<_>>(); // semi[v] initially = v
    let mut ancestor = vec![usize::MAX; n]; // ancestor in forest
    let mut label = (0..n).collect::<Vec<_>>(); // label[v] = node with min semi on path to root
    let mut bucket: Vec<Vec<usize>> = vec![Vec::new(); n]; // nodes with same semidominator
    let mut idom = vec![usize::MAX; n];

    // EVAL: find node with minimum semi on path from v to root of tree containing v
    fn eval(
        v: usize,
        ancestor: &mut [usize],
        label: &mut [usize],
        semi: &[usize],
        dfs_num: &[usize],
    ) -> usize {
        if ancestor[v] == usize::MAX {
            return v;
        }
        compress(v, ancestor, label, semi, dfs_num);
        label[v]
    }

    // COMPRESS: iterative path compression with semi-dominator minimization.
    // Converted from recursive to iterative to avoid stack overflow on deep
    // union-find forests (O(n) depth possible after loop unrolling).
    fn compress(
        v: usize,
        ancestor: &mut [usize],
        label: &mut [usize],
        semi: &[usize],
        dfs_num: &[usize],
    ) {
        // Phase 1: collect the path from v up to the root of the tree
        let mut path = Vec::new();
        let mut curr = v;
        while ancestor[curr] != usize::MAX && ancestor[ancestor[curr]] != usize::MAX {
            path.push(curr);
            curr = ancestor[curr];
        }
        // Phase 2: compress from top to bottom (same order as recursive unwinding)
        for &node in path.iter().rev() {
            let a = ancestor[node];
            if dfs_num[semi[label[a]]] < dfs_num[semi[label[node]]] {
                label[node] = label[a];
            }
            ancestor[node] = ancestor[a];
        }
    }

    // LINK: add edge from v to w in forest
    fn link(v: usize, w: usize, ancestor: &mut [usize]) {
        ancestor[w] = v;
    }

    // Process nodes in reverse DFS order (excluding entry)
    for i in (1..dfs_count).rev() {
        let w = vertex[i];
        if w == usize::MAX {
            continue;
        }

        // Step 2: Compute semi-dominators
        for &v in &cfg.predecessors[w] {
            if v >= n || dfs_num[v] == usize::MAX {
                continue;
            }
            let u = eval(v, &mut ancestor, &mut label, &semi, &dfs_num);
            if dfs_num[semi[u]] < dfs_num[semi[w]] {
                semi[w] = semi[u];
            }
        }
        bucket[semi[w]].push(w);

        // Link w to its DFS parent
        let p = parent[w];
        if p != usize::MAX {
            link(p, w, &mut ancestor);
        }

        // Step 3: Compute immediate dominators for nodes in bucket[parent[w]]
        if p != usize::MAX {
            for v in std::mem::take(&mut bucket[p]) {
                let u = eval(v, &mut ancestor, &mut label, &semi, &dfs_num);
                if semi[u] == semi[v] {
                    idom[v] = p;
                } else {
                    idom[v] = u; // Deferred: idom[v] = idom[u]
                }
            }
        }
    }

    // Step 4: Finalize deferred immediate dominators
    for i in 1..dfs_count {
        let w = vertex[i];
        if w == usize::MAX {
            continue;
        }
        if idom[w] != usize::MAX && idom[w] != semi[w] {
            idom[w] = idom[idom[w]];
        }
    }

    idom
}

/// Check if `ancestor` dominates `descendant` by walking up the idom tree.
///
/// O(depth) per query instead of O(n) for matrix lookup. Total work for loop
/// header detection is O(edges * depth) which is typically O(n log n) vs O(n^2)
/// for the matrix approach.
pub(in crate::codegen_ay) fn dominates(
    idom: &[usize],
    ancestor: usize,
    descendant: usize,
    n: usize,
) -> bool {
    let mut curr = descendant;
    let mut steps = 0;
    while curr != usize::MAX {
        if curr == ancestor {
            return true;
        }
        steps += 1;
        if steps > n {
            // Cycle in idom tree - should not happen with correct Lengauer-Tarjan
            return false;
        }
        curr = idom[curr];
    }
    false
}

/// Validate idom array for cycles and return error if found.
/// Separated from dominates() to keep the hot path fast.
#[allow(clippy::needless_range_loop)] // node index needed for error reporting
pub(in crate::codegen_ay) fn validate_idom(
    idom: &[usize],
    reachable: &[bool],
) -> Result<(), LoopUnrollError> {
    let n = idom.len();
    // 0 = unvisited, 1 = visiting (in current chain), 2 = done.
    let mut state = vec![0_u8; n];

    for start in 0..n {
        if !reachable[start] || state[start] == 2 {
            continue;
        }

        let mut path = Vec::new();
        let mut curr = start;
        while curr != usize::MAX {
            if !reachable[curr] {
                break;
            }
            match state[curr] {
                0 => {
                    state[curr] = 1;
                    path.push(curr);
                    curr = idom[curr];
                }
                1 => {
                    return Err(LoopUnrollError::IdomCycle {
                        node: start,
                        revisited: curr,
                        steps: path.len(),
                    });
                }
                2 => break,
                _ => unreachable!("state values are limited to 0,1,2"), // non-enum: u8 (state values)
            }
        }

        for node in path {
            state[node] = 2;
        }
    }
    Ok(())
}

/// Find loop headers using idom tree walking (O(n) space).
///
/// Returns a map from header block to its latch blocks (back-edge sources).
/// A back-edge src->dst exists when dst dominates src.
///
/// Replaces the O(n^2) `compute_dominators` + matrix scan approach.
pub(in crate::codegen_ay) fn find_loop_headers(
    cfg: &Cfg,
) -> Result<HashMap<usize, Vec<usize>>, LoopUnrollError> {
    let idom = compute_idom_lengauer_tarjan(cfg);
    let n = cfg.successors.len();

    // Validate idom for cycles before using it
    validate_idom(&idom, &cfg.reachable)?;

    let mut headers: HashMap<usize, Vec<usize>> = HashMap::new();
    for src in 0..n {
        if !cfg.reachable[src] {
            continue;
        }
        for &dst in &cfg.successors[src] {
            if !cfg.reachable[dst] {
                continue;
            }
            if dominates(&idom, dst, src, n) {
                headers.entry(dst).or_default().push(src);
            }
        }
    }
    Ok(headers)
}

/// Compute full dominator matrix from immediate dominators.
///
/// Returns `dom` where `dom[a][b]` = true iff `b` dominates `a`.
///
/// NOTE: This function is O(n^2) in space and is retained only for tests.
/// Production code uses `find_loop_headers()` which walks the idom tree directly.
///
/// # Errors
///
/// Returns `LoopUnrollError::IdomCycle` if a cycle is detected in the immediate
/// dominator array, indicating a bug in the Lengauer-Tarjan computation.
#[cfg(test)]
#[allow(clippy::needless_range_loop)]
pub(super) fn compute_dominators(cfg: &Cfg) -> Result<Vec<Vec<bool>>, LoopUnrollError> {
    let n = cfg.successors.len();
    let idom = compute_idom_lengauer_tarjan(cfg);

    let mut dom = vec![vec![false; n]; n];

    for node in 0..n {
        if !cfg.reachable[node] {
            continue;
        }
        let mut visited = vec![false; n];
        let mut curr = node;
        while curr != usize::MAX {
            if visited[curr] {
                return Err(LoopUnrollError::IdomCycle {
                    node,
                    revisited: curr,
                    steps: visited.iter().filter(|&&v| v).count(),
                });
            }
            visited[curr] = true;
            dom[node][curr] = true;
            curr = idom[curr];
        }
    }

    Ok(dom)
}

/// Test-only: compute dominator matrix from a pre-computed idom array.
/// This allows testing the cycle detection without going through Lengauer-Tarjan.
#[cfg(test)]
pub(super) fn compute_dom_matrix_from_idom(
    idom: &[usize],
    reachable: &[bool],
) -> Result<Vec<Vec<bool>>, LoopUnrollError> {
    let n = idom.len();
    let mut dom = vec![vec![false; n]; n];

    for node in 0..n {
        if !reachable[node] {
            continue;
        }
        let mut visited = vec![false; n];
        let mut curr = node;
        while curr != usize::MAX {
            if visited[curr] {
                return Err(LoopUnrollError::IdomCycle {
                    node,
                    revisited: curr,
                    steps: visited.iter().filter(|&&v| v).count(),
                });
            }
            visited[curr] = true;
            dom[node][curr] = true;
            curr = idom[curr];
        }
    }

    Ok(dom)
}

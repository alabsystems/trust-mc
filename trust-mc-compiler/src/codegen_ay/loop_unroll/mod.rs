// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bounded CFG loop unrolling for the AY backend.
//!
//! The AY backend currently requires an acyclic CFG so it can process basic blocks in a
//! topological order. Rust MIR uses CFG cycles to represent loops, so we perform a bounded
//! unrolling transformation that converts natural loops into an acyclic graph by:
//! - duplicating the loop body `k` times
//! - redirecting back-edges to the next copy
//! - cutting off the final copy (either with an "unwinding assertion" or by truncating)
//!
//! This is a Phase 2 bounded model checking (BMC) strategy. Phase 3 will use CHCs for unbounded
//! loop reasoning.

mod cfg;
mod const_trip;
mod dominators;
mod unroll;

#[cfg(test)]
mod tests;

// Re-export CFG infrastructure for large-step CHC encoding (#112).
pub(in crate::codegen_ay) use cfg::Cfg;
pub(in crate::codegen_ay) use cfg::topo_sort;
pub(in crate::codegen_ay) use const_trip::derive_const_trip_unroll_depth;
pub(in crate::codegen_ay) use dominators::find_loop_headers;
use rustc_public::mir::Body;
use tracing::{debug, warn};
use unroll::{
    MAX_EXPANDED_BLOCKS, check_single_entry, compute_effective_unwind_depth, natural_loop,
    unroll_natural_loop,
};

/// Errors that can occur during loop unrolling.
#[derive(Debug)]
pub(in crate::codegen_ay) enum LoopUnrollError {
    /// The CFG contains a cycle but no natural-loop backedge (irreducible CFG).
    IrreducibleCycle,
    /// The loop has multiple entry points (non-header entries).
    MultipleEntries { header: usize, entry: usize, pred: usize },
    /// Too many unroll iterations (defensive).
    TooManyIterations { iterations: usize },
    /// The immediate dominator array contains a cycle (malformed dominator tree).
    IdomCycle { node: usize, revisited: usize, steps: usize },
    /// Total block count exceeded global cap after unrolling.
    MaxBlocksExceeded { block_count: usize, limit: usize },
}

impl std::fmt::Display for LoopUnrollError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IrreducibleCycle => {
                write!(f, "irreducible control flow (non-natural loop)")
            }
            Self::MultipleEntries { header, entry, pred } => {
                write!(f, "multiple loop entries: header={header}, entry={entry}, pred={pred}")
            }
            Self::TooManyIterations { iterations } => {
                write!(f, "exceeded max unroll iterations ({iterations})")
            }
            Self::IdomCycle { node, revisited, steps } => {
                write!(
                    f,
                    "dominator tree cycle: node {node} revisited {revisited} after {steps} steps"
                )
            }
            Self::MaxBlocksExceeded { block_count, limit } => {
                write!(f, "total block count {block_count} exceeds limit {limit}")
            }
        }
    }
}

// LoopUnrollError is a leaf error with no underlying cause.
// source() returns None (default), enabling use with anyhow/eyre.
impl std::error::Error for LoopUnrollError {}

/// Perform bounded loop unrolling so the CFG becomes acyclic.
///
/// `unwind_depth` is the maximum number of loop iterations to model for each loop.
/// If `unwinding_assertions` is true, any attempt to continue a loop beyond `unwind_depth`
/// is redirected to an `Unreachable` terminator, making the run conservative.
///
/// REQUIRES: `body` is a valid MIR body.
/// REQUIRES: `unwind_depth >= 1` (at least one iteration).
/// ENSURES: On success, returned body has no back-edges (CFG is acyclic).
/// ENSURES: On error, returns LoopUnrollError describing the failure.
pub(in crate::codegen_ay) fn unroll_cfg_loops(
    mut body: Body,
    unwind_depth: u32,
    unwinding_assertions: bool,
) -> Result<Body, LoopUnrollError> {
    let unwind_depth = unwind_depth as usize;

    // Defensive: avoid non-termination in pathological graphs.
    const MAX_ITERATIONS: usize = 256;
    // Global block count cap: abort if total blocks exceed this after unrolling.
    // Prevents memory blowup from nested loops with high unwind depth.
    const MAX_TOTAL_BLOCKS: usize = 100_000;

    for iteration in 0..MAX_ITERATIONS {
        if body.blocks.len() > MAX_TOTAL_BLOCKS {
            tracing::warn!(
                "unroll_cfg_loops: body has {} blocks (> {}), stopping unrolling",
                body.blocks.len(),
                MAX_TOTAL_BLOCKS,
            );
            return Err(LoopUnrollError::MaxBlocksExceeded {
                block_count: body.blocks.len(),
                limit: MAX_TOTAL_BLOCKS,
            });
        }

        let cfg = Cfg::from_body(&body);
        if cfg.is_acyclic() {
            return Ok(body);
        }

        let headers = find_loop_headers(&cfg)?;

        if headers.is_empty() {
            return Err(LoopUnrollError::IrreducibleCycle);
        }

        let mut candidates: Vec<(usize, Vec<usize>)> = headers.into_iter().collect();
        candidates.sort_by_key(|(h, _)| *h);

        // Pick the smallest natural loop to unroll (heuristic: likely innermost).
        let mut best: Option<unroll::NaturalLoop> = None;
        let mut first_entry_err: Option<LoopUnrollError> = None;
        for (header, mut latches) in candidates {
            latches.sort_unstable();
            latches.dedup();
            let lp = natural_loop(&cfg, header, &latches);
            if let Err(e) = check_single_entry(&cfg, &lp) {
                if first_entry_err.is_none() {
                    first_entry_err = Some(e);
                }
                continue;
            }
            if best.as_ref().is_none_or(|b| lp.blocks.len() < b.blocks.len()) {
                best = Some(lp);
            }
        }

        let Some(lp) = best else {
            return Err(first_entry_err.unwrap_or(LoopUnrollError::IrreducibleCycle));
        };

        check_single_entry(&cfg, &lp)?;

        // Apply memory bounds heuristic to prevent quadratic/exponential memory growth.
        let loop_blocks = lp.blocks.len();
        let (effective_depth, was_reduced) =
            compute_effective_unwind_depth(unwind_depth, loop_blocks);
        let projected_expansion = unwind_depth.saturating_mul(loop_blocks);
        if was_reduced {
            warn!(
                "Loop unrolling: reducing depth from {} to {} for {}-block loop \
                 ({}×{}={} would exceed {} block threshold)",
                unwind_depth,
                effective_depth,
                loop_blocks,
                unwind_depth,
                loop_blocks,
                projected_expansion,
                MAX_EXPANDED_BLOCKS
            );
        }

        debug!(
            header = lp.header,
            latches = ?lp.latches,
            blocks = lp.blocks.len(),
            depth = effective_depth,
            "unrolling natural loop"
        );
        unroll_natural_loop(&mut body, &cfg, &lp, effective_depth, unwinding_assertions);
        if iteration + 1 == MAX_ITERATIONS {
            return Err(LoopUnrollError::TooManyIterations { iterations: MAX_ITERATIONS });
        }
    }

    Err(LoopUnrollError::TooManyIterations { iterations: MAX_ITERATIONS })
}

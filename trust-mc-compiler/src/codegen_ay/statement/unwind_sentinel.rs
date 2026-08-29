// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Recognition of the BMC loop-unroller's *unwinding assertion* sentinel block.
//!
//! `loop_unroll::unroll_natural_loop` makes a cyclic CFG acyclic by duplicating
//! the loop body `k` times and redirecting the exhausted back-edge of the last
//! copy into a freshly appended dead-end pair:
//!
//! ```text
//!   fail_bb        { }  ->  Unreachable   // the loop wanted a (k+1)th trip
//!   silent_fail_bb { }  ->  Return        // the --no-default-checks twin
//! ```
//!
//! Both are stamped with the SAME span (one `let span = body.blocks[lp.header]
//! .terminator.span` feeds both), and while unwinding assertions are on nothing
//! is ever wired to `silent_fail_bb`.
//!
//! Codegen only ever sees the already-unrolled body, so without this recognizer
//! `fail_bb` is just another `TerminatorKind::Unreachable`: its violation gets
//! the `unreachable` label, which the driver's taxonomy renders as "panic
//! reached" and the classifier calls `[AY:CTREX_CAT:Genuine]`. That tells the
//! user their program has a bug when what actually happened is that their
//! `--unwind` bound was too small — the most misleading verdict a bounded model
//! checker can print.
//!
//! FAIL-CLOSED DIRECTION. A false NEGATIVE costs nothing new: the block keeps
//! today's `unreachable` label and today's (wrong but pre-existing) rendering. A
//! false POSITIVE would relabel a genuine reachable `unreachable` as a bound
//! problem and hide a real panic, so every clause below is one the unroller's
//! own construction guarantees, and the conjunction may only ever be narrowed:
//!
//!   1. block `i` is statement-free with an `Unreachable` terminator;
//!   2. block `i + 1` is statement-free with a `Return` terminator;
//!   3. their terminator `Span`s are identical;
//!   4. block `i` is reachable from entry — the cut back-edge targets it. (With
//!      `--no-unwinding-checks` / `--no-default-checks` the two roles swap and
//!      `fail_bb` is the unwired one, so this clause rejects the pair. Correct:
//!      those modes deliberately emit no unwinding assertion at all.)
//!   5. block `i + 1` has NO predecessors whatsoever;
//!   6. at least one PREDECESSOR of block `i` carries that same terminator span.
//!      `remap_target`'s first rule sends every in-loop successor of the LAST
//!      header copy to `fail_bb`, and that copy kept the header terminator's
//!      span — the very span the sentinels were stamped with. So a true sentinel
//!      always has a same-span predecessor, and an accidental `unreachable` +
//!      dead `return` pair essentially never does.

use rustc_public::mir::{Body, TerminatorKind};
use std::collections::HashSet;

use crate::codegen_ay::loop_unroll::Cfg;

/// Indices of the loop-unroller's unwinding-assertion sentinel blocks in `body`.
///
/// Empty for every body that was not unrolled — the overwhelmingly common case,
/// which is why the allocation-free pre-scan runs before any CFG is built.
pub(super) fn unwind_assert_sentinel_blocks(body: &Body) -> HashSet<usize> {
    // Clauses 1-3, on adjacent pairs.
    let mut candidates: Vec<usize> = Vec::new();
    for (idx, pair) in body.blocks.windows(2).enumerate() {
        let (fail, silent) = (&pair[0], &pair[1]);
        if fail.statements.is_empty()
            && matches!(fail.terminator.kind, TerminatorKind::Unreachable)
            && silent.statements.is_empty()
            && matches!(silent.terminator.kind, TerminatorKind::Return)
            && fail.terminator.span == silent.terminator.span
        {
            candidates.push(idx);
        }
    }
    if candidates.is_empty() {
        return HashSet::new();
    }

    // Clauses 4-6 need edges.
    let cfg = Cfg::from_body(body);
    let sentinels: HashSet<usize> = candidates
        .into_iter()
        .filter(|&idx| {
            let span = body.blocks[idx].terminator.span;
            cfg.reachable[idx]
                && cfg.predecessors[idx + 1].is_empty()
                && cfg.predecessors[idx]
                    .iter()
                    .any(|&pred| body.blocks[pred].terminator.span == span)
        })
        .collect();

    if !sentinels.is_empty() {
        tracing::debug!(
            ?sentinels,
            blocks = body.blocks.len(),
            "BMC: recognized loop-unwinding assertion sentinel block(s)"
        );
    }
    sentinels
}

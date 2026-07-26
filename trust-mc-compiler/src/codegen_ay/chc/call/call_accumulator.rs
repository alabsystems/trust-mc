// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Mutable accumulators threaded through CHC call handler helpers.
//!
//! Groups the per-call mutation state: extra constraints and modified
//! destination indices emitted by collection/Vec/HashMap stub handlers.
//! Part of #3517: reduces parameter count across 27 call handler functions.

use ay_bindings::Expr;

/// Mutable accumulators passed through CHC call handler helpers.
///
/// Bundles the `(extra_constraints, extra_dests)` pair that call handlers
/// use to emit additional equality constraints and track which state
/// variable indices were modified during call encoding.
pub(in crate::codegen_ay::chc) struct CallAccumulator<'a> {
    pub constraints: &'a mut Vec<Expr>,
    pub dests: &'a mut Vec<usize>,
}

impl<'a> CallAccumulator<'a> {
    #[must_use]
    pub(in crate::codegen_ay::chc) fn new(
        constraints: &'a mut Vec<Expr>,
        dests: &'a mut Vec<usize>,
    ) -> Self {
        Self { constraints, dests }
    }
}

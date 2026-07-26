// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared mutable accumulators threaded through statement codegen helpers.
//!
//! Groups the per-block mutation state carried across statement/store handlers:
//! - `modified`: locals modified in the current block
//! - `constraints`: emitted CHC constraints
//! - `last_constraint_for_local`: overwrite index for latest local assignment

use ay_bindings::Expr;
use std::collections::{HashMap, HashSet};

/// Mutable accumulators passed through statement/store codegen helpers.
pub(in crate::codegen_ay::chc) struct StmtAccumulator<'a> {
    pub modified: &'a mut HashSet<usize>,
    pub constraints: &'a mut Vec<Expr>,
    pub last_constraint_for_local: &'a mut HashMap<usize, usize>,
}

impl<'a> StmtAccumulator<'a> {
    #[must_use]
    pub(in crate::codegen_ay::chc) fn new(
        modified: &'a mut HashSet<usize>,
        constraints: &'a mut Vec<Expr>,
        last_constraint_for_local: &'a mut HashMap<usize, usize>,
    ) -> Self {
        Self { modified, constraints, last_constraint_for_local }
    }

    /// Replace the previous constraint for `key` with `true` and push `constraint`
    /// as the new latest constraint for this key.
    ///
    /// Implements SSA-style "last write wins" semantics: within a basic block,
    /// only the final assignment to each local/field matters. Earlier assignments
    /// are replaced with `true` to avoid contradictory constraints.
    pub(in crate::codegen_ay::chc) fn replace_constraint(&mut self, key: usize, constraint: Expr) {
        replace_constraint_in(self.constraints, self.last_constraint_for_local, key, constraint);
    }
}

/// Standalone version of the constraint-replacement idiom for callers
/// that don't use `StmtAccumulator`.
///
/// Replaces the previous constraint for `key` with `true` and pushes
/// `constraint` as the new latest constraint. See [`StmtAccumulator::replace_constraint`].
pub(in crate::codegen_ay::chc) fn replace_constraint_in(
    constraints: &mut Vec<Expr>,
    last_constraint_for_local: &mut HashMap<usize, usize>,
    key: usize,
    constraint: Expr,
) {
    if let Some(&prev) = last_constraint_for_local.get(&key) {
        constraints[prev] = Expr::bool_const(true);
    }
    let c_idx = constraints.len();
    constraints.push(constraint);
    last_constraint_for_local.insert(key, c_idx);
}

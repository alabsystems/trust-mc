// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `enforce_modified_constraint_invariant` from codegen_stmt_mirror.
//!
//! Part of #3526: acceptance criterion 4 — verify the invariant is caught in
//! release mode by exercising the runtime enforcement path directly.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::{HashMap, HashSet};

use super::super::codegen_stmt_vtable_tracking::enforce_modified_constraint_invariant;
use super::super::stmt_accumulator::StmtAccumulator;

/// All modified locals have constraints → no repair needed.
#[test]
fn test_all_constrained_no_repair() {
    let mut modified: HashSet<usize> = [1, 2, 3].into();
    let mut constraints = Vec::new();
    let mut last_cfl: HashMap<usize, usize> = [(1, 0), (2, 1), (3, 2)].into();
    let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);
    let fixups = enforce_modified_constraint_invariant(0, &mut acc);
    assert_eq!(fixups, 0);
    assert_eq!(*acc.modified, HashSet::from([1, 2, 3]));
}

/// Some modified locals lack constraints → tautological `true` emitted (#3138).
#[test]
fn test_unconstrained_locals_repaired() {
    let mut modified: HashSet<usize> = [1, 2, 3, 4].into();
    let mut constraints = Vec::new();
    // Only locals 1 and 3 have constraints; 2 and 4 do not.
    let mut last_cfl: HashMap<usize, usize> = [(1, 0), (3, 1)].into();
    let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);
    let fixups = enforce_modified_constraint_invariant(5, &mut acc);
    // Part of #3138: locals 2 and 4 STAY in modified (universally quantified),
    // with tautological `true` constraints emitted to prevent identity-copy.
    assert_eq!(fixups, 2);
    assert_eq!(*acc.modified, HashSet::from([1, 2, 3, 4]));
    // Two `true` constraints emitted for locals 2 and 4.
    assert_eq!(acc.constraints.len(), 2);
    // Both unconstrained locals now have entries in last_constraint_for_local.
    assert!(acc.last_constraint_for_local.contains_key(&2));
    assert!(acc.last_constraint_for_local.contains_key(&4));
}

/// All modified locals lack constraints → tautological `true` emitted (#3138).
#[test]
fn test_all_unconstrained_repaired() {
    let mut modified: HashSet<usize> = [10, 20].into();
    let mut constraints = Vec::new();
    let mut last_cfl: HashMap<usize, usize> = HashMap::new();
    let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);
    let fixups = enforce_modified_constraint_invariant(0, &mut acc);
    assert_eq!(fixups, 2);
    // Part of #3138: locals stay in modified (universally quantified, sound).
    assert_eq!(*acc.modified, HashSet::from([10, 20]));
    assert_eq!(acc.constraints.len(), 2);
    assert!(acc.last_constraint_for_local.contains_key(&10));
    assert!(acc.last_constraint_for_local.contains_key(&20));
}

/// Empty modified set → no-op.
#[test]
fn test_empty_modified_no_op() {
    let mut modified: HashSet<usize> = HashSet::new();
    let mut constraints = Vec::new();
    let mut last_cfl: HashMap<usize, usize> = [(1, 0)].into();
    let mut acc = StmtAccumulator::new(&mut modified, &mut constraints, &mut last_cfl);
    let fixups = enforce_modified_constraint_invariant(0, &mut acc);
    assert_eq!(fixups, 0);
    assert!(acc.modified.is_empty());
}

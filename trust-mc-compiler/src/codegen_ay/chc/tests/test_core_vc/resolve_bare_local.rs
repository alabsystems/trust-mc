// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use std::sync::Arc;

// =============================================================================
// resolve_bare_local tests (Part of #2016)
// =============================================================================
// Tests for the static helper that resolves plain locals to state variable exprs.

/// Test resolve_bare_local returns input state var for unmodified local.
#[test]
#[allow(clippy::useless_conversion)]
fn test_resolve_bare_local_unmodified() {
    let state_vars =
        vec![(Arc::from("_fn_0"), Sort::bitvec(32)), (Arc::from("_fn_1"), Sort::bool())];
    let output_state_vars =
        vec![(Arc::from("_fn_0__out"), Sort::bitvec(32)), (Arc::from("_fn_1__out"), Sort::bool())];
    let modified: HashSet<usize> = HashSet::new();

    // Local 0 is unmodified — should resolve to input state var _fn_0
    let arg = Operand::Copy(Place { local: 0usize.into(), projection: vec![] });
    let idx_map: HashMap<usize, usize> = [(0, 0), (1, 1)].into_iter().collect();
    let result = ChcCtx::resolve_bare_local(
        &arg,
        &state_vars,
        &output_state_vars,
        &modified,
        &idx_map,
        "test_core_vc",
    );
    assert!(result.is_some());
    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(32));
    assert!(expr.to_string().contains("_fn_0"));
}

/// Test resolve_bare_local returns output state var for modified local.
#[test]
#[allow(clippy::useless_conversion)]
fn test_resolve_bare_local_modified() {
    let state_vars =
        vec![(Arc::from("_fn_0"), Sort::bitvec(32)), (Arc::from("_fn_1"), Sort::bool())];
    let output_state_vars =
        vec![(Arc::from("_fn_0__out"), Sort::bitvec(32)), (Arc::from("_fn_1__out"), Sort::bool())];
    let modified: HashSet<usize> = [1].into_iter().collect();

    // Local 1 is modified — should resolve to output state var _fn_1__out
    let arg = Operand::Copy(Place { local: 1usize.into(), projection: vec![] });
    let idx_map: HashMap<usize, usize> = [(0, 0), (1, 1)].into_iter().collect();
    let result = ChcCtx::resolve_bare_local(
        &arg,
        &state_vars,
        &output_state_vars,
        &modified,
        &idx_map,
        "test_core_vc",
    );
    assert!(result.is_some());
    let expr = result.unwrap();
    assert!(expr.sort().is_bool());
    assert!(expr.to_string().contains("_fn_1__out"));
}

/// Test resolve_bare_local returns None for projected place (not bare).
#[test]
#[allow(clippy::useless_conversion)]
fn test_resolve_bare_local_projected_returns_none() {
    let state_vars = vec![(Arc::from("_fn_0"), Sort::bitvec(32))];
    let output_state_vars = vec![(Arc::from("_fn_0__out"), Sort::bitvec(32))];
    let modified: HashSet<usize> = HashSet::new();

    // Place with Deref projection — not a bare local, should return None
    let arg =
        Operand::Copy(Place { local: 0usize.into(), projection: vec![ProjectionElem::Deref] });
    let idx_map: HashMap<usize, usize> = HashMap::new();
    let result = ChcCtx::resolve_bare_local(
        &arg,
        &state_vars,
        &output_state_vars,
        &modified,
        &idx_map,
        "test_core_vc",
    );
    assert!(result.is_none());
}

/// Test resolve_bare_local returns None for out-of-bounds local index.
#[test]
#[allow(clippy::useless_conversion)]
fn test_resolve_bare_local_out_of_bounds() {
    let state_vars = vec![(Arc::from("_fn_0"), Sort::bitvec(32))];
    let output_state_vars = vec![(Arc::from("_fn_0__out"), Sort::bitvec(32))];
    let modified: HashSet<usize> = HashSet::new();

    // Local 5 maps to vec index 5, which exceeds state_vars length — should return None
    let arg = Operand::Copy(Place { local: 5usize.into(), projection: vec![] });
    let idx_map: HashMap<usize, usize> = [(5, 5)].into_iter().collect();
    let result = ChcCtx::resolve_bare_local(
        &arg,
        &state_vars,
        &output_state_vars,
        &modified,
        &idx_map,
        "test_core_vc",
    );
    assert!(result.is_none());
}

/// Test resolve_bare_local returns None for in-bounds but unmapped local (#2709).
/// Previously this used an unsound identity fallback (local_idx as vec_idx).
#[test]
#[allow(clippy::useless_conversion)]
fn test_resolve_bare_local_unmapped_returns_none() {
    let state_vars =
        vec![(Arc::from("_fn_0"), Sort::bitvec(32)), (Arc::from("_fn_1"), Sort::bool())];
    let output_state_vars =
        vec![(Arc::from("_fn_0__out"), Sort::bitvec(32)), (Arc::from("_fn_1__out"), Sort::bool())];
    let modified: HashSet<usize> = HashSet::new();

    // Local 0 is within bounds but NOT in idx_map — must return None (fail-closed)
    let arg = Operand::Copy(Place { local: 0usize.into(), projection: vec![] });
    let idx_map: HashMap<usize, usize> = HashMap::new();
    let result = ChcCtx::resolve_bare_local(
        &arg,
        &state_vars,
        &output_state_vars,
        &modified,
        &idx_map,
        "test_core_vc",
    );
    assert!(result.is_none(), "unmapped in-bounds local must return None per #2698/#2709");
}

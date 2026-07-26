// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// collect_nested_datatypes tests
// ═══════════════════════════════════════════════════════════════════════

/// Test that primitive sorts produce no nested datatypes.
#[test]
fn test_collect_nested_datatypes_primitive() {
    let mut seen = HashSet::new();
    let mut collected = Vec::new();

    ChcCtx::collect_nested_datatypes(&Sort::bitvec(32), &mut seen, &mut collected);
    assert!(collected.is_empty(), "bitvec should have no nested datatypes");

    ChcCtx::collect_nested_datatypes(&Sort::bool(), &mut seen, &mut collected);
    assert!(collected.is_empty(), "bool should have no nested datatypes");

    ChcCtx::collect_nested_datatypes(&Sort::int(), &mut seen, &mut collected);
    assert!(collected.is_empty(), "int should have no nested datatypes");

    ChcCtx::collect_nested_datatypes(&Sort::real(), &mut seen, &mut collected);
    assert!(collected.is_empty(), "real should have no nested datatypes");
}

/// Test that a struct sort collects one datatype.
#[test]
fn test_collect_nested_datatypes_struct() {
    let point = struct_sort("Point", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);

    let mut seen = HashSet::new();
    let mut collected = Vec::new();
    ChcCtx::collect_nested_datatypes(&point, &mut seen, &mut collected);

    assert_eq!(collected.len(), 1, "struct Point should produce 1 datatype");
    assert_eq!(collected[0].name, "Point");
}

/// Test that nested structs collect datatypes in dependency order.
#[test]
fn test_collect_nested_datatypes_nested_struct() {
    let inner = struct_sort("Inner", [("val", Sort::bitvec(32))]);
    let outer = struct_sort("Outer", [("inner", inner)]);

    let mut seen = HashSet::new();
    let mut collected = Vec::new();
    ChcCtx::collect_nested_datatypes(&outer, &mut seen, &mut collected);

    assert_eq!(collected.len(), 2, "nested struct should produce 2 datatypes");
    // Inner should come before Outer (dependency order)
    assert_eq!(collected[0].name, "Inner", "dependency should be collected first");
    assert_eq!(collected[1].name, "Outer", "dependent should be collected second");
}

/// Test that array sorts with datatype elements are traversed.
#[test]
fn test_collect_nested_datatypes_array_with_struct_elem() {
    let point = struct_sort("ArrayPoint", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);
    let array_sort = Sort::array(Sort::int(), point);

    let mut seen = HashSet::new();
    let mut collected = Vec::new();
    ChcCtx::collect_nested_datatypes(&array_sort, &mut seen, &mut collected);

    assert_eq!(collected.len(), 1, "array of struct should find the struct datatype");
    assert_eq!(collected[0].name, "ArrayPoint");
}

/// Test that duplicate datatypes are not collected twice.
#[test]
fn test_collect_nested_datatypes_dedup() {
    let shared_inner = struct_sort("Shared", [("v", Sort::bitvec(32))]);
    // Two different sorts referencing the same inner type
    let outer1 = struct_sort("Outer1", [("a", shared_inner.clone())]);
    let outer2 = struct_sort("Outer2", [("b", shared_inner)]);

    let mut seen = HashSet::new();
    let mut collected = Vec::new();
    ChcCtx::collect_nested_datatypes(&outer1, &mut seen, &mut collected);
    ChcCtx::collect_nested_datatypes(&outer2, &mut seen, &mut collected);

    // "Shared" should only appear once
    let shared_count = collected.iter().filter(|dt| dt.name == "Shared").count();
    assert_eq!(shared_count, 1, "shared datatype should be collected exactly once");
    // Total: Shared + Outer1 + Outer2
    assert_eq!(collected.len(), 3);
}

/// Test that enum-like sorts collect datatypes.
#[test]
fn test_collect_nested_datatypes_enum() {
    let option_sort =
        enum_sort("MyOption", [("None", vec![]), ("Some", vec![("value", Sort::bitvec(32))])]);

    let mut seen = HashSet::new();
    let mut collected = Vec::new();
    ChcCtx::collect_nested_datatypes(&option_sort, &mut seen, &mut collected);

    assert_eq!(collected.len(), 1, "enum should produce 1 datatype");
    assert_eq!(collected[0].name, "MyOption");
}

// ═══════════════════════════════════════════════════════════════════════
// VC structure verification tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify that after declare_block_relations, the VC has the expected structure.
#[test]
fn test_vc_structure_after_declaration() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // VC should have relations matching block count
        let block_count = body.blocks.len();
        // Relations include block relations (one per BB)
        assert!(
            chc_ctx.vc.relations.len() >= block_count,
            "VC should have at least {} relations (one per block), got {}",
            block_count,
            chc_ctx.vc.relations.len()
        );

        // VC should have input + output variable declarations
        assert!(
            !chc_ctx.vc.vars().is_empty(),
            "VC should have variable declarations for state vars"
        );
    });
}

/// Verify that all block relations have consistent arity (same number of state vars).
#[test]
fn test_block_relations_consistent_arity() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let state_var_count = chc_ctx.state_var_mgr.state_vars.len();
        assert!(state_var_count > 0);

        // All block relations should have the same arity
        for rel in &chc_ctx.vc.relations {
            if rel.name.contains("multi_local") {
                assert_eq!(
                    rel.arity(),
                    state_var_count,
                    "relation {} has arity {} but expected {} (state var count)",
                    rel.name,
                    rel.arity(),
                    state_var_count
                );
            }
        }
    });
}

/// Verify that local_to_state_idx mapping is populated correctly.
#[test]
fn test_local_to_state_idx_mapping() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // local_to_state_idx should have entries for MIR locals
        assert!(
            !chc_ctx.state_var_mgr.local_to_state_idx.is_empty(),
            "local_to_state_idx should be populated"
        );

        // Each local index should map to a unique state index
        let mut seen_state_indices: HashSet<usize> = HashSet::new();
        for state_idx in chc_ctx.state_var_mgr.local_to_state_idx.values() {
            assert!(
                seen_state_indices.insert(*state_idx),
                "state index {} appears for multiple locals",
                state_idx
            );
        }
    });
}

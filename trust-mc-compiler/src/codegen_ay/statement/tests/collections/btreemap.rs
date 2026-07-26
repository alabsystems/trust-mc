// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BTreeMap internal stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

// =============================================================================
// BTreeMap internal stub tests (Part of #2016)
// =============================================================================
// These tests exercise codegen_btreemap_internal_stub — the Entry API operations
// used internally by BTreeSet when MIR inlines BTreeMap<K, SetValZST> calls.

/// Test BTreeMapEntry creates entry tracking state.
/// btreemap.rs: BTreeMapEntry branch — requires map + key in env.
/// Uses probe_u32_binary (3 locals: 0=ret, 1=x, 2=_y) so local 2 exists for key operand.
#[test]
fn test_codegen_btreemap_entry_returns_target() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed a map in the env (Array<bv32, Bool> for BTreeSet model)
        let key_sort = Sort::bitvec(32);
        let map_sort = Sort::array(key_sort, Sort::bool());
        let map_expr = Expr::var("test_btree_map", map_sort);
        let map_op = seed_collections_local(&mut codegen, 1, map_expr);

        // Seed key
        let key_val = Expr::bitvec_const(42u128, 32);
        let key_op = seed_collections_local(&mut codegen, 2, key_val);

        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntry,
            &[map_op, key_op],
            &dest,
            Some(1),
            "std::collections::BTreeMap::entry",
        );
        assert_eq!(result, Some(1));
    });
}

/// Test BTreeMapEntry with insufficient args returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_entry_insufficient_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        // Only 1 arg, needs 2
        let map_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntry,
            &[map_op],
            &dest,
            Some(2),
            "std::collections::BTreeMap::entry",
        );
        assert_eq!(result, None, "insufficient args must fail-closed (#2497)");
    });
}

/// Test BTreeMapVacantInsert without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapVacantInsert — requires entry_map_bases populated by prior BTreeMapEntry.
#[test]
fn test_codegen_btreemap_vacant_insert_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        // Without entry tracking state, fail-closed returns None
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapVacantInsert,
            &[entry_op],
            &dest,
            Some(3),
            "std::collections::btree_map::VacantEntry::insert",
        );
        assert_eq!(result, None, "VacantInsert without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapVacantInsert with empty args returns target.
#[test]
fn test_codegen_btreemap_vacant_insert_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapVacantInsert,
            &[],
            &dest,
            Some(4),
            "std::collections::btree_map::VacantEntry::insert",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
    });
}

/// Test BTreeMapVacantInsertEntry without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapVacantInsertEntry — requires entry_map_bases from prior BTreeMapEntry.
#[test]
fn test_codegen_btreemap_vacant_insert_entry_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapVacantInsertEntry,
            &[entry_op],
            &dest,
            Some(5),
            "std::collections::btree_map::VacantEntry::insert_entry",
        );
        assert_eq!(result, None, "VacantInsertEntry without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapVacantInsertEntry with empty args returns target.
#[test]
fn test_codegen_btreemap_vacant_insert_entry_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapVacantInsertEntry,
            &[],
            &dest,
            Some(6),
            "std::collections::btree_map::VacantEntry::insert_entry",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
    });
}

/// Test BTreeMapOccupiedInsert without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapOccupiedInsert — requires entry_map_bases from prior BTreeMapEntry.
#[test]
fn test_codegen_btreemap_occupied_insert_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapOccupiedInsert,
            &[entry_op],
            &dest,
            Some(7),
            "std::collections::btree_map::OccupiedEntry::insert",
        );
        assert_eq!(result, None, "OccupiedInsert without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapOccupiedInsert with empty args returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_occupied_insert_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapOccupiedInsert,
            &[],
            &dest,
            Some(8),
            "std::collections::btree_map::OccupiedEntry::insert",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
    });
}

/// Test BTreeMapOccupiedGetMut without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapOccupiedGetMut — requires entry_map_bases from prior BTreeMapEntry.
#[test]
fn test_codegen_btreemap_occupied_get_mut_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapOccupiedGetMut,
            &[entry_op],
            &dest,
            Some(9),
            "std::collections::btree_map::OccupiedEntry::get_mut",
        );
        assert_eq!(result, None, "OccupiedGetMut without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapOccupiedGetMut with empty args returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_occupied_get_mut_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapOccupiedGetMut,
            &[],
            &dest,
            Some(10),
            "std::collections::btree_map::OccupiedEntry::get_mut",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
    });
}

/// Test BTreeMapOccupiedIntoMut without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapOccupiedIntoMut — delegates to get_mut, requires entry state.
#[test]
fn test_codegen_btreemap_occupied_into_mut_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapOccupiedIntoMut,
            &[entry_op],
            &dest,
            Some(11),
            "std::collections::btree_map::OccupiedEntry::into_mut",
        );
        assert_eq!(result, None, "OccupiedIntoMut without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapEntryOrInsert without entry tracking state returns None (fail-closed #2497).
/// btreemap.rs: BTreeMapEntryOrInsert — requires entry_map_bases from prior BTreeMapEntry.
#[test]
fn test_codegen_btreemap_entry_or_insert_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntryOrInsert,
            &[entry_op],
            &dest,
            Some(12),
            "std::collections::btree_map::Entry::or_insert",
        );
        assert_eq!(result, None, "EntryOrInsert without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapEntryOrInsertWith without entry tracking state returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_entry_or_insert_with_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntryOrInsertWith,
            &[entry_op],
            &dest,
            Some(13),
            "std::collections::btree_map::Entry::or_insert_with",
        );
        assert_eq!(result, None, "EntryOrInsertWith without entry state must fail-closed (#2497)");
    });
}

/// Test BTreeMapEntryOrInsertWithKey without entry tracking state returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_entry_or_insert_with_key_no_entry_state() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let entry_op = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };

        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntryOrInsertWithKey,
            &[entry_op],
            &dest,
            Some(14),
            "std::collections::btree_map::Entry::or_insert_with_key",
        );
        assert_eq!(
            result, None,
            "EntryOrInsertWithKey without entry state must fail-closed (#2497)"
        );
    });
}

/// Test BTreeMapEntryOrInsert with empty args returns None (fail-closed #2497).
#[test]
fn test_codegen_btreemap_entry_or_insert_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeMapEntryOrInsert,
            &[],
            &dest,
            Some(15),
            "std::collections::btree_map::Entry::or_insert",
        );
        assert_eq!(result, None, "empty args must fail-closed (#2497)");
    });
}

/// Test BTreeSearchTree returns None — not modeled, fail-closed (#2497).
/// btreemap.rs: BTreeSearchTree — internal node op, unconditionally None.
#[test]
fn test_codegen_btreemap_search_tree_not_modeled() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeSearchTree,
            &[],
            &dest,
            Some(16),
            "std::collections::btree::search::search_tree",
        );
        assert_eq!(result, None, "BTreeSearchTree not modeled — fail-closed (#2497)");
    });
}

/// Test BTreeNodeReborrow returns None — not modeled, fail-closed (#2497).
/// btreemap.rs: BTreeNodeReborrow — internal node op, unconditionally None.
#[test]
fn test_codegen_btreemap_node_reborrow_not_modeled() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeNodeReborrow,
            &[],
            &dest,
            Some(17),
            "std::collections::btree::node::NodeRef::reborrow",
        );
        assert_eq!(result, None, "BTreeNodeReborrow not modeled — fail-closed (#2497)");
    });
}

/// Test BTreeHandleIntoKv returns None — not modeled, fail-closed (#2497).
/// btreemap.rs: BTreeHandleIntoKv — internal node op, unconditionally None.
#[test]
fn test_codegen_btreemap_handle_into_kv_not_modeled() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::BTreeHandleIntoKv,
            &[],
            &dest,
            Some(18),
            "std::collections::btree::node::Handle::into_kv",
        );
        assert_eq!(result, None, "BTreeHandleIntoKv not modeled — fail-closed (#2497)");
    });
}

/// Test that passing a non-btreemap stub kind returns None (graceful fallback).
#[test]
fn test_codegen_btreemap_non_btreemap_stub_returns_none() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        // Non-btreemap stub kind returns None — warn!() logs the mismatch
        let result = codegen.codegen_btreemap_internal_stub(
            StubKind::VecNew,
            &[],
            &dest,
            Some(19),
            "unrelated::path",
        );
        assert!(result.is_none(), "non-btreemap stub should return None");
    });
}

// =============================================================================
// BTreeMap CRUD real-operand tests (Part of #2148)
// =============================================================================
// BTreeMap CRUD operations share the codegen_hashmap_stub dispatch with HashMap.
// These tests verify the shared path works correctly with BTreeMap stub kinds.

/// Test BTreeMapInsert with real key/value operands updates map.
/// hashmap.rs: BTreeMapInsert branch (shared with HashMapInsert).
#[test]
fn test_codegen_btreemap_insert_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create BTreeMap at local 1
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::BTreeMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::BTreeMap::new",
        );

        // Insert: args[0]=map ref, args[1]=key, args[2]=value
        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(50u64, POINTER_WIDTH));
        let val = seed_collections_local(&mut codegen, 3, Expr::bitvec_const(77u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::BTreeMapInsert,
            &[map_ref, key, val],
            &dest,
            Some(2),
            "std::collections::BTreeMap::insert",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Insert should assign destination");
        assert!(
            dest_val.sort().is_datatype(),
            "BTreeMapInsert should return Option<V> datatype, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeMapGet with real key after Insert returns Option.
/// hashmap.rs: BTreeMapGet branch (shared with HashMapGet).
#[test]
fn test_codegen_btreemap_get_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create map, insert a key
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::BTreeMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::BTreeMap::new",
        );
        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(88u64, POINTER_WIDTH));
        let val = seed_collections_local(&mut codegen, 3, Expr::bitvec_const(11u64, POINTER_WIDTH));
        let ins_dest = Place { local: 4, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::BTreeMapInsert,
            &[map_ref, key, val],
            &ins_dest,
            Some(2),
            "std::collections::BTreeMap::insert",
        );

        // Get the key
        let map_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let get_key =
            seed_collections_local(&mut codegen, 5, Expr::bitvec_const(88u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::BTreeMapGet,
            &[map_ref2, get_key],
            &dest,
            Some(3),
            "std::collections::BTreeMap::get",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Get should assign destination");
        assert!(
            dest_val.sort().is_datatype(),
            "BTreeMapGet should return Option<V> datatype, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeMapLen with a seeded map returns tracked length.
/// hashmap.rs: BTreeMapLen branch (shared with HashMapLen).
#[test]
fn test_codegen_btreemap_len_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create map at local 1
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::BTreeMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::BTreeMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::BTreeMapLen,
            &[map_ref],
            &dest,
            Some(2),
            "std::collections::BTreeMap::len",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Len should assign destination");
        assert!(
            dest_val.sort().is_bitvec(),
            "BTreeMapLen should produce bitvec sort, got {:?}",
            dest_val.sort()
        );
    });
}

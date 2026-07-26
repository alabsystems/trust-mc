// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! HashSet collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

// =============================================================================
// HashSet stub gap tests (Part of #2016)
// =============================================================================

/// Test HashSetClone with empty args returns target.
/// hashset.rs: HashSetClone branch — clones set with length copy.
#[test]
fn test_codegen_hashset_clone_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetClone,
            &[],
            &dest,
            Some(1),
            "std::collections::HashSet::clone",
        );
        assert_eq!(result, None, "HashSetClone with empty args must fail-closed (#2497)");
    });
}

/// Test HashSetIter with empty args returns None (fail-closed #2497).
/// hashset.rs: HashSetIter branch — creates borrow iterator.
#[test]
fn test_codegen_hashset_iter_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetIter,
            &[],
            &dest,
            Some(2),
            "std::collections::HashSet::iter",
        );
        assert_eq!(result, None, "HashSetIter with empty args must fail-closed (#2497)");
    });
}

/// Test HashSetLen with empty args returns None (fail-closed #2497).
/// hashset.rs: HashSetLen branch.
#[test]
fn test_codegen_hashset_len_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetLen,
            &[],
            &dest,
            Some(3),
            "std::collections::HashSet::len",
        );
        assert_eq!(result, None, "HashSetLen with empty args must fail-closed (#2497)");
    });
}

/// Test HashSetIsEmpty with empty args returns None (fail-closed #2497).
/// hashset.rs: HashSetIsEmpty branch.
#[test]
fn test_codegen_hashset_is_empty_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetIsEmpty,
            &[],
            &dest,
            Some(4),
            "std::collections::HashSet::is_empty",
        );
        assert_eq!(result, None, "HashSetIsEmpty with empty args must fail-closed (#2497)");
    });
}

/// Test HashSetIntoIter with empty args returns None (fail-closed #2497).
/// hashset.rs: HashSetIntoIter branch.
#[test]
fn test_codegen_hashset_into_iter_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetIntoIter,
            &[],
            &dest,
            Some(5),
            "std::collections::HashSet::into_iter",
        );
        assert_eq!(result, None, "HashSetIntoIter with empty args must fail-closed (#2497)");
    });
}

// =============================================================================
// HashSet real-operand tests (Part of #2148)
// =============================================================================
// These tests exercise real HashSet stub logic with seeded sets, not just
// the empty-args fallback path. HashSet is modeled as Array<Key, Bool>.

/// Test HashSetInsert with real operand seeds set and returns was_absent Bool.
/// hashset.rs: HashSetInsert branch — store(set, key, true), return !was_present.
#[test]
fn test_codegen_hashset_insert_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create empty HashSet at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );

        // Insert key=42
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(42u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetInsert,
            &[set_ref, key],
            &dest,
            Some(2),
            "std::collections::HashSet::insert",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Insert should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "HashSetInsert should return Bool (was_absent), got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashSetContains after insert returns Bool from select(set, key).
/// hashset.rs: HashSetContains branch — select(set, key).
#[test]
fn test_codegen_hashset_contains_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set and insert key=10
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let ins_key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(10u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetInsert,
            &[set_ref, ins_key],
            &ins_dest,
            Some(2),
            "std::collections::HashSet::insert",
        );

        // Check contains for the same key
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let query_key =
            seed_collections_local(&mut codegen, 4, Expr::bitvec_const(10u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetContains,
            &[set_ref2, query_key],
            &dest,
            Some(3),
            "std::collections::HashSet::contains",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Contains should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "HashSetContains should return Bool, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashSetRemove with real operand returns was_present Bool.
/// hashset.rs: HashSetRemove branch — store(set, key, false), return was_present.
#[test]
fn test_codegen_hashset_remove_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set and insert key=7
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let ins_key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(7u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetInsert,
            &[set_ref, ins_key],
            &ins_dest,
            Some(2),
            "std::collections::HashSet::insert",
        );

        // Remove key=7
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let rm_key =
            seed_collections_local(&mut codegen, 4, Expr::bitvec_const(7u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetRemove,
            &[set_ref2, rm_key],
            &dest,
            Some(3),
            "std::collections::HashSet::remove",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Remove should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "HashSetRemove should return Bool (was_present), got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashSetLen with a seeded set returns tracked bitvec length.
/// hashset.rs: HashSetLen branch — returns tracked length.
#[test]
fn test_codegen_hashset_len_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );

        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetLen,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::HashSet::len",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Len should assign destination");
        assert!(
            dest_val.sort().is_bitvec(),
            "HashSetLen should produce bitvec sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashSetIsEmpty with a seeded set returns Bool.
/// hashset.rs: HashSetIsEmpty branch — len == 0.
#[test]
fn test_codegen_hashset_is_empty_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );

        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetIsEmpty,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::HashSet::is_empty",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("IsEmpty should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "HashSetIsEmpty should produce Bool sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashSetClear with a seeded set resets array and length.
/// hashset.rs: HashSetClear branch — const_array(false), len=0.
#[test]
fn test_codegen_hashset_clear_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set and insert a key
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(99u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetInsert,
            &[set_ref, key],
            &ins_dest,
            Some(2),
            "std::collections::HashSet::insert",
        );

        // Clear the set
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetClear,
            &[set_ref2],
            &dest,
            Some(3),
            "std::collections::HashSet::clear",
        );
        assert_eq!(result, Some(3));
        let set_base = codegen.ssa_base_name(&set_dest);
        let set_val =
            codegen.env_lookup(&set_base).expect("Set should still be in env after clear");
        assert!(set_val.sort().is_array(), "Cleared set should be array sort");
    });
}

/// Test HashSetClone with a seeded set copies array and length.
/// hashset.rs: HashSetClone branch — identity copy + length copy.
#[test]
fn test_codegen_hashset_clone_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashset_stub(
            StubKind::HashSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::HashSet::new",
        );

        // Clone the set
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashset_stub(
            StubKind::HashSetClone,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::HashSet::clone",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Clone should assign destination");
        assert!(
            dest_val.sort().is_array(),
            "HashSetClone should produce Array sort, got {:?}",
            dest_val.sort()
        );
    });
}

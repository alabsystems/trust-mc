// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BTreeSet collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;

// =============================================================================
// BTreeSet stub gap tests (Part of #2016)
// =============================================================================

/// Test BTreeSetLen with empty args returns target.
/// btreeset.rs: BTreeSetLen branch — returns tracked or symbolic length.
#[test]
fn test_codegen_btreeset_len_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetLen,
            &[],
            &dest,
            Some(1),
            "std::collections::BTreeSet::len",
        );
        assert_eq!(result, None, "BTreeSetLen with empty args must fail-closed (#2497)");
    });
}

/// Test BTreeSetIsEmpty with empty args returns None (fail-closed #2497).
/// btreeset.rs: BTreeSetIsEmpty branch.
#[test]
fn test_codegen_btreeset_is_empty_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetIsEmpty,
            &[],
            &dest,
            Some(2),
            "std::collections::BTreeSet::is_empty",
        );
        assert_eq!(result, None, "BTreeSetIsEmpty with empty args must fail-closed (#2497)");
    });
}

/// Test BTreeSetIntoIter with empty args returns None (fail-closed #2497).
/// btreeset.rs: BTreeSetIntoIter branch — creates iterator with membership constraint.
#[test]
fn test_codegen_btreeset_into_iter_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetIntoIter,
            &[],
            &dest,
            Some(3),
            "std::collections::BTreeSet::into_iter",
        );
        assert_eq!(result, None, "BTreeSetIntoIter with empty args must fail-closed (#2497)");
    });
}

/// Test BTreeSetIter with empty args returns None (fail-closed #2497).
/// btreeset.rs: BTreeSetIter branch — borrows iterator.
#[test]
fn test_codegen_btreeset_iter_empty_args() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetIter,
            &[],
            &dest,
            Some(4),
            "std::collections::BTreeSet::iter",
        );
        assert_eq!(result, None, "BTreeSetIter with empty args must fail-closed (#2497)");
    });
}

// =============================================================================
// BTreeSet real-operand tests (Part of #2148)
// =============================================================================
// These tests exercise real BTreeSet stub logic with seeded sets, not just
// the empty-args fallback path. BTreeSet is modeled as Array<Key, Bool>.

/// Test BTreeSetInsert with real operand seeds set and returns was_absent Bool.
/// btreeset.rs: BTreeSetInsert branch — store(set, key, true), return !was_present.
#[test]
fn test_codegen_btreeset_insert_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create empty BTreeSet at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );

        // Insert key=42 into the set
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(42u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetInsert,
            &[set_ref, key],
            &dest,
            Some(2),
            "std::collections::BTreeSet::insert",
        );
        assert_eq!(result, Some(2));
        // Insert returns bool (was_absent = !was_present)
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Insert should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "BTreeSetInsert should return Bool (was_absent), got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeSetContains after insert returns Bool from select(set, key).
/// btreeset.rs: BTreeSetContains branch — select(set, key).
#[test]
fn test_codegen_btreeset_contains_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create empty BTreeSet at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );

        // Insert key=10 first
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let ins_key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(10u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetInsert,
            &[set_ref, ins_key],
            &ins_dest,
            Some(2),
            "std::collections::BTreeSet::insert",
        );

        // Now check contains with the same key
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let query_key =
            seed_collections_local(&mut codegen, 4, Expr::bitvec_const(10u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetContains,
            &[set_ref2, query_key],
            &dest,
            Some(3),
            "std::collections::BTreeSet::contains",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Contains should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "BTreeSetContains should return Bool, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeSetRemove with real operand returns was_present Bool.
/// btreeset.rs: BTreeSetRemove branch — store(set, key, false), return was_present.
#[test]
fn test_codegen_btreeset_remove_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set and insert key=7
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let ins_key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(7u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetInsert,
            &[set_ref, ins_key],
            &ins_dest,
            Some(2),
            "std::collections::BTreeSet::insert",
        );

        // Remove key=7
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let rm_key =
            seed_collections_local(&mut codegen, 4, Expr::bitvec_const(7u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetRemove,
            &[set_ref2, rm_key],
            &dest,
            Some(3),
            "std::collections::BTreeSet::remove",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Remove should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "BTreeSetRemove should return Bool (was_present), got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeSetLen with a seeded set returns tracked bitvec length.
/// btreeset.rs: BTreeSetLen branch — returns tracked length.
#[test]
fn test_codegen_btreeset_len_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1 (initializes len tracking to 0)
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );

        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetLen,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::BTreeSet::len",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Len should assign destination");
        assert!(
            dest_val.sort().is_bitvec(),
            "BTreeSetLen should produce bitvec sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeSetIsEmpty with a seeded set returns Bool equality check.
/// btreeset.rs: BTreeSetIsEmpty branch — len == 0.
#[test]
fn test_codegen_btreeset_is_empty_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );

        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetIsEmpty,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::BTreeSet::is_empty",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("IsEmpty should assign destination");
        assert!(
            dest_val.sort().is_bool(),
            "BTreeSetIsEmpty should produce Bool sort, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test BTreeSetClear with a seeded set resets the array and length.
/// btreeset.rs: BTreeSetClear branch — const_array(false), len=0.
#[test]
fn test_codegen_btreeset_clear_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set and insert a key
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(99u64, POINTER_WIDTH));
        let ins_dest = Place { local: 3, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetInsert,
            &[set_ref, key],
            &ins_dest,
            Some(2),
            "std::collections::BTreeSet::insert",
        );

        // Clear the set
        let set_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetClear,
            &[set_ref2],
            &dest,
            Some(3),
            "std::collections::BTreeSet::clear",
        );
        assert_eq!(result, Some(3));
        // Verify the set was reset in env — look up the base and check it's an array
        let set_base = codegen.ssa_base_name(&set_dest);
        let set_val =
            codegen.env_lookup(&set_base).expect("Set should still be in env after clear");
        assert!(set_val.sort().is_array(), "Cleared set should be array sort");
    });
}

/// Test BTreeSetClone with a seeded set copies array and length.
/// btreeset.rs: BTreeSetClone branch — identity copy + length copy.
#[test]
fn test_codegen_btreeset_clone_real_operand() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create set at local 1
        let set_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_btreeset_stub(
            StubKind::BTreeSetNew,
            &[],
            &set_dest,
            Some(1),
            "std::collections::BTreeSet::new",
        );

        // Clone the set to destination local 0
        let set_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_btreeset_stub(
            StubKind::BTreeSetClone,
            &[set_ref],
            &dest,
            Some(2),
            "std::collections::BTreeSet::clone",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Clone should assign destination");
        assert!(
            dest_val.sort().is_array(),
            "BTreeSetClone should produce Array sort, got {:?}",
            dest_val.sort()
        );
    });
}

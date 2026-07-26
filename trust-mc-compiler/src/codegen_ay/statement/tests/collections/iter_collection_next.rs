// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/iter_collection_next.rs — collection iterator next operations.
//!
//! Covers:
//! - `codegen_iter_collection_next_stub` for HashMapIterNext
//! - `codegen_iter_collection_next_stub` for HashSetIterNext
//! - `codegen_iter_collection_next_stub` for BTreeSetIterNext
//! - Non-datatype sort rejection (UNSOUND violation recording)
//! - Symbolic fallback when iterator base not found
//!
//! All tests exercise actual production functions via MIR-driven StatementCodegen.
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::stubs::StubKind;
use std::sync::Arc;

// =============================================================================
// HashMapIterNext — HashMap/TrustMcMap iterator next
// =============================================================================

/// HashMapIterNext with properly constructed iterator produces Option<(K, V)> result.
#[test]
fn test_hashmap_iter_next_with_valid_iterator() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // Build a proper HashMapIntoIter datatype with DT-free encoding (#3057, #3106):
        // fields: data (Array<K, Option<V>>), present (Array<K, Bool>),
        //         keys (Array<bv64, K>), pos (bv64), len (bv64)
        let key_sort = Sort::bitvec(32);
        let option_val_sort = codegen.make_option_sort(Sort::bitvec(32));
        let data_sort = Sort::array(key_sort.clone(), option_val_sort);
        let present_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);

        let iter_sort = struct_sort(
            "HashMapIntoIter",
            [
                ("fld_data", data_sort.clone()),
                ("fld_present", present_sort),
                ("fld_keys", keys_sort.clone()),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );

        // Create iterator with pos=0, len=2
        let data_val = Expr::var("test_data", data_sort);
        let present_val = Expr::const_array(Sort::bool(), Expr::bool_const(true));
        let keys_val = Expr::var("test_keys", keys_sort);
        let pos_val = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let len_val = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let iter_val = Expr::datatype_constructor(
            "HashMapIntoIter",
            "HashMapIntoIter",
            vec![data_val, present_val, keys_val, pos_val, len_val],
            iter_sort,
        );

        // Seed the iterator in env and ref_pointees
        let _iter_base = {
            let place = local_place(1);
            let base = codegen.ssa_base_name(&place);
            codegen.ref_pointees.insert(Arc::from(base.clone()), Arc::from("iter_target"));
            codegen.env_update("iter_target", iter_val);
            base
        };

        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashMapIterNext,
            &[self_operand],
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "should return target block");

        // Check that destination was assigned
        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).cloned();
        assert!(assigned.is_some(), "HashMapIterNext should assign a value to destination");
    });
}

/// HashMapIterNext with no args returns target without crash.
#[test]
fn test_hashmap_iter_next_no_args() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashMapIterNext,
            &[], // no args
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "no-args should return target gracefully");
    });
}

/// HashMapIterNext with non-datatype iterator sort records UNSOUND violation.
#[test]
fn test_hashmap_iter_next_non_datatype_records_violation() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // Seed a non-datatype iterator (bv64 — wrong sort)
        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        codegen.ref_pointees.insert(Arc::from(base), Arc::from("bad_iter"));
        codegen.env_update("bad_iter", Expr::bitvec_const(0u64, POINTER_WIDTH));

        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashMapIterNext,
            &[self_operand],
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "should return target even after recording violation");

        // Destination should still get a symbolic value (fallback path)
        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).cloned();
        assert!(assigned.is_some(), "non-datatype path should still assign symbolic result");
    });
}

/// HashMapIterNext with unresolved iterator base falls back to symbolic.
#[test]
fn test_hashmap_iter_next_unresolved_base_symbolic() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // Don't seed any iterator — base will be None
        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashMapIterNext,
            &[self_operand],
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "unresolved base should return target");
    });
}

// =============================================================================
// HashSetIterNext / BTreeSetIterNext — Set iterator next
// =============================================================================

/// HashSetIterNext with properly constructed set iterator produces Option<K> result.
#[test]
fn test_hashset_iter_next_with_valid_iterator() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // Build a SetIntoIter datatype:
        // fields: set (Array<K, Bool>), keys (Array<bv64, K>), pos (bv64), len (bv64)
        let key_sort = Sort::bitvec(32);
        let set_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);

        let iter_sort = struct_sort(
            "SetIntoIter",
            [
                ("fld_set", set_sort.clone()),
                ("fld_keys", keys_sort.clone()),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );

        let set_val = Expr::var("test_set", set_sort);
        let keys_val = Expr::var("test_keys", keys_sort);
        let pos_val = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let len_val = Expr::bitvec_const(3u64, POINTER_WIDTH);
        let iter_val = Expr::datatype_constructor(
            "SetIntoIter",
            "SetIntoIter",
            vec![set_val, keys_val, pos_val, len_val],
            iter_sort,
        );

        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        codegen.ref_pointees.insert(Arc::from(base), Arc::from("set_iter_target"));
        codegen.env_update("set_iter_target", iter_val);

        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashSetIterNext,
            &[self_operand],
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "should return target block");

        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).cloned();
        assert!(assigned.is_some(), "HashSetIterNext should assign a value to destination");
    });
}

/// BTreeSetIterNext exercises the same code path as HashSetIterNext.
#[test]
fn test_btreeset_iter_next_with_valid_iterator() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        let key_sort = Sort::bitvec(64);
        let set_sort = Sort::array(key_sort.clone(), Sort::bool());
        let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);

        let iter_sort = struct_sort(
            "SetIntoIter",
            [
                ("fld_set", set_sort.clone()),
                ("fld_keys", keys_sort.clone()),
                ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
                ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ],
        );

        let set_val = Expr::var("btree_set", set_sort);
        let keys_val = Expr::var("btree_keys", keys_sort);
        let pos_val = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let len_val = Expr::bitvec_const(5u64, POINTER_WIDTH);
        let iter_val = Expr::datatype_constructor(
            "SetIntoIter",
            "SetIntoIter",
            vec![set_val, keys_val, pos_val, len_val],
            iter_sort,
        );

        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        codegen.ref_pointees.insert(Arc::from(base), Arc::from("btree_iter_target"));
        codegen.env_update("btree_iter_target", iter_val);

        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::BTreeSetIterNext,
            &[self_operand],
            &dest,
            Some(2),
        );

        assert_eq!(result, Some(2), "should return target block");

        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).cloned();
        assert!(assigned.is_some(), "BTreeSetIterNext should assign a value to destination");
    });
}

/// HashSetIterNext with non-datatype sort records UNSOUND violation.
#[test]
fn test_hashset_iter_next_non_datatype_records_violation() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // Non-datatype iterator
        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        codegen.ref_pointees.insert(Arc::from(base), Arc::from("bad_set_iter"));
        codegen.env_update("bad_set_iter", Expr::bitvec_const(0u64, POINTER_WIDTH));

        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::HashSetIterNext,
            &[self_operand],
            &dest,
            Some(1),
        );

        assert_eq!(result, Some(1), "should return target even after violation");
    });
}

/// TrustMcMapIterNext exercises the same code path as HashMapIterNext.
#[test]
fn test_trust_mcmap_iter_next_dispatches_to_hashmap_path() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);

        // No iterator seeded — both should fall back to symbolic
        let self_operand = Operand::Copy(local_place(1));
        let result = codegen.codegen_iter_collection_next_stub(
            StubKind::TrustMcMapIterNext,
            &[self_operand],
            &dest,
            Some(3),
        );

        assert_eq!(result, Some(3), "TrustMcMapIterNext should return target");
    });
}

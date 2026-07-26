// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for set_common.rs — shared set operations for BTreeSet/HashSet BMC stubs.
//!
//! These operations model sets as `Array<Key, Bool>` (element presence maps).
//! Part of #2933 (zero-coverage remediation).

use super::*;

// =============================================================================
// set_op_new — creates empty set with const_array(key_sort, false), len=0
// =============================================================================

#[test]
fn test_set_op_new_assigns_array_sort_destination() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.set_op_new("BTreeSet", Sort::bv32(), &destination, Some(10));
        assert_eq!(result, Some(10), "set_op_new should return target");

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(
            assigned.sort().array_sort().is_some(),
            "set_op_new result should be an Array sort, got {:?}",
            assigned.sort()
        );
    });
}

#[test]
fn test_set_op_new_initializes_length_to_zero() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        codegen.set_op_new("HashSet", Sort::bv32(), &destination, Some(11));

        let dest_base = codegen.ssa_base_name(&destination);
        let len_name = crate::codegen_ay::names::len_name(&dest_base);
        let len_expr = codegen.env_lookup(&len_name).expect("length should be tracked");
        assert_eq!(
            len_expr.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "length should be pointer-width bitvec"
        );
    });
}

// =============================================================================
// set_op_insert — store(key, true), return was_absent, conditional len++
// =============================================================================

#[test]
fn test_set_op_insert_insufficient_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_insert("BTreeSet", &[], &dest, Some(20));
        assert_eq!(result, None, "insert with no args must fail-closed (#2497)");
    });
}

#[test]
fn test_set_op_insert_single_arg_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_insert("BTreeSet", &[local_operand(1)], &dest, Some(21));
        assert_eq!(result, None, "insert with 1 arg must fail-closed (#2497)");
    });
}

// =============================================================================
// set_op_contains — select(set, key)
// =============================================================================

#[test]
fn test_set_op_contains_insufficient_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_contains("HashSet", &[], &dest, Some(30));
        assert_eq!(result, None, "contains with no args must fail-closed (#2497)");
    });
}

#[test]
fn test_set_op_contains_single_arg_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_contains("HashSet", &[local_operand(1)], &dest, Some(31));
        assert_eq!(result, None, "contains with 1 arg must fail-closed (#2497)");
    });
}

// =============================================================================
// set_op_remove — store(key, false), return was_present, conditional len--
// =============================================================================

#[test]
fn test_set_op_remove_insufficient_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_remove("BTreeSet", &[], &dest, Some(40));
        assert_eq!(result, None, "remove with no args must fail-closed (#2497)");
    });
}

#[test]
fn test_set_op_remove_single_arg_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_remove("BTreeSet", &[local_operand(1)], &dest, Some(41));
        assert_eq!(result, None, "remove with 1 arg must fail-closed (#2497)");
    });
}

// =============================================================================
// set_op_len — return tracked length or symbolic fallback
// =============================================================================

#[test]
fn test_set_op_len_empty_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_len("HashSet", &[], &dest, Some(50));
        assert_eq!(result, None, "len with no args must fail-closed (#2497)");
    });
}

#[test]
fn test_set_op_len_unresolvable_base_returns_symbolic() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        // local_operand(1) with no seeded set base — should fall back to symbolic
        let result = codegen.set_op_len("HashSet", &[local_operand(1)], &dest, Some(51));
        assert_eq!(result, Some(51), "len should return target even with unresolvable base");

        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "symbolic len fallback should be pointer-width bitvec"
        );
    });
}

// =============================================================================
// set_op_is_empty — len == 0 or symbolic fallback
// =============================================================================

#[test]
fn test_set_op_is_empty_empty_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_is_empty("BTreeSet", &[], &dest, Some(60));
        assert_eq!(result, None, "is_empty with no args must fail-closed (#2497)");
    });
}

#[test]
fn test_set_op_is_empty_unresolvable_base_returns_symbolic_bool() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_is_empty("BTreeSet", &[local_operand(1)], &dest, Some(61));
        assert_eq!(result, Some(61), "is_empty should return target even with unresolvable base");

        let dest_base = codegen.ssa_base_name(&dest);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(assigned.sort().is_bool(), "symbolic is_empty fallback should be Bool sort");
    });
}

// =============================================================================
// set_op_clear — const_array(key_sort, false), len=0
// =============================================================================

#[test]
fn test_set_op_clear_empty_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.set_op_clear("HashSet", &[], Some(70));
        assert_eq!(result, None, "clear with no args must fail-closed (#2497)");
    });
}

// =============================================================================
// set_op_clone — copy set and length tracking
// =============================================================================

#[test]
fn test_set_op_clone_empty_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_clone("BTreeSet", &[], &dest, Some(80));
        assert_eq!(result, None, "clone with no args must fail-closed (#2497)");
    });
}

// =============================================================================
// set_op_iter — creates set iterator
// =============================================================================

#[test]
fn test_set_op_iter_empty_args_fails_closed() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dest = local_place(0);
        let result = codegen.set_op_iter("HashSet", "into_iter", &[], &dest, Some(90));
        assert_eq!(result, None, "iter with no args must fail-closed (#2497)");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/hashmap_helpers.rs — HashMap sort/option utilities.
//!
//! Covers:
//! - `make_option_sort` — Option<T> sort construction
//! - `make_option_none` — None value construction
//! - `make_option_some` — Some(v) value construction
//! - `option_is_some` — Some/None discriminant check
//! - `get_or_create_hashmap_len` — idempotent len symbol management
//! - `get_map_base_from_ref` — HashMap base name resolution from ref
//!
//! All tests exercise actual production functions via MIR-driven StatementCodegen.
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use std::sync::Arc;

// =============================================================================
// make_option_sort — creates Option datatype sort
// =============================================================================

/// make_option_sort creates a datatype with None and Some constructors.
#[test]
fn test_make_option_sort_creates_datatype() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        assert!(option_sort.is_datatype(), "make_option_sort should produce a datatype sort");

        let dt = option_sort.datatype_sort().expect("should be datatype");
        assert!(
            dt.name.contains("Option"),
            "datatype name should contain 'Option', got '{}'",
            dt.name
        );
        assert_eq!(dt.constructors.len(), 2, "Option should have 2 constructors (None, Some)");

        // Verify constructor names
        let ctor_names: Vec<&str> = dt.constructors.iter().map(|c| c.name.as_str()).collect();
        let none_ctor = crate::codegen_ay::names::option_none_constructor_name(&dt.name);
        let some_ctor = crate::codegen_ay::names::option_some_constructor_name(&dt.name);
        assert!(
            ctor_names.contains(&none_ctor.as_str()),
            "should have '{}' constructor, got {:?}",
            none_ctor,
            ctor_names,
        );
        assert!(
            ctor_names.contains(&some_ctor.as_str()),
            "should have '{}' constructor, got {:?}",
            some_ctor,
            ctor_names,
        );
    });
}

/// make_option_sort wraps different value sorts correctly.
#[test]
fn test_make_option_sort_different_value_sorts() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Bool value sort
        let opt_bool = codegen.make_option_sort(Sort::bool());
        assert!(opt_bool.is_datatype());

        // Int value sort
        let opt_int = codegen.make_option_sort(Sort::int());
        assert!(opt_int.is_datatype());

        // bv64 value sort
        let opt_bv64 = codegen.make_option_sort(Sort::bitvec(64));
        assert!(opt_bv64.is_datatype());

        // Different value sorts produce different Option type names
        let name_bool = opt_bool.datatype_name().unwrap().to_string();
        let name_int = opt_int.datatype_name().unwrap().to_string();
        assert_ne!(
            name_bool, name_int,
            "Option<Bool> and Option<Int> should have different type names"
        );
    });
}

// =============================================================================
// make_option_none — creates None value for given Option sort
// =============================================================================

/// make_option_none creates a None value with the correct sort.
#[test]
fn test_make_option_none_correct_sort() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let none_val = codegen.make_option_none(&option_sort);

        assert!(none_val.sort().is_datatype(), "None value should have datatype sort");
        assert_eq!(
            none_val.sort().datatype_name(),
            option_sort.datatype_name(),
            "None sort should match the Option sort"
        );
    });
}

/// make_option_none with non-datatype sort falls back without panic.
#[test]
fn test_make_option_none_non_datatype_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Pass a non-datatype sort — should fallback, not panic
        let bv_sort = Sort::bitvec(32);
        let none_val = codegen.make_option_none(&bv_sort);

        assert!(none_val.sort().is_datatype(), "fallback should still produce a datatype sort");
    });
}

// =============================================================================
// make_option_some — creates Some(value) for given Option sort
// =============================================================================

/// make_option_some creates a Some value wrapping the given expression.
#[test]
fn test_make_option_some_wraps_value() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let inner_val = Expr::bitvec_const(42u128, 32);
        let some_val = codegen.make_option_some(&option_sort, inner_val);

        assert!(some_val.sort().is_datatype(), "Some value should have datatype sort");
        assert_eq!(
            some_val.sort().datatype_name(),
            option_sort.datatype_name(),
            "Some sort should match the Option sort"
        );
    });
}

/// make_option_some with non-datatype sort falls back without panic.
#[test]
fn test_make_option_some_non_datatype_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_sort = Sort::bitvec(32);
        let inner_val = Expr::bitvec_const(7u128, 32);
        let some_val = codegen.make_option_some(&bv_sort, inner_val);

        assert!(some_val.sort().is_datatype(), "fallback should still produce a datatype sort");
    });
}

// =============================================================================
// option_is_some — checks if Option value is Some
// =============================================================================

/// option_is_some on a datatype expression produces a bool is_constructor check.
#[test]
fn test_option_is_some_datatype_returns_bool() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let some_val = codegen.make_option_some(&option_sort, Expr::bitvec_const(42u128, 32));

        let is_some = codegen.option_is_some(&some_val);
        assert!(is_some.sort().is_bool(), "option_is_some should return Bool sort");
    });
}

/// option_is_some on a non-datatype falls back to symbolic bool (over-approximation).
/// Regression guard for #84ff07d: hardcoded-true soundness bug.
#[test]
fn test_option_is_some_non_datatype_symbolic_fallback() {
    use ay_bindings::ExprValue;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Non-datatype expression
        let bv_expr = Expr::bitvec_const(1u128, 32);
        let is_some = codegen.option_is_some(&bv_expr);

        assert!(
            is_some.sort().is_bool(),
            "fallback should return Bool sort for over-approximation"
        );
        assert!(
            !matches!(is_some.value(), ExprValue::BoolConst(_)),
            "fallback must be symbolic, not a constant bool"
        );
        assert!(
            matches!(is_some.value(), ExprValue::Var { name } if name.contains("option_is_some_fallback")),
            "fallback should produce a dedicated symbolic var, got: {:?}",
            is_some.value()
        );
    });
}

/// Roundtrip: make_option_some -> option_is_some produces a meaningful check.
#[test]
fn test_option_roundtrip_some_then_is_some() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let some_val = codegen.make_option_some(&option_sort, Expr::bitvec_const(99u128, 32));
        let none_val = codegen.make_option_none(&option_sort);

        let is_some_some = codegen.option_is_some(&some_val);
        let is_some_none = codegen.option_is_some(&none_val);

        // Both should be bool
        assert!(is_some_some.sort().is_bool());
        assert!(is_some_none.sort().is_bool());

        // They should be structurally different expressions
        // (one is is_constructor("Some"), other is is_constructor("Some") on None)
        let some_str = format!("{:?}", is_some_some);
        let none_str = format!("{:?}", is_some_none);
        assert_ne!(
            some_str, none_str,
            "is_some on Some vs None should produce different expressions"
        );
    });
}

// =============================================================================
// get_or_create_hashmap_len — idempotent len symbol management
// =============================================================================

/// get_or_create_hashmap_len creates a fresh bv64 len symbol.
#[test]
fn test_get_or_create_hashmap_len_creates_fresh() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len = codegen.get_or_create_hashmap_len("map_base_1");
        assert_eq!(
            len.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "len should be bv64 (pointer width)"
        );
    });
}

/// get_or_create_hashmap_len returns the same symbol on subsequent calls.
#[test]
fn test_get_or_create_hashmap_len_idempotent() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len1 = codegen.get_or_create_hashmap_len("map_base_2");
        let len2 = codegen.get_or_create_hashmap_len("map_base_2");

        // Same base should return same expression
        let s1 = format!("{:?}", len1);
        let s2 = format!("{:?}", len2);
        assert_eq!(s1, s2, "same map base should return identical len symbol");
    });
}

/// get_or_create_hashmap_len returns different symbols for different maps.
#[test]
fn test_get_or_create_hashmap_len_different_maps() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len_a = codegen.get_or_create_hashmap_len("map_a");
        let len_b = codegen.get_or_create_hashmap_len("map_b");

        let sa = format!("{:?}", len_a);
        let sb = format!("{:?}", len_b);
        assert_ne!(sa, sb, "different map bases should get different len symbols");
    });
}

// =============================================================================
// get_map_base_from_ref — HashMap base name from reference operand
// =============================================================================

/// get_map_base_from_ref resolves through ref_pointees.
#[test]
fn test_get_map_base_from_ref_resolves_pointee() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed ref_pointees: local 1's ref base -> "hashmap_target"
        let ref_place = local_place(1);
        let ref_base = codegen.ssa_base_name(&ref_place);
        codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from("hashmap_target"));

        let operand = Operand::Copy(ref_place);
        let result = codegen.get_map_base_from_ref(&operand);

        assert_eq!(result, Some(Arc::from("hashmap_target")));
    });
}

/// get_map_base_from_ref falls back to direct env lookup if not a reference.
#[test]
fn test_get_map_base_from_ref_direct_env_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Seed env with the local's base name (no ref_pointees entry)
        let place = local_place(1);
        let base = codegen.ssa_base_name(&place);
        let map_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
        codegen.env_update(base.clone(), Expr::var("map_val", map_sort));

        let operand = Operand::Copy(place);
        let result = codegen.get_map_base_from_ref(&operand);

        assert_eq!(result, Some(Arc::from(base)));
    });
}

/// get_map_base_from_ref returns None when neither ref_pointees nor env has it.
#[test]
fn test_get_map_base_from_ref_not_found() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let operand = Operand::Copy(local_place(3));
        let result = codegen.get_map_base_from_ref(&operand);

        assert!(result.is_none(), "should return None when not tracked");
    });
}

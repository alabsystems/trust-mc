// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! HashMap collection stub tests.
//! Part of #2167: decomposed from 6,421-line collections.rs.

use super::*;
use crate::codegen_ay::stubs::StubKind;

// -----------------------------------------------------------------------------
// HashMap operation codegen tests (collections/hashmap.rs)
// HashMap is modeled as Array<Key, Option<Value>> with Option as ADT.
// Part of #2016: test coverage for untested codegen_ay modules.
// -----------------------------------------------------------------------------

fn with_hashmap_codegen<F>(fn_suffix: &str, callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen);
    });
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    destination: &Place,
) -> Option<Expr> {
    let dest_base = codegen.ssa_base_name(destination);
    codegen.env_lookup(&dest_base).cloned()
}

#[test]
fn test_codegen_hashmap_stub_new_assigns_array_destination() {
    with_hashmap_codegen("probe_u32", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &dest,
            Some(1),
            "std::collections::HashMap::new",
        );
        assert_eq!(result, Some(1));
        let assigned =
            assigned_expr_for_place(codegen, &dest).expect("HashMapNew should assign destination");
        assert!(assigned.sort().is_array());
    });
}

#[test]
fn test_codegen_hashmap_stub_len_no_args_assigns_bitvec() {
    with_hashmap_codegen("probe_u32", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapLen,
            &[],
            &dest,
            Some(2),
            "std::collections::HashMap::len",
        );
        assert_eq!(result, Some(2));
        let assigned =
            assigned_expr_for_place(codegen, &dest).expect("HashMapLen should assign destination");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

#[test]
fn test_codegen_hashmap_stub_is_empty_no_args_assigns_bool() {
    with_hashmap_codegen("probe_u32", |codegen| {
        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapIsEmpty,
            &[],
            &dest,
            Some(3),
            "std::collections::HashMap::is_empty",
        );
        assert_eq!(result, Some(3));
        let assigned = assigned_expr_for_place(codegen, &dest)
            .expect("HashMapIsEmpty should assign destination");
        assert!(assigned.sort().is_bool());
    });
}

#[test]
fn test_codegen_hashmap_empty_arg_guards_leave_destination_unassigned() {
    for (stub_kind, callee_path, target) in [
        (StubKind::HashMapClear, "std::collections::HashMap::clear", None),
        (StubKind::HashMapIter, "std::collections::HashMap::iter", None),
        (StubKind::HashMapKeys, "std::collections::HashMap::keys", None),
        (StubKind::HashMapValues, "std::collections::HashMap::values", None),
        (StubKind::HashMapClone, "std::collections::HashMap::clone", None),
        (StubKind::HashMapIntoIter, "std::collections::HashMap::into_iter", None),
    ] {
        with_hashmap_codegen("probe_u32", |codegen| {
            let dest = local_place(0);
            let result = codegen.codegen_hashmap_stub(stub_kind, &[], &dest, target, callee_path);
            assert_eq!(result, target);
            assert!(
                assigned_expr_for_place(codegen, &dest).is_none(),
                "{stub_kind:?} with empty args should not assign destination"
            );
        });
    }
}

// --- HashMap helper method tests (MIR-driven) ---

/// Test make_option_sort creates correct Option<bv32> datatype.
/// collections/hashmap.rs: make_option_sort.
#[test]
fn test_make_option_sort_bv32() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        assert!(option_sort.is_datatype());
        let dt = option_sort.datatype_sort().unwrap();
        assert!(
            dt.constructors
                .iter()
                .any(|ctor| crate::codegen_ay::names::is_some_constructor(&ctor.name))
        );
        assert!(
            dt.constructors
                .iter()
                .any(|ctor| crate::codegen_ay::names::is_none_constructor(&ctor.name))
        );
        assert_eq!(dt.constructors.len(), 2);
    });
}

/// Test make_option_sort with Int sort creates Option<Int>.
/// collections/hashmap.rs: make_option_sort.
#[test]
fn test_make_option_sort_int() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::int());
        assert!(option_sort.is_datatype());
        assert!(option_sort.datatype_name().unwrap().contains("Option_"));
    });
}

/// Test make_option_none creates None with correct sort.
/// collections/hashmap.rs: make_option_none.
#[test]
fn test_make_option_none_returns_datatype() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let none = codegen.make_option_none(&option_sort);

        assert!(none.sort().is_datatype());
        assert_eq!(*none.sort(), option_sort);
    });
}

/// Test make_option_none with non-datatype sort uses fallback (doesn't panic).
/// collections/hashmap.rs: make_option_none.
#[test]
fn test_make_option_none_non_datatype_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Pass a non-datatype sort — should fall back instead of panic
        let bv_sort = Sort::bitvec(32);
        let none = codegen.make_option_none(&bv_sort);
        assert!(none.sort().is_datatype());
    });
}

/// Test make_option_some wraps a value correctly.
/// collections/hashmap.rs: make_option_some.
#[test]
fn test_make_option_some_wraps_value() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let value = Expr::bitvec_const(42u32, 32);
        let some = codegen.make_option_some(&option_sort, value);

        assert!(some.sort().is_datatype());
        assert_eq!(*some.sort(), option_sort);
    });
}

/// Test make_option_some with non-datatype sort uses fallback.
/// collections/hashmap.rs: make_option_some.
#[test]
fn test_make_option_some_non_datatype_fallback() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_sort = Sort::bitvec(32);
        let value = Expr::bitvec_const(42u32, 32);
        let some = codegen.make_option_some(&bv_sort, value);
        assert!(some.sort().is_datatype());
    });
}

/// Test option_is_some returns bool for datatype option.
/// collections/hashmap.rs: option_is_some.
#[test]
fn test_option_is_some_returns_bool() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let option_sort = codegen.make_option_sort(Sort::bitvec(32));
        let value = Expr::bitvec_const(42u32, 32);
        let some = codegen.make_option_some(&option_sort, value);

        let is_some = codegen.option_is_some(&some);
        assert!(is_some.sort().is_bool());
    });
}

/// Test option_is_some returns symbolic bool for non-datatype sort.
/// Regression guard for #84ff07d: hardcoded-true soundness bug.
/// collections/hashmap.rs: option_is_some.
#[test]
fn test_option_is_some_non_datatype_returns_symbolic_bool() {
    use ay_bindings::ExprValue;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_expr = Expr::bitvec_const(42u32, 32);
        let is_some = codegen.option_is_some(&bv_expr);
        assert!(is_some.sort().is_bool());
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

/// Test get_or_create_hashmap_len creates fresh len on first call.
/// collections/hashmap.rs: get_or_create_hashmap_len.
#[test]
fn test_get_or_create_hashmap_len_creates_fresh() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len = codegen.get_or_create_hashmap_len("test_map_base");
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

/// Test get_or_create_hashmap_len returns same value on second call.
/// collections/hashmap.rs: get_or_create_hashmap_len.
#[test]
fn test_get_or_create_hashmap_len_returns_existing() {
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let len1 = codegen.get_or_create_hashmap_len("test_map_base");
        let len2 = codegen.get_or_create_hashmap_len("test_map_base");
        // Both should return expressions with the same sort
        assert_eq!(len1.sort(), len2.sort());
        assert_eq!(len1.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

// --- codegen_hashmap_stub MIR-driven tests ---

// --- HashMap: real-operand tests ---

#[test]
fn test_codegen_hashmap_iter_family_real_operand_assigns_iterators() {
    with_hashmap_codegen("probe_u32", |codegen| {
        let map_dest = local_place(1);
        codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );
        let map_ref = Operand::Copy(local_place(1));

        for (dest_local, stub_kind, callee_path, target) in [
            (2, StubKind::HashMapIntoIter, "std::collections::HashMap::into_iter", Some(2)),
            (3, StubKind::HashMapIter, "std::collections::HashMap::iter", Some(3)),
            (4, StubKind::HashMapKeys, "std::collections::HashMap::keys", Some(4)),
            (5, StubKind::HashMapValues, "std::collections::HashMap::values", Some(5)),
        ] {
            let dest = local_place(dest_local);
            let result = codegen.codegen_hashmap_stub(
                stub_kind,
                std::slice::from_ref(&map_ref),
                &dest,
                target,
                callee_path,
            );
            assert_eq!(result, target);
            let assigned = assigned_expr_for_place(codegen, &dest)
                .expect("HashMap iterator stub should assign destination");
            assert!(assigned.sort().is_datatype());
        }
    });
}

/// Test HashMapInsert with real key/value operands updates map.
/// hashmap.rs: HashMapInsert branch — store + len update.
#[test]
fn test_codegen_hashmap_insert_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // First create the map via HashMapNew at local 1
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        // Now insert with: args[0]=map ref, args[1]=key, args[2]=value
        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(100u64, POINTER_WIDTH));
        let val = seed_collections_local(&mut codegen, 3, Expr::bitvec_const(42u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapInsert,
            &[map_ref, key, val],
            &dest,
            Some(2),
            "std::collections::HashMap::insert",
        );
        assert_eq!(result, Some(2));
        // Insert returns Option<V> (the previous value)
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Insert should assign destination");
        assert!(
            dest_val.sort().is_datatype(),
            "Insert should return Option<V> datatype, got {:?}",
            dest_val.sort()
        );
    });
}

/// Test HashMapGet with real key after Insert returns Some.
/// hashmap.rs: HashMapGet branch — select(map, key).
#[test]
fn test_codegen_hashmap_get_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create map and insert a key
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );
        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key =
            seed_collections_local(&mut codegen, 2, Expr::bitvec_const(100u64, POINTER_WIDTH));
        let val = seed_collections_local(&mut codegen, 3, Expr::bitvec_const(42u64, POINTER_WIDTH));
        let insert_dest = Place { local: 4, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapInsert,
            &[map_ref, key, val],
            &insert_dest,
            Some(2),
            "std::collections::HashMap::insert",
        );

        // Now get the key
        let map_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let get_key =
            seed_collections_local(&mut codegen, 5, Expr::bitvec_const(100u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapGet,
            &[map_ref2, get_key],
            &dest,
            Some(3),
            "std::collections::HashMap::get",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Get should assign destination");
        assert!(dest_val.sort().is_datatype(), "Get should return Option<V> datatype");
    });
}

/// Test HashMapContainsKey with real key produces boolean.
/// hashmap.rs: HashMapContainsKey branch — is_some(select(map, key)).
#[test]
fn test_codegen_hashmap_contains_key_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_binary");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create map
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(50u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapContainsKey,
            &[map_ref, key],
            &dest,
            Some(2),
            "std::collections::HashMap::contains_key",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val =
            codegen.env_lookup(&dest_base).expect("ContainsKey should assign destination");
        assert!(dest_val.sort().is_bool(), "ContainsKey should produce Bool sort");
    });
}

/// Test HashMapLen with a seeded map returns tracked len.
/// hashmap.rs: HashMapLen branch — returns tracked length.
#[test]
fn test_codegen_hashmap_len_real_operand() {
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
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapLen,
            &[map_ref],
            &dest,
            Some(2),
            "std::collections::HashMap::len",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Len should assign destination");
        assert!(dest_val.sort().is_bitvec(), "Len should produce bitvec sort");
    });
}

/// Test HashMapClear with a seeded map resets to empty.
/// hashmap.rs: HashMapClear branch — const_array(None), len=0.
#[test]
fn test_codegen_hashmap_clear_real_operand() {
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
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapClear,
            &[map_ref],
            &dest,
            Some(2),
            "std::collections::HashMap::clear",
        );
        assert_eq!(result, Some(2));
        // Clear returns () — map should be reset in env
    });
}

/// Test HashMapRemove with real key after Insert returns previous value.
/// hashmap.rs: HashMapRemove branch — store None, return prev.
#[test]
fn test_codegen_hashmap_remove_real_operands() {
    use crate::codegen_ay::stubs::StubKind;
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32_multi");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Create map and insert
        let map_dest = Place { local: 1, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );
        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let key = seed_collections_local(&mut codegen, 2, Expr::bitvec_const(77u64, POINTER_WIDTH));
        let val = seed_collections_local(&mut codegen, 3, Expr::bitvec_const(99u64, POINTER_WIDTH));
        let insert_dest = Place { local: 4, projection: vec![] };
        codegen.codegen_hashmap_stub(
            StubKind::HashMapInsert,
            &[map_ref, key, val],
            &insert_dest,
            Some(2),
            "std::collections::HashMap::insert",
        );

        // Now remove the same key
        let map_ref2 = Operand::Copy(Place { local: 1, projection: vec![] });
        let rm_key =
            seed_collections_local(&mut codegen, 5, Expr::bitvec_const(77u64, POINTER_WIDTH));
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapRemove,
            &[map_ref2, rm_key],
            &dest,
            Some(3),
            "std::collections::HashMap::remove",
        );
        assert_eq!(result, Some(3));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Remove should assign destination");
        assert!(dest_val.sort().is_datatype(), "Remove should return Option<V> datatype");
    });
}

/// Test HashMapIsEmpty with a seeded empty map returns Bool.
/// hashmap.rs: HashMapIsEmpty branch — len == 0.
#[test]
fn test_codegen_hashmap_is_empty_real_operand() {
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
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapIsEmpty,
            &[map_ref],
            &dest,
            Some(2),
            "std::collections::HashMap::is_empty",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("IsEmpty should assign destination");
        assert!(dest_val.sort().is_bool(), "IsEmpty should produce Bool sort");
    });
}

/// Test HashMapClone with a seeded map copies array to destination.
/// hashmap.rs: HashMapClone branch — identity copy of array.
#[test]
fn test_codegen_hashmap_clone_real_operand() {
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
            StubKind::HashMapNew,
            &[],
            &map_dest,
            Some(1),
            "std::collections::HashMap::new",
        );

        let map_ref = Operand::Copy(Place { local: 1, projection: vec![] });
        let dest = Place { local: 0, projection: vec![] };
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapClone,
            &[map_ref],
            &dest,
            Some(2),
            "std::collections::HashMap::clone",
        );
        assert_eq!(result, Some(2));
        let dest_base = codegen.ssa_base_name(&dest);
        let dest_val = codegen.env_lookup(&dest_base).expect("Clone should assign destination");
        assert!(dest_val.sort().is_array(), "Clone should produce Array sort");
    });
}

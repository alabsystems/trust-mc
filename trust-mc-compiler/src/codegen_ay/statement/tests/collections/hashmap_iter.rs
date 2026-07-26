// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for collections/hashmap_iter.rs: HashMap iterator creation.
//!
//! Covers `make_hashmap_into_iter` (private fn) via the public dispatch path:
//! - `codegen_hashmap_stub(HashMapIntoIter, ...)` → `make_hashmap_into_iter`
//! - `codegen_hashmap_stub(HashMapIter, ...)` → `make_hashmap_into_iter`
//! - `codegen_hashmap_stub(HashMapKeys, ...)` → `make_hashmap_into_iter`
//! - `codegen_hashmap_stub(HashMapValues, ...)` → `make_hashmap_into_iter`
//!
//! Tests verify: sort structure (fld_data, fld_present, fld_keys, fld_pos, fld_len),
//! membership constraint emission, tracked length integration.
//!
//! Part of #2303: zero-coverage production file test coverage.

use super::*;
use crate::codegen_ay::stubs::StubKind;
use std::sync::Arc;

fn with_hashmap_codegen<F>(callback: F)
where
    F: FnOnce(&mut StatementCodegen<'_, '_, '_>) + Send,
{
    with_test_ay_ctx_for_source(COLLECTIONS_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_u32");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        callback(&mut codegen);
    });
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

/// Create a HashMap-like Array<bv32, Option<bv64>> for testing.
fn make_test_hashmap(codegen: &mut StatementCodegen<'_, '_, '_>) -> (Expr, String) {
    let value_sort = Sort::bitvec(64);
    let option_sort = codegen.make_option_sort(value_sort);
    let map_sort = Sort::array(Sort::bitvec(32), option_sort);
    let map_name = codegen.ctx.fresh_name("test_hashmap");
    let map = codegen.ctx.declare_var(&map_name, map_sort);

    let fn_name =
        codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
    let map_base = format!("{}::local_2", fn_name);
    codegen.env_update(map_base.clone(), map.clone());

    (map, map_base)
}

/// Set up a reference operand that resolves to a given base name.
fn setup_ref_operand(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    ref_local: usize,
    target_base: &str,
) -> Operand {
    let fn_name =
        codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
    let ref_base = format!("{}::local_{}", fn_name, ref_local);
    codegen.env_update(ref_base.clone(), Expr::bitvec_const(0x6000u64, POINTER_WIDTH));
    codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(target_base));
    Operand::Copy(Place { local: ref_local, projection: vec![] })
}

// =============================================================================
// HashMapIntoIter — exercises make_hashmap_into_iter
// =============================================================================

/// Test HashMapIntoIter with real map produces iterator datatype with correct fields.
/// hashmap_iter.rs: make_hashmap_into_iter — full path (map resolved, iter constructed).
#[test]
fn test_codegen_hashmap_into_iter_produces_iterator_datatype() {
    with_hashmap_codegen(|codegen| {
        let (_map, map_base) = make_test_hashmap(codegen);
        let ref_op = setup_ref_operand(codegen, 1, &map_base);

        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapIntoIter,
            &[ref_op],
            &dest,
            Some(1),
            "std::collections::HashMap::into_iter",
        );
        assert_eq!(result, Some(1));

        let dest_expr = assigned_expr_for_place(codegen, &dest)
            .expect("HashMapIntoIter should assign destination");
        assert!(
            dest_expr.sort().is_datatype(),
            "HashMapIntoIter should produce datatype sort, got {:?}",
            dest_expr.sort()
        );

        let sort = dest_expr.sort();
        let dt_name = sort.datatype_name().unwrap_or("");
        assert!(
            dt_name.starts_with("HashMapIntoIter_"),
            "Iterator sort name should start with 'HashMapIntoIter_', got '{}'",
            dt_name
        );

        // Part of #3057: DT-free — fld_data + fld_present replace fld_map
        assert!(
            sort.datatype_has_field("fld_data"),
            "HashMapIntoIter should have fld_data (#3057)"
        );
        assert!(
            sort.datatype_has_field("fld_present"),
            "HashMapIntoIter should have fld_present (#3057)"
        );
        assert!(sort.datatype_has_field("fld_keys"), "HashMapIntoIter should have fld_keys");
        assert!(sort.datatype_has_field("fld_pos"), "HashMapIntoIter should have fld_pos");
        assert!(sort.datatype_has_field("fld_len"), "HashMapIntoIter should have fld_len");
    });
}

/// Test HashMapIntoIter emits membership constraint (forall soundness).
/// hashmap_iter.rs: make_hashmap_into_iter — membership constraint assertion.
#[test]
fn test_codegen_hashmap_into_iter_emits_membership_constraint() {
    with_hashmap_codegen(|codegen| {
        let before = codegen.ctx.bmc_vc.constraints.len();

        let (_map, map_base) = make_test_hashmap(codegen);
        let ref_op = setup_ref_operand(codegen, 1, &map_base);

        let dest = local_place(0);
        codegen.codegen_hashmap_stub(
            StubKind::HashMapIntoIter,
            &[ref_op],
            &dest,
            Some(2),
            "std::collections::HashMap::into_iter",
        );

        let after = codegen.ctx.bmc_vc.constraints.len();
        assert!(
            after > before,
            "make_hashmap_into_iter should emit constraints \
             (membership + possibly len >= 0); before={}, after={}",
            before,
            after
        );
    });
}

/// Test HashMapIntoIter uses tracked length when available.
/// hashmap_iter.rs: make_hashmap_into_iter — tracked length path.
#[test]
fn test_codegen_hashmap_into_iter_uses_tracked_length() {
    with_hashmap_codegen(|codegen| {
        let (_map, map_base) = make_test_hashmap(codegen);

        // Pre-seed a tracked length for this map
        let tracked_len = Expr::bitvec_const(5u64, POINTER_WIDTH);
        codegen.hashmap_len_symbols.insert(map_base.as_str().into(), tracked_len);

        let before = codegen.ctx.bmc_vc.constraints.len();
        let ref_op = setup_ref_operand(codegen, 1, &map_base);

        let dest = local_place(0);
        codegen.codegen_hashmap_stub(
            StubKind::HashMapIntoIter,
            &[ref_op],
            &dest,
            Some(3),
            "std::collections::HashMap::into_iter",
        );

        let after = codegen.ctx.bmc_vc.constraints.len();
        // With tracked length, we should have the membership constraint
        // but NOT the len >= 0 constraint (tracked length is concrete).
        // Still should have at least the membership constraint.
        assert!(
            after > before,
            "make_hashmap_into_iter with tracked length should still emit membership constraint"
        );

        // Verify the destination was assigned
        let dest_expr = assigned_expr_for_place(codegen, &dest)
            .expect("HashMapIntoIter should assign destination");
        assert!(dest_expr.sort().is_datatype());
    });
}

// =============================================================================
// HashMapIter — also exercises make_hashmap_into_iter
// =============================================================================

/// Test HashMapIter (borrow path) produces same iterator structure.
/// hashmap_iter.rs: make_hashmap_into_iter via HashMapIter stub.
#[test]
fn test_codegen_hashmap_iter_borrow_path_produces_iterator() {
    with_hashmap_codegen(|codegen| {
        let (_map, map_base) = make_test_hashmap(codegen);
        let ref_op = setup_ref_operand(codegen, 1, &map_base);

        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapIter,
            &[ref_op],
            &dest,
            Some(4),
            "std::collections::HashMap::iter",
        );
        assert_eq!(result, Some(4));

        let dest_expr =
            assigned_expr_for_place(codegen, &dest).expect("HashMapIter should assign destination");
        assert!(dest_expr.sort().is_datatype(), "HashMapIter should produce datatype sort");
        // Part of #3057: DT-free — fld_data + fld_present replace fld_map
        assert!(
            dest_expr.sort().datatype_has_field("fld_data"),
            "HashMapIter should have fld_data (#3057)"
        );
        assert!(
            dest_expr.sort().datatype_has_field("fld_present"),
            "HashMapIter should have fld_present (#3057)"
        );
    });
}

// =============================================================================
// HashMapKeys / HashMapValues — also exercise make_hashmap_into_iter
// =============================================================================

/// Test HashMapKeys and HashMapValues produce iterator datataypes.
/// hashmap_iter.rs: make_hashmap_into_iter via HashMapKeys/HashMapValues stubs.
#[test]
fn test_codegen_hashmap_keys_values_produce_iterators() {
    for (stub_kind, callee) in [
        (StubKind::HashMapKeys, "std::collections::HashMap::keys"),
        (StubKind::HashMapValues, "std::collections::HashMap::values"),
    ] {
        with_hashmap_codegen(|codegen| {
            let (_map, map_base) = make_test_hashmap(codegen);
            let ref_op = setup_ref_operand(codegen, 1, &map_base);

            let dest = local_place(0);
            let result = codegen.codegen_hashmap_stub(stub_kind, &[ref_op], &dest, Some(5), callee);
            assert_eq!(result, Some(5));

            let dest_expr = assigned_expr_for_place(codegen, &dest)
                .expect(&format!("{:?} should assign destination", stub_kind));
            assert!(
                dest_expr.sort().is_datatype(),
                "{:?} should produce datatype sort, got {:?}",
                stub_kind,
                dest_expr.sort()
            );
        });
    }
}

/// Test HashMapIntoIter with unresolved ref falls back to symbolic.
/// hashmap_iter.rs: make_hashmap_into_iter is NOT called when map_expr is None.
#[test]
fn test_codegen_hashmap_into_iter_unresolved_ref_symbolic_fallback() {
    with_hashmap_codegen(|codegen| {
        // Use a local that has no env entry and no ref_pointees mapping
        let unknown_op = Operand::Copy(Place { local: 9, projection: vec![] });

        let dest = local_place(0);
        let result = codegen.codegen_hashmap_stub(
            StubKind::HashMapIntoIter,
            &[unknown_op],
            &dest,
            Some(6),
            "std::collections::HashMap::into_iter",
        );
        assert_eq!(result, Some(6));

        // Unresolved ref → codegen_symbolic_result assigns a symbolic value
        // based on the destination's MIR type. Since probe_u32 returns u32,
        // local_0 will get a bitvec(32) symbolic result.
        let dest_expr = assigned_expr_for_place(codegen, &dest);
        // codegen_symbolic_result should assign to dest (sort inferred from MIR type).
        // If it returns None, the fallback silently dropped the assignment — that's a bug.
        assert!(
            dest_expr.is_some(),
            "HashMapIntoIter fallback should assign symbolic result to destination"
        );
    });
}

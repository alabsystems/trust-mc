// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_stmt_store.rs — array element store coverage (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_array_index_store() {
    // (#2188) Exercise handle_array_element_store: arr[idx] = value
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_store(mut arr: [u32; 4], idx: usize, val: u32) -> [u32; 4] {
            arr[idx] = val;
            arr
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_store");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_store", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_array_store", bb_count);

        // Array store should produce Array-sorted state vars (in relations or declare-var)
        assert_relation_has_arg_sort(
            &vc,
            "probe_array_store",
            ay_bindings::Sort::is_array,
            "Array",
        );

        // Transition rules should have constraints (the store operation)
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "array index store should have constrained transition rules for the store"
        );

        // Constraint content: at least one constraint must contain a AY Store operation
        // (not just "any constraint exists" — the store must actually encode arr' = store(arr, idx, val))
        let is_store = |e: &ay_bindings::Expr| matches!(e.value(), ExprValue::Store { .. });
        assert_rule_contains_expr_kind(&vc, "probe_array_store", is_store, "Store");

        // The Store's array operand should have Array sort
        let store_has_array_sort = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e: &ay_bindings::Expr| {
                    matches!(e.value(), ExprValue::Store { array, .. } if array.sort().is_array())
                })
            })
        });
        assert!(
            store_has_array_sort,
            "array index store constraint should contain Store with Array-sorted array operand"
        );
    });
}

#[test]
fn test_mir_to_chc_array_constant_index_store() {
    // (#2188) Exercise handle_array_element_store with ConstantIndex path
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_const_index_store(mut arr: [u32; 4]) -> [u32; 4] {
            arr[0] = 100;
            arr[1] = 200;
            arr
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_index_store");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_const_index_store", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_const_index_store", bb_count);

        // Constant index store should also produce Array-sorted state vars (in relations or declare-var)
        assert_relation_has_arg_sort(
            &vc,
            "probe_const_index_store",
            ay_bindings::Sort::is_array,
            "Array",
        );

        // Two stores → transition rules should have constraints
        let constrained_count = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_count >= 1,
            "constant index store should have constrained transition rules, got {constrained_count}"
        );

        // Constraint content: constraints must contain AY Store operations
        let is_store = |e: &ay_bindings::Expr| matches!(e.value(), ExprValue::Store { .. });
        assert_rule_contains_expr_kind(&vc, "probe_const_index_store", is_store, "Store");

        // Two constant-index stores (arr[0]=100, arr[1]=200) should produce Store ops
        // with bitvec constant indices. Verify via SMT-LIB2 serialization.
        let store_count = count_constraint_str(&vc, |s| s.contains("store"));
        assert!(
            store_count >= 2,
            "two constant-index stores should produce ≥2 store constraints, got {store_count}"
        );
    });
}

#[test]
fn test_mir_to_chc_mem_level_deref_store() {
    // (#2188) Exercise handle_deref_store_mem_level: *ptr = value at Mem level
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_deref_store(ptr: *mut u32) {
            unsafe { *ptr = 42; }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_store");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_deref_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_deref_store", bb_count);

        // Mem-level deref store operates on pointers → should have bitvec state vars
        // for the pointer argument (BV64 on 64-bit)
        let has_bv =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bitvec));
        assert!(has_bv, "Mem-level deref store VC should have bitvec state vars for pointer arg");

        // Mem level should have Array sort for heap memory model
        let has_array =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_array));
        assert!(
            has_array,
            "Mem-level deref store VC should have Array state var for the heap model"
        );

        // Constraint content: heap-model store should produce AY Store operations
        // encoding the memory write (*ptr = 42 → mem' = store(mem, ptr_addr, 42))
        let is_store = |e: &ay_bindings::Expr| matches!(e.value(), ExprValue::Store { .. });
        assert_rule_contains_expr_kind(&vc, "probe_deref_store", is_store, "Store");

        // Verify the Store targets the heap (Array sort), not a spurious non-heap array
        let heap_store = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e: &ay_bindings::Expr| {
                    matches!(e.value(), ExprValue::Store { array, .. } if array.sort().is_array())
                })
            })
        });
        assert!(heap_store, "Mem-level deref store should contain Store on Array-sorted heap var");
    });
}

#[test]
fn test_mir_to_chc_ref_target_scalar_store() {
    // (#2188) Exercise handle_deref_store_via_ref_targets for scalar ref store
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ref_store(x: &mut u32) {
            *x = 99;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_store");
        let body = instance.body().expect("function body");

        // Reg level: uses ref_targets for inlining
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_store", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_ref_store", bb_count);

        // Reg-level ref store on &mut u32 → should have bitvec state vars
        // (BV64 for the pointer, and/or BV32 for the u32 value)
        let has_bv =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bitvec));
        assert!(has_bv, "Reg-level ref store VC should have bitvec state vars for pointer/value");

        // Reg-level ref_targets inlining may fold the deref store into a single BB;
        // verify that at least some rules carry constraints encoding the assignment
        let any_constrained = vc.rules.iter().any(|r| !r.body.constraints.is_empty());
        assert!(
            any_constrained,
            "Reg-level ref store should have at least one rule with constraints encoding the store"
        );

        // Constraint content: ref-target scalar store should produce Eq constraints
        // encoding the assignment (x_out = 99). The codegen uses coerce_eq_constraint
        // which produces Eq(var, value) or equivalent.
        let is_eq = |e: &ay_bindings::Expr| matches!(e.value(), ExprValue::Eq(..));
        assert_rule_contains_expr_kind(&vc, "probe_ref_store", is_eq, "Eq");

        // The Eq constraint should reference a bitvec constant for the value 99
        let has_const_99 =
            any_constraint_str(&vc, |s| s.contains("#x00000063") || s.contains("99"));
        assert!(
            has_const_99,
            "Reg-level ref store should encode the constant value 99 (0x63) in constraints"
        );
    });
}

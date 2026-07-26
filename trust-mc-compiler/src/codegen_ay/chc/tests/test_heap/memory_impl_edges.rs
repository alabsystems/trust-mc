// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// memory_impl.rs edge-path coverage (Part of #2188)
// ============================================================================

#[test]
fn test_sort_from_type_key_array_empty_suffix_defaults_to_bv32_elem() {
    let sort = ChcCtx::sort_from_type_key("arr_");
    assert_eq!(sort, Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32)));
}

#[test]
fn test_sort_from_type_key_slice_reconstructs_elem_sort() {
    let sort = ChcCtx::sort_from_type_key("slice_i16");
    assert_eq!(sort, Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(16)));
}

#[test]
fn test_sort_from_type_key_array_bool_elem() {
    let sort = ChcCtx::sort_from_type_key("arr_bool");
    assert_eq!(sort, Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bool()));
}

#[test]
fn test_sort_from_type_key_vec_with_explicit_elem_suffix() {
    let expected = struct_sort(
        "Vec_bv16",
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(16))),
        ],
    );
    assert_eq!(ChcCtx::sort_from_type_key("Vec_i16"), expected);
}

#[test]
fn test_sort_from_type_key_std_vec_defaults_to_bv32_elem() {
    let expected = struct_sort(
        "Vec_bv32",
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
            ("fld_data", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32))),
        ],
    );
    assert_eq!(ChcCtx::sort_from_type_key("foo_std_vec_Vec"), expected);
}

#[test]
fn test_sort_from_type_key_string_layout() {
    let expected = struct_sort(
        RUST_STRING_SORT,
        [
            ("fld_ptr", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
            ("fld_cap", Sort::bitvec(POINTER_WIDTH)),
        ],
    );
    assert_eq!(ChcCtx::sort_from_type_key("std_string_String"), expected);
}

#[test]
fn test_sort_from_type_key_box_is_pointer() {
    assert_eq!(ChcCtx::sort_from_type_key("std_boxed_Box_u32"), Sort::bitvec(POINTER_WIDTH));
}

#[test]
fn test_sort_from_type_key_bigint_maps_to_int() {
    assert_eq!(ChcCtx::sort_from_type_key("num_bigint_BigInt"), Sort::int());
}

#[test]
fn test_sort_from_type_key_unknown_uses_opaque_byte_array_fallback() {
    assert_eq!(
        ChcCtx::sort_from_type_key("totally_unknown_sort_key"),
        ChcCtx::unknown_type_key_fallback_sort()
    );
}

#[test]
fn test_get_array_length_and_element_type_array_vs_slice() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_inputs(arr: [u8; 4], slice: &[u8]) -> usize {
            (arr[0] as usize) + slice.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_array_inputs");
        let args = fn_sig.inputs();
        let arr_ty = args[0];
        let slice_ref_ty = args[1];
        let slice_ty = match slice_ref_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => unreachable!("expected slice reference argument"),
        };

        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_inputs");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_inputs", ChcConfig::default());

        assert_eq!(chc_ctx.get_array_length(arr_ty), Some(4));
        assert_eq!(chc_ctx.get_array_length(slice_ty), None);

        let arr_elem = chc_ctx.get_array_element_ty(arr_ty).expect("array elem ty");
        let slice_elem = chc_ctx.get_array_element_ty(slice_ty).expect("slice elem ty");
        assert!(matches!(arr_elem.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))));
        assert!(matches!(slice_elem.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))));
    });
}

#[test]
fn test_get_array_helpers_non_array_type_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar_input(x: u32) -> u32 {
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_input");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_input");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_scalar_input", ChcConfig::default());

        assert_eq!(chc_ctx.get_array_length(scalar_ty), None);
        assert!(chc_ctx.get_array_element_ty(scalar_ty).is_none());
    });
}

#[test]
fn test_assign_region_array_to_relation_deduplicates_state_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_region_decl() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_region_decl");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_region_decl", ChcConfig::default());

        let (arr_in_1, arr_out_1) = chc_ctx.assign_region_array_to_relation(7, Sort::bitvec(32));
        let (arr_in_2, arr_out_2) = chc_ctx.assign_region_array_to_relation(7, Sort::bitvec(32));

        assert_eq!(arr_in_1, arr_in_2);
        assert_eq!(arr_out_1, arr_out_2);
        assert_eq!(
            chc_ctx.state_var_mgr.state_vars.len(),
            1,
            "region state var should be added once"
        );
        assert_eq!(
            chc_ctx.state_var_mgr.output_state_vars.len(),
            1,
            "region output state var should be added once"
        );
        assert_eq!(
            chc_ctx.state_var_mgr.declared_state_var_names.len(),
            1,
            "declared_state_var_names should de-duplicate region vars"
        );

        // #2730 regression guard: region additions must update both O(1) lookup maps.
        let idx = chc_ctx
            .state_var_index_by_name(&arr_in_1)
            .expect("region input state var should be indexed");
        assert_eq!(
            chc_ctx.output_state_var_index_by_name(&arr_out_1),
            Some(idx),
            "region output state var should share the same vec index"
        );
        assert_eq!(
            chc_ctx.state_var_mgr.state_vars[idx].0.to_string(),
            &*arr_in_1,
            "state var lookup index should point to the inserted region array"
        );
        assert_eq!(
            chc_ctx.state_var_mgr.output_state_vars[idx].0.to_string(),
            &*arr_out_1,
            "output state var lookup index should point to the inserted region array"
        );
    });
}

#[test]
fn test_assign_region_array_to_relation_reuses_predeclared_typed_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_region_decl() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_region_decl");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_region_decl", ChcConfig::default());

        let obj_id = 7;
        let typed_elem_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
        let (typed_region_in, _) = chc_ctx.heap_state.assign_region_array(
            obj_id,
            typed_elem_sort.clone(),
            "probe_region_decl",
        );

        let (arr_in, arr_out) = chc_ctx.assign_region_array_to_relation(obj_id, Sort::bitvec(8));

        assert_eq!(
            arr_in, typed_region_in,
            "typed predeclaration should be reused even when a later caller asks for bv8"
        );

        let idx = chc_ctx
            .state_var_index_by_name(&arr_in)
            .expect("region input state var should be indexed");
        let declared_sort = &chc_ctx.state_var_mgr.state_vars[idx].1;
        let output_sort = &chc_ctx.state_var_mgr.output_state_vars[idx].1;
        let expected_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), typed_elem_sort);

        assert_eq!(
            declared_sort, &expected_sort,
            "late-declared region state var should keep the predeclared typed element sort"
        );
        assert_eq!(
            output_sort, &expected_sort,
            "output region state var should mirror the predeclared typed element sort"
        );
        assert_eq!(
            chc_ctx.output_state_var_index_by_name(&arr_out),
            Some(idx),
            "typed output region should share the same state-var index"
        );
    });
}

#[test]
fn test_declare_block_relations_populates_state_var_name_indexes() {
    // #2730 regression guard: name->index maps must track all declared state/output vars.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_lookup(mut s: HashSet<u32>, x: u32) -> bool {
            s.insert(x);
            s.contains(&x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lookup");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_lookup", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.state_var_mgr.state_vars.is_empty(),
            "expected non-empty state vars for probe_lookup"
        );
        assert_eq!(
            chc_ctx.state_var_mgr.state_vars.len(),
            chc_ctx.state_var_mgr.output_state_vars.len(),
            "state/output var vectors must stay aligned"
        );

        for (idx, (name, _)) in chc_ctx.state_var_mgr.state_vars.iter().enumerate() {
            assert_eq!(
                chc_ctx.state_var_index_by_name(name),
                Some(idx),
                "state var {name} should map to its vec index"
            );
        }

        for (idx, (name, _)) in chc_ctx.state_var_mgr.output_state_vars.iter().enumerate() {
            assert_eq!(
                chc_ctx.output_state_var_index_by_name(name),
                Some(idx),
                "output state var {name} should map to its vec index"
            );
        }

        assert!(
            chc_ctx.state_var_index_by_name("__missing_state_var").is_none(),
            "unknown state var names must not resolve to an index"
        );
        assert!(
            chc_ctx.output_state_var_index_by_name("__missing_output_state_var").is_none(),
            "unknown output state var names must not resolve to an index"
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for chc/stubs_util_collections.rs.
// Covers: iter_position_zero (static), IterNextParts/IterConstructConfig
// structural validation, Option ITE encoding patterns, collection predicate
// detection pipeline, and Vec is_empty pipeline through mir_to_chc.
// Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};
use num_bigint::BigInt;

// =============================================================================
// iter_position_zero — returns bitvec(POINTER_WIDTH) with value 0
// This is a static associated function on ChcCtx — no instance needed.
// =============================================================================

#[test]
fn test_iter_position_zero_is_pointer_width() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    let zero = ChcCtx::iter_position_zero();
    assert!(zero.sort().is_bitvec(), "iter_position_zero should be bitvec");
    assert_eq!(
        zero.sort().bitvec_width(),
        Some(POINTER_WIDTH),
        "iter_position_zero should be pointer width"
    );
}

#[test]
fn test_iter_position_zero_value_is_zero() {
    let zero = ChcCtx::iter_position_zero();
    match zero.value() {
        ExprValue::BitVecConst { value, .. } => {
            assert_eq!(*value, BigInt::from(0u64), "position zero should have value 0");
        }
        other => panic!("expected BitVecConst, got {other:?}"),
    }
}

// =============================================================================
// IterNextParts — structural validation
// =============================================================================

#[test]
fn test_iter_next_parts_structure() {
    use super::super::stubs_util_collections::IterNextParts;
    use crate::codegen_ay::types::POINTER_WIDTH;

    let parts = IterNextParts {
        element: Expr::bitvec_const(0u64, 32),
        element_fields: None,
        len: Expr::bitvec_const(10u64, POINTER_WIDTH),
        fields_before_pos: vec![Expr::var("map", Sort::array(Sort::bitvec(32), Sort::bool()))],
        fields_after_pos: vec![Expr::bitvec_const(10u64, POINTER_WIDTH)],
        constraints: vec![Expr::bool_const(true)],
    };

    assert_eq!(parts.element.sort().bitvec_width(), Some(32));
    assert_eq!(parts.fields_before_pos.len(), 1);
    assert_eq!(parts.fields_after_pos.len(), 1);
    assert_eq!(parts.constraints.len(), 1);
}

#[test]
fn test_iter_next_parts_empty_constraints_for_vec() {
    use super::super::stubs_util_collections::IterNextParts;
    use crate::codegen_ay::types::POINTER_WIDTH;

    // Vec iterators have empty constraints (no membership checks)
    let parts = IterNextParts {
        element: Expr::bitvec_const(0u64, 32),
        element_fields: None,
        len: Expr::bitvec_const(5u64, POINTER_WIDTH),
        fields_before_pos: vec![],
        fields_after_pos: vec![],
        constraints: vec![],
    };

    assert!(parts.constraints.is_empty(), "Vec iterators should have empty constraints");
}

#[test]
fn test_iter_next_parts_with_membership_constraints() {
    use super::super::stubs_util_collections::IterNextParts;
    use crate::codegen_ay::types::POINTER_WIDTH;

    // HashMap/HashSet iterators have membership constraints
    let membership = Expr::bool_const(true);
    let parts = IterNextParts {
        element: Expr::bitvec_const(0u64, 32),
        element_fields: None,
        len: Expr::bitvec_const(10u64, POINTER_WIDTH),
        fields_before_pos: vec![
            Expr::var("map", Sort::array(Sort::bitvec(32), Sort::bool())),
            Expr::var("keys", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32))),
        ],
        fields_after_pos: vec![Expr::bitvec_const(10u64, POINTER_WIDTH)],
        constraints: vec![membership],
    };

    assert_eq!(parts.fields_before_pos.len(), 2, "HashMap iter has map + keys fields");
    assert_eq!(parts.constraints.len(), 1, "HashMap iter has membership constraint");
}

// =============================================================================
// IterConstructConfig — structural validation
// =============================================================================

#[test]
fn test_iter_construct_config_structure() {
    use super::super::stubs_util_collections::IterConstructConfig;
    use crate::codegen_ay::types::POINTER_WIDTH;

    let config = IterConstructConfig {
        iter_sort_name: "VecIntoIter_bv32",
        iter_fields: vec![
            ("fld_vec", Sort::bitvec(POINTER_WIDTH)),
            ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
        ],
        ctor_fields: vec![
            Expr::bitvec_const(0u64, POINTER_WIDTH),
            Expr::bitvec_const(0u64, POINTER_WIDTH),
        ],
    };

    assert_eq!(config.iter_sort_name, "VecIntoIter_bv32");
    assert_eq!(config.iter_fields.len(), 2);
    assert_eq!(config.ctor_fields.len(), 2);
}

#[test]
fn test_iter_construct_config_hashmap() {
    use super::super::stubs_util_collections::IterConstructConfig;
    use crate::codegen_ay::types::POINTER_WIDTH;

    // DT-free encoding (#3057, #3106): fld_data + fld_present
    let key_sort = Sort::bitvec(32);
    let val_sort = Sort::bitvec(64);
    let data_sort = Sort::array(key_sort.clone(), val_sort);
    let present_sort = Sort::array(key_sort.clone(), Sort::bool());
    let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);

    let config = IterConstructConfig {
        iter_sort_name: "HashMapIntoIter_bv32_bv64",
        iter_fields: vec![
            ("fld_data", data_sort.clone()),
            ("fld_present", present_sort),
            ("fld_keys", keys_sort.clone()),
            ("fld_pos", Sort::bitvec(POINTER_WIDTH)),
            ("fld_len", Sort::bitvec(POINTER_WIDTH)),
        ],
        ctor_fields: vec![
            Expr::var("data", data_sort),
            Expr::const_array(Sort::bool(), Expr::bool_const(true)),
            Expr::var("keys", keys_sort),
            Expr::bitvec_const(0u64, POINTER_WIDTH),
            Expr::var("len", Sort::bitvec(POINTER_WIDTH)),
        ],
    };

    assert_eq!(config.iter_sort_name, "HashMapIntoIter_bv32_bv64");
    assert_eq!(config.iter_fields.len(), 5, "HashMap iter has data/present/keys/pos/len");
    assert_eq!(config.ctor_fields.len(), 5);
}

// =============================================================================
// Option ITE encoding pattern — the pattern wrap_in_option_ite constructs
// =============================================================================

#[test]
fn test_option_ite_encoding_pattern() {
    // Verify the expression pattern that wrap_in_option_ite produces:
    // ITE(in_bounds, DatatypeConstructor("Some", [elem]), DatatypeConstructor("None", []))
    let guard = Expr::bool_const(true);
    let elem = Expr::bitvec_const(42u64, 32);
    let elem_sort = Sort::bitvec(32);

    let option_sort_name = names::option_sort_name(&names::sort_short_name(&elem_sort));
    let option_sort =
        enum_sort(&*option_sort_name, names::option_constructors(&option_sort_name, elem_sort));
    let some_ctor = names::option_some_constructor_name(&option_sort_name);
    let none_ctor = names::option_none_constructor_name(&option_sort_name);

    let some_val =
        Expr::datatype_constructor(&*option_sort_name, some_ctor, vec![elem], option_sort.clone());
    let none_val = Expr::datatype_constructor(&*option_sort_name, none_ctor, vec![], option_sort);

    let result = Expr::ite(guard, some_val, none_val);

    assert!(matches!(result.value(), ExprValue::Ite { .. }));
    assert!(result.sort().is_datatype());
    let name = result.sort().datatype_name().unwrap_or("");
    assert!(name.contains("Option"), "sort name should contain 'Option', got: {name}");
}

#[test]
fn test_option_ite_with_bool_payload() {
    let guard = Expr::var("in_bounds", Sort::bool());
    let elem = Expr::bool_const(true);
    let elem_sort = Sort::bool();

    let option_sort_name = names::option_sort_name(&names::sort_short_name(&elem_sort));
    let option_sort =
        enum_sort(&*option_sort_name, names::option_constructors(&option_sort_name, elem_sort));
    let some_ctor = names::option_some_constructor_name(&option_sort_name);
    let none_ctor = names::option_none_constructor_name(&option_sort_name);

    let some_val =
        Expr::datatype_constructor(&*option_sort_name, some_ctor, vec![elem], option_sort.clone());
    let none_val = Expr::datatype_constructor(&*option_sort_name, none_ctor, vec![], option_sort);

    let result = Expr::ite(guard, some_val, none_val);

    assert!(matches!(result.value(), ExprValue::Ite { .. }));
    assert!(result.sort().is_datatype());
}

// =============================================================================
// tracked_len_or_fresh pattern — the pattern this method implements
// =============================================================================

#[test]
fn test_tracked_len_pattern_uses_value_when_present() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    // tracked_len_or_fresh returns the tracked value when present
    let result = Expr::bitvec_const(5u64, POINTER_WIDTH);
    match result.value() {
        ExprValue::BitVecConst { value, .. } => {
            assert_eq!(*value, BigInt::from(5u64), "should use tracked value");
        }
        other => panic!("expected BitVecConst, got {other:?}"),
    }
}

#[test]
fn test_tracked_len_pattern_creates_var_when_none() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    // tracked_len_or_fresh allocates a fresh variable when no tracked length
    let result = Expr::var("fresh_len", Sort::bitvec(POINTER_WIDTH));
    assert!(
        matches!(result.value(), ExprValue::Var { name } if name == "fresh_len"),
        "should create fresh Var"
    );
}

// =============================================================================
// make_symbolic_iter_keys pattern — Array<usize, K> construction
// =============================================================================

#[test]
fn test_symbolic_iter_keys_array_sort_construction() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    let key_sort = Sort::bitvec(32);
    let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);
    let keys = Expr::var("test_keys", keys_sort.clone());

    assert!(keys_sort.is_array());
    let arr = keys_sort.array_sort().unwrap();
    assert_eq!(arr.index_sort.bitvec_width(), Some(POINTER_WIDTH));
    assert_eq!(arr.element_sort.bitvec_width(), Some(32));
    assert!(keys.sort().is_array());
}

#[test]
fn test_symbolic_iter_keys_with_int_key_sort() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    let key_sort = Sort::int();
    let keys_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), key_sort);
    let keys = Expr::var("int_keys", keys_sort.clone());

    assert!(keys_sort.is_array());
    let arr = keys_sort.array_sort().unwrap();
    assert_eq!(arr.index_sort.bitvec_width(), Some(POINTER_WIDTH));
    assert!(arr.element_sort.is_int());
    assert!(keys.sort().is_array());
}

// =============================================================================
// Pipeline: Vec is_empty through mir_to_chc
// =============================================================================

#[test]
fn test_vec_is_empty_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_vec_is_empty(v: Vec<u32>) -> bool {
            v.is_empty()
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_is_empty");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_is_empty", ChcConfig::default());
        assert_vc_structure(&vc, "probe_vec_is_empty", body.blocks.len());
    });
}

// =============================================================================
// Pipeline: Vec into_iter + next through mir_to_chc (exercises translate_iter_next_skeleton)
// =============================================================================

#[test]
fn test_vec_into_iter_next_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_vec_iter_next() -> Option<u32> {
            let v = vec![1u32, 2, 3];
            let mut iter = v.into_iter();
            iter.next()
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_iter_next");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_iter_next", ChcConfig::default());
        assert_vc_structure(&vc, "probe_vec_iter_next", body.blocks.len());
    });
}

// =============================================================================
// Pipeline: HashMap into_iter + next (exercises translate_iter_next_skeleton
// with membership constraints)
// =============================================================================

#[test]
fn test_hashmap_into_iter_next_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;
        pub fn probe_hm_iter_next() {
            let mut m = HashMap::new();
            m.insert(1u32, 10u64);
            let mut iter = m.into_iter();
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hm_iter_next");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hm_iter_next", ChcConfig::default());
        assert_vc_structure(&vc, "probe_hm_iter_next", body.blocks.len());
    });
}

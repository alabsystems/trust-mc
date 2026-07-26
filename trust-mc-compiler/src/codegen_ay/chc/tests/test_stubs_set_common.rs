// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for chc/stubs_set_common.rs.
// Covers: set CHC encoding via full pipeline (HashSet insert/contains/remove),
// set algebra expression patterns (Array<K, Bool> store/select), and
// convert_key_to_array_index sort coercion paths.
// Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::{Expr, ExprValue, Sort};

// =============================================================================
// Set algebra — Array<K, Bool> encoding of set operations
// =============================================================================

/// An empty set is a const_array(key_sort, false).
#[test]
fn test_empty_set_is_const_array_false() {
    let key_sort = Sort::bitvec(32);
    let empty = Expr::const_array(key_sort, Expr::bool_const(false));
    assert!(empty.sort().is_array());
    let arr = empty.sort().array_sort().unwrap();
    assert_eq!(arr.index_sort.bitvec_width(), Some(32));
    assert!(arr.element_sort.is_bool());
}

/// Set insert: store(set, key, true) produces a new Array<K, Bool>.
#[test]
fn test_set_insert_is_store_true() {
    let key_sort = Sort::bitvec(32);
    let set = Expr::var("s", Sort::array(key_sort, Sort::bool()));
    let key = Expr::bitvec_const(42u64, 32);

    let was_present = set.clone().select(key.clone());
    let new_set = set.store(key, Expr::bool_const(true));

    assert!(was_present.sort().is_bool(), "was_present should be Bool (select from Bool array)");
    assert!(new_set.sort().is_array(), "insert should produce a new Array");
    assert!(
        matches!(new_set.value(), ExprValue::Store { .. }),
        "insert should be a Store expression"
    );
}

/// Set contains: select(set, key) returns Bool.
#[test]
fn test_set_contains_is_select() {
    let key_sort = Sort::bitvec(32);
    let set = Expr::var("s", Sort::array(key_sort, Sort::bool()));
    let key = Expr::bitvec_const(1u64, 32);

    let result = set.select(key);
    assert!(result.sort().is_bool());
    assert!(matches!(result.value(), ExprValue::Select { .. }));
}

/// Set remove: store(set, key, false) produces a new Array<K, Bool>.
#[test]
fn test_set_remove_is_store_false() {
    let key_sort = Sort::bitvec(32);
    let set = Expr::var("s", Sort::array(key_sort, Sort::bool()));
    let key = Expr::bitvec_const(1u64, 32);

    let was_present = set.clone().select(key.clone());
    let new_set = set.store(key, Expr::bool_const(false));

    assert!(was_present.sort().is_bool());
    assert!(new_set.sort().is_array());
    assert!(matches!(new_set.value(), ExprValue::Store { .. }));
}

/// Set clone: identity in SMT (arrays are structural values).
#[test]
fn test_set_clone_is_identity() {
    let key_sort = Sort::bitvec(32);
    let set = Expr::var("s", Sort::array(key_sort, Sort::bool()));
    let cloned = set.clone();
    assert_eq!(set.sort().to_string(), cloned.sort().to_string(), "clone should preserve sort");
}

/// Set clear: const_array(key_sort, false) replaces the set.
#[test]
fn test_set_clear_is_const_array_false() {
    let key_sort = Sort::bitvec(32);
    let set = Expr::var("s", Sort::array(key_sort.clone(), Sort::bool()));
    let cleared = Expr::const_array(key_sort, Expr::bool_const(false));
    assert!(cleared.sort().is_array());
    assert_eq!(
        set.sort().to_string(),
        cleared.sort().to_string(),
        "cleared set should have same sort as original"
    );
}

// =============================================================================
// convert_key_to_array_index — sort coercion expression patterns
//
// The actual method is on ChcCtx, but the logic is pure expression
// algebra. These tests verify the coercion patterns it applies.
// =============================================================================

/// Same-sort keys need no coercion.
#[test]
fn test_key_coercion_same_sort_identity() {
    let key = Expr::bitvec_const(42u64, 32);
    let index_sort = Sort::bitvec(32);
    assert_eq!(key.sort(), &index_sort);
}

/// BV→Int coercion: bv2int produces Int sort.
#[test]
fn test_key_coercion_bv_to_int_unsigned() {
    let key = Expr::bitvec_const(5u64, 32);
    let result = key.bv2int();
    assert!(result.sort().is_int(), "bv2int should produce Int sort");
}

/// BV→Int signed coercion: bv2int_signed produces Int sort.
#[test]
fn test_key_coercion_bv_to_int_signed() {
    let key = Expr::bitvec_const(0xFFFFFFFFu64, 32);
    let result = key.bv2int_signed();
    assert!(result.sort().is_int(), "bv2int_signed should produce Int sort");
}

/// Int→BV coercion: int2bv produces bitvec of target width.
#[test]
fn test_key_coercion_int_to_bv() {
    let key = Expr::int_const(42);
    let result = key.int2bv(32);
    assert_eq!(result.sort().bitvec_width(), Some(32), "int2bv should produce BV32");
}

/// BV width coercion: zero_extend widens the bitvector.
#[test]
fn test_key_coercion_bv_width_widening() {
    use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
    let key = Expr::bitvec_const(7u64, 8);
    let result = coerce_bitvec_width_safe(key, 64, SignExtension::ZeroExtend);
    assert_eq!(result.sort().bitvec_width(), Some(64), "BV8 should be widened to BV64");
}

/// BV width coercion: sign_extend for signed values.
#[test]
fn test_key_coercion_bv_width_sign_extend() {
    use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
    let key = Expr::bitvec_const(0xFFu64, 8);
    let result = coerce_bitvec_width_safe(key, 32, SignExtension::SignExtend);
    assert_eq!(
        result.sort().bitvec_width(),
        Some(32),
        "signed BV8 should be sign-extended to BV32"
    );
}

// =============================================================================
// Set insert length tracking — ITE(was_absent, old_len + 1, old_len)
// =============================================================================

#[test]
fn test_set_insert_length_ite_pattern() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    let old_len = Expr::var("old_len", Sort::bitvec(POINTER_WIDTH));
    let was_absent = Expr::var("was_absent", Sort::bool());
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let new_len = old_len.clone().bvadd(one);
    let ite = Expr::ite(was_absent, new_len, old_len);

    assert!(matches!(ite.value(), ExprValue::Ite { .. }));
    assert_eq!(ite.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Set remove length tracking — ITE(was_present, old_len - 1, old_len)
// =============================================================================

#[test]
fn test_set_remove_length_ite_pattern() {
    use crate::codegen_ay::types::POINTER_WIDTH;
    let old_len = Expr::var("old_len", Sort::bitvec(POINTER_WIDTH));
    let was_present = Expr::var("was_present", Sort::bool());
    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
    let new_len = old_len.clone().bvsub(one);
    let ite = Expr::ite(was_present, new_len, old_len);

    assert!(matches!(ite.value(), ExprValue::Ite { .. }));
    assert_eq!(ite.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Pipeline: HashSet operations through mir_to_chc
// =============================================================================

#[test]
fn test_hashset_insert_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hashset_insert() {
            let mut s = HashSet::new();
            s.insert(1u32);
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_insert", ChcConfig::default());
        assert_vc_structure(&vc, "probe_hashset_insert", body.blocks.len());
    });
}

#[test]
fn test_hashset_contains_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hashset_contains(s: HashSet<u32>) -> bool {
            s.contains(&1u32)
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_contains");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_contains", ChcConfig::default());
        assert_vc_structure(&vc, "probe_hashset_contains", body.blocks.len());
    });
}

#[test]
fn test_hashset_remove_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;
        pub fn probe_hashset_remove() -> bool {
            let mut s = HashSet::new();
            s.insert(1u32);
            s.remove(&1u32)
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_remove");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_remove", ChcConfig::default());
        assert_vc_structure(&vc, "probe_hashset_remove", body.blocks.len());
    });
}

// =============================================================================
// Pipeline: BTreeSet operations through mir_to_chc
// =============================================================================

#[test]
fn test_btreeset_insert_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;
        pub fn probe_btreeset_insert() {
            let mut s = BTreeSet::new();
            s.insert(1u32);
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_insert");
        let body = instance.body().unwrap();
        let vc = mir_to_chc(ctx.tcx, &body, "probe_btreeset_insert", ChcConfig::default());
        assert_vc_structure(&vc, "probe_btreeset_insert", body.blocks.len());
    });
}

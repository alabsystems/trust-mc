// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven iterator dispatch tests: HashSet, Vec iterator, iterator adapters,
//! HashMap iterator, BTreeMap.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::{assert_semantic_return_equals, build_codegen_for_fn_info};

// HashSet dispatch: MIR-driven tests
// =============================================================================

/// Probe source: HashSet operations — triggers HashSet stubs.
const HASHSET_DISPATCH_PROBE: &str = r#"
use std::collections::HashSet;

pub fn hashset_insert_contains() -> bool {
    let mut s: HashSet<i32> = HashSet::new();
    s.insert(42);
    s.contains(&42)
}

pub fn hashset_remove_len() -> usize {
    let mut s: HashSet<i32> = HashSet::new();
    s.insert(1);
    s.insert(2);
    s.remove(&1);
    s.len()
}

pub fn hashset_is_empty_clear() -> bool {
    let mut s: HashSet<i32> = HashSet::new();
    s.insert(10);
    s.clear();
    s.is_empty()
}
"#;

/// Test HashSet::new + insert + contains dispatches through stub pipeline.
#[test]
fn test_mir_hashset_insert_contains_dispatch() {
    with_test_ay_ctx_for_source(HASHSET_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashset_insert_contains");
        assert!(info.call_count >= 3, "HashSet ops should have >=3 Calls, got {}", info.call_count);
        let has_hashset =
            info.call_paths.iter().any(|p| p.contains("HashSet") || p.contains("hash_set"));
        assert!(has_hashset, "should resolve HashSet-related paths, got {:?}", info.call_paths);
        assert!(info.ret_is_bool, "hashset_insert_contains should return bool");
    });
}

/// Critical semantic stub #3 (#2250): insert then contains must return true.
#[test]
fn test_mir_hashset_insert_contains_semantic_true() {
    with_test_ay_ctx_for_source(HASHSET_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashset_insert_contains");
        let ret_expr = info.ret_expr.expect("hashset_insert_contains should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "hashset_insert_contains_true",
        );
    });
}

/// Test HashSet::remove + len dispatches through stub pipeline.
#[test]
fn test_mir_hashset_remove_len_dispatch() {
    with_test_ay_ctx_for_source(HASHSET_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashset_remove_len");
        assert!(
            info.call_count >= 4,
            "HashSet insert+insert+remove+len should have >=4 Calls, got {}",
            info.call_count
        );
        // len returns usize (pointer width bitvec)
        assert!(
            info.ret_bitvec_width.is_some(),
            "hashset_remove_len should return bitvec (usize), got {:?}",
            info.ret_bitvec_width
        );
    });
}

/// Test HashSet::clear + is_empty dispatches through stub pipeline.
#[test]
fn test_mir_hashset_is_empty_clear_dispatch() {
    with_test_ay_ctx_for_source(HASHSET_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashset_is_empty_clear");
        assert!(
            info.call_count >= 3,
            "HashSet insert+clear+is_empty should have >=3 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "hashset_is_empty_clear should return bool");
    });
}

// =============================================================================
// Iterator dispatch: MIR-driven tests
// =============================================================================

/// Probe source: Vec iterator operations — triggers VecIntoIter/IntoIterNext stubs.
const VEC_ITER_DISPATCH_PROBE: &str = r#"
pub fn vec_into_iter_sum() -> i32 {
    let v = vec![1i32, 2, 3];
    let mut sum = 0i32;
    for x in v {
        sum += x;
    }
    sum
}

pub fn vec_into_iter_count() -> usize {
    let v = vec![10i32, 20, 30];
    v.into_iter().count()
}

pub fn vec_iter_fold() -> i32 {
    let v = vec![1i32, 2, 3, 4];
    v.iter().fold(0, |acc, x| acc + x)
}
"#;

/// Test Vec for-loop (into_iter + next) dispatches through stub pipeline.
#[test]
fn test_mir_vec_into_iter_sum_dispatch() {
    with_test_ay_ctx_for_source(VEC_ITER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_into_iter_sum");
        // for-loop desugars to into_iter() + loop { match next() { Some(x) => ..., None => break } }
        assert!(
            info.call_count >= 1,
            "Vec for-loop should have >=1 Call (into_iter/next), got {}",
            info.call_count
        );
        // Sum returns i32 (bv32)
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "vec_into_iter_sum should return bv32, got {:?}",
            info.ret_bitvec_width
        );
    });
}

/// Test Vec::into_iter().count() dispatches through stub pipeline.
#[test]
fn test_mir_vec_into_iter_count_dispatch() {
    with_test_ay_ctx_for_source(VEC_ITER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_into_iter_count");
        // count() may be inlined by rustc; verify we at least generate basic blocks
        assert!(
            info.call_count >= 1 || info.block_count >= 2,
            "into_iter().count() should have calls or multiple BBs, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
    });
}

/// Test Vec::iter().fold() dispatches through stub pipeline.
#[test]
fn test_mir_vec_iter_fold_dispatch() {
    with_test_ay_ctx_for_source(VEC_ITER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_iter_fold");
        // fold involves iter() + fold(init, closure) — may be inlined
        assert!(
            info.call_count >= 1 || info.block_count >= 2,
            "iter().fold() should have calls or multiple BBs, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
    });
}

// =============================================================================
// Iterator adapter dispatch: map/filter/collect
// =============================================================================

/// Probe source: Iterator adapter chain — triggers IterMap/IterFilter/IterCollect stubs.
const ITER_ADAPTER_DISPATCH_PROBE: &str = r#"
pub fn iter_map_collect() -> Vec<i32> {
    let v = vec![1i32, 2, 3];
    v.into_iter().map(|x| x * 2).collect()
}

pub fn iter_filter_collect() -> Vec<i32> {
    let v = vec![1i32, 2, 3, 4, 5];
    v.into_iter().filter(|x| *x > 2).collect()
}

pub fn iter_sum() -> i32 {
    let v = vec![1i32, 2, 3];
    v.into_iter().sum()
}
"#;

/// Test into_iter().map().collect() dispatches through stub pipeline.
#[test]
fn test_mir_iter_map_collect_dispatch() {
    with_test_ay_ctx_for_source(ITER_ADAPTER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "iter_map_collect");
        // map + collect: at minimum into_iter + map + collect calls
        assert!(
            info.call_count >= 1,
            "map().collect() should have >=1 Call, got {}",
            info.call_count
        );
        assert!(info.any_dest_assigned, "map().collect() should assign destinations");
    });
}

/// Test into_iter().filter().collect() dispatches through stub pipeline.
#[test]
fn test_mir_iter_filter_collect_dispatch() {
    with_test_ay_ctx_for_source(ITER_ADAPTER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "iter_filter_collect");
        assert!(
            info.call_count >= 1,
            "filter().collect() should have >=1 Call, got {}",
            info.call_count
        );
        assert!(info.any_dest_assigned, "filter().collect() should assign destinations");
    });
}

/// Test into_iter().sum() dispatches through stub pipeline.
#[test]
fn test_mir_iter_sum_dispatch() {
    with_test_ay_ctx_for_source(ITER_ADAPTER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "iter_sum");
        assert!(
            info.call_count >= 1,
            "into_iter().sum() should have >=1 Call, got {}",
            info.call_count
        );
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "iter_sum should return bv32, got {:?}",
            info.ret_bitvec_width
        );
    });
}

// =============================================================================
// HashMap iterator dispatch: MIR-driven tests
// =============================================================================

/// Probe source: HashMap operations — triggers HashMap stubs.
const HASHMAP_ITER_DISPATCH_PROBE: &str = r#"
use std::collections::HashMap;

pub fn hashmap_keys_count() -> usize {
    let mut m: HashMap<i32, i32> = HashMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.keys().count()
}

pub fn hashmap_values_sum() -> i32 {
    let mut m: HashMap<i32, i32> = HashMap::new();
    m.insert(1, 10);
    m.insert(2, 20);
    m.values().sum()
}
"#;

/// Test HashMap::keys().count() dispatches through stub pipeline.
#[test]
fn test_mir_hashmap_keys_count_dispatch() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashmap_keys_count");
        assert!(
            info.call_count >= 2,
            "keys().count() should have >=2 Calls, got {}",
            info.call_count
        );
        let has_hashmap =
            info.call_paths.iter().any(|p| p.contains("HashMap") || p.contains("hash_map"));
        assert!(has_hashmap, "should resolve HashMap-related paths, got {:?}", info.call_paths);
    });
}

/// Test HashMap::values().sum() dispatches through stub pipeline.
#[test]
fn test_mir_hashmap_values_sum_dispatch() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashmap_values_sum");
        assert!(
            info.call_count >= 2,
            "values().sum() should have >=2 Calls, got {}",
            info.call_count
        );
        let has_hashmap =
            info.call_paths.iter().any(|p| p.contains("HashMap") || p.contains("hash_map"));
        assert!(has_hashmap, "should resolve HashMap-related paths, got {:?}", info.call_paths);
    });
}

// =============================================================================
// BTreeMap dispatch: MIR-driven tests
// =============================================================================

/// Probe source: BTreeMap operations — triggers BTreeMap stubs.
const BTREEMAP_DISPATCH_PROBE: &str = r#"
use std::collections::BTreeMap;

pub fn btreemap_insert_get() -> Option<i32> {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 42);
    m.get(&1).copied()
}

pub fn btreemap_len_contains() -> bool {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(10, 100);
    m.len() > 0 && m.contains_key(&10)
}

pub fn btreemap_remove_is_empty() -> bool {
    let mut m: BTreeMap<i32, i32> = BTreeMap::new();
    m.insert(1, 10);
    m.remove(&1);
    m.is_empty()
}
"#;

/// Test BTreeMap::new + insert + get dispatches through stub pipeline.
#[test]
fn test_mir_btreemap_insert_get_dispatch() {
    with_test_ay_ctx_for_source(BTREEMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "btreemap_insert_get");
        assert!(
            info.call_count >= 3,
            "BTreeMap ops should have >=3 Calls, got {}",
            info.call_count
        );
        let has_btree =
            info.call_paths.iter().any(|p| p.contains("BTreeMap") || p.contains("btree"));
        assert!(has_btree, "should resolve BTreeMap-related paths, got {:?}", info.call_paths);
        assert!(info.any_dest_assigned, "at least one call destination should be assigned");
    });
}

/// Test BTreeMap::len + contains_key dispatches through stub pipeline.
#[test]
fn test_mir_btreemap_len_contains_dispatch() {
    with_test_ay_ctx_for_source(BTREEMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "btreemap_len_contains");
        assert!(
            info.call_count >= 3,
            "BTreeMap len/contains should have >=3 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "btreemap_len_contains should return bool");
    });
}

/// Critical semantic stub #4 (#2250): len/contains_key conjunction should return true.
#[test]
fn test_mir_btreemap_len_contains_semantic_true() {
    with_test_ay_ctx_for_source(BTREEMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "btreemap_len_contains");
        let ret_expr = info.ret_expr.expect("btreemap_len_contains should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "btreemap_len_contains_true",
        );
    });
}

/// Test BTreeMap::remove + is_empty dispatches through stub pipeline.
#[test]
fn test_mir_btreemap_remove_is_empty_dispatch() {
    with_test_ay_ctx_for_source(BTREEMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "btreemap_remove_is_empty");
        assert!(
            info.call_count >= 3,
            "BTreeMap insert+remove+is_empty should have >=3 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "btreemap_remove_is_empty should return bool");
    });
}

// =============================================================================

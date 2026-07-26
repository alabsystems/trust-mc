// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven collection dispatch tests: HashMap, BTreeSet, primitive traits,
//! Option unwrap, Result predicates.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::mir_alloc_kani_mem::codegen_matching_call_destination;
use super::{assert_semantic_return_equals, build_codegen_for_fn, build_codegen_for_fn_info};

// HashMap dispatch: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: HashMap operations — triggers HashMap stubs.
const HASHMAP_DISPATCH_PROBE: &str = r#"
use std::collections::HashMap;

pub fn hashmap_insert_get() -> Option<i32> {
    let mut m: HashMap<i32, i32> = HashMap::new();
    m.insert(1, 42);
    m.get(&1).copied()
}

pub fn hashmap_len_contains() -> bool {
    let mut m: HashMap<String, i32> = HashMap::new();
    m.insert(String::new(), 1);
    m.len() > 0 && m.contains_key(&String::new())
}
"#;

/// Test HashMap::new + insert + get dispatches through stub pipeline.
#[test]
fn test_mir_hashmap_insert_get_dispatch() {
    with_test_ay_ctx_for_source(HASHMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashmap_insert_get");
        assert!(info.call_count >= 3, "HashMap ops should have >=3 Calls, got {}", info.call_count);
        let has_hashmap =
            info.call_paths.iter().any(|p| p.contains("HashMap") || p.contains("hash_map"));
        assert!(has_hashmap, "should resolve HashMap-related paths, got {:?}", info.call_paths);
        assert!(info.any_dest_assigned, "at least one call destination should be assigned");
    });
}

/// Test HashMap::len + contains_key dispatches through stub pipeline.
#[test]
fn test_mir_hashmap_len_contains_dispatch() {
    with_test_ay_ctx_for_source(HASHMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashmap_len_contains");
        assert!(
            info.call_count >= 3,
            "HashMap len/contains should have >=3 Calls, got {}",
            info.call_count
        );
        let has_hashmap =
            info.call_paths.iter().any(|p| p.contains("HashMap") || p.contains("hash_map"));
        assert!(has_hashmap, "should resolve HashMap-related paths, got {:?}", info.call_paths);
        // hashmap_len_contains returns bool
        assert!(info.ret_is_bool, "hashmap_len_contains should return bool");
    });
}

/// Critical semantic stub #2 (#2250): insert + len/contains_key should evaluate to true.
#[test]
fn test_mir_hashmap_len_contains_semantic_true() {
    with_test_ay_ctx_for_source(HASHMAP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "hashmap_len_contains");
        let ret_expr = info.ret_expr.expect("hashmap_len_contains should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "hashmap_len_contains_true",
        );
    });
}

// -----------------------------------------------------------------------------
// BTreeSet dispatch: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: BTreeSet operations — triggers BTreeSet stubs.
const BTREESET_DISPATCH_PROBE: &str = r#"
use std::collections::BTreeSet;

pub fn btreeset_insert_contains() -> bool {
    let mut s: BTreeSet<i32> = BTreeSet::new();
    s.insert(42);
    s.contains(&42)
}
"#;

/// Test BTreeSet::new + insert + contains dispatches through stub pipeline.
#[test]
fn test_mir_btreeset_dispatch() {
    with_test_ay_ctx_for_source(BTREESET_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "btreeset_insert_contains");
        assert!(
            info.call_count >= 3,
            "BTreeSet ops should have >=3 Calls, got {}",
            info.call_count
        );
        let has_btree =
            info.call_paths.iter().any(|p| p.contains("BTreeSet") || p.contains("btree"));
        assert!(has_btree, "should resolve BTreeSet-related paths, got {:?}", info.call_paths);
        // btreeset_insert_contains returns bool
        assert!(info.ret_is_bool, "btreeset_insert_contains should return bool");
    });
}

// -----------------------------------------------------------------------------
// Primitive trait stubs (PartialEq, Clone, Ord): MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: primitive trait operations that hit PrimitivePartialEqEq/Ne/Clone/OrdCmp stubs.
const PRIMITIVE_TRAIT_PROBE: &str = r#"
pub fn primitive_eq_ne(a: i32, b: i32) -> (bool, bool) {
    (a == b, a != b)
}

pub fn primitive_clone_ord(x: i32, y: i32) -> (i32, core::cmp::Ordering) {
    (x.clone(), x.cmp(&y))
}
"#;

/// Test primitive PartialEq::eq and PartialEq::ne dispatch.
#[test]
fn test_mir_primitive_eq_ne_dispatch() {
    with_test_ay_ctx_for_source(PRIMITIVE_TRAIT_PROBE, |mut ctx| {
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "primitive_eq_ne");
        assert_eq!(block_count, 1, "eq/ne: expected 1 BB (compare+return), got {block_count}");
        assert_eq!(
            call_count, 0,
            "eq/ne: expected 0 calls (BinaryOp, not trait), got {call_count}"
        );
    });
}

/// Test Clone and Ord::cmp dispatch on primitives.
#[test]
fn test_mir_primitive_clone_ord_dispatch() {
    with_test_ay_ctx_for_source(PRIMITIVE_TRAIT_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "primitive_clone_ord");
        // MIR may inline clone/cmp so call_count varies, but blocks must exist
        assert!(
            info.block_count >= 1,
            "codegen should produce at least 1 block, got {}",
            info.block_count
        );
        // Return is (i32, Ordering) — any dest should be assigned
        assert!(info.any_dest_assigned, "clone/ord should produce assigned destinations");
    });
}

// -----------------------------------------------------------------------------
// Option unwrap dispatch: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: Option::unwrap — triggers OptionUnwrap stub.
const OPTION_UNWRAP_PROBE: &str = r#"
pub fn option_unwrap_probe(x: Option<i32>) -> i32 {
    x.unwrap()
}
"#;

/// Test Option::unwrap dispatches through stub pipeline.
/// Note: unwrap involves discriminant check + panic path + value extraction.
/// The panic call may diverge (no destination assigned), so we verify callee path
/// resolution and block count rather than destination assignment.
#[test]
fn test_mir_option_unwrap_dispatch() {
    with_test_ay_ctx_for_source(OPTION_UNWRAP_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "option_unwrap_probe");
        assert!(info.call_count >= 1, "Option::unwrap should have Call, got {}", info.call_count);
        // unwrap generates multiple basic blocks (discriminant check, success, panic)
        assert!(
            info.block_count >= 2,
            "Option::unwrap should have >=2 BBs (check+success), got {}",
            info.block_count
        );
        // Verify callee paths were resolved
        assert!(
            !info.call_paths.is_empty(),
            "Option::unwrap should resolve callee paths, got empty"
        );
    });
}

/// Probe source: Result::is_ok/is_err predicates.
const RESULT_PREDICATE_PROBE: &str = r#"
pub fn result_is_ok_probe(x: Result<i32, i32>) -> bool {
    x.is_ok()
}

pub fn result_is_err_probe(x: Result<i32, i32>) -> bool {
    x.is_err()
}
"#;

/// Test Result::is_ok dispatches through stub pipeline with bool destination assignment.
#[test]
fn test_mir_result_is_ok_dispatch() {
    with_test_ay_ctx_for_source(RESULT_PREDICATE_PROBE, |mut ctx| {
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(&mut ctx, "result_is_ok_probe", "is_ok");
        assert!(
            call_paths.iter().any(|p| p.contains("is_ok")),
            "expected resolved Result::is_ok call, got {call_paths:?}"
        );
        let matched_path = matched_path.expect("expected matching Result::is_ok call");
        assert_eq!(
            crate::codegen_ay::stubs::StubRegistry::new().lookup(&matched_path),
            Some(crate::codegen_ay::stubs::StubKind::ResultIsOk)
        );
        assert!(
            successor_count.unwrap_or(0) > 0,
            "Result::is_ok stub should continue (non-divergent), paths: {call_paths:?}"
        );
        let ret = assigned.expect("Result::is_ok destination should be assigned");
        assert!(ret.sort().is_bool(), "expected bool destination, got {:?}", ret.sort());
    });
}

/// Test Result::is_err dispatches through stub pipeline with bool destination assignment.
#[test]
fn test_mir_result_is_err_dispatch() {
    with_test_ay_ctx_for_source(RESULT_PREDICATE_PROBE, |mut ctx| {
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(&mut ctx, "result_is_err_probe", "is_err");
        assert!(
            call_paths.iter().any(|p| p.contains("is_err")),
            "expected resolved Result::is_err call, got {call_paths:?}"
        );
        let matched_path = matched_path.expect("expected matching Result::is_err call");
        assert_eq!(
            crate::codegen_ay::stubs::StubRegistry::new().lookup(&matched_path),
            Some(crate::codegen_ay::stubs::StubKind::ResultIsErr)
        );
        assert!(
            successor_count.unwrap_or(0) > 0,
            "Result::is_err stub should continue (non-divergent), paths: {call_paths:?}"
        );
        let ret = assigned.expect("Result::is_err destination should be assigned");
        assert!(ret.sort().is_bool(), "expected bool destination, got {:?}", ret.sort());
    });
}

// -----------------------------------------------------------------------------

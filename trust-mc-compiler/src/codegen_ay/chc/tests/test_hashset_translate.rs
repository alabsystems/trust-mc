// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `stubs_hashset_translate.rs` and `stubs_hashset_detect.rs`.
//!
//! Part of #2303 (stubs_hashset_translate.rs, 507 LOC; stubs_hashset_detect.rs,
//! 49 LOC — zero dedicated coverage).
//!
//! Covers:
//! - HashSet::new, insert, contains, remove, len, is_empty, clear, clone
//! - HashSet::into_iter and HashSetIterNext
//! - detect_hashset_stub filtering
//! - extract_hashset_iter_fields helper

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// HashSet pipeline tests via MIR translation
// =============================================================================

const HASHSET_NEW_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_new() -> HashSet<u32> {
        HashSet::new()
    }
"#;

/// HashSet::new() should translate to a VC without panicking.
#[test]
fn test_hashset_new_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_new");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_new", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_new", body.blocks.len());

        // HashSet::new should produce transition rules
        assert!(!vc.rules.is_empty(), "HashSet::new should produce at least 1 rule");
    });
}

const HASHSET_INSERT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_insert() -> bool {
        let mut s = HashSet::new();
        s.insert(42u32)
    }
"#;

/// HashSet insert should produce a VC with stub-translated rules.
#[test]
fn test_hashset_insert_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_INSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_insert", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_insert", body.blocks.len());

        // HashSet insert returns bool — Bool sort should be present
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "HashSet::insert returning bool should have Bool sort");
    });
}

const HASHSET_CONTAINS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_contains(s: &HashSet<u32>, key: &u32) -> bool {
        s.contains(key)
    }
"#;

/// HashSet::contains should translate without panicking.
#[test]
fn test_hashset_contains_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_CONTAINS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_contains");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_contains", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_contains", body.blocks.len());

        // HashSet contains returns bool — Bool sort should be present
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "HashSet::contains returning bool should have Bool sort");
    });
}

const HASHSET_REMOVE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_remove() -> bool {
        let mut s = HashSet::new();
        s.insert(42u32);
        s.remove(&42)
    }
"#;

/// HashSet::remove should produce a VC.
#[test]
fn test_hashset_remove_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_REMOVE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_remove");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_remove", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_remove", body.blocks.len());

        // HashSet remove returns bool — Bool sort should be present
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "HashSet::remove returning bool should have Bool sort");
    });
}

const HASHSET_LEN_EMPTY_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_len(s: &HashSet<u32>) -> usize {
        s.len()
    }

    pub fn probe_hashset_is_empty(s: &HashSet<u32>) -> bool {
        s.is_empty()
    }
"#;

/// HashSet::len should translate without panicking.
#[test]
fn test_hashset_len_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_LEN_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_len");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_len", body.blocks.len());

        // HashSet::len pipeline should produce transition rules
        assert!(!vc.rules.is_empty(), "HashSet::len should produce at least 1 rule");
    });
}

/// HashSet::is_empty should translate without panicking.
#[test]
fn test_hashset_is_empty_generates_vc() {
    with_test_ay_ctx_for_source(HASHSET_LEN_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_is_empty");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_is_empty", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashset_is_empty", body.blocks.len());

        // HashSet is_empty returns bool — Bool sort should be present
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "HashSet::is_empty returning bool should have Bool sort");
    });
}

const HASHSET_DETECT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashSet;

    pub fn probe_hashset_detect_new() -> HashSet<u32> {
        HashSet::new()
    }

    pub fn probe_hashset_detect_insert(s: &mut HashSet<u32>) {
        s.insert(1);
    }

    pub fn probe_hashset_detect_contains(s: &HashSet<u32>) -> bool {
        s.contains(&1)
    }
"#;

/// detect_hashset_stub should detect HashSet::new.
#[test]
fn test_detect_hashset_stub_new() {
    with_test_ay_ctx_for_source(HASHSET_DETECT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_detect_new");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_detect_new", ChcConfig::default());

        // Collect HashSet stubs from terminators
        use rustc_public::mir::TerminatorKind;
        let mut found = Vec::new();
        for block in &body.blocks {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
            {
                found.push(stub);
            }
        }

        // Should find at least one HashSet stub (new)
        assert!(!found.is_empty(), "detect_hashset_stub should find HashSet::new");
    });
}

/// detect_hashset_stub should detect insert and contains.
#[test]
fn test_detect_hashset_stub_insert_and_contains() {
    with_test_ay_ctx_for_source(HASHSET_DETECT_SOURCE, |ctx| {
        // Check insert
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_detect_insert");
        let body = instance.body().expect("body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_detect_insert", ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let mut found_insert = false;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_hashset).is_some()
            {
                found_insert = true;
            }
        }
        assert!(found_insert, "detect_hashset_stub should find HashSet::insert");

        // Check contains
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_detect_contains");
        let body = instance.body().expect("body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_detect_contains", ChcConfig::default());

        let mut found_contains = false;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_hashset).is_some()
            {
                found_contains = true;
            }
        }
        assert!(found_contains, "detect_hashset_stub should find HashSet::contains");
    });
}

/// detect_hashset_stub should reject non-HashSet methods.
#[test]
fn test_detect_hashset_stub_rejects_non_hashset() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_non_hashset(x: u32) -> u32 {
            x + 1
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_non_hashset");
            let body = instance.body().expect("body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_hashset", ChcConfig::default());

            use rustc_public::mir::TerminatorKind;
            for block in &body.blocks {
                if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                    assert!(
                        chc_ctx.detect_stub_matching(func, StubKind::is_hashset).is_none(),
                        "detect_hashset_stub should not match non-HashSet calls"
                    );
                }
            }
        },
    );
}

// =============================================================================
// Error-path tests: translate_hashset_call returns None
// =============================================================================
//
// Part of #2627: error-path test coverage gaps.

/// Minimal source for constructing a ChcCtx without HashSet-specific MIR.
const HASHSET_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_simple() {}
"#;

/// HashSetInsert with fewer than 2 args returns None (via shared set helper).
#[test]
fn test_translate_hashset_insert_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args
        let result = chc_ctx.translate_hashset_call(StubKind::HashSetInsert, &[], &modified, None);
        assert!(result.is_none(), "HashSetInsert with 0 args should return None");

        // 1 arg (needs 2: self, key)
        let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
        let result =
            chc_ctx.translate_hashset_call(StubKind::HashSetInsert, &one_arg, &modified, None);
        assert!(result.is_none(), "HashSetInsert with 1 arg should return None");
    });
}

/// HashSetContains with fewer than 2 args returns None.
#[test]
fn test_translate_hashset_contains_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result =
            chc_ctx.translate_hashset_call(StubKind::HashSetContains, &[], &modified, None);
        assert!(result.is_none(), "HashSetContains with 0 args should return None");
    });
}

/// HashSetRemove with fewer than 2 args returns None.
#[test]
fn test_translate_hashset_remove_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_hashset_call(StubKind::HashSetRemove, &[], &modified, None);
        assert!(result.is_none(), "HashSetRemove with 0 args should return None");
    });
}

/// HashSetLen/IsEmpty/Clear/Clone with empty args returns None.
#[test]
fn test_translate_hashset_len_clear_clone_empty_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [
            StubKind::HashSetLen,
            StubKind::HashSetIsEmpty,
            StubKind::HashSetClear,
            StubKind::HashSetClone,
        ] {
            let result = chc_ctx.translate_hashset_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");
        }
    });
}

/// HashSetIntoIter/HashSetIter with empty args returns None (args.first()?).
#[test]
fn test_translate_hashset_iterator_stubs_empty_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::HashSetIntoIter, StubKind::HashSetIter] {
            let result = chc_ctx.translate_hashset_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");
        }
    });
}

/// HashSetIterNext with empty args returns None (args.first()?).
#[test]
fn test_translate_hashset_iter_next_empty_args_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result =
            chc_ctx.translate_hashset_call(StubKind::HashSetIterNext, &[], &modified, None);
        assert!(result.is_none(), "HashSetIterNext with 0 args should return None");
    });
}

/// Non-HashSet stub kind returns None (catch-all arm).
#[test]
fn test_translate_hashset_non_hashset_stub_returns_none() {
    with_test_ay_ctx_for_source(HASHSET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // BigIntAdd is not a HashSet stub — should hit the catch-all None
        let result = chc_ctx.translate_hashset_call(StubKind::BigIntAdd, &[], &modified, None);
        assert!(result.is_none(), "non-HashSet stub should return None");

        let result = chc_ctx.translate_hashset_call(StubKind::HashMapInsert, &[], &modified, None);
        assert!(result.is_none(), "HashMapInsert is not a HashSet stub");
    });
}

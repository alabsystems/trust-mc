// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for HashSet CHC stub interception and translation (stubs_hashset.rs).
// Covers: detect_hashset_stub, translate_hashset_call, make_hashset_into_iter,
// and HashSet-specific collection pipeline paths.
//
// Part of #2188: CHC module test coverage.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =========================================================================
// HashSet detection tests
// =========================================================================

#[test]
fn test_hashset_new_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_new() -> HashSet<u32> {
            HashSet::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_new", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_hashset).is_some()
            {
                found = true;
            }
        }
        assert!(found, "expected HashSet stub to be detected in MIR");
    });
}

#[test]
fn test_hashset_insert_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_insert() {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(42);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_insert", ChcConfig::default());

        let mut stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
            {
                stubs.push(stub);
            }
        }
        assert!(
            stubs.len() >= 2,
            "expected at least 2 HashSet stubs (new + insert), got {}: {:?}",
            stubs.len(),
            stubs
        );
        assert!(
            stubs.contains(&StubKind::HashSetInsert),
            "expected HashSetInsert in stubs: {:?}",
            stubs
        );
    });
}

#[test]
fn test_hashset_contains_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_contains() -> bool {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(10);
            s.contains(&10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_contains");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_contains", ChcConfig::default());

        let mut has_contains = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetContains
            {
                has_contains = true;
            }
        }
        assert!(has_contains, "expected HashSetContains stub in MIR");
    });
}

#[test]
fn test_hashset_remove_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_remove() -> bool {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(5);
            s.remove(&5)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_remove");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_remove", ChcConfig::default());

        let mut has_remove = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetRemove
            {
                has_remove = true;
            }
        }
        assert!(has_remove, "expected HashSetRemove stub in MIR");
    });
}

#[test]
fn test_hashset_len_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_len() -> usize {
            let s: HashSet<u32> = HashSet::new();
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_len", ChcConfig::default());

        let mut has_len = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetLen
            {
                has_len = true;
            }
        }
        assert!(has_len, "expected HashSetLen stub in MIR");
    });
}

#[test]
fn test_hashset_is_empty_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_is_empty() -> bool {
            let s: HashSet<u32> = HashSet::new();
            s.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_is_empty", ChcConfig::default());

        let mut has_is_empty = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetIsEmpty
            {
                has_is_empty = true;
            }
        }
        assert!(has_is_empty, "expected HashSetIsEmpty stub in MIR");
    });
}

#[test]
fn test_hashset_clear_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_clear() {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(1);
            s.clear();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_clear");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_clear", ChcConfig::default());

        let mut has_clear = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetClear
            {
                has_clear = true;
            }
        }
        assert!(has_clear, "expected HashSetClear stub in MIR");
    });
}

#[test]
fn test_hashset_clone_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_clone() -> HashSet<u32> {
            let s: HashSet<u32> = HashSet::new();
            s.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_clone");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_clone", ChcConfig::default());

        let mut has_clone = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetClone
            {
                has_clone = true;
            }
        }
        assert!(has_clone, "expected HashSetClone stub in MIR");
    });
}

// =========================================================================
// HashSet CHC translation pipeline tests
// =========================================================================

#[test]
fn test_hashset_full_pipeline_all_bbs_processed() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_pipeline() -> bool {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(10);
            s.insert(20);
            s.contains(&10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_pipeline", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_hashset_pipeline", bb_count);

        // HashSet operations produce relations with non-trivial arity
        // (state vars for locals including the set)
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "HashSet pipeline VC relations should have arity >= 2, got {max_arity}"
        );

        // Multiple call stubs → should have transition rules with constraints
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "HashSet pipeline should have constrained transition rules for stub operations"
        );
    });
}

#[test]
fn test_hashset_insert_remove_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_insert_remove() -> bool {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(42);
            s.remove(&42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert_remove");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_insert_remove", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_hashset_insert_remove", bb_count);

        // insert + remove are mutation stubs → should have non-trivial arity
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "HashSet insert+remove VC relations should have arity >= 2, got {max_arity}"
        );

        // Should have constrained transition rules for the mutation operations
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "HashSet insert+remove should have constrained transition rules");
    });
}

#[test]
fn test_hashset_len_is_empty_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_len_empty() -> (usize, bool) {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(1);
            (s.len(), s.is_empty())
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_len_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_len_empty", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_hashset_len_empty", bb_count);

        // len returns usize (BV64), is_empty returns bool → should have bitvec state vars
        let has_bv =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bitvec));
        assert!(has_bv, "HashSet len+is_empty VC should have bitvec state vars");

        // Should have constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "HashSet len+is_empty should have constrained transition rules");
    });
}

#[test]
fn test_hashset_clear_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_clear_pipeline() {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(1);
            s.insert(2);
            s.clear();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_clear_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashset_clear_pipeline", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_hashset_clear_pipeline", bb_count);

        // Clear resets the set → should have non-trivial arity and constrained transitions
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "HashSet clear VC relations should have arity >= 2, got {max_arity}"
        );

        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "HashSet clear should have constrained transition rules for the clear operation"
        );
    });
}

// =========================================================================
// HashSet detect_collection_type integration tests
// =========================================================================

#[test]
fn test_hashset_detect_collection_type_returns_hashset() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_type(s: HashSet<u32>) {
            let _ = s;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashset_type");
        let arg_ty = sig.inputs()[0];

        let (kind, name) =
            ChcCtx::detect_collection_type(arg_ty).expect("HashSet should be detected");
        assert_eq!(kind, "hashset", "HashSet should be detected as hashset kind");
        assert!(name.contains("HashSet"), "name should contain HashSet, got: {}", name);
    });
}

#[test]
fn test_hashset_ref_detect_collection_type() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_ref(s: &HashSet<u32>, s_mut: &mut HashSet<u32>) {
            let _ = (s, s_mut);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashset_ref");

        let ref_ty = sig.inputs()[0];
        let (kind, _) =
            ChcCtx::detect_collection_type(ref_ty).expect("&HashSet should be detected");
        assert_eq!(kind, "hashset");

        let mut_ref_ty = sig.inputs()[1];
        let (kind, _) =
            ChcCtx::detect_collection_type(mut_ref_ty).expect("&mut HashSet should be detected");
        assert_eq!(kind, "hashset");
    });
}

#[test]
fn test_hashset_into_iter_detected_as_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashSet;

        pub fn probe_hashset_into_iter() {
            let mut s: HashSet<u32> = HashSet::new();
            s.insert(1);
            let _iter = s.into_iter();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_into_iter");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashset_into_iter", ChcConfig::default());

        let mut has_into_iter = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetIntoIter
            {
                has_into_iter = true;
            }
        }
        assert!(has_into_iter, "expected HashSetIntoIter stub in MIR");
    });
}

// =============================================================================
// Part of #2255: HashSet detector negative-gating tests
// =============================================================================

/// Verify detect_hashset_stub returns None for HashMap calls — must not
/// produce false positives by leaking HashMap stubs through the HashSet path.
#[test]
fn test_hashset_detector_rejects_hashmap_calls() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashmap_not_hashset() {
            let mut m: HashMap<u32, u32> = HashMap::new();
            m.insert(1, 10);
            let _ = m.contains_key(&1);
            let _ = m.len();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_not_hashset");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_not_hashset", ChcConfig::default());

        let mut hashset_stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
            {
                hashset_stubs.push(stub);
            }
        }

        assert!(
            hashset_stubs.is_empty(),
            "HashMap calls must not be detected as HashSet stubs; got: {:?}",
            hashset_stubs
        );
    });
}

/// Verify detect_hashset_stub returns None for non-collection method calls.
#[test]
fn test_hashset_detector_rejects_non_collection_methods() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MySet {
            data: Vec<u32>,
        }

        impl MySet {
            pub fn new() -> Self { MySet { data: Vec::new() } }
            pub fn insert(&mut self, v: u32) { self.data.push(v); }
            pub fn contains(&self, v: &u32) -> bool { self.data.contains(v) }
            pub fn len(&self) -> usize { self.data.len() }
            pub fn is_empty(&self) -> bool { self.data.is_empty() }
        }

        pub fn probe_custom_set() {
            let mut s = MySet::new();
            s.insert(1);
            let _ = s.contains(&1);
            let _ = s.len();
            let _ = s.is_empty();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_set");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_custom_set", ChcConfig::default());

        let mut hashset_stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
            {
                hashset_stubs.push(stub);
            }
        }

        assert!(
            hashset_stubs.is_empty(),
            "Custom MySet methods must not be detected as HashSet stubs; got: {:?}",
            hashset_stubs
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for BTreeSet CHC stub interception and translation (stubs_btreeset.rs).
// Covers: detect_btreeset_stub, translate_btreeset_call, extract/make helpers,
// and convert_key_to_array_index paths specific to BTreeSet.
//
// Part of #2188: CHC module test coverage.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =========================================================================
// BTreeSet detection tests
// =========================================================================

#[test]
fn test_btreeset_new_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_new() -> BTreeSet<u32> {
            BTreeSet::new()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_new");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_new", ChcConfig::default());

        // Check that at least one BTreeSet call is detected in the MIR
        let mut found_btreeset = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let callee_path = chc_ctx.resolve_callee_path(func);
                if let Some(ref path) = callee_path
                    && (path.contains("BTreeSet") || path.contains("btree_set"))
                {
                    found_btreeset = true;
                }
            }
        }
        // BTreeSet::new() should appear in MIR as a call
        assert!(found_btreeset, "expected BTreeSet call in MIR for BTreeSet::new()");
    });
}

#[test]
fn test_btreeset_insert_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_insert() {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(42);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_insert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_insert", ChcConfig::default());

        let mut btreeset_calls = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && (path.contains("BTreeSet") || path.contains("btree_set"))
            {
                btreeset_calls.push(path);
            }
        }
        // Should find at least new() and insert()
        assert!(
            btreeset_calls.len() >= 2,
            "expected at least 2 BTreeSet calls (new + insert), got {}: {:?}",
            btreeset_calls.len(),
            btreeset_calls
        );
    });
}

#[test]
fn test_btreeset_contains_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_contains() -> bool {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(10);
            s.contains(&10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_contains");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_contains", ChcConfig::default());

        let mut has_contains = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("contains")
            {
                has_contains = true;
            }
        }
        assert!(has_contains, "expected BTreeSet::contains call in MIR");
    });
}

#[test]
fn test_btreeset_remove_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_remove() -> bool {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(5);
            s.remove(&5)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_remove");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_remove", ChcConfig::default());

        let mut has_remove = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("remove")
            {
                has_remove = true;
            }
        }
        assert!(has_remove, "expected BTreeSet::remove call in MIR");
    });
}

#[test]
fn test_btreeset_len_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_len() -> usize {
            let s: BTreeSet<u32> = BTreeSet::new();
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_len", ChcConfig::default());

        let mut has_len = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("len")
            {
                has_len = true;
            }
        }
        assert!(has_len, "expected BTreeSet::len call in MIR");
    });
}

#[test]
fn test_btreeset_is_empty_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_is_empty() -> bool {
            let s: BTreeSet<u32> = BTreeSet::new();
            s.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_is_empty");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_is_empty", ChcConfig::default());

        let mut has_is_empty = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("is_empty")
            {
                has_is_empty = true;
            }
        }
        assert!(has_is_empty, "expected BTreeSet::is_empty call in MIR");
    });
}

#[test]
fn test_btreeset_clear_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_clear() {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(1);
            s.clear();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_clear");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_clear", ChcConfig::default());

        let mut has_clear = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("clear")
            {
                has_clear = true;
            }
        }
        assert!(has_clear, "expected BTreeSet::clear call in MIR");
    });
}

#[test]
fn test_btreeset_clone_detected_via_mir() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_clone() -> BTreeSet<u32> {
            let s: BTreeSet<u32> = BTreeSet::new();
            s.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_clone");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_btreeset_clone", ChcConfig::default());

        let mut has_clone = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("clone")
            {
                has_clone = true;
            }
        }
        assert!(has_clone, "expected BTreeSet::clone call in MIR");
    });
}

// =========================================================================
// BTreeSet CHC translation pipeline tests
// =========================================================================

#[test]
fn test_btreeset_full_pipeline_all_bbs_processed() {
    // End-to-end: compile BTreeSet code, run mir_to_chc, verify all BBs processed
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_pipeline() -> bool {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(10);
            s.insert(20);
            s.contains(&10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_btreeset_pipeline", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_btreeset_pipeline", bb_count);

        // BTreeSet operations produce relations with non-trivial arity
        // (state vars for locals including the set)
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "BTreeSet pipeline VC relations should have arity >= 2, got {max_arity}"
        );

        // Multiple call stubs → should have transition rules with constraints
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "BTreeSet pipeline should have constrained transition rules for stub operations"
        );
    });
}

#[test]
fn test_btreeset_insert_remove_pipeline() {
    // Tests insert followed by remove — exercises both tracked length mutation paths
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_insert_remove() -> bool {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(42);
            s.remove(&42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_insert_remove");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_btreeset_insert_remove", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_btreeset_insert_remove", bb_count);

        // insert + remove are mutation stubs → should have non-trivial arity
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "BTreeSet insert+remove VC relations should have arity >= 2, got {max_arity}"
        );

        // Should have constrained transition rules for the mutation operations
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "BTreeSet insert+remove should have constrained transition rules");

        assert!(
            any_constraint_str(&vc, |c| c.contains("hashset_probe_btreeset_insert_remove_")
                && c.contains("_len")),
            "insert/remove should constrain tracked BTreeSet length vars"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvadd")),
            "insert should generate a tracked length increment constraint (bvadd)"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvsub")),
            "remove should generate a tracked length decrement constraint (bvsub)"
        );
    });
}

#[test]
fn test_btreeset_len_is_empty_pipeline() {
    // Tests len and is_empty — exercises tracked-length return paths
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_len_empty() -> (usize, bool) {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(1);
            (s.len(), s.is_empty())
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_len_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_btreeset_len_empty", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_btreeset_len_empty", bb_count);

        // len/is_empty should be tied to tracked set length, not symbolic fallbacks.
        // The unconstrained fallback vars are "btreeset_len_N" / "btreeset_is_empty_N"
        // appearing as standalone tokens in SMT (space or paren-prefixed).
        // Normal state vars like "_probe_btreeset_len_empty_1" contain
        // "btreeset_len_" as a function-name substring — match by SMT token boundary.
        assert!(
            !any_constraint_str(&vc, |c| c.contains(" btreeset_len_")
                || c.contains("(btreeset_len_")),
            "BTreeSet len should not introduce unconstrained symbolic btreeset_len_* vars"
        );
        assert!(
            !any_constraint_str(&vc, |c| c.contains(" btreeset_is_empty_")
                || c.contains("(btreeset_is_empty_")),
            "BTreeSet is_empty should not introduce unconstrained symbolic btreeset_is_empty_* vars"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("hashset_probe_btreeset_len_empty_")
                && c.contains("_len")),
            "len/is_empty should reference tracked BTreeSet length vars"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("bvadd")),
            "insert should update tracked length before len/is_empty reads"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("#x0000000000000000")
                || c.contains("(_ bv0 64)")),
            "tracked is_empty/initialization should compare/update against zero"
        );

        // len returns usize (BV64), is_empty returns bool -> should have bitvec state vars.
        let has_bv =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bitvec));
        assert!(has_bv, "BTreeSet len+is_empty VC should have bitvec state vars");

        // Should have constrained transition rules
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "BTreeSet len+is_empty should have constrained transition rules");
    });
}

#[test]
fn test_btreeset_clear_pipeline() {
    // Tests clear — exercises cleared-map path and tracked length reset
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_clear_pipeline() {
            let mut s: BTreeSet<u32> = BTreeSet::new();
            s.insert(1);
            s.insert(2);
            s.clear();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_clear_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_btreeset_clear_pipeline", ChcConfig::default());
        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_btreeset_clear_pipeline", bb_count);

        // Clear resets the set → should have non-trivial arity and constrained transitions
        let max_arity =
            vc.relations.iter().map(trust_mc_core::RelationDecl::arity).max().unwrap_or(0);
        assert!(
            max_arity >= 2,
            "BTreeSet clear VC relations should have arity >= 2, got {max_arity}"
        );

        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "BTreeSet clear should have constrained transition rules for the clear operation"
        );

        assert!(
            any_constraint_str(&vc, |c| c.contains("hashset_probe_btreeset_clear_pipeline_")
                && c.contains("_len")),
            "clear should constrain tracked BTreeSet length vars"
        );
        assert!(
            any_constraint_str(&vc, |c| c.contains("#x0000000000000000")
                || c.contains("(_ bv0 64)")),
            "clear should reset tracked BTreeSet length to zero"
        );
    });
}

// =========================================================================
// BTreeSet detect_collection_type integration tests
// =========================================================================

#[test]
fn test_btreeset_detect_collection_type_returns_hashset() {
    // BTreeSet is detected as "hashset" kind by detect_collection_type
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_type(s: BTreeSet<u32>) {
            let _ = s;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_btreeset_type");
        let arg_ty = sig.inputs()[0];

        let (kind, name) =
            ChcCtx::detect_collection_type(arg_ty).expect("BTreeSet should be detected");
        assert_eq!(kind, "hashset", "BTreeSet should be detected as hashset kind");
        assert!(name.contains("BTreeSet"), "name should contain BTreeSet, got: {}", name);
    });
}

#[test]
fn test_btreeset_ref_detect_collection_type() {
    // &BTreeSet<u32> and &mut BTreeSet<u32> should also be detected
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeSet;

        pub fn probe_btreeset_ref(s: &BTreeSet<u32>, s_mut: &mut BTreeSet<u32>) {
            let _ = (s, s_mut);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_btreeset_ref");

        // &BTreeSet<u32>
        let ref_ty = sig.inputs()[0];
        let (kind, _) =
            ChcCtx::detect_collection_type(ref_ty).expect("&BTreeSet should be detected");
        assert_eq!(kind, "hashset");

        // &mut BTreeSet<u32>
        let mut_ref_ty = sig.inputs()[1];
        let (kind, _) =
            ChcCtx::detect_collection_type(mut_ref_ty).expect("&mut BTreeSet should be detected");
        assert_eq!(kind, "hashset");
    });
}

// =============================================================================
// Error-path tests: translate_btreeset_call returns None
// =============================================================================
//
// Part of #2627: error-path test coverage gaps.

/// Minimal source for constructing a ChcCtx without BTreeSet-specific MIR.
const BTREESET_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_simple() {}
"#;

/// BTreeSet iterator stubs (IntoIter, Iter, IterNext) return None — unconstrained.
#[test]
fn test_translate_btreeset_iterator_stubs_return_none() {
    with_test_ay_ctx_for_source(BTREESET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::BTreeSetIntoIter, StubKind::BTreeSetIter, StubKind::BTreeSetIterNext]
        {
            let result = chc_ctx.translate_btreeset_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} should return None (unconstrained iterator)");
        }
    });
}

/// Non-BTreeSet stub kind returns None (catch-all arm).
#[test]
fn test_translate_btreeset_non_btreeset_stub_returns_none() {
    with_test_ay_ctx_for_source(BTREESET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_btreeset_call(StubKind::BigIntAdd, &[], &modified, None);
        assert!(result.is_none(), "non-BTreeSet stub should return None");

        let result = chc_ctx.translate_btreeset_call(StubKind::VecPush, &[], &modified, None);
        assert!(result.is_none(), "VecPush is not a BTreeSet stub");
    });
}

/// BTreeSetNew with dest_local=None returns None (no output state var to initialize).
#[test]
fn test_translate_btreeset_new_no_dest_returns_none() {
    with_test_ay_ctx_for_source(BTREESET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // dest_local=None means no output state var → translate_set_new_common returns None
        let result = chc_ctx.translate_btreeset_call(StubKind::BTreeSetNew, &[], &modified, None);
        assert!(result.is_none(), "BTreeSetNew with no dest_local should return None");
    });
}

/// BTreeSet mutating operations with empty args return None (propagated from shared helpers).
#[test]
fn test_translate_btreeset_mutating_ops_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BTREESET_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // Insert, Contains, Remove need at least 2 args (self + key)
        for stub in [StubKind::BTreeSetInsert, StubKind::BTreeSetContains, StubKind::BTreeSetRemove]
        {
            let result = chc_ctx.translate_btreeset_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");
        }

        // Len, IsEmpty, Clear, Clone need at least 1 arg (self)
        for stub in [
            StubKind::BTreeSetLen,
            StubKind::BTreeSetIsEmpty,
            StubKind::BTreeSetClear,
            StubKind::BTreeSetClone,
        ] {
            let result = chc_ctx.translate_btreeset_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");
        }
    });
}

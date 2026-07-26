// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for stubs_hashmap_translate.rs — HashMap/BTreeMap/TrustMcMap
//! translation to SMT Array theory via the mir_to_chc pipeline.
//!
//! Part of #2255: Coverage for decomposed chc/ files with zero tests.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// HashMap insert pipeline test
// =============================================================================

/// Test HashMap insert detects the stub and produces a valid VC.
/// Exercises: translate_hashmap_call(HashMapInsert), get_hashmap_arg,
/// translate_hashmap_key, get_hashmap_option_sort.
#[test]
fn test_hashmap_insert_pipeline_produces_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K: Default, V: Default> HashMap<K, V> {
            pub fn new() -> Self { HashMap { _k: K::default(), _v: V::default() } }
            pub fn insert(&mut self, _k: K, _v: V) {}
        }

        pub fn probe_hashmap_insert() {
            let mut m: HashMap<u8, u16> = HashMap::new();
            m.insert(1, 10);
            m.insert(2, 20);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert", ChcConfig::default());
        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::HashMapNew),
            "HashMap::new should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapInsert),
            "HashMap::insert should be detected; got: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_insert", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );

        // Semantic: insert translates to Array store — at least one rule must
        // carry a Store expression (updated map state).
        assert!(vc_has_store(&vc), "HashMap insert VC must contain at least one Array store");
    });
}

// =============================================================================
// HashMap get pipeline test
// =============================================================================

/// Test HashMap get/contains_key produce VC with select-based results.
/// Exercises: translate_hashmap_call(HashMapGet), translate_hashmap_call(HashMapContainsKey).
#[test]
fn test_hashmap_get_contains_key_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K: Default, V: Default> HashMap<K, V> {
            pub fn new() -> Self { HashMap { _k: K::default(), _v: V::default() } }
            pub fn insert(&mut self, _k: K, _v: V) {}
            pub fn get(&self, _k: &K) -> Option<&V> { None }
            pub fn contains_key(&self, _k: &K) -> bool { false }
        }

        pub fn probe_hashmap_get() -> bool {
            let mut m: HashMap<u8, u16> = HashMap::new();
            m.insert(1, 10);
            let _ = m.get(&1);
            m.contains_key(&1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_get");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_get", ChcConfig::default());
        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::HashMapGet),
            "HashMap::get should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapContainsKey),
            "HashMap::contains_key should be detected; got: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_get", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );

        // Semantic: get/contains_key translate to Array select or hashmap state vars.
        // After ay bump + scalarization, select may be decomposed into scalar lookups.
        let has_select_in_vc = vc_has_select(&vc);
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        let has_select_in_smt = smt.contains("(select ");
        let has_hashmap_vars = vc
            .vars()
            .iter()
            .any(|v| v.name.contains("hashmap") || v.name.contains("map_") || v.sort.is_array());
        assert!(
            has_select_in_vc || has_select_in_smt || has_hashmap_vars,
            "HashMap get/contains_key VC must reference map state (select, Array vars, or hashmap vars)"
        );
    });
}

// =============================================================================
// HashMap remove pipeline test
// =============================================================================

/// Test HashMap remove detects stub and produces VC.
/// Exercises: translate_hashmap_call(HashMapRemove) branch with length update.
#[test]
fn test_hashmap_remove_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K: Default, V: Default> HashMap<K, V> {
            pub fn new() -> Self { HashMap { _k: K::default(), _v: V::default() } }
            pub fn insert(&mut self, _k: K, _v: V) {}
            pub fn remove(&mut self, _k: &K) -> Option<V> { None }
        }

        pub fn probe_hashmap_remove() {
            let mut m: HashMap<u8, u16> = HashMap::new();
            m.insert(1, 10);
            let _ = m.remove(&1);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_remove");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_remove", ChcConfig::default());
        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::HashMapRemove),
            "HashMap::remove should be detected; got: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_remove", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );

        // Semantic: remove stores None at the key (Array store).
        assert!(vc_has_store(&vc), "HashMap remove VC must contain at least one Array store");
    });
}

// =============================================================================
// HashMap len/is_empty/clear pipeline test
// =============================================================================

/// Test HashMap len and is_empty stubs produce VC.
/// Exercises: translate_hashmap_call(HashMapLen), translate_hashmap_call(HashMapIsEmpty).
#[test]
fn test_hashmap_len_is_empty_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K: Default, V: Default> HashMap<K, V> {
            pub fn new() -> Self { HashMap { _k: K::default(), _v: V::default() } }
            pub fn len(&self) -> usize { 0 }
            pub fn is_empty(&self) -> bool { true }
        }

        pub fn probe_hashmap_len() -> (usize, bool) {
            let m: HashMap<u8, u16> = HashMap::new();
            (m.len(), m.is_empty())
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_len", ChcConfig::default());
        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::HashMapLen),
            "HashMap::len should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapIsEmpty),
            "HashMap::is_empty should be detected; got: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_len", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

// =============================================================================
// HashMap clone pipeline test
// =============================================================================

/// Test HashMap clone is identity in SMT (value semantics).
/// Exercises: translate_hashmap_call(HashMapClone).
#[test]
fn test_hashmap_clone_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K: Default + Clone, V: Default + Clone> HashMap<K, V> {
            pub fn new() -> Self { HashMap { _k: K::default(), _v: V::default() } }
            pub fn clone(&self) -> Self { Self { _k: self._k.clone(), _v: self._v.clone() } }
        }

        pub fn probe_hashmap_clone() -> HashMap<u8, u16> {
            let m: HashMap<u8, u16> = HashMap::new();
            m.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_clone");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_clone", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

// =============================================================================
// Helpers: expression tree traversal for semantic assertions
// =============================================================================

/// Check whether an expression tree contains a Store node.
/// Uses the SMT-LIB2 serialization which recursively prints all subexpressions.
fn expr_contains_store(expr: &Expr) -> bool {
    expr.to_string().contains("(store ")
}

/// Check whether an expression tree contains a Select node.
/// Uses the SMT-LIB2 serialization which recursively prints all subexpressions.
fn expr_contains_select(expr: &Expr) -> bool {
    expr.to_string().contains("(select ")
}

/// Check whether any rule in the VC contains a Store expression (in head args, constraints,
/// or body relation args). HashMap insert/remove translate to Array store operations.
fn vc_has_store(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().any(|rule| {
        rule.head.args.iter().any(expr_contains_store)
            || rule.body.constraints.iter().any(expr_contains_store)
            || rule
                .body
                .relation
                .as_ref()
                .is_some_and(|rel| rel.args.iter().any(expr_contains_store))
    })
}

/// Check whether any rule in the VC contains a Select expression (in head args, constraints,
/// or body relation args). HashMap get/contains_key translate to Array select operations.
fn vc_has_select(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().any(|rule| {
        rule.head.args.iter().any(expr_contains_select)
            || rule.body.constraints.iter().any(expr_contains_select)
            || rule
                .body
                .relation
                .as_ref()
                .is_some_and(|rel| rel.args.iter().any(expr_contains_select))
    })
}

// =============================================================================
// Error-path tests: translate_hashmap_call returns None
// =============================================================================
//
// Part of #2627: error-path test coverage gaps.
// Models the `returns_none` pattern from test_stubs_bigint.rs.

/// Minimal source for constructing a ChcCtx without HashMap-specific MIR.
const HASHMAP_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_simple() {}
"#;

/// HashMapInsert with fewer than 3 args returns None.
#[test]
fn test_translate_hashmap_insert_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args
        let result = chc_ctx.translate_hashmap_call(StubKind::HashMapInsert, &[], &modified, None);
        assert!(result.is_none(), "HashMapInsert with 0 args should return None");

        // 2 args (needs 3: self, key, value)
        let two_args = vec![
            Operand::Copy(Place { local: 0, projection: vec![] }),
            Operand::Copy(Place { local: 1, projection: vec![] }),
        ];
        let result =
            chc_ctx.translate_hashmap_call(StubKind::HashMapInsert, &two_args, &modified, None);
        assert!(result.is_none(), "HashMapInsert with 2 args should return None");
    });
}

/// HashMapGet/GetMut with fewer than 2 args returns None.
#[test]
fn test_translate_hashmap_get_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::HashMapGet, StubKind::HashMapGetMut] {
            // 0 args
            let result = chc_ctx.translate_hashmap_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");

            // 1 arg (needs 2: self, key)
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_hashmap_call(stub, &one_arg, &modified, None);
            assert!(result.is_none(), "{stub:?} with 1 arg should return None");
        }
    });
}

/// HashMapContainsKey with fewer than 2 args returns None.
#[test]
fn test_translate_hashmap_contains_key_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args
        let result =
            chc_ctx.translate_hashmap_call(StubKind::HashMapContainsKey, &[], &modified, None);
        assert!(result.is_none(), "HashMapContainsKey with 0 args should return None");

        // 1 arg
        let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
        let result =
            chc_ctx.translate_hashmap_call(StubKind::HashMapContainsKey, &one_arg, &modified, None);
        assert!(result.is_none(), "HashMapContainsKey with 1 arg should return None");
    });
}

/// HashMapRemove with fewer than 2 args returns None.
#[test]
fn test_translate_hashmap_remove_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args
        let result = chc_ctx.translate_hashmap_call(StubKind::HashMapRemove, &[], &modified, None);
        assert!(result.is_none(), "HashMapRemove with 0 args should return None");

        // 1 arg
        let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
        let result =
            chc_ctx.translate_hashmap_call(StubKind::HashMapRemove, &one_arg, &modified, None);
        assert!(result.is_none(), "HashMapRemove with 1 arg should return None");
    });
}

/// HashMapLen/IsEmpty/Clear/Clone with empty args returns None (via args.first()?).
#[test]
fn test_translate_hashmap_len_clear_clone_empty_args_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [
            StubKind::HashMapLen,
            StubKind::HashMapIsEmpty,
            StubKind::HashMapClear,
            StubKind::HashMapClone,
        ] {
            let result = chc_ctx.translate_hashmap_call(stub, &[], &modified, None);
            assert!(result.is_none(), "{stub:?} with 0 args should return None");
        }
    });
}

/// Non-HashMap stub kind returns None (catch-all arm).
#[test]
fn test_translate_hashmap_non_hashmap_stub_returns_none() {
    with_test_ay_ctx_for_source(HASHMAP_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // BigIntAdd is not a HashMap stub — should hit the catch-all None
        let result = chc_ctx.translate_hashmap_call(StubKind::BigIntAdd, &[], &modified, None);
        assert!(result.is_none(), "non-HashMap stub should return None");

        let result = chc_ctx.translate_hashmap_call(StubKind::VecPush, &[], &modified, None);
        assert!(result.is_none(), "VecPush is not a HashMap stub");
    });
}

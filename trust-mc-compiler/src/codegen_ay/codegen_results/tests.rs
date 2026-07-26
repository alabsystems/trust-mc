// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for AY codegen result aggregation metadata.

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX;
use std::path::PathBuf;
use trust_mc_metadata::{HarnessAttributes, HarnessKind};

/// Helper to construct a `AYCodegenResults` without `TyCtxt`.
fn make_results(reachability: ReachabilityType, crate_name: &str) -> AYCodegenResults {
    AYCodegenResults {
        reachability,
        harnesses: vec![],
        unsupported_constructs: BTreeMap::new(),
        items: vec![],
        crate_name: crate_name.into(),
    }
}

fn make_harness(name: &str) -> HarnessMetadata {
    let name = name.to_owned();
    HarnessMetadata {
        pretty_name: name.clone(),
        mangled_name: name,
        crate_name: "test_crate".into(),
        original_file: "test.rs".into(),
        original_start_line: 1,
        original_end_line: 10,
        model_file: PathBuf::from("test.smt2"),
        attributes: HarnessAttributes::new(HarnessKind::Proof),
        contract: None,
        has_loop_contracts: false,
        is_automatically_generated: false,
    }
}

fn numbered_locations(prefix: &str, suffix: &str, count: usize) -> Vec<String> {
    let mut locations = Vec::with_capacity(count);
    for i in 0..count {
        let mut location = String::with_capacity(prefix.len() + suffix.len() + 20);
        location.push_str(prefix);
        write!(&mut location, "{i}").expect("writing location index to String should not fail");
        location.push_str(suffix);
        locations.push(location);
    }
    locations
}

// --- AYCodegenResults metadata generation ---

#[test]
fn test_generate_metadata_empty_harnesses_mode() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let results = make_results(ReachabilityType::Harnesses, "my_crate");
    let md = results.generate_metadata();
    assert_eq!(md.crate_name, "my_crate");
    assert!(md.proof_harnesses.is_empty());
    assert!(md.test_harnesses.is_empty());
    assert!(md.unsupported_features.is_empty());
}

#[test]
fn test_generate_metadata_harnesses_routed_to_proofs() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::Harnesses, "proof_crate");
    results.harnesses.push(make_harness("my_proof"));
    let md = results.generate_metadata();
    assert_eq!(md.proof_harnesses.len(), 1);
    assert_eq!(md.proof_harnesses[0].pretty_name, "my_proof");
    assert!(md.test_harnesses.is_empty());
}

#[test]
fn test_generate_metadata_allfns_routed_to_tests() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::AllFns, "test_crate");
    results.harnesses.push(make_harness("my_test"));
    let md = results.generate_metadata();
    assert!(md.proof_harnesses.is_empty());
    assert_eq!(md.test_harnesses.len(), 1);
    assert_eq!(md.test_harnesses[0].pretty_name, "my_test");
}

#[test]
fn test_generate_metadata_none_routed_to_tests() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::None, "none_crate");
    results.harnesses.push(make_harness("none_mode_harness"));
    let md = results.generate_metadata();
    assert!(md.proof_harnesses.is_empty());
    assert_eq!(md.test_harnesses.len(), 1);
    assert_eq!(md.test_harnesses[0].pretty_name, "none_mode_harness");
}

#[test]
fn test_generate_metadata_pubfns_routed_to_tests() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::PubFns, "lib_crate");
    results.harnesses.push(make_harness("pub_fn"));
    let md = results.generate_metadata();
    assert!(md.proof_harnesses.is_empty());
    assert_eq!(md.test_harnesses.len(), 1);
}

#[test]
fn test_generate_metadata_unsupported_features() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::Harnesses, "crate_with_unsupported");
    results
        .unsupported_constructs
        .insert("global_asm".into(), vec!["foo.rs:10".into(), "bar.rs:20".into()]);
    let md = results.generate_metadata();
    assert_eq!(md.unsupported_features.len(), 1);
    assert_eq!(md.unsupported_features[0].feature, "global_asm");
    assert_eq!(md.unsupported_features[0].locations.len(), 2);
    assert!(
        md.unsupported_features[0]
            .locations
            .contains(&trust_mc_metadata::Location { filename: "foo.rs:10".into(), start_line: 0 })
    );
}

#[test]
fn test_generate_metadata_multiple_unsupported() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    results.unsupported_constructs.insert("asm".into(), vec!["a.rs".into()]);
    results.unsupported_constructs.insert("coroutine".into(), vec!["b.rs".into()]);
    let md = results.generate_metadata();
    assert_eq!(md.unsupported_features.len(), 2);
}

#[test]
fn test_generate_metadata_emits_and_consumes_chc_fallback_metrics() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    crate::codegen_ay::chc::clear_chc_fallback_counts();
    crate::codegen_ay::chc::set_place_translation_drop_count_for_test(0);
    crate::codegen_ay::chc::set_constant_translation_drop_count_for_test(0);
    crate::codegen_ay::chc::set_unsupported_field_projection_count_for_test(0);
    crate::codegen_ay::chc::set_chc_fallback_count_for_test("foo::harness", 2);

    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();

    let info = md.chc_fallbacks.expect("expected chc_fallbacks in metadata");
    assert_eq!(info.total_count, 2);
    assert_eq!(info.per_harness.get("foo::harness").copied(), Some(2));

    // generate_metadata uses take_chc_fallback_counts(); the second call should be empty.
    let md_again = results.generate_metadata();
    assert!(md_again.chc_fallbacks.is_none());
}

#[test]
fn test_generate_metadata_populates_chc_translation_drops() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    crate::codegen_ay::chc::set_place_translation_drop_count_for_test(2);
    crate::codegen_ay::chc::set_constant_translation_drop_count_for_test(3);
    crate::codegen_ay::chc::set_unsupported_field_projection_count_for_test(4);

    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();

    let info = md.chc_translation_drops.expect("expected chc_translation_drops in metadata");
    assert_eq!(info.place_count, 2);
    assert_eq!(info.constant_count, 3);
    assert_eq!(info.field_projection_count, 4);

    // generate_metadata must consume all translation-drop counters via take_* accessors.
    assert_eq!(crate::codegen_ay::take_place_translation_drop_count(), 0);
    assert_eq!(crate::codegen_ay::take_constant_translation_drop_count(), 0);
    assert_eq!(crate::codegen_ay::take_unsupported_field_projection_count(), 0);
}

#[test]
fn test_generate_metadata_populates_coerce_eq_drops() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::{
        clear_chc_coerce_eq_dropped_constraint_counts_by_fn,
        set_chc_coerce_eq_dropped_constraint_count_for_test,
        take_chc_coerce_eq_dropped_constraint_counts_by_fn,
    };

    clear_chc_coerce_eq_dropped_constraint_counts_by_fn();
    set_chc_coerce_eq_dropped_constraint_count_for_test("foo::harness", 3);

    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();

    // Metadata should contain the coerce-eq drop info.
    let info = md.chc_coerce_eq_drops.expect("expected chc_coerce_eq_drops in metadata");
    assert_eq!(info.total_count, 3);
    assert_eq!(info.per_harness.get("foo::harness").copied(), Some(3));

    // generate_metadata drains per-harness coerce_eq drop counts via `take_*`.
    assert!(
        take_chc_coerce_eq_dropped_constraint_counts_by_fn().is_empty(),
        "coerce_eq drop counts should be consumed by metadata generation"
    );

    // Second generation should have no drops.
    let md_again = results.generate_metadata();
    assert!(md_again.chc_coerce_eq_drops.is_none());

    clear_chc_coerce_eq_dropped_constraint_counts_by_fn();
}

#[test]
fn test_generate_metadata_consumes_constant_zero_fallback_counter() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    crate::codegen_ay::set_constant_zero_fallback_count_for_test(3);

    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();

    let info = md.constant_zero_fallbacks.expect("expected constant_zero_fallbacks in metadata");
    assert_eq!(info.count, 3);

    assert_eq!(
        crate::codegen_ay::take_constant_zero_fallback_count(),
        0,
        "metadata generation should consume constant zero fallback count"
    );
}

// --- extend ---

#[test]
fn test_extend_merges_unsupported() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    results.unsupported_constructs.insert("asm".into(), vec!["existing.rs".into()]);

    let mut min_ctx = MinimalAYCtx::default();
    min_ctx.unsupported_constructs.insert("asm", vec!["new.rs".into()]);
    min_ctx.unsupported_constructs.insert("coroutine", vec!["coro.rs".into()]);

    results.extend(min_ctx, vec![], None);

    assert_eq!(results.unsupported_constructs.len(), 2);
    assert_eq!(results.unsupported_constructs["asm"].len(), 2);
    assert_eq!(results.unsupported_constructs["coroutine"].len(), 1);
}

#[test]
fn test_extend_appends_harness() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    let min_ctx = MinimalAYCtx::default();

    results.extend(min_ctx, vec![], Some(make_harness("h1")));
    assert_eq!(results.harnesses.len(), 1);
    assert_eq!(results.harnesses[0].pretty_name, "h1");
}

#[test]
fn test_extend_none_harness_noop() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    let min_ctx = MinimalAYCtx::default();

    results.extend(min_ctx, vec![], None);
    assert!(results.harnesses.is_empty());
}

// --- format_unsupported_report ---

#[test]
fn test_format_report_empty() {
    let results = make_results(ReachabilityType::Harnesses, "crate");
    assert!(results.format_unsupported_report().is_none());
}

#[test]
fn test_format_report_single_construct() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    results.unsupported_constructs.insert("global_asm".into(), vec!["foo.rs:10".into()]);
    let report = results.format_unsupported_report().unwrap();
    assert!(report.contains("global_asm"));
    assert!(report.contains("foo.rs:10"));
    assert!(report.contains("Verification will fail"));
}

#[test]
fn test_format_report_truncates_at_5() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    let locations = numbered_locations("file", ".rs", 8);
    results.unsupported_constructs.insert("many_locs".into(), locations);
    let report = results.format_unsupported_report().unwrap();
    assert!(report.contains("file0.rs"));
    assert!(report.contains("file4.rs"));
    assert!(!report.contains("file5.rs"));
    assert!(report.contains("and 3 more"));
}

#[test]
fn test_format_report_truncates_each_construct_independently() {
    let mut results = make_results(ReachabilityType::Harnesses, "crate");
    let asm_locs = numbered_locations("asm_", ".rs", 7);
    let coro_locs = numbered_locations("coro_", ".rs", 6);
    results.unsupported_constructs.insert("asm".into(), asm_locs);
    results.unsupported_constructs.insert("coroutine".into(), coro_locs);

    let report = results.format_unsupported_report().unwrap();

    assert!(report.contains("asm_0.rs"));
    assert!(report.contains("asm_4.rs"));
    assert!(!report.contains("asm_5.rs"));
    assert!(report.contains("and 2 more"));
    assert!(report.contains("coro_0.rs"));
    assert!(report.contains("coro_4.rs"));
    assert!(!report.contains("coro_5.rs"));
    assert!(report.contains("and 1 more"));
}

// --- Unsoundness counter metadata coverage/gap proofs (#2424, #2584) ---

/// Proves that `ASSUME_DROPPED_TRANSITION_COUNT` is serialized into
/// `KaniMetadata` so the driver can gate verification confidence.
#[test]
fn test_assume_dropped_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.assume_dropped_transition.swap(5, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.assume_dropped_transition.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.assume_dropped_transitions.as_ref().map(|info| info.count),
        Some(5),
        "KaniMetadata must carry assume_dropped_transitions count"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("assume_dropped_transitions"),
        "KaniMetadata should contain assume_dropped_transitions field: {json}"
    );
}

/// Proves that `STORE_DROPPED_TRANSITION_COUNT` IS serialized into
/// `KaniMetadata`, making dropped stores visible to the driver for demotion.
/// Fixes gap #2424: dropped stores previously only emitted stderr warnings.
#[test]
fn test_store_dropped_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.store_dropped_transition.swap(3, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.store_dropped_transition.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.store_dropped_transitions.as_ref().map(|info| info.count),
        Some(3),
        "KaniMetadata must carry store_dropped_transitions count"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("store_dropped_transitions"),
        "KaniMetadata should contain store_dropped_transitions field (fix #2424): {json}"
    );
}

/// Proves that `HEAP_CHECK_UNTRANSLATABLE_COUNT` is serialized into
/// `KaniMetadata`, so driver-side reporting can observe fail-closed heap checks.
#[test]
fn test_heap_check_untranslatable_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.heap_check_untranslatable.swap(2, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.heap_check_untranslatable.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.heap_check_untranslatable.as_ref().map(|info| info.count),
        Some(2),
        "KaniMetadata must carry heap_check_untranslatable count"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("heap_check_untranslatable"),
        "KaniMetadata should contain heap_check_untranslatable field: {json}"
    );
}

/// Proves that `ASSERT_UNTRANSLATABLE_COUNT` is serialized into
/// `KaniMetadata`, so driver-side reporting can observe fail-closed assertion rules.
#[test]
fn test_assert_untranslatable_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.assert_untranslatable.swap(4, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.assert_untranslatable.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.assert_untranslatable.as_ref().map(|info| info.count),
        Some(4),
        "KaniMetadata must carry assert_untranslatable count"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("assert_untranslatable"),
        "KaniMetadata should contain assert_untranslatable field: {json}"
    );
}

/// Proves that `HEAP_CHECK_UNKNOWN_LAYOUT_COUNT` is serialized into
/// `KaniMetadata` to preserve visibility into unknown-layout fail-closed checks.
#[test]
fn test_heap_check_unknown_layout_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.heap_check_unknown_layout.swap(6, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.heap_check_unknown_layout.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.heap_check_unknown_layout.as_ref().map(|info| info.count),
        Some(6),
        "KaniMetadata must carry heap_check_unknown_layout count"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("heap_check_unknown_layout"),
        "KaniMetadata should contain heap_check_unknown_layout field: {json}"
    );
}

/// Proves that `TYPE_SORT_FALLBACK_COUNT` is serialized into
/// `KaniMetadata`, so the driver can demote proofs using narrower type sorts (#2705).
///
/// Uses `>= 3` because `record_type_sort_fallback()` is called by parallel
/// tests (e.g. `test_codegen_types.rs`), each doing `fetch_add(1)` on the
/// same global counter.
#[test]
fn test_type_sort_fallback_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    crate::codegen_ay::chc::set_type_sort_fallback_count_for_test(3);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();

    let count = md.type_sort_fallbacks.as_ref().map(|info| info.count);
    assert!(
        count.is_some_and(|c| c >= 3),
        "KaniMetadata must carry type_sort_fallbacks count >= 3, got {count:?}"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("type_sort_fallbacks"),
        "KaniMetadata should contain type_sort_fallbacks field (fix #2705): {json}"
    );
}

/// Proves that the signedness fallback counter is serialized into
/// `KaniMetadata`, so driver-side demotion can trigger on signedness defaults (#2749).
///
/// Uses `>= 7` instead of `== 7` because `signedness_fallback()` is a free
/// function called by parallel tests (each does `fetch_add(1)` on the same
/// global counter). Between `set(7)` and `take()` inside `generate_metadata`,
/// parallel tests may have incremented the counter. The important property is
/// that the counter value (at least 7) IS serialized — not its exact value.
#[test]
fn test_signedness_fallback_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev = crate::codegen_ay::shared::replace_signedness_fallback_count_for_test(7);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    crate::codegen_ay::shared::replace_signedness_fallback_count_for_test(prev);

    let count = md.signedness_fallbacks.as_ref().map(|info| info.count);
    assert!(
        count.is_some_and(|c| c >= 7),
        "KaniMetadata must carry signedness_fallbacks count >= 7, got {count:?}"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("signedness_fallbacks"),
        "KaniMetadata should contain signedness_fallbacks field (fix #2749): {json}"
    );
}

/// Proves that `UNHANDLED_CALL_COUNT` is serialized into
/// `KaniMetadata`, so driver-side demotion can trigger on unhandled calls (#2602).
#[test]
fn test_unhandled_call_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev = crate::codegen_ay::chc::get_chc_unhandled_call_count();
    crate::codegen_ay::chc::set_chc_unhandled_call_count_for_test(5);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    crate::codegen_ay::chc::set_chc_unhandled_call_count_for_test(prev);

    assert_eq!(
        md.unhandled_calls.as_ref().map(|info| info.count),
        Some(5),
        "KaniMetadata must carry unhandled_calls count of 5"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("unhandled_calls"),
        "KaniMetadata should contain unhandled_calls field (#2602): {json}"
    );
}

// --- Unsoundness counter coverage for categories added after initial metadata tests ---
// These test categories in collect_unsoundness_fields() that had zero test coverage.
// Part of #3369: proof_coverage phase audit.

/// Proves that `error_blocked_fmt` counter flows through to metadata.
/// This counter tracks formatting calls blocked to prevent false proofs from fmt::Debug.
#[test]
fn test_error_blocked_fmt_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.error_blocked_fmt.swap(4, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.error_blocked_fmt.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.error_blocked_fmt.as_ref().map(|info| info.count),
        Some(4),
        "KaniMetadata must carry error_blocked_fmt count of 4"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("error_blocked_fmt"),
        "KaniMetadata should contain error_blocked_fmt field: {json}"
    );
}

/// Proves that `known_stdlib_unconstrained` counter flows through to metadata.
/// Tracks calls to known stdlib functions left unconstrained by dispatch.
#[test]
fn test_known_stdlib_unconstrained_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.known_stdlib_unconstrained.swap(3, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.known_stdlib_unconstrained.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.known_stdlib_unconstrained.as_ref().map(|info| info.count),
        Some(3),
        "KaniMetadata must carry known_stdlib_unconstrained count of 3"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("known_stdlib_unconstrained"),
        "KaniMetadata should contain known_stdlib_unconstrained field: {json}"
    );
}

// test_inferable_predicate_count_in_metadata: Staged for relay commit.
// Requires inferable_predicate field on GlobalDiagnosticCounters and
// inferable_predicates field on KaniMetadata (both in unstaged production code).
// Part of #3369.

/// Proves that `diverging_call_drops` counter flows through to metadata.
/// Tracks diverging calls dropped without rules (#3164).
#[test]
fn test_diverging_call_drop_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.diverging_call_drop.swap(2, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.diverging_call_drop.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.diverging_call_drops.as_ref().map(|info| info.count),
        Some(2),
        "KaniMetadata must carry diverging_call_drops count of 2"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("diverging_call_drops"),
        "KaniMetadata should contain diverging_call_drops field (#3164): {json}"
    );
}

/// Proves that `kani_mem_overapprox` counter flows through to metadata.
/// Tracks kani::mem predicates over-approximated as true (#3165).
#[test]
fn test_kani_mem_overapprox_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.kani_mem_overapprox.swap(5, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.kani_mem_overapprox.store(prev, Ordering::Relaxed);

    assert_eq!(
        md.kani_mem_overapprox.as_ref().map(|info| info.count),
        Some(5),
        "KaniMetadata must carry kani_mem_overapprox count of 5"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("kani_mem_overapprox"),
        "KaniMetadata should contain kani_mem_overapprox field (#3165): {json}"
    );
}

/// Proves that `iterator_unsoundness` counter flows through to metadata.
/// Tracks iterator unsound skip counts for both CHC and BMC paths.
#[test]
fn test_iterator_unsoundness_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.iterator_unsound_skip.swap(3, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.iterator_unsound_skip.store(prev, Ordering::Relaxed);

    let info = md.iterator_unsoundness.as_ref().expect("expected iterator_unsoundness in metadata");
    assert_eq!(info.chc_skip_count, 3, "CHC iterator unsound skip count must be 3");

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("iterator_unsoundness"),
        "KaniMetadata should contain iterator_unsoundness field: {json}"
    );
}

/// Proves that `bigint_unsoundness` counter flows through to metadata.
/// Tracks BigInt unsound skip counts for CHC path.
#[test]
fn test_bigint_unsoundness_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    use crate::codegen_ay::chc::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    let prev = GLOBAL_COUNTERS.bigint_unsound_skip.swap(2, Ordering::Relaxed);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    GLOBAL_COUNTERS.bigint_unsound_skip.store(prev, Ordering::Relaxed);

    let info = md.bigint_unsoundness.as_ref().expect("expected bigint_unsoundness in metadata");
    assert_eq!(info.chc_skip_count, 2, "BigInt CHC unsound skip count must be 2");

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("bigint_unsoundness"),
        "KaniMetadata should contain bigint_unsoundness field: {json}"
    );
}

/// Proves that the `into_option_drops` counter flows through to metadata.
/// Tracks Result::Err dropped by IntoOption conversion.
#[test]
fn test_into_option_dropped_count_in_metadata() {
    let _guard = METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let prev = crate::codegen_ay::shared::replace_into_option_dropped_count_for_test(6);
    let results = make_results(ReachabilityType::Harnesses, "crate");
    let md = results.generate_metadata();
    crate::codegen_ay::shared::replace_into_option_dropped_count_for_test(prev);

    assert_eq!(
        md.into_option_drops.as_ref().map(|info| info.count),
        Some(6),
        "KaniMetadata must carry into_option_drops count of 6"
    );

    let json = serde_json::to_string(&md).expect("serialize metadata");
    assert!(
        json.contains("into_option_drops"),
        "KaniMetadata should contain into_option_drops field: {json}"
    );
}

// --- Statement-level counter tests (require set_*_for_test relay infrastructure) ---
// 8 additional tests covering internal_workarounds, abstracted_fallbacks,
// vec_field_fallbacks, pointee_synthesis_fallbacks, unsupported_construct_fallbacks,
// unconstrained_assignments, bmc_store_coercion_fallbacks, and
// sort_harmonize_fresh_var_fallbacks are staged for relay commit with their
// corresponding set_*_for_test() setter functions in production code.
// Worker relay: Part of #3369.

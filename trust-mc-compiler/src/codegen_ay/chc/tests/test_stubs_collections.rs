// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_util_collections.rs — translate_collection_predicate_call,
//! extract_local_index, and get_collection_len_var.
//!
//! Part of #2303 (test coverage for decomposed CHC modules).

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// translate_collection_predicate_call — Phase 2 content-based predicates
// =============================================================================

/// Phase 2: VecContains produces a symbolic Bool (no content model).
#[test]
fn test_translate_vec_contains_returns_symbolic_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_vec_contains(v: &Vec<u32>, item: &u32) -> bool {
            v.contains(item)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_contains");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_contains", ChcConfig::default());

        let modified = HashSet::new();
        // Find a Call terminator with the contains method
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_collection_predicate)
                && stub == StubKind::VecContains
            {
                let result = chc_ctx.translate_collection_predicate_call(stub, args, &modified);
                assert!(result.is_some(), "VecContains should produce a result");
                let expr = result.unwrap();
                assert!(
                    expr.sort().is_bool(),
                    "VecContains result should be Bool, got: {:?}",
                    expr.sort()
                );
                let smt = expr.to_string();
                assert!(
                    smt.contains("vec_contains"),
                    "symbolic var should have vec_contains prefix, got: {smt}"
                );
                return;
            }
        }
        // Vec::contains may lower to slice::contains in MIR; test the stub
        // directly if detection didn't find it in the probe function.
        // Build a synthetic Operand::Copy for local 1 (the &Vec<u32> arg).
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::VecContains,
            &[operand],
            &modified,
        );
        assert!(result.is_some(), "Direct VecContains translation should produce a result");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "VecContains result should be Bool");
    });
}

/// Phase 2: StringContains produces a symbolic Bool.
#[test]
fn test_translate_string_contains_returns_symbolic_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_contains(s: &String, pat: &str) -> bool {
            s.contains(pat)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_contains");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_string_contains", ChcConfig::default());

        let modified = HashSet::new();
        // Test the stub translation directly
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::StringContains,
            &[operand],
            &modified,
        );
        assert!(result.is_some(), "StringContains translation should produce a result");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "StringContains result should be Bool");
        let smt = expr.to_string();
        assert!(
            smt.contains("str_contains"),
            "symbolic var should have str_contains prefix, got: {smt}"
        );
    });
}

/// Phase 2: StringStartsWith produces a symbolic Bool.
#[test]
fn test_translate_string_starts_with_returns_symbolic_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_starts_with(s: &String) -> bool {
            s.starts_with("abc")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_starts_with");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_starts_with", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::StringStartsWith,
            &[operand],
            &modified,
        );
        assert!(result.is_some(), "StringStartsWith translation should produce a result");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "StringStartsWith result should be Bool");
        let smt = expr.to_string();
        assert!(
            smt.contains("str_starts_with"),
            "symbolic var should have str_starts_with prefix, got: {smt}"
        );
    });
}

/// Phase 2: StringEndsWith produces a symbolic Bool.
#[test]
fn test_translate_string_ends_with_returns_symbolic_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ends_with(s: &String) -> bool {
            s.ends_with("xyz")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ends_with");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ends_with", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::StringEndsWith,
            &[operand],
            &modified,
        );
        assert!(result.is_some(), "StringEndsWith translation should produce a result");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "StringEndsWith result should be Bool");
        let smt = expr.to_string();
        assert!(
            smt.contains("str_ends_with"),
            "symbolic var should have str_ends_with prefix, got: {smt}"
        );
    });
}

/// Phase 2: StringIsAscii produces a symbolic Bool.
#[test]
fn test_translate_string_is_ascii_returns_symbolic_bool() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_ascii(s: &String) -> bool {
            s.is_ascii()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_ascii");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_is_ascii", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::StringIsAscii,
            &[operand],
            &modified,
        );
        assert!(result.is_some(), "StringIsAscii translation should produce a result");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "StringIsAscii result should be Bool");
        let smt = expr.to_string();
        assert!(
            smt.contains("str_is_ascii"),
            "symbolic var should have str_is_ascii prefix, got: {smt}"
        );
    });
}

// =============================================================================
// translate_collection_predicate_call — Phase 1 is_empty (sound fallback)
// =============================================================================

/// Phase 1: VecIsEmpty without tracked length returns None for sound fallback.
#[test]
fn test_translate_vec_is_empty_without_tracked_len_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec::Vec;

        pub fn probe_vec_empty(v: &Vec<u32>) -> bool {
            v.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_empty");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_empty", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::VecIsEmpty,
            &[operand],
            &modified,
        );
        assert!(
            result.is_none(),
            "VecIsEmpty without tracked length should return None for sound fallback"
        );
    });
}

/// Phase 1: StringIsEmpty without tracked length returns None for sound fallback.
#[test]
fn test_translate_string_is_empty_without_tracked_len_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_string_empty(s: &String) -> bool {
            s.is_empty()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_empty");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_empty", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);
        let result = chc_ctx.translate_collection_predicate_call(
            StubKind::StringIsEmpty,
            &[operand],
            &modified,
        );
        assert!(
            result.is_none(),
            "StringIsEmpty without tracked length should return None for sound fallback"
        );
    });
}

// =============================================================================
// translate_collection_predicate_call — empty args returns None
// =============================================================================

/// Empty args list should return None for all collection predicates.
#[test]
fn test_translate_collection_predicate_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_empty_args() -> u32 { 42 }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_empty_args");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_empty_args", ChcConfig::default());

        let modified = HashSet::new();
        let empty_args: &[rustc_public::mir::Operand] = &[];

        for stub in [
            StubKind::VecIsEmpty,
            StubKind::StringIsEmpty,
            StubKind::VecContains,
            StubKind::StringContains,
            StubKind::StringStartsWith,
            StubKind::StringEndsWith,
            StubKind::StringIsAscii,
        ] {
            let result = chc_ctx.translate_collection_predicate_call(stub, empty_args, &modified);
            assert!(result.is_none(), "{:?} with empty args should return None", stub);
        }
    });
}

// =============================================================================
// Phase 2 symbolic Bools are distinct (unique counter)
// =============================================================================

/// Each Phase 2 translation produces a distinct symbolic variable.
#[test]
fn test_phase2_predicates_produce_distinct_symbols() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_distinct(s: &String) -> bool {
            s.is_ascii()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_distinct");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_distinct", ChcConfig::default());

        let modified = HashSet::new();
        let place = rustc_public::mir::Place { local: 1, projection: Vec::new() };
        let operand = rustc_public::mir::Operand::Copy(place);

        let r1 = chc_ctx
            .translate_collection_predicate_call(
                StubKind::StringContains,
                std::slice::from_ref(&operand),
                &modified,
            )
            .unwrap();
        let r2 = chc_ctx
            .translate_collection_predicate_call(
                StubKind::StringContains,
                std::slice::from_ref(&operand),
                &modified,
            )
            .unwrap();

        // Each call should produce a unique variable name
        let smt1 = r1.to_string();
        let smt2 = r2.to_string();
        assert_ne!(
            smt1, smt2,
            "Two calls to translate_collection_predicate_call should produce distinct symbols"
        );
    });
}

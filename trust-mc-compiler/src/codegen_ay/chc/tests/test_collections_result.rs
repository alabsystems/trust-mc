// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Result datatype expression-level tests (Part of #2016)
// =============================================================================

/// Verify Result<T, E> datatype has correct Ok/Err constructors.
/// Parallels test_option_datatype_has_some_none for Option.
#[test]
fn test_result_datatype_has_ok_err() {
    use crate::codegen_ay::test_fixtures::result_datatype_sort;

    let ok_sort = Sort::bitvec(32);
    let err_sort = Sort::bitvec(64);
    let result_sort = result_datatype_sort(ok_sort.clone(), err_sort.clone());

    let dt = result_sort.datatype_sort();
    assert!(dt.is_some(), "Result should be a datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 2, "Result should have 2 constructors");

    let ok_ctor = dt.constructors.iter().find(|c| c.name == "Ok");
    assert!(ok_ctor.is_some(), "Result should have Ok constructor");
    let ok_ctor = ok_ctor.unwrap();
    assert_eq!(ok_ctor.fields.len(), 1, "Ok should have 1 field");
    assert_eq!(ok_ctor.fields[0].name, "value", "Ok field should be named 'value'");
    assert_eq!(ok_ctor.fields[0].sort, ok_sort, "Ok field sort should match T");

    let err_ctor = dt.constructors.iter().find(|c| c.name == "Err");
    assert!(err_ctor.is_some(), "Result should have Err constructor");
    let err_ctor = err_ctor.unwrap();
    assert_eq!(err_ctor.fields.len(), 1, "Err should have 1 field");
    assert_eq!(err_ctor.fields[0].name, "value", "Err field should be named 'value'");
    assert_eq!(err_ctor.fields[0].sort, err_sort, "Err field sort should match E");
}

/// Verify result_variant_tester finds scoped Ok/Err constructors (Part of #2631).
///
/// When sort_inference_adt.rs creates Result datatypes via scope_option_ctor(),
/// the constructor names become scoped (e.g., Ok_Result_bv32_bv64 instead of Ok).
/// result_variant_tester must find these scoped names using is_ok_constructor/
/// is_err_constructor predicates.
#[test]
fn test_result_variant_tester_scoped_constructors() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let result_sort_name = "Result_bv32_bv64";
        let ok_ctor_name = names::result_ok_constructor_name(result_sort_name);
        let err_ctor_name = names::result_err_constructor_name(result_sort_name);
        assert_eq!(ok_ctor_name, "Ok_Result_bv32_bv64");
        assert_eq!(err_ctor_name, "Err_Result_bv32_bv64");

        // Create Result sort with scoped constructor names (as sort_inference_adt produces)
        let scoped_result_sort = enum_sort(
            result_sort_name,
            vec![
                (ok_ctor_name.as_str(), vec![("value", Sort::bitvec(32))]),
                (err_ctor_name.as_str(), vec![("value", Sort::bitvec(64))]),
            ],
        );
        let result_var = Expr::var("test_result", scoped_result_sort);

        // result_variant_tester should find scoped Ok/Err via is_ok/is_err predicates
        let is_ok = chc_ctx.result_variant_tester(result_var.clone(), "Ok", "is_ok");
        assert!(is_ok.sort().is_bool(), "scoped Ok should produce Bool tester");
        // Verify it's a real is_constructor tester, not a symbolic fallback
        assert!(
            !matches!(is_ok.value(), ExprValue::Var { .. }),
            "scoped Ok should use is_constructor, not symbolic fallback"
        );

        let is_err = chc_ctx.result_variant_tester(result_var, "Err", "is_err");
        assert!(is_err.sort().is_bool(), "scoped Err should produce Bool tester");
        assert!(
            !matches!(is_err.value(), ExprValue::Var { .. }),
            "scoped Err should use is_constructor, not symbolic fallback"
        );
    });
}

/// Verify scope_option_ctor scopes Result constructors (Part of #2631).
#[test]
fn test_scope_option_ctor_handles_result_variants() {
    use crate::codegen_ay::names;

    let sort_name = "Result_bv32_String";

    // Ok and Err should be scoped
    assert_eq!(names::scope_option_ctor("Ok", sort_name), "Ok_Result_bv32_String");
    assert_eq!(names::scope_option_ctor("Err", sort_name), "Err_Result_bv32_String");

    // Some/None should still be scoped (backward compat)
    assert_eq!(names::scope_option_ctor("Some", sort_name), "Some_Result_bv32_String");
    assert_eq!(names::scope_option_ctor("None", sort_name), "None_Result_bv32_String");

    // Part of #3041: General names are now scoped to avoid Z3 ambiguity
    assert_eq!(names::scope_option_ctor("Continue", sort_name), "Continue_Result_bv32_String");
    assert_eq!(names::scope_option_ctor("Break", sort_name), "Break_Result_bv32_String");
}

// =============================================================================
// MIR-driven Result predicate detection tests
// =============================================================================

#[test]
fn test_detect_result_is_ok_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_ok() -> bool {
            let r: Result<u8, u16> = Ok(1);
            r.is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_is_ok", ChcConfig::default());

        let detected = collect_detected_result_predicate_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::ResultIsOk),
            "Result::is_ok should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_result_is_err_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_err() -> bool {
            let r: Result<u8, u16> = Err(2);
            r.is_err()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_err");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_result_is_err", ChcConfig::default());

        let detected = collect_detected_result_predicate_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::ResultIsErr),
            "Result::is_err should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_bool_stub_registry_and_chc_dispatch_parity() {
    // Guardrail for #2125: registry bool-method stubs must be reachable by CHC
    // predicate dispatch (or explicit mapping in CHC collection stubs).
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::BTreeMap;

        pub fn probe_bool_stubs() {
            let v: Vec<u8> = Vec::new();
            let _ = v.is_empty();
            let _ = v.contains(&1u8);

            let s = String::new();
            let _ = s.is_empty();
            let _ = s.contains("x");
            let _ = s.starts_with("x");
            let _ = s.ends_with("x");
            let _ = s.is_ascii();

            let m: BTreeMap<u8, u16> = BTreeMap::new();
            let _ = m.contains_key(&1);
            let _ = m.is_empty();

            let o: Option<u8> = Some(1);
            let _ = o.is_some();
            let _ = o.is_none();

            let r: Result<u8, u16> = Ok(1);
            let _ = r.is_ok();
            let _ = r.is_err();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_stubs");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bool_stubs", ChcConfig::default());

        let mut detected = HashSet::new();
        detected.extend(collect_detected_collection_predicate_stubs(&chc_ctx, &body));
        detected.extend(collect_detected_result_predicate_stubs(&chc_ctx, &body));

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
            {
                if let Some(stub) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_option_predicate)
                {
                    detected.insert(stub);
                }
                if let Some(stub) = chc_ctx.detect_hashmap_stub(func, args)
                    && matches!(stub, StubKind::HashMapContainsKey | StubKind::HashMapIsEmpty)
                {
                    detected.insert(stub);
                }
            }
        }

        let registry = StubRegistry::new();

        // Phase 1 + Phase 2: registry-to-CHC detection parity for paths that
        // appear in compiled MIR from the probe function above.
        let expected_mir_paths = [
            // Phase 1: length-based predicates
            ("alloc::vec::Vec::<u8>::is_empty", StubKind::VecIsEmpty),
            ("alloc::string::String::is_empty", StubKind::StringIsEmpty),
            ("std::collections::BTreeMap::<u8, u16>::contains_key", StubKind::BTreeMapContainsKey),
            ("std::collections::BTreeMap::<u8, u16>::is_empty", StubKind::BTreeMapIsEmpty),
            ("core::option::Option::<u8>::is_some", StubKind::OptionIsSome),
            ("core::option::Option::<u8>::is_none", StubKind::OptionIsNone),
            ("core::result::Result::<u8, u16>::is_ok", StubKind::ResultIsOk),
            ("core::result::Result::<u8, u16>::is_err", StubKind::ResultIsErr),
            // Phase 2: content-based predicates (Part of #2170)
            // NOTE: VecContains is registry-only because rustc lowers Vec::contains
            // to <[T]>::contains (slice method) in MIR, so the Vec-level path never
            // appears in CHC detection. String methods are dispatched directly.
            ("alloc::string::String::contains", StubKind::StringContains),
            ("alloc::string::String::starts_with", StubKind::StringStartsWith),
            ("alloc::string::String::ends_with", StubKind::StringEndsWith),
            ("alloc::string::String::is_ascii", StubKind::StringIsAscii),
        ];

        for (path, expected_stub) in expected_mir_paths {
            assert_eq!(
                registry.lookup(path),
                Some(expected_stub),
                "registry should classify bool stub path: {}",
                path
            );

            let chc_stub = match expected_stub {
                StubKind::BTreeMapContainsKey => StubKind::HashMapContainsKey,
                StubKind::BTreeMapIsEmpty => StubKind::HashMapIsEmpty,
                _ => expected_stub, // internal enum: StubKind (test scan)
            };

            assert!(
                detected.contains(&chc_stub),
                "CHC should detect bool stub {:?} (from registry {:?} / path {}), got {:?}",
                chc_stub,
                expected_stub,
                path,
                detected
            );
        }

        // Phase 2: registry-only parity checks for paths that don't appear
        // directly in MIR from the probe function. Registry correctness ensures
        // CHC detection will work when these paths appear in real harnesses.
        let registry_only_paths = [
            // Vec::contains lowers to <[T]>::contains in MIR (slice method)
            ("alloc::vec::Vec::<u8>::contains", StubKind::VecContains),
            // Trait-lowered Pattern paths for str::contains/starts_with/ends_with
            ("<&str as core::str::pattern::Pattern>::is_contained_in", StubKind::StringContains),
            ("<&str as core::str::pattern::Pattern>::is_prefix_of", StubKind::StringStartsWith),
            ("<&str as core::str::pattern::Pattern>::is_suffix_of", StubKind::StringEndsWith),
            // Internal ascii helpers
            ("core::str::is_ascii_simple", StubKind::StringIsAscii),
            ("core::str::contains_nonascii", StubKind::StringIsAscii),
            ("core::slice::ascii::<impl [u8]>::is_ascii", StubKind::StringIsAscii),
        ];
        for (path, expected_stub) in registry_only_paths {
            assert_eq!(
                registry.lookup(path),
                Some(expected_stub),
                "registry should classify trait-lowered path: {}",
                path
            );
        }
    });
}

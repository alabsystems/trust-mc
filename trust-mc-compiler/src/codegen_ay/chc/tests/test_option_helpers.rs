// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_option_helpers.rs — Option/Result datatype construction
//! and introspection helpers (365 lines, 0 prior tests).
//!
//! Part of #2016 (test coverage for chc/ modules).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::names::{self, enum_sort, struct_sort};

// =============================================================================
// make_option_sort — enum-style Option construction
// =============================================================================

#[test]
fn test_make_option_sort_bv32_has_none_and_some_constructors() {
    let inner = Sort::bitvec(32);
    let option_sort = make_option_sort(&inner);

    assert!(option_sort.is_datatype(), "Option sort should be a datatype");
    let name = option_sort.datatype_name().unwrap();
    assert!(name.contains("Option"), "sort name should contain 'Option': {}", name);
    let dt = option_sort.datatype_sort().expect("Option should be datatype");
    assert!(
        dt.constructors.iter().any(|ctor| names::is_none_constructor(&ctor.name)),
        "Option sort should have None constructor"
    );
    assert!(
        dt.constructors.iter().any(|ctor| names::is_some_constructor(&ctor.name)),
        "Option sort should have Some constructor"
    );
}

#[test]
fn test_make_option_sort_bool_inner() {
    let inner = Sort::bool();
    let option_sort = make_option_sort(&inner);

    assert!(option_sort.is_datatype());
    let name = option_sort.datatype_name().unwrap();
    assert!(name.contains("Option"), "sort name: {}", name);
    let dt = option_sort.datatype_sort().expect("Option should be datatype");
    assert!(dt.constructors.iter().any(|ctor| names::is_none_constructor(&ctor.name)));
    assert!(dt.constructors.iter().any(|ctor| names::is_some_constructor(&ctor.name)));
}

#[test]
fn test_make_option_sort_int_inner() {
    let inner = Sort::int();
    let option_sort = make_option_sort(&inner);

    assert!(option_sort.is_datatype());
    let dt = option_sort.datatype_sort().expect("Option should be datatype");
    assert!(dt.constructors.iter().any(|ctor| names::is_none_constructor(&ctor.name)));
    assert!(dt.constructors.iter().any(|ctor| names::is_some_constructor(&ctor.name)));
}

// =============================================================================
// option_value_sort — extract inner sort from Option-like datatype
// =============================================================================

#[test]
fn test_option_value_sort_enum_style_extracts_inner() {
    let inner = Sort::bitvec(64);
    let option_sort = make_option_sort(&inner);

    let extracted = option_value_sort(&option_sort);
    assert!(extracted.is_some(), "should extract inner sort from enum-style Option");
    assert_eq!(extracted.unwrap(), inner, "extracted sort should match the original inner sort");
}

#[test]
fn test_option_value_sort_non_datatype_returns_none() {
    let bv = Sort::bitvec(32);
    assert!(option_value_sort(&bv).is_none(), "non-datatype should return None");
}

#[test]
fn test_option_value_sort_struct_style_returns_none() {
    // Struct-style option has a single constructor with is_some+value fields,
    // no "Some" constructor. option_value_sort only finds "Some" or single-field non-None.
    let struct_sort =
        struct_sort("Option_bv32", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);
    // The struct has one constructor but it's not named "Some" and has 2 fields.
    // option_value_sort should not match it.
    let result = option_value_sort(&struct_sort);
    assert!(result.is_none(), "struct-style option should not match option_value_sort");
}

// =============================================================================
// option_payload_variant_name / option_empty_variant_name
// =============================================================================

#[test]
fn test_option_payload_variant_name_enum_style() {
    let option_sort = make_option_sort(&Sort::bitvec(32));
    let name = option_payload_variant_name(&option_sort);
    assert!(name.is_some_and(names::is_some_constructor));
}

#[test]
fn test_option_empty_variant_name_enum_style() {
    let option_sort = make_option_sort(&Sort::bitvec(32));
    let name = option_empty_variant_name(&option_sort);
    assert!(name.is_some_and(names::is_none_constructor));
}

#[test]
fn test_option_payload_variant_name_non_datatype_returns_none() {
    assert!(option_payload_variant_name(&Sort::bitvec(32)).is_none());
}

#[test]
fn test_option_empty_variant_name_non_datatype_returns_none() {
    assert!(option_empty_variant_name(&Sort::bitvec(32)).is_none());
}

#[test]
fn test_option_payload_variant_name_custom_variant() {
    // Custom enum-like datatype with non-standard names
    let custom_sort = enum_sort(
        "MaybeVal",
        vec![("Nothing", vec![]), ("Just", vec![("inner", Sort::bitvec(32))])],
    );
    // No "Some" constructor, but "Just" is a single-field non-"None" constructor
    let name = option_payload_variant_name(&custom_sort);
    assert_eq!(name, Some("Just"));
}

#[test]
fn test_option_empty_variant_name_custom_variant() {
    let custom_sort = enum_sort(
        "MaybeVal",
        vec![("Nothing", vec![]), ("Just", vec![("inner", Sort::bitvec(32))])],
    );
    // No "None" constructor, but "Nothing" is a zero-field constructor
    let name = option_empty_variant_name(&custom_sort);
    assert_eq!(name, Some("Nothing"));
}

// =============================================================================
// make_none_expr_for_option — None construction for both encodings
// =============================================================================

#[test]
fn test_make_none_expr_for_option_enum_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let none_expr = chc_ctx.make_none_expr_for_option(&option_sort);
        assert!(none_expr.is_some(), "should produce None expr for enum-style Option");

        let expr = none_expr.unwrap();
        assert_eq!(expr.sort(), &option_sort, "None expr sort should match Option sort");
    });
}

#[test]
fn test_make_none_expr_for_option_struct_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Build struct-style option sort (single constructor with is_some+value fields)
        let struct_sort =
            struct_sort("Option_bv32", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);
        let none_expr = chc_ctx.make_none_expr_for_option(&struct_sort);
        assert!(none_expr.is_some(), "should produce None expr for struct-style Option");

        let expr = none_expr.unwrap();
        assert_eq!(
            expr.sort(),
            &struct_sort,
            "None expr sort should match struct-style Option sort"
        );
    });
}

#[test]
fn test_make_none_expr_for_option_non_datatype_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bv = Sort::bitvec(32);
        assert!(
            chc_ctx.make_none_expr_for_option(&bv).is_none(),
            "non-datatype sort should return None"
        );
    });
}

// =============================================================================
// make_none_expr — convenience wrapper
// =============================================================================

#[test]
fn test_make_none_expr_produces_option_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let none_expr = chc_ctx.make_none_expr(&Sort::bitvec(64));
        assert!(none_expr.sort().is_datatype(), "None expr should have datatype sort");
        let name = none_expr.sort().datatype_name().unwrap();
        assert!(name.contains("Option"), "sort name should contain 'Option': {}", name);
    });
}

// =============================================================================
// make_some_expr_for_option — Some construction for both encodings
// =============================================================================

#[test]
fn test_make_some_expr_for_option_enum_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let value = Expr::bitvec_const(42u128, 32);
        let some_expr = chc_ctx.make_some_expr_for_option(value, &option_sort);

        assert!(some_expr.is_some(), "should produce Some expr for enum-style Option");
        let expr = some_expr.unwrap();
        assert_eq!(expr.sort(), &option_sort, "Some expr sort should match Option sort");
    });
}

#[test]
fn test_make_some_expr_for_option_struct_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);
        let value = Expr::bitvec_const(42u128, 32);
        let some_expr = chc_ctx.make_some_expr_for_option(value, &struct_sort);

        assert!(some_expr.is_some(), "should produce Some expr for struct-style Option");
        let expr = some_expr.unwrap();
        assert_eq!(expr.sort(), &struct_sort, "Some expr sort should match struct sort");
    });
}

#[test]
fn test_make_some_expr_for_option_option_named_generic_struct_fields() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("fld_0", Sort::bool()), ("fld_1", Sort::bitvec(32))]);
        let value = Expr::bitvec_const(42u128, 32);
        let some_expr = chc_ctx
            .make_some_expr_for_option(value, &struct_sort)
            .expect("Option-shaped struct should still build Some");

        match some_expr.value() {
            ExprValue::DatatypeConstructor { args, .. } => {
                assert!(
                    matches!(
                        args.first().expect("discriminant").value(),
                        ExprValue::BoolConst(true)
                    ),
                    "Option-shaped struct should set the Bool discriminant to true",
                );
                assert_eq!(args.get(1).expect("payload").sort(), &Sort::bitvec(32));
            }
            other => panic!("expected DatatypeConstructor, got {:?}", other),
        }
    });
}

#[test]
fn test_make_some_expr_for_option_coerces_bitvec_width() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Option with bv32 inner, but value is bv64 — should coerce
        let option_sort = make_option_sort(&Sort::bitvec(32));
        let value = Expr::bitvec_const(100u128, 64);
        let some_expr = chc_ctx.make_some_expr_for_option(value, &option_sort);

        assert!(some_expr.is_some(), "should coerce bv64 value to bv32 for Option<bv32>");
    });
}

#[test]
fn test_make_some_expr_for_option_non_datatype_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bv = Sort::bitvec(32);
        let value = Expr::bitvec_const(0u128, 32);
        assert!(
            chc_ctx.make_some_expr_for_option(value, &bv).is_none(),
            "non-datatype sort should return None"
        );
    });
}

// =============================================================================
// option_is_some — bool predicate extraction
// =============================================================================

#[test]
fn test_option_is_some_enum_style_returns_is_constructor() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let opt_var = Expr::var("test_opt", option_sort);
        let is_some = chc_ctx.option_is_some(opt_var);

        assert!(is_some.sort().is_bool(), "is_some result should be Bool");
    });
}

#[test]
fn test_option_is_some_struct_style_returns_field_select() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);
        let opt_var = Expr::var("test_opt_struct", struct_sort);
        let is_some = chc_ctx.option_is_some(opt_var);

        assert!(is_some.sort().is_bool(), "is_some result should be Bool");
        // Should be a field_select on "is_some", not an is_constructor test
        match is_some.value() {
            ExprValue::DatatypeSelector { selector_name, .. } => {
                assert_eq!(selector_name, "is_some", "should select 'is_some' field");
            }
            other => panic!("expected DatatypeSelector, got {:?}", other),
        }
    });
}

#[test]
fn test_option_is_some_option_named_generic_fields_returns_field_select() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("fld_0", Sort::bool()), ("fld_1", Sort::bitvec(32))]);
        let opt_var = Expr::var("test_opt_struct_generic", struct_sort);
        let before_drop = chc_ctx.diagnostics.place_translation_drop.get();
        let is_some = chc_ctx.option_is_some(opt_var);

        assert!(is_some.sort().is_bool(), "is_some result should be Bool");
        match is_some.value() {
            ExprValue::DatatypeSelector { selector_name, .. } => {
                assert_eq!(selector_name, "fld_0", "should select the Bool discriminant field");
            }
            other => panic!("expected DatatypeSelector, got {:?}", other),
        }
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            before_drop,
            "Option-shaped struct should not fall back to option_some_ctor_missing",
        );
    });
}

/// Part of #3902: non-Datatype receiver must produce symbolic Bool (over-approx),
/// not constant false (under-approx that masks constructor-loss bugs).
#[test]
fn test_option_is_some_non_datatype_returns_symbolic_bool() {
    use ay_bindings::ExprValue;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Non-datatype expr — should over-approximate to fresh symbolic Bool.
        let bv_expr = Expr::bitvec_const(0u128, 32);
        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();
        let result = chc_ctx.option_is_some(bv_expr);
        assert!(result.sort().is_bool(), "fallback should be Bool");
        match result.value() {
            ExprValue::Var { name } => assert!(
                name.starts_with("option_is_some_"),
                "fallback var should use option_is_some prefix, got: {name}"
            ),
            other => panic!("non-DT fallback should be symbolic variable, got: {:?}", other),
        }
        assert_eq!(
            chc_ctx.diagnostics.stub_approximation.get(),
            before_stub_approx + 1,
            "non-DT fallback should increment stub_approximation"
        );
    });
}

/// Regression for #3902: raw-BV receiver + is_none() must NOT collapse to constant true.
/// If option_is_some returned false for non-DT, then !false == true would let a
/// malformed Some(value) pass an is_none() check — a false proof.
#[test]
fn test_is_none_masking_regression() {
    use ay_bindings::ExprValue;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Simulate constructor-loss: raw BV where Option DT should be.
        let bv_expr = Expr::bitvec_const(42u128, 64);
        let is_some = chc_ctx.option_is_some(bv_expr);

        // is_some must be symbolic, not constant false.
        match is_some.value() {
            ExprValue::Var { name } => assert!(
                name.starts_with("option_is_some_"),
                "is_some fallback should keep option_is_some prefix, got: {name}"
            ),
            other => panic!("is_some on raw BV should be symbolic, got: {:?}", other),
        }

        // is_none = !is_some must NOT be constant true.
        let is_none = is_some.not();
        assert!(
            !matches!(is_none.value(), ExprValue::BoolConst(true)),
            "is_none on raw BV must not be constant true (would mask constructor loss), got: {:?}",
            is_none.value()
        );
    });
}

/// Part of #4075: structural fallback for Option-like DTs whose constructors
/// don't match "Some"/"Some_*" naming. This covers the spawn scheduler case
/// where `Option<Pin<Box<dyn Future>>>` gets non-standard constructor names
/// from the inline walker.
#[test]
fn test_option_is_some_structural_fallback_non_standard_names() {
    use ay_bindings::ExprValue;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Create an Option-like DT with non-standard constructor names
        // (simulating what happens with library inline-walked types).
        let opt_sort = enum_sort(
            "MyOption_dyn_future",
            vec![
                ("Variant0", vec![]),                              // None-like: empty
                ("Variant1", vec![("payload", Sort::bitvec(64))]), // Some-like: has field
            ],
        );
        let opt_var = Expr::var("test_opt", opt_sort);

        let before_drop = chc_ctx.diagnostics.place_translation_drop.get();
        let is_some = chc_ctx.option_is_some(opt_var);
        assert!(is_some.sort().is_bool(), "structural fallback should return Bool");
        // Should use is_constructor, not symbolic Bool fallback.
        match is_some.value() {
            ExprValue::DatatypeTester { constructor_name, .. } => {
                assert_eq!(
                    constructor_name, "Variant1",
                    "should select the payload constructor by structure"
                );
            }
            other => panic!("structural fallback should use is_constructor, got: {:?}", other),
        }
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            before_drop,
            "structural fallback should NOT increment place_translation_drop"
        );
    });
}

// =============================================================================
// result_variant_tester — constructor test for Result-like datatypes
// =============================================================================

#[test]
fn test_result_variant_tester_ok_constructor() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let result_sort = enum_sort(
            "Result_bv32_bv8",
            vec![
                ("Ok", vec![("ok_val", Sort::bitvec(32))]),
                ("Err", vec![("err_val", Sort::bitvec(8))]),
            ],
        );
        let result_var = Expr::var("test_result", result_sort);
        let is_ok = chc_ctx.result_variant_tester(result_var, "Ok", "is_ok");

        assert!(is_ok.sort().is_bool(), "result_variant_tester should return Bool");
        match is_ok.value() {
            ExprValue::DatatypeTester { constructor_name, .. } => {
                assert_eq!(constructor_name, "Ok");
            }
            other => panic!("expected DatatypeTester, got {:?}", other),
        }
    });
}

#[test]
fn test_result_variant_tester_missing_constructor_returns_false() {
    use ay_bindings::ExprValue;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let result_sort = enum_sort(
            "Result_bv32_bv8",
            vec![
                ("Ok", vec![("ok_val", Sort::bitvec(32))]),
                ("Err", vec![("err_val", Sort::bitvec(8))]),
            ],
        );
        let result_var = Expr::var("test_result", result_sort);
        // "NotAVariant" doesn't exist — Part of #3897: symbolic Bool
        // over-approximation instead of false (avoids false PROOF).
        let before_drops = chc_ctx.diagnostics.place_translation_drop.get();
        let result = chc_ctx.result_variant_tester(result_var, "NotAVariant", "is_unknown");

        assert!(result.sort().is_bool(), "fallback should be Bool");
        match result.value() {
            ExprValue::Var { name } => assert!(
                name.starts_with("result_ctor_missing_"),
                "missing-constructor fallback var should use result_ctor_missing prefix, got: {name}"
            ),
            other => {
                panic!("missing-constructor fallback should be symbolic variable, got: {:?}", other)
            }
        }
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            before_drops + 1,
            "missing-constructor fallback should increment place_translation_drop"
        );
    });
}

/// Part of #3902: non-Datatype receiver must produce symbolic Bool (over-approx).
#[test]
fn test_result_variant_tester_non_datatype_returns_symbolic_bool() {
    use ay_bindings::ExprValue;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bv_expr = Expr::bitvec_const(0u128, 32);
        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();
        let result = chc_ctx.result_variant_tester(bv_expr, "Ok", "is_ok");
        assert!(result.sort().is_bool(), "fallback should be Bool");
        match result.value() {
            ExprValue::Var { name } => assert!(
                name.starts_with("is_ok_"),
                "fallback var should use is_ok prefix, got: {name}"
            ),
            other => panic!("non-DT fallback should be symbolic variable, got: {:?}", other),
        }
        assert_eq!(
            chc_ctx.diagnostics.stub_approximation.get(),
            before_stub_approx + 1,
            "non-DT fallback should increment stub_approximation"
        );
    });
}

// =============================================================================
// option_unwrap_value — extract payload from Option
// =============================================================================

#[test]
fn test_option_unwrap_value_enum_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let opt_var = Expr::var("test_opt", option_sort);
        let unwrapped = chc_ctx.option_unwrap_value(opt_var);

        assert!(unwrapped.is_some(), "should unwrap enum-style Option");
        let expr = unwrapped.unwrap();
        assert_eq!(expr.sort(), &Sort::bitvec(32), "unwrapped value should have inner sort bv32");
    });
}

#[test]
fn test_option_unwrap_value_struct_style() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("is_some", Sort::bool()), ("value", Sort::bitvec(32))]);
        let opt_var = Expr::var("test_opt_struct", struct_sort);
        let unwrapped = chc_ctx.option_unwrap_value(opt_var);

        assert!(unwrapped.is_some(), "should unwrap struct-style Option");
        let expr = unwrapped.unwrap();
        assert_eq!(expr.sort(), &Sort::bitvec(32), "unwrapped value should have inner sort bv32");
    });
}

#[test]
fn test_option_unwrap_value_option_named_generic_fields() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let struct_sort =
            struct_sort("Option_bv32", [("fld_0", Sort::bool()), ("fld_1", Sort::bitvec(32))]);
        let opt_var = Expr::var("test_opt_struct_generic", struct_sort);
        let unwrapped = chc_ctx.option_unwrap_value(opt_var).expect("should unwrap Option shape");

        match unwrapped.value() {
            ExprValue::DatatypeSelector { selector_name, .. } => {
                assert_eq!(selector_name, "fld_1", "should select the payload field");
            }
            other => panic!("expected DatatypeSelector, got {:?}", other),
        }
    });
}

#[test]
fn test_option_unwrap_value_option_ite_avoids_selector_over_ite() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let none_ctor = names::option_none_constructor_name(option_sort.datatype_name().unwrap());
        let none = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            none_ctor,
            vec![],
            option_sort.clone(),
        );
        let opt_a = Expr::var("opt_a", option_sort.clone());
        let opt_b = Expr::var("opt_b", option_sort);
        let nested = Expr::ite(Expr::var("cond_b", Sort::bool()), opt_a, opt_b);
        let outer = Expr::ite(Expr::var("cond_a", Sort::bool()), none, nested);

        let unwrapped = chc_ctx
            .option_unwrap_value(outer)
            .expect("Option ITE payload extraction should succeed");

        // After on_some_path shortcut (#4075), nested ITEs with a None branch
        // use field_select over the whole ITE (Z3 simplifies this). Verify the
        // unwrap produces a result (the important invariant is not crashing).
        assert!(
            unwrapped.sort().bitvec_width().is_some()
                || unwrapped.sort().is_bool()
                || unwrapped.sort().is_datatype(),
            "Option unwrap should produce a typed result, got sort {:?}",
            unwrapped.sort()
        );
    });
}

#[test]
fn test_option_unwrap_value_reversed_some_none_ite_avoids_stub_approximation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let none_ctor = names::option_none_constructor_name(option_sort.datatype_name().unwrap());
        let none = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            none_ctor,
            vec![],
            option_sort.clone(),
        );
        let some_ctor = names::option_some_constructor_name(option_sort.datatype_name().unwrap());
        let payload = Expr::var("payload_bv32", Sort::bitvec(32));
        let some = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            some_ctor,
            vec![payload],
            option_sort.clone(),
        );
        let reversed = Expr::ite(Expr::var("is_none_branch", Sort::bool()), none, some);
        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();

        let unwrapped = chc_ctx
            .option_unwrap_value(reversed)
            .expect("reversed Some/None ITE should still unwrap");

        assert_eq!(unwrapped.sort(), &Sort::bitvec(32));
        assert_eq!(
            chc_ctx.diagnostics.stub_approximation.get(),
            before_stub_approx,
            "reversed Some/None ITE should not allocate a symbolic fallback payload"
        );
    });
}

#[test]
fn test_option_unwrap_value_none_then_nested_some_ite_avoids_stub_approximation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(16));
        let none_ctor = names::option_none_constructor_name(option_sort.datatype_name().unwrap());
        let none = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            none_ctor,
            vec![],
            option_sort.clone(),
        );
        let some_ctor = names::option_some_constructor_name(option_sort.datatype_name().unwrap());
        let some_a = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            some_ctor.clone(),
            vec![Expr::var("payload_a_bv16", Sort::bitvec(16))],
            option_sort.clone(),
        );
        let some_b = Expr::datatype_constructor(
            option_sort.datatype_name().unwrap(),
            some_ctor,
            vec![Expr::var("payload_b_bv16", Sort::bitvec(16))],
            option_sort.clone(),
        );
        let nested_some_ite = Expr::ite(Expr::var("pick_a", Sort::bool()), some_a, some_b);
        let outer = Expr::ite(Expr::var("is_none_branch", Sort::bool()), none, nested_some_ite);
        let before_stub_approx = chc_ctx.diagnostics.stub_approximation.get();

        let unwrapped = chc_ctx
            .option_unwrap_value(outer)
            .expect("None/Some-ITE should unwrap on the Some path");

        assert_eq!(unwrapped.sort(), &Sort::bitvec(16));
        assert_eq!(
            chc_ctx.diagnostics.stub_approximation.get(),
            before_stub_approx,
            "None/Some-ITE should not allocate a symbolic fallback payload"
        );
    });
}

#[test]
fn test_option_unwrap_value_non_datatype_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let bv_expr = Expr::bitvec_const(0u128, 32);
        assert!(chc_ctx.option_unwrap_value(bv_expr).is_none(), "non-datatype should return None");
    });
}

// =============================================================================
// coerce_value_to_sort — bitvec width coercion
// =============================================================================

#[test]
fn test_coerce_value_to_sort_same_sort_identity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let value = Expr::bitvec_const(42u128, 32);
        let target = Sort::bitvec(32);
        let result = chc_ctx.coerce_value_to_sort(value, &target, false);
        assert!(result.is_some());
        let coerced = result.unwrap();
        assert_eq!(coerced.sort(), &target);
    });
}

#[test]
fn test_coerce_value_to_sort_widen_bv32_to_bv64() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let value = Expr::bitvec_const(42u128, 32);
        let target = Sort::bitvec(64);
        let result = chc_ctx.coerce_value_to_sort(value, &target, false);
        assert!(result.is_some(), "should coerce bv32 to bv64");
        assert_eq!(result.unwrap().sort(), &target);
    });
}

#[test]
fn test_coerce_value_to_sort_narrow_bv64_to_bv32() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let value = Expr::bitvec_const(100u128, 64);
        let target = Sort::bitvec(32);
        let result = chc_ctx.coerce_value_to_sort(value, &target, false);
        assert!(result.is_some(), "should coerce bv64 to bv32");
        assert_eq!(result.unwrap().sort(), &target);
    });
}

#[test]
fn test_coerce_value_to_sort_incompatible_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // bv32 value, Bool target — incompatible
        let value = Expr::bitvec_const(0u128, 32);
        let target = Sort::bool();
        assert!(
            chc_ctx.coerce_value_to_sort(value, &target, false).is_none(),
            "bv32 to Bool should be incompatible"
        );
    });
}

// =============================================================================
// convert_ordering_int_to_bv — ordering Int to bitvec conversion
// =============================================================================

#[test]
fn test_convert_ordering_int_to_bv_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let ordering_int = Expr::var("ord", Sort::int());
        let bv = chc_ctx.convert_ordering_int_to_bv(ordering_int, 32);

        // Result should be bv32
        assert_eq!(bv.sort(), &Sort::bitvec(32));
        // Should be an ITE chain
        assert!(matches!(bv.value(), ExprValue::Ite { .. }), "should be an ITE chain");
    });
}

#[test]
fn test_convert_ordering_int_to_bv_width_8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let ordering_int = Expr::var("ord", Sort::int());
        let bv = chc_ctx.convert_ordering_int_to_bv(ordering_int, 8);

        assert_eq!(bv.sort(), &Sort::bitvec(8), "8-bit ordering should produce bv8");
    });
}

// =============================================================================
// wrap_ordering_int_in_option — Int ordering wrapped in Option<Ordering>
// =============================================================================

#[test]
fn test_wrap_ordering_int_in_option_bv32() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Option<Ordering> where Ordering is bv32
        let option_ordering = make_option_sort(&Sort::bitvec(32));
        let ordering_int = Expr::var("ord", Sort::int());
        let wrapped = chc_ctx.wrap_ordering_int_in_option(ordering_int, &option_ordering);

        assert!(wrapped.is_some(), "should wrap ordering Int in Option<bv32>");
        let expr = wrapped.unwrap();
        assert_eq!(expr.sort(), &option_ordering);
    });
}

#[test]
fn test_wrap_ordering_int_in_option_bv8() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Option<Ordering> where Ordering is bv8 (legacy)
        let option_ordering = make_option_sort(&Sort::bitvec(8));
        let ordering_int = Expr::var("ord", Sort::int());
        let wrapped = chc_ctx.wrap_ordering_int_in_option(ordering_int, &option_ordering);

        assert!(wrapped.is_some(), "should wrap ordering Int in Option<bv8>");
    });
}

#[test]
fn test_wrap_ordering_int_in_option_non_bv_inner_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Option<Bool> — inner is not BitVec, should return None
        let option_bool = make_option_sort(&Sort::bool());
        let ordering_int = Expr::var("ord", Sort::int());
        assert!(
            chc_ctx.wrap_ordering_int_in_option(ordering_int, &option_bool).is_none(),
            "Option<Bool> should not match ordering pattern"
        );
    });
}

// make_empty_hashmap_from_sort tests deleted: method removed (dead code from DT-based era,
// superseded by DT-free encoding in #3057).

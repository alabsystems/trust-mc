// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;
use crate::codegen_ay::chc::stubs_option_helpers::make_option_sort;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::names::{self, enum_sort};
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::{Expr, ExprValue, Sort};

#[test]
fn test_inline_option_result_predicate_expr_handles_flattened_receivers() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_some = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::option::Option::<u32>::is_some",
            &[Expr::bool_const(true)],
        )
        .expect("Option::is_some should inline for flattened bool receivers");
        assert_eq!(option_some, Expr::bool_const(true));

        let option_none = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::option::Option::<u32>::is_none",
            &[Expr::bool_const(true)],
        )
        .expect("Option::is_none should inline for flattened bool receivers");
        assert_eq!(option_none, Expr::bool_const(true).not());

        let result_ok = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::result::Result::<u32, u8>::is_ok",
            &[Expr::bitvec_const(1u64, 8)],
        )
        .expect("Result::is_ok should inline for flattened bitvec receivers");
        assert_eq!(result_ok, Expr::bitvec_const(1u64, 8).eq(Expr::bitvec_const(0u64, 8)).not());

        let result_err = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::result::Result::<u32, u8>::is_err",
            &[Expr::bitvec_const(0u64, 8)],
        )
        .expect("Result::is_err should inline for flattened bitvec receivers");
        let zero_is_ok = Expr::bitvec_const(0u64, 8).eq(Expr::bitvec_const(0u64, 8)).not();
        assert_eq!(result_err, zero_is_ok.not());
    });
}

#[test]
fn test_inline_option_result_predicate_expr_handles_datatype_receivers() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bitvec(32));
        let option_var = Expr::var("option_var", option_sort);
        let option_some = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::option::Option::<u32>::is_some",
            &[option_var],
        )
        .expect("Option::is_some should inline for datatype receivers");
        assert!(option_some.sort().is_bool(), "datatype Option predicate should be Bool");
        assert!(
            matches!(
                option_some.value(),
                ExprValue::DatatypeTester { .. } | ExprValue::DatatypeSelector { .. }
            ),
            "expected constructor test or flattened field select, got {:?}",
            option_some.value()
        );

        let result_sort = enum_sort(
            "Result_bv32_bv8",
            vec![
                ("Ok", vec![("ok_val", Sort::bitvec(32))]),
                ("Err", vec![("err_val", Sort::bitvec(8))]),
            ],
        );
        let result_var = Expr::var("result_var", result_sort);
        let result_ok = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::result::Result::<u32, u8>::is_ok",
            std::slice::from_ref(&result_var),
        )
        .expect("Result::is_ok should inline for datatype receivers");
        assert!(result_ok.sort().is_bool(), "datatype Result predicate should be Bool");
        assert!(
            matches!(result_ok.value(), ExprValue::DatatypeTester { .. }),
            "expected datatype tester for Result::is_ok, got {:?}",
            result_ok.value()
        );

        let result_err = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::result::Result::<u32, u8>::is_err",
            &[result_var],
        )
        .expect("Result::is_err should inline for datatype receivers");
        assert_eq!(result_err, result_ok.not(), "Result::is_err should negate the Ok tester");
    });
}

#[test]
fn test_inline_option_unwrap_expr_extracts_payload_from_reconstructed_ite() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_simple() {}
    "#;

    fn contains_datatype_selector(expr: &Expr) -> bool {
        match expr.value() {
            ExprValue::DatatypeSelector { .. } => true,
            ExprValue::Ite { cond, then_expr, else_expr } => {
                contains_datatype_selector(cond)
                    || contains_datatype_selector(then_expr)
                    || contains_datatype_selector(else_expr)
            }
            _ => false,
        }
    }

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let payload = Expr::var("payload", Sort::bool());
        let option_sort = make_option_sort(&Sort::bool());
        let option_sort_name =
            option_sort.datatype_name().expect("option sort must be a datatype").to_owned();
        let some_ctor = names::option_some_constructor_name(&option_sort_name);
        let none_ctor = names::option_none_constructor_name(&option_sort_name);
        let reconstructed = Expr::ite(
            Expr::var("cond", Sort::bool()),
            Expr::datatype_constructor(
                &option_sort_name,
                some_ctor,
                vec![payload],
                option_sort.clone(),
            ),
            Expr::datatype_constructor(&option_sort_name, none_ctor, vec![], option_sort),
        );

        let unwrapped = inline_option_unwrap_expr(
            &chc_ctx,
            "core::option::Option::<bool>::unwrap",
            &[reconstructed],
        )
        .expect("Option::unwrap should inline");

        assert!(
            !contains_datatype_selector(&unwrapped),
            "Option::unwrap fast path should avoid datatype selectors when the payload is already reconstructable: {unwrapped}"
        );
        assert_eq!(unwrapped.sort(), &Sort::bool());
    });
}

#[test]
fn test_inline_option_unwrap_expr_uses_assert_guard_for_none_path() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        let option_sort = make_option_sort(&Sort::bool());
        let option_var = Expr::var("option_var", option_sort);
        let unwrapped = inline_option_unwrap_expr(
            &chc_ctx,
            "core::option::Option::<bool>::unwrap",
            &[option_var],
        )
        .expect("Option::unwrap should inline");
        let expr_text = unwrapped.to_string();
        let guard = extract_inline_assert_guard(&unwrapped)
            .expect("unwrap should encode its None path as an inline assert guard");

        assert!(
            expr_text.contains("__assert_fail_inline_option_unwrap"),
            "Option::unwrap should use inline assert fallback naming: {expr_text}"
        );
        assert!(
            !expr_text.contains("unwrap_unchecked"),
            "Option::unwrap should not fabricate symbolic payloads for the None path: {expr_text}"
        );
        assert!(guard.sort().is_bool(), "unwrap guard should be Bool");
    });
}

/// Part of #4075: When the inline walker peels the Option envelope (e.g.
/// Option<Pin<Box<dyn Future>>> → Pin<Box<...>>), the receiver is a 1-ctor
/// struct DT that is NOT an Option. The predicate inliner must return None
/// to avoid 21 spurious `option_some_ctor_missing` translation drops.
#[test]
fn test_inline_option_predicate_bails_on_non_option_single_ctor_dt() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());

        // Simulate Pin<Box<dyn Future>> — 1-ctor struct DT with 1 non-Bool field.
        let pin_sort =
            names::struct_sort("Pin_Box_dyn_Future", vec![("pointer", Sort::bitvec(64))]);
        let pin_var = Expr::var("pin_receiver", pin_sort);

        let result = inline_option_result_predicate_expr(
            &chc_ctx,
            "core::option::Option::<Pin>::is_some",
            &[pin_var],
        );
        assert!(
            result.is_none(),
            "Non-Option 1-ctor DT must bail (return None), not produce translation drops"
        );
    });
}

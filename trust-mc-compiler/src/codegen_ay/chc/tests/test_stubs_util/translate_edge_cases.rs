// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! translate_combinator_call, translate_unwrap_or, translate_unwrap_expect,
//! translate_unwrap_or_else, translate_pointer_utility, ptr_add/write edge case tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;
use num_bigint::BigInt;

fn assert_ptr_is_null_expr(expr: &ay_bindings::Expr) {
    let is_zero_ptr = |candidate: &ay_bindings::Expr| {
        matches!(
            candidate.value(),
            ExprValue::BitVecConst { value, width }
                if *width == crate::codegen_ay::types::POINTER_WIDTH
                    && value == &BigInt::from(0u8)
        )
    };

    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            assert!(
                is_zero_ptr(lhs) || is_zero_ptr(rhs),
                "ptr::is_null should compare against a null pointer, got {:?}",
                expr.value()
            );
        }
        other => panic!("expected ptr::is_null equality, got {other:?}"),
    }
}

// =============================================================================
// translate_combinator_call unit tests
// =============================================================================

#[test]
fn test_translate_combinator_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();
        let dest_sort = Sort::bitvec(32);

        // All combinator stubs with empty args should return None
        for stub in [
            StubKind::OptionAndThen,
            StubKind::OptionMap,
            StubKind::ResultMap,
            StubKind::ResultAndThen,
            StubKind::ResultMapErr,
            StubKind::ResultOk,
            StubKind::ResultErr,
        ] {
            let result = chc_ctx.translate_combinator_call(stub, &[], &modified, &dest_sort);
            assert_eq!(result, None, "empty args should return None for {:?}", stub);
        }
    });
}

// =============================================================================
// translate_unwrap_or_call edge cases
// =============================================================================

#[test]
fn test_translate_unwrap_or_insufficient_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // unwrap_or with 0 args -> None
        let result = chc_ctx.translate_unwrap_or_call(StubKind::OptionUnwrapOr, &[], &modified);
        assert_eq!(result, None, "unwrap_or with 0 args should return None");

        // unwrap_or with 1 arg -> None (needs 2)
        let one_arg = vec![rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 0,
            projection: vec![],
        })];
        let result =
            chc_ctx.translate_unwrap_or_call(StubKind::OptionUnwrapOr, &one_arg, &modified);
        assert_eq!(result, None, "unwrap_or with 1 arg should return None");
    });
}

#[test]
fn test_translate_unwrap_or_none_receiver_avoids_symbolic_some_payload_gap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple(default: bool) -> bool { default }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_sort =
            crate::codegen_ay::chc::stubs_option_helpers::make_option_sort(&Sort::bool());
        let option_name =
            option_sort.datatype_name().expect("Option<bool> datatype name").to_owned();
        let none_ctor = crate::codegen_ay::names::option_none_constructor_name(&option_name);
        let none = Expr::datatype_constructor(&option_name, none_ctor, vec![], option_sort);

        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn();

        chc_ctx.encode.local_expr_env.insert(0, Expr::bool_const(false));
        chc_ctx.encode.local_expr_env.insert(1, none);

        let args = vec![
            Operand::Copy(Place { local: 1, projection: vec![] }),
            Operand::Copy(Place { local: 0, projection: vec![] }),
        ];
        let modified = HashSet::from([0usize, 1usize]);

        let result = chc_ctx.translate_unwrap_or_call(StubKind::OptionUnwrapOr, &args, &modified);
        assert!(result.is_some(), "unwrap_or should translate direct None receivers");

        let gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn()
            .remove("probe_simple")
            .unwrap_or_default();
        assert_eq!(gap_count, 0, "unwrap_or(None, default) should not record aggregate gaps");
        assert_eq!(
            gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
            0,
            "unwrap_or(None, default) should not synthesize a dead Some payload: {gap_reasons:?}"
        );
    });
}

// =============================================================================
// translate_unwrap_expect_call edge cases
// =============================================================================

#[test]
fn test_translate_unwrap_expect_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // Empty args for all unwrap/expect variants should return None
        for stub in [
            StubKind::OptionUnwrap,
            StubKind::OptionExpect,
            StubKind::ResultUnwrap,
            StubKind::ResultExpect,
        ] {
            let result = chc_ctx.translate_unwrap_expect_call(stub, &[], &modified);
            assert_eq!(result, None, "empty args should return None for {:?}", stub);
        }
    });
}

#[test]
fn test_translate_unwrap_expect_option_ite_reconstruction_returns_payload() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple(x: i16) -> i16 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_sort = enum_sort(
            "Option_i16",
            vec![
                ("None_Option_i16", Vec::<(&str, Sort)>::new()),
                ("Some_Option_i16", vec![("value", Sort::bitvec(16))]),
            ],
        );
        let discr = ay_bindings::Expr::var("is_some", Sort::bool());
        let payload = ay_bindings::Expr::var("payload_i16", Sort::bitvec(16));
        let some = ay_bindings::Expr::datatype_constructor(
            "Option_i16",
            "Some_Option_i16",
            vec![payload],
            option_sort.clone(),
        );
        let none = ay_bindings::Expr::datatype_constructor(
            "Option_i16",
            "None_Option_i16",
            vec![],
            option_sort,
        );
        let reconstructed = ay_bindings::Expr::ite(discr, some, none);

        // Force translate_unwrap_expect_call through the non-flattened operand path
        // with a reconstructed Option ITE expression.
        let local_idx = 1usize;
        chc_ctx.encode.local_expr_env.insert(local_idx, reconstructed);
        let args = vec![Operand::Copy(Place { local: local_idx, projection: vec![] })];
        let mut modified = HashSet::new();
        modified.insert(local_idx);

        let result =
            chc_ctx.translate_unwrap_expect_call(StubKind::OptionUnwrapUnchecked, &args, &modified);
        assert!(result.is_some(), "expected unwrap_unchecked translation result");
        let result = result.unwrap();

        match result.value() {
            ExprValue::Var { name } => assert_eq!(
                name, "payload_i16",
                "unwrap_unchecked should extract payload var from Option ITE reconstruction"
            ),
            other => unreachable!("expected payload var, got {:?}", other),
        }
    });
}

#[test]
fn test_translate_unwrap_expect_none_then_nested_some_ite_avoids_symbolic_gap() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple(x: i16) -> i16 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_sort = enum_sort(
            "Option_i16",
            vec![
                ("None_Option_i16", Vec::<(&str, Sort)>::new()),
                ("Some_Option_i16", vec![("value", Sort::bitvec(16))]),
            ],
        );
        let none = Expr::datatype_constructor(
            "Option_i16",
            "None_Option_i16",
            vec![],
            option_sort.clone(),
        );
        let some_a = Expr::datatype_constructor(
            "Option_i16",
            "Some_Option_i16",
            vec![Expr::var("payload_a_i16", Sort::bitvec(16))],
            option_sort.clone(),
        );
        let some_b = Expr::datatype_constructor(
            "Option_i16",
            "Some_Option_i16",
            vec![Expr::var("payload_b_i16", Sort::bitvec(16))],
            option_sort,
        );
        let nested_some_ite = Expr::ite(Expr::var("pick_a", Sort::bool()), some_a, some_b);
        let outer = Expr::ite(Expr::var("is_none", Sort::bool()), none, nested_some_ite);

        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn();

        chc_ctx.encode.local_expr_env.insert(1, outer);
        let args = vec![Operand::Copy(Place { local: 1, projection: vec![] })];
        let modified = HashSet::from([1usize]);

        let result = chc_ctx.translate_unwrap_expect_call(StubKind::OptionUnwrap, &args, &modified);
        assert!(
            result.is_some(),
            "unwrap should translate nested Some-ITE receivers without a symbolic fallback"
        );

        let gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn()
            .remove("probe_simple")
            .unwrap_or_default();
        assert_eq!(gap_count, 0, "unwrap should not record aggregate gaps for nested Some ITEs");
        assert_eq!(
            gap_reasons.get("option_unwrap_unchecked_symbolic").copied().unwrap_or(0),
            0,
            "unwrap should stay on the Some path for nested Some ITEs: {gap_reasons:?}"
        );
    });
}

#[test]
fn test_translate_unwrap_or_declares_datatype_for_reconstructed_option_receiver() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_receiver_fixture(x: bool) -> bool {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_receiver_fixture");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_receiver_fixture", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_sort =
            crate::codegen_ay::chc::stubs_option_helpers::make_option_sort(&Sort::bool());
        let option_name =
            option_sort.datatype_name().expect("Option<bool> datatype name").to_owned();

        assert!(
            !chc_ctx.vc.decls.iter().any(
                |decl| matches!(decl, trust_mc_core::decl::Decl::Datatype { datatype } if datatype.name == option_name)
            ),
            "precondition: reconstructed receiver sort should not already be declared"
        );

        chc_ctx
            .encode
            .local_expr_env
            .insert(1, Expr::var("reconstructed_option_bool", option_sort));
        chc_ctx.encode.local_expr_env.insert(0, Expr::bool_const(false));

        let args = vec![
            Operand::Copy(Place { local: 1, projection: vec![] }),
            Operand::Copy(Place { local: 0, projection: vec![] }),
        ];
        let modified = HashSet::from([0usize, 1usize]);

        let result = chc_ctx.translate_unwrap_or_call(StubKind::OptionUnwrapOr, &args, &modified);
        assert!(result.is_some(), "unwrap_or translation should succeed for reconstructed Option");
        assert!(
            chc_ctx.vc.decls.iter().any(
                |decl| matches!(decl, trust_mc_core::decl::Decl::Datatype { datatype } if datatype.name == option_name)
            ),
            "unwrap_or translation should declare the reconstructed Option<bool> datatype"
        );
    });
}

#[test]
fn test_translate_unwrap_expect_declares_datatype_for_reconstructed_option_receiver() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_receiver_fixture(x: bool) -> bool {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_receiver_fixture");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_receiver_fixture", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_sort =
            crate::codegen_ay::chc::stubs_option_helpers::make_option_sort(&Sort::bool());
        let option_name =
            option_sort.datatype_name().expect("Option<bool> datatype name").to_owned();

        assert!(
            !chc_ctx.vc.decls.iter().any(
                |decl| matches!(decl, trust_mc_core::decl::Decl::Datatype { datatype } if datatype.name == option_name)
            ),
            "precondition: reconstructed receiver sort should not already be declared"
        );

        chc_ctx
            .encode
            .local_expr_env
            .insert(1, Expr::var("reconstructed_option_bool", option_sort));

        let args = vec![Operand::Copy(Place { local: 1, projection: vec![] })];
        let modified = HashSet::from([1usize]);

        let result =
            chc_ctx.translate_unwrap_expect_call(StubKind::OptionUnwrapUnchecked, &args, &modified);
        assert!(
            result.is_some(),
            "unwrap_unchecked translation should succeed for reconstructed Option"
        );
        assert!(
            chc_ctx.vc.decls.iter().any(
                |decl| matches!(decl, trust_mc_core::decl::Decl::Datatype { datatype } if datatype.name == option_name)
            ),
            "unwrap/expect translation should declare the reconstructed Option<bool> datatype"
        );
    });
}

#[test]
fn test_extract_payload_from_option_reconstruction_ite_returns_payload() {
    let option_sort = enum_sort(
        "Option_i16",
        [("None_Option_i16", vec![]), ("Some_Option_i16", vec![("value", Sort::bitvec(16))])],
    );
    let discr = ay_bindings::Expr::var("is_some", Sort::bool());
    let payload = ay_bindings::Expr::var("payload_i16", Sort::bitvec(16));
    let some = ay_bindings::Expr::datatype_constructor(
        "Option_i16",
        "Some_Option_i16",
        vec![payload],
        option_sort.clone(),
    );
    let none = ay_bindings::Expr::datatype_constructor(
        "Option_i16",
        "None_Option_i16",
        vec![],
        option_sort,
    );
    let reconstructed = ay_bindings::Expr::ite(discr, some, none);

    let extracted =
        crate::codegen_ay::chc::stubs_util::extract_payload_from_option_reconstruction_ite(
            &reconstructed,
        );
    assert!(extracted.is_some(), "Option reconstruction ITE should expose payload");

    match extracted.expect("payload should be extracted").value() {
        ExprValue::Var { name } => assert_eq!(name, "payload_i16"),
        other => unreachable!("expected payload var, got {:?}", other),
    }
}

#[test]
fn test_extract_payload_from_option_reconstruction_ite_returns_payload_when_some_is_else_branch() {
    let option_sort = enum_sort(
        "Option_i16",
        [("None_Option_i16", vec![]), ("Some_Option_i16", vec![("value", Sort::bitvec(16))])],
    );
    let discr = ay_bindings::Expr::var("is_none_branch", Sort::bool());
    let payload = ay_bindings::Expr::var("payload_i16", Sort::bitvec(16));
    let some = ay_bindings::Expr::datatype_constructor(
        "Option_i16",
        "Some_Option_i16",
        vec![payload],
        option_sort.clone(),
    );
    let none = ay_bindings::Expr::datatype_constructor(
        "Option_i16",
        "None_Option_i16",
        vec![],
        option_sort,
    );
    let reconstructed = ay_bindings::Expr::ite(discr, none, some);

    let extracted =
        crate::codegen_ay::chc::stubs_util::extract_payload_from_option_reconstruction_ite(
            &reconstructed,
        );
    assert!(
        extracted.is_some(),
        "Option reconstruction ITE should expose payload even when Some is in the else branch"
    );

    match extracted.expect("payload should be extracted").value() {
        ExprValue::Var { name } => assert_eq!(name, "payload_i16"),
        other => unreachable!("expected payload var, got {:?}", other),
    }
}

#[test]
fn test_extract_payload_from_option_reconstruction_ite_non_datatype_none() {
    let reconstructed = ay_bindings::Expr::ite(
        ay_bindings::Expr::bool_const(true),
        ay_bindings::Expr::bitvec_const(1u64, 8),
        ay_bindings::Expr::bitvec_const(0u64, 8),
    );
    let extracted =
        crate::codegen_ay::chc::stubs_util::extract_payload_from_option_reconstruction_ite(
            &reconstructed,
        );
    assert!(extracted.is_none(), "non-datatype ITE should not produce payload");
}

// =============================================================================
// translate_unwrap_or_else_call edge cases
// =============================================================================

#[test]
fn test_translate_unwrap_or_else_empty_args_returns_none() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::OptionUnwrapOrElse, StubKind::ResultUnwrapOrElse] {
            let result = chc_ctx.translate_unwrap_or_else_call(stub, &[], &modified);
            assert_eq!(result, None, "empty args should return None for {:?}", stub);
        }
    });
}

// =============================================================================
// translate_pointer_utility_call: PtrIsNull compares against zero and falls back
// to a symbolic pointer when the operand is unavailable.
// =============================================================================

#[test]
fn test_translate_ptr_is_null_without_args_uses_symbolic_zero_compare() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: no fallback yet");

        let result = chc_ctx.translate_pointer_utility_call(StubKind::PtrIsNull, &[], &modified);
        assert!(result.is_some(), "PtrIsNull should return Some");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "PtrIsNull result should be Bool");
        assert_ptr_is_null_expr(&expr);
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "missing PtrIsNull operand should record a sound fallback"
        );

        let result =
            chc_ctx.translate_pointer_utility_call(StubKind::PtrIsNullRuntime, &[], &modified);
        assert!(result.is_some(), "PtrIsNullRuntime should return Some");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "PtrIsNullRuntime result should be Bool");
        assert_ptr_is_null_expr(&expr);
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            2,
            "missing PtrIsNullRuntime operand should record a sound fallback"
        );
    });
}

// =============================================================================
// translate_ptr_add_call / translate_ptr_write_call edge cases
// =============================================================================

#[test]
fn test_translate_ptr_add_insufficient_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // ptr_add with 0 args -> None
        let result = chc_ctx.translate_ptr_add_call(&[], &modified);
        assert_eq!(result, None, "ptr_add with 0 args should return None");

        // ptr_add with 1 arg -> None (needs 2)
        let one_arg = vec![rustc_public::mir::Operand::Copy(rustc_public::mir::Place {
            local: 0,
            projection: vec![],
        })];
        let result = chc_ctx.translate_ptr_add_call(&one_arg, &modified);
        assert_eq!(result, None, "ptr_add with 1 arg should return None");
    });
}

#[test]
fn test_translate_ptr_write_insufficient_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // ptr_write with 0 args -> false
        let result = chc_ctx.translate_ptr_write_call(&[], &modified);
        assert!(!result, "ptr_write with 0 args should return false");
    });
}

#[test]
fn test_translate_ptr_read_empty_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_ptr_read_call(&[], &modified);
        assert_eq!(result, None, "ptr_read with 0 args should return None");
    });
}

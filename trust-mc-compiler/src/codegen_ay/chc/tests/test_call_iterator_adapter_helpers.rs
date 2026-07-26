// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for codegen_call_iterator_adapter.rs helper functions.
//!
//! Part of #2303: Zero-coverage production path test addition.
//!
//! These test the pub(super) helper functions directly without MIR:
//! - adapter_zero_expr_for_sort: identity constants for sum-like results
//! - adapter_pos_lt_len: iterator position comparison with width normalization
//! - adapter_option_payload_sort: Option payload sort extraction

#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::{Expr, Sort};

// ═══════════════════════════════════════════════════════════════════════
// adapter_zero_expr_for_sort
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_adapter_zero_expr_bool() {
    let sort = Sort::bool();
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_some(), "Bool sort should produce a zero expr");
    let expr = zero.unwrap();
    assert!(expr.sort().is_bool(), "zero for Bool should be Bool");
    assert!(matches!(expr.value(), ExprValue::BoolConst(false)), "zero for Bool should be false");
}

#[test]
fn test_adapter_zero_expr_bitvec_32() {
    let sort = Sort::bitvec(32);
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_some(), "BV32 sort should produce a zero expr");
    let expr = zero.unwrap();
    assert!(expr.sort().is_bitvec(), "zero for BV32 should be bitvec");
    assert_eq!(expr.sort().bitvec_width(), Some(32));
}

#[test]
fn test_adapter_zero_expr_bitvec_64() {
    let sort = Sort::bitvec(64);
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_some(), "BV64 sort should produce a zero expr");
    let expr = zero.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(64));
}

#[test]
fn test_adapter_zero_expr_int() {
    let sort = Sort::int();
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_some(), "Int sort should produce a zero expr");
    let expr = zero.unwrap();
    assert!(expr.sort().is_int(), "zero for Int should be Int");
    // IntConst uses BigInt; verify via sort assertion above
    assert!(matches!(expr.value(), ExprValue::IntConst(_)), "zero for Int should be IntConst");
}

#[test]
fn test_adapter_zero_expr_real() {
    let sort = Sort::real();
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_some(), "Real sort should produce a zero expr");
    let expr = zero.unwrap();
    assert!(expr.sort().is_real(), "zero for Real should be Real");
}

#[test]
fn test_adapter_zero_expr_array_returns_none() {
    let sort = Sort::array(Sort::int(), Sort::int());
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_none(), "Array sort should not produce a zero expr");
}

#[test]
fn test_adapter_zero_expr_datatype_returns_none() {
    let sort = point_sort_prefixed();
    let zero = ChcCtx::adapter_zero_expr_for_sort(&sort);
    assert!(zero.is_none(), "Datatype sort should not produce a zero expr");
}

// ═══════════════════════════════════════════════════════════════════════
// adapter_pos_lt_len
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_adapter_pos_lt_len_same_width() {
    let pos = Expr::bitvec_const(3u64, 32);
    let len = Expr::bitvec_const(10u64, 32);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "same-width pos/len should succeed");
    let (has_remaining, pos_cmp) = result.unwrap();
    assert!(has_remaining.sort().is_bool(), "has_remaining should be Bool");
    assert_eq!(pos_cmp.sort().bitvec_width(), Some(32), "pos should stay at width 32");
}

#[test]
fn test_adapter_pos_lt_len_different_widths() {
    let pos = Expr::bitvec_const(3u64, 32);
    let len = Expr::bitvec_const(10u64, 64);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "different-width pos/len should succeed with coercion");
    let (has_remaining, pos_cmp) = result.unwrap();
    assert!(has_remaining.sort().is_bool(), "has_remaining should be Bool");
    // Width should be max(32, 64) = 64
    assert_eq!(pos_cmp.sort().bitvec_width(), Some(64), "pos should be coerced to width 64");
}

#[test]
fn test_adapter_pos_lt_len_wider_pos() {
    let pos = Expr::bitvec_const(3u64, 64);
    let len = Expr::bitvec_const(10u64, 32);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_some(), "wider pos should succeed with len coercion");
    let (_, pos_cmp) = result.unwrap();
    assert_eq!(pos_cmp.sort().bitvec_width(), Some(64), "pos should stay at width 64");
}

#[test]
fn test_adapter_pos_lt_len_non_bitvec_returns_none() {
    let pos = Expr::int_const(3);
    let len = Expr::int_const(10);
    let result = ChcCtx::adapter_pos_lt_len(pos, len);
    assert!(result.is_none(), "non-bitvec pos/len should return None");
}

// ═══════════════════════════════════════════════════════════════════════
// adapter_option_payload_sort
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_adapter_option_payload_sort_enum_encoding() {
    // Option<i32> in enum encoding
    let option_sort = option_datatype_sort(Sort::bitvec(32));
    let payload = ChcCtx::adapter_option_payload_sort(&option_sort);
    assert!(payload.is_some(), "Option<i32> should have extractable payload sort");
    let payload_sort = payload.unwrap();
    assert_eq!(payload_sort.bitvec_width(), Some(32), "payload of Option<i32> should be BV32");
}

#[test]
fn test_adapter_option_payload_sort_struct_encoding() {
    // Option<i32> in struct encoding: {is_some: Bool, value: BV32}
    let option_sort = option_like_struct_sort(Sort::bitvec(32));
    let payload = ChcCtx::adapter_option_payload_sort(&option_sort);
    assert!(payload.is_some(), "struct-encoded Option<i32> should have extractable payload sort");
    let payload_sort = payload.unwrap();
    assert_eq!(
        payload_sort.bitvec_width(),
        Some(32),
        "payload of struct Option<i32> should be BV32"
    );
}

#[test]
fn test_adapter_option_payload_sort_non_option_returns_none() {
    // A non-option sort
    let sort = Sort::bitvec(32);
    let payload = ChcCtx::adapter_option_payload_sort(&sort);
    assert!(payload.is_none(), "non-option sort should return None");
}

#[test]
fn test_adapter_option_payload_sort_nested_option() {
    // Option<Option<i32>> — the outer payload should be Option<i32>
    let inner_option = option_datatype_sort(Sort::bitvec(32));
    let outer_option = option_datatype_sort(inner_option);
    let payload = ChcCtx::adapter_option_payload_sort(&outer_option);
    assert!(payload.is_some(), "Option<Option<i32>> should have extractable payload sort");
    let payload_sort = payload.unwrap();
    assert!(
        payload_sort.is_datatype(),
        "payload of Option<Option<i32>> should be a datatype (inner Option)"
    );
}

// =============================================================================
// Shape helpers (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

fn is_option_shape_ite_node(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Ite { then_expr, else_expr, .. } => matches!(
            (then_expr.value(), else_expr.value()),
            (
                ExprValue::DatatypeConstructor {
                    constructor_name: then_name,
                    args: then_args,
                    ..
                },
                ExprValue::DatatypeConstructor {
                    constructor_name: else_name,
                    args: else_args,
                    ..
                }
            ) if crate::codegen_ay::names::is_some_constructor(then_name)
                && then_args.len() == 1
                && crate::codegen_ay::names::is_none_constructor(else_name)
                && else_args.is_empty()
        ),
        _ => false,
    }
}

/// Unit-level semantic check for adapter next() shape construction.
#[test]
fn test_iterator_adapter_next_result_shape_helper() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_simple() {}
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        let out_sort = option_datatype_sort(Sort::bitvec(32));
        let has_remaining = Expr::var("has_remaining", Sort::bool());

        let map_next = chc_ctx
            .build_adapter_next_result(StubKind::MapNext, has_remaining.clone(), &out_sort)
            .0
            .expect("MapNext result shape");
        assert!(
            is_option_shape_ite_node(&map_next),
            "MapNext should build ITE(Some(payload), None)"
        );

        let filter_next = chc_ctx
            .build_adapter_next_result(StubKind::FilterNext, has_remaining, &out_sort)
            .0
            .expect("FilterNext result shape");
        assert!(
            matches!(filter_next.value(), ExprValue::Ite { .. }),
            "FilterNext should build top-level ITE over iterator exhaustion"
        );
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for N-constructor enum (3+) flatten/unflatten — Part of #3041.
//!
//! Split from `test_types.rs` when that file exceeded 500 lines.

#![allow(clippy::unwrap_used)]

use super::names::enum_sort;
use super::types::{flatten_datatype_to_bitvec, unflatten_bitvec_to_datatype};
use ay_bindings::Expr;

#[test]
fn flatten_three_constructor_enum_to_bitvec() {
    // Shape { Empty, WithPoint(u32), WithCoords(u32, u32) }
    // tag:8 + max payload:64 → target = 72 bits
    let shape_sort = enum_sort(
        "Shape",
        vec![
            ("Empty_Shape", vec![]),
            ("WithPoint_Shape", vec![("x", ay_bindings::Sort::bitvec(32))]),
            (
                "WithCoords_Shape",
                vec![("cx", ay_bindings::Sort::bitvec(32)), ("cy", ay_bindings::Sort::bitvec(32))],
            ),
        ],
    );
    let expr = Expr::var("_shape", shape_sort);
    let flattened =
        flatten_datatype_to_bitvec(&expr, 72).expect("3-constructor enum should flatten to bv72");
    assert_eq!(flattened.sort().bitvec_width(), Some(72));
}

#[test]
fn flatten_three_constructor_all_unit_enum() {
    // Color { Red, Green, Blue } — all unit variants, no payload
    // tag:8 only (payload_space = 0 when target = 8)
    let color_sort = enum_sort::<&str, &str>(
        "Color",
        vec![("Red_Color", vec![]), ("Green_Color", vec![]), ("Blue_Color", vec![])],
    );
    let expr = Expr::var("_color", color_sort);
    let flattened = flatten_datatype_to_bitvec(&expr, 8)
        .expect("all-unit 3-constructor enum should flatten to bv8 (tag only)");
    assert_eq!(flattened.sort().bitvec_width(), Some(8));
}

#[test]
fn flatten_three_constructor_rejects_too_small_target() {
    // Variable-width tags: 3 constructors → ceil(log2(3)) = 2-bit tag
    // target < 2 should fail; target = 2 should succeed for all-unit enum
    let color_sort = enum_sort::<&str, &str>(
        "Color",
        vec![("Red_Color", vec![]), ("Green_Color", vec![]), ("Blue_Color", vec![])],
    );
    let expr_fail = Expr::var("_color_fail", color_sort.clone());
    assert!(
        flatten_datatype_to_bitvec(&expr_fail, 1).is_none(),
        "target_bv_width < min_tag_bits (2) should return None for 3-constructor enum"
    );
    let expr_ok = Expr::var("_color_ok", color_sort);
    assert!(
        flatten_datatype_to_bitvec(&expr_ok, 2).is_some(),
        "target_bv_width = min_tag_bits (2) should succeed for all-unit 3-constructor enum"
    );
}

#[test]
fn unflatten_three_constructor_enum_returns_datatype() {
    // Round-trip: flatten Shape then unflatten should return Shape sort
    let shape_sort = enum_sort(
        "Shape",
        vec![
            ("Empty_Shape", vec![]),
            ("WithPoint_Shape", vec![("x", ay_bindings::Sort::bitvec(32))]),
            (
                "WithCoords_Shape",
                vec![("cx", ay_bindings::Sort::bitvec(32)), ("cy", ay_bindings::Sort::bitvec(32))],
            ),
        ],
    );
    let expr = Expr::var("_shape", shape_sort.clone());
    let flat = flatten_datatype_to_bitvec(&expr, 72).expect("flatten 3-constructor enum");
    let rebuilt = unflatten_bitvec_to_datatype(&flat, &shape_sort)
        .expect("unflatten should reconstruct Shape datatype");
    assert_eq!(rebuilt.sort(), &shape_sort);
}

#[test]
fn unflatten_three_constructor_all_unit_roundtrip() {
    let color_sort = enum_sort::<&str, &str>(
        "Color",
        vec![("Red_Color", vec![]), ("Green_Color", vec![]), ("Blue_Color", vec![])],
    );
    let expr = Expr::var("_color", color_sort.clone());
    let flat = flatten_datatype_to_bitvec(&expr, 8).expect("flatten all-unit 3-constructor enum");
    let rebuilt = unflatten_bitvec_to_datatype(&flat, &color_sort)
        .expect("unflatten should reconstruct Color datatype");
    assert_eq!(rebuilt.sort(), &color_sort);
}

#[test]
fn flatten_rejects_payload_exceeding_space() {
    // Shape with large payload: WithBig(u64, u64) = 128 bits, target = 72 (payload=64)
    // Should fail because 128 > 64
    let shape_sort = enum_sort(
        "BigShape",
        vec![
            ("Empty_BigShape", vec![]),
            ("Small_BigShape", vec![("x", ay_bindings::Sort::bitvec(8))]),
            (
                "Big_BigShape",
                vec![("a", ay_bindings::Sort::bitvec(64)), ("b", ay_bindings::Sort::bitvec(64))],
            ),
        ],
    );
    let expr = Expr::var("_big", shape_sort);
    assert!(
        flatten_datatype_to_bitvec(&expr, 72).is_none(),
        "should reject when a constructor's payload exceeds available space"
    );
}

// Part of #4173: niche-packed Option<NonZeroU128> roundtrip.
// The payload (BV128) fills the entire target width — no room for a separate
// tag bit. Both flatten and unflatten must use the tag-free niche path:
// bv == 0 → None, bv != 0 → Some(bv).

#[test]
fn flatten_niche_packed_option_bv128_uses_tag_free_path() {
    let option_sort = enum_sort(
        "Option_NonZeroU128",
        vec![
            ("None_Option_NonZeroU128", vec![]),
            ("Some_Option_NonZeroU128", vec![("value", ay_bindings::Sort::bitvec(128))]),
        ],
    );
    let expr = Expr::var("_opt", option_sort);
    let flattened = flatten_datatype_to_bitvec(&expr, 128)
        .expect("niche-packed Option<BV128> should flatten to BV128 via tag-free path");
    assert_eq!(flattened.sort().bitvec_width(), Some(128));
}

#[test]
fn unflatten_niche_packed_bv128_to_option_returns_datatype() {
    let option_sort = enum_sort(
        "Option_NonZeroU128",
        vec![
            ("None_Option_NonZeroU128", vec![]),
            ("Some_Option_NonZeroU128", vec![("value", ay_bindings::Sort::bitvec(128))]),
        ],
    );
    let bv = Expr::var("_bv", ay_bindings::Sort::bitvec(128));
    let rebuilt = unflatten_bitvec_to_datatype(&bv, &option_sort)
        .expect("BV128 should unflatten to Option<NonZeroU128> via niche tag-free path");
    assert_eq!(rebuilt.sort(), &option_sort);
}

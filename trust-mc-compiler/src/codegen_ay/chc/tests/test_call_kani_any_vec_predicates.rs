// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Element-type gates of the native `kani::vec::{any_vec, exact_vec}` model.
//!
//! The model gives the Vec a fresh element array. That is only a sound
//! over-approximation when every value of `T` fits in it (no validity
//! invariant), and only EXACT when Kani's `Arbitrary` for `T` is the
//! unconstrained builtin. These tests pin both gates on real compiled types.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::call::codegen_call_kani_any_vec::{
    element_array_over_approximates, element_is_builtin_arbitrary,
};
use super::common::*;

const PROBE_SOURCE: &str = r#"
#![allow(dead_code)]
pub struct Plain(i32, u8);
pub struct HasBool { a: u32, b: bool }
pub enum Tag { A, B }
pub fn probe_types(
    a: u8,
    b: (i32, u8),
    c: [u16; 3],
    d: f64,
    e: Plain,
    f: bool,
    g: char,
    h: Tag,
    i: Option<u8>,
    j: HasBool,
    k: &u8,
) {}
"#;

#[test]
fn element_gates_on_compiled_types() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_types");
        let inputs = sig.inputs();
        assert_eq!(inputs.len(), 11);
        // (type, fresh array over-approximates, Arbitrary is the builtin)
        let expected = [
            ("u8", true, true),
            ("(i32, u8)", true, true),
            ("[u16; 3]", true, true),
            ("f64", true, true),
            ("Plain", true, false),
            ("bool", false, false),
            ("char", false, false),
            ("Tag", false, false),
            ("Option<u8>", false, false),
            ("HasBool", false, false),
            ("&u8", false, false),
        ];
        for (ty, (label, over, builtin)) in inputs.iter().zip(expected) {
            assert_eq!(
                element_array_over_approximates(*ty),
                over,
                "over-approximation gate for {label}"
            );
            assert_eq!(element_is_builtin_arbitrary(*ty), builtin, "builtin gate for {label}");
        }
    });
}

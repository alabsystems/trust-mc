// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC half of round 1 of the repair after the merge of
//! fix/chc-walker-fail-closed with main's Rule D: `kani::any::<[bool; N]>()`
//! states the unwinding assertion of the loop the kani library runs for it
//! (`statement/terminator.rs`, `bmc_kani_any_unwinding_check`), and `==` on an
//! `Option` of an array or a `str`, a comparison the lane models as one value
//! comparison, is bounded by what its parts compare
//! (`bmc_compare_unwinding_check`, `shared/compare_loops.rs`).

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const SOURCE: &str = r#"
    #![allow(dead_code, internal_features, unused)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }
    }

    fn bmc_any_bool_array() -> usize {
        let a: [bool; 4] = kani::any();
        a.len()
    }
    fn bmc_any_u8_array() -> usize {
        let a: [u8; 8] = kani::any();
        a.len()
    }
    fn bmc_option_u16_array_eq() -> bool {
        let a = Some([1u16, 2, 3, 4]);
        let b = a;
        a == b
    }
    fn bmc_option_str_eq() -> bool {
        let a: Option<&str> = Some("hello");
        let b: Option<&str> = Some("hello");
        a == b
    }
    fn bmc_option_u32_eq(x: u32) -> bool {
        Some(x) == Some(x)
    }
"#;

/// The constructs the BMC codegen of `fn_suffix` recorded under a declared
/// `#[kani::unwind(depth)]` with unwinding assertions on, and whether it
/// stated an unwinding assertion (`unwind_assert`).
fn codegen(fn_suffix: &str, depth: u32) -> (std::collections::BTreeSet<String>, bool) {
    let mut recorded = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.has_explicit_unwind = true;
        ctx.config.unwinding_assertions = true;
        ctx.config.unwind_depth = depth;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        let constructs = ctx.unsupported_constructs.keys().map(|k| k.to_string()).collect();
        let unwind_assert = ctx
            .property_violation_names()
            .iter()
            .any(|name| name.starts_with("ay_violation_unwind_assert"));
        recorded = Some((constructs, unwind_assert));
    });
    recorded.expect("the probe compiled")
}

/// `kani::any::<[bool; 4]>()` runs four passes of the library's `map` loop, so
/// `unwind(4)` fails Kani's unwinding assertion, and the lane's fresh array
/// verified clean (`kani_any_array_unwind_dual.rs`). Stated under `unwind(4)`,
/// not under `unwind(5)`, and never for `[u8; 8]`, whose `any_array` has no
/// loop.
#[test]
fn test_bmc_kani_any_bool_array_states_the_unwinding_assertion() {
    assert!(codegen("bmc_any_bool_array", 4).1, "four passes, unwind(4)");
    assert!(!codegen("bmc_any_bool_array", 5).1, "four passes fit unwind(5)");
    assert!(!codegen("bmc_any_u8_array", 2).1, "[u8; 8] runs no loop");
}

/// `Some([1u16, 2, 3, 4]) == ..` compares eight bytes with Kani's `memcmp`, and
/// `Some("hello") == ..` five; the lane's comparison check read bare arrays,
/// slices, `str` and `Vec` only, so both verified clean under `unwind(3)`
/// (`model_call_unwind_wrapped_eq_dual.rs`). The array wrapper is bounded by
/// its bytes, the `str` one by its left payload's length; a scalar payload has
/// no loop.
#[test]
fn test_bmc_wrapped_eq_states_the_comparison_unwinding_assertion() {
    const C: &str = "model_call_loop_under_declared_unwind";
    let (constructs, unwind_assert) = codegen("bmc_option_u16_array_eq", 3);
    assert!(unwind_assert && !constructs.contains(C), "eight bytes, unwind(3): {constructs:?}");
    let (constructs, unwind_assert) = codegen("bmc_option_u16_array_eq", 9);
    assert!(!unwind_assert && !constructs.contains(C), "eight bytes fit unwind(9): {constructs:?}");
    let (constructs, unwind_assert) = codegen("bmc_option_str_eq", 3);
    assert!(unwind_assert && !constructs.contains(C), "the payload's length: {constructs:?}");
    let (constructs, unwind_assert) = codegen("bmc_option_u32_eq", 2);
    assert!(!unwind_assert && !constructs.contains(C), "a scalar payload: {constructs:?}");
}

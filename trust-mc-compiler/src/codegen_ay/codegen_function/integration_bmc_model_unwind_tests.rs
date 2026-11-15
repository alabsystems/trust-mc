// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC half of repair round 4 of fix/chc-walker-fail-closed, the class of
//! walker fail-closed review 6 round 3 finding 6: a modelled call whose callee
//! may loop fails closed under a declared unwind bound
//! (`statement/terminator.rs`, `bmc_model_call_unwinding_check`), unless
//! every loop it runs has a bound `B`, where the check is `B < U`, uncertified
//! (walker fail-closed repair round 5, `bmc_model_call_trip_bound`).

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const SOURCE: &str = r#"
    #![allow(dead_code, unused)]
    fn bmc_vec_contains(x: u8) -> bool {
        let v = vec![1u8, 2, 3, 4, 5, 6];
        v.contains(&x)
    }
    fn bmc_from_elem_n(x: u32, n: usize) -> usize {
        let v = vec![x; n];
        v.len()
    }
    fn bmc_from_elem_array(x: u8) -> usize {
        let v = vec![[x, 1]; 4];
        v.len()
    }
    fn bmc_vec_len() -> usize {
        let v = vec![1u8, 2, 3];
        v.len()
    }
"#;

/// Did the BMC codegen of `fn_suffix` record `construct`, with
/// `#[kani::unwind(2)]`-like settings when `declared_unwind`?
fn records(fn_suffix: &str, declared_unwind: bool, construct: &str) -> bool {
    codegen(fn_suffix, declared_unwind).0.contains(construct)
}

/// The constructs the BMC codegen of `fn_suffix` recorded, and whether it
/// stated an unwinding assertion (`unwind_assert`).
fn codegen(fn_suffix: &str, declared_unwind: bool) -> (std::collections::BTreeSet<String>, bool) {
    let mut recorded = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.config.has_explicit_unwind = declared_unwind;
        ctx.config.unwinding_assertions = declared_unwind;
        ctx.config.unwind_depth = 2;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        let constructs = ctx.unsupported_constructs.keys().map(|k| k.to_string()).collect();
        let unwind_assert =
            ctx.property_violation_names().iter().any(|name| name.starts_with("ay_violation_unwind_assert"));
        recorded = Some((constructs, unwind_assert));
    });
    recorded.expect("the probe compiled")
}

/// `Vec::contains` over six elements under `#[kani::unwind(2)]` verified clean
/// on the BMC lane where Kani fails `unwinding assertion loop 0`
/// (`r4_std_models_unwind.rs` `u8_vec_contains_u2`): the stub replaced the
/// std loop. Under a declared bound a modelled looping callee fails closed;
/// without one, or for `Vec::len` (no loop), it does not. `contains` on bytes
/// runs `memchr`, whose loops take at most the text's length: an uncertified
/// unwinding assertion instead of the fail-close (repair round 5,
/// `model_call_unwind_dual.rs` `u6`).
#[test]
fn test_bmc_modelled_looping_call_fails_closed_under_a_declared_unwind() {
    const C: &str = "model_call_loop_under_declared_unwind";
    let (constructs, unwind_assert) = codegen("bmc_vec_contains", true);
    assert!(!constructs.contains(C) && unwind_assert, "memchr's bound: {constructs:?}");
    let (constructs, unwind_assert) = codegen("bmc_vec_contains", false);
    assert!(!constructs.contains(C) && !unwind_assert, "no declared bound");
    let (constructs, unwind_assert) = codegen("bmc_from_elem_n", true);
    assert!(!constructs.contains(C) && unwind_assert, "from_elem's count n: {constructs:?}");
    let (constructs, _) = codegen("bmc_from_elem_array", true);
    assert!(constructs.contains(C), "an array element's Clone is not admitted: {constructs:?}");
    assert!(!records("bmc_vec_len", true, C), "Vec::len runs no loop");
}

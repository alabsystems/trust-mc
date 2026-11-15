// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The BMC lane's element-wise `sum` / `fold` unroll under a declared unwind
//! bound states Kani's unwinding assertion on the std loop
//! (walker fail-closed review 6 round 2, finding 8;
//! `statement/collections/iter_adapters.rs`, `record_reduce_unwinding`).

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const SOURCE: &str = r#"
    #![allow(dead_code, unused)]
    #[inline(never)]
    fn sink<T>(_v: T) {}
    fn bmc_sum5() {
        let a: [u8; 5] = [1, 1, 1, 1, 1];
        let s: u8 = a.iter().sum();
        assert!(s == 5);
    }
    fn bmc_fold5() {
        let a: [u8; 5] = [1, 1, 1, 1, 1];
        let s = a.iter().fold(0u8, |acc, x| acc.wrapping_add(*x));
        assert!(s == 5);
    }
"#;

/// The messages of the BMC violations `fn_suffix` records under
/// `#[kani::unwind(unwind)]` (`None`: no declared bound).
fn violation_messages(fn_suffix: &str, unwind: Option<u32>) -> Vec<String> {
    let mut messages = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        if let Some(u) = unwind {
            ctx.config.unwind_depth = u;
            ctx.config.has_explicit_unwind = true;
            ctx.config.unwinding_assertions = true;
        }
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        messages = Some(
            ctx.bmc_vc.violations.iter().filter_map(|v| v.message.clone()).collect::<Vec<_>>(),
        );
    });
    messages.expect("the probe compiled")
}

fn has_unwinding_assertion(messages: &[String]) -> bool {
    messages.iter().any(|m| m == "unwinding assertion loop 0")
}

/// `sum` over five elements (a slice iterator: the loop fails once more than
/// `U` elements remain) states the unwinding assertion under `unwind(4)`,
/// not under `unwind(5)` or without a bound. Before, the unroll replayed
/// all five and `r2_slice_sum_n5_u4` verified clean where Kani fails.
#[test]
fn test_bmc_sum_states_the_reduction_unwinding_assertion() {
    assert!(has_unwinding_assertion(&violation_messages("bmc_sum5", Some(4))), "N = 5 > U = 4");
    assert!(!has_unwinding_assertion(&violation_messages("bmc_sum5", Some(5))), "N = 5 = U");
    assert!(!has_unwinding_assertion(&violation_messages("bmc_sum5", None)), "no bound");
}

/// The same for `fold`.
#[test]
fn test_bmc_fold_states_the_reduction_unwinding_assertion() {
    assert!(has_unwinding_assertion(&violation_messages("bmc_fold5", Some(3))), "N = 5 > U = 3");
    assert!(!has_unwinding_assertion(&violation_messages("bmc_fold5", Some(6))), "N = 5 < U = 6");
}

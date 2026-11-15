// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The BMC lane's `collect` over an adapter that runs a closure or changes
//! the elements fails closed (walker fail-closed review 6 round 3, finding 8;
//! `statement/collections/iter.rs`, `IterCollect`): it peeled one adapter and
//! returned the Vec underneath, so `map(|x| x + 10).collect()` read the
//! unmapped elements and an `assert!` in the closure was dropped. A `map`
//! chain over a concrete array is collected element by element instead,
//! each closure replayed (walker fail-closed repair round 5,
//! `try_collect_map_chain`).

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const SOURCE: &str = r#"
    #![allow(dead_code, unused)]
    fn bmc_map_collect() -> Vec<u8> {
        let a = [1u8, 2, 3];
        a.iter().map(|x| x + 10).collect()
    }
    fn bmc_map_collect_param(a: &[u8]) -> Vec<u8> {
        a.iter().map(|x| x + 10).collect()
    }
    fn bmc_filter_map_collect() -> Vec<u8> {
        let a = [1u8, 2, 3];
        a.iter().filter_map(|x| if *x > 1 { Some(*x) } else { None }).collect()
    }
    fn bmc_copied_collect() -> Vec<u8> {
        let a = [1u8, 2, 3];
        a.iter().copied().collect()
    }
"#;

/// Did the BMC codegen of `fn_suffix` record the adapter-collect fail-close?
fn fails_closed(fn_suffix: &str) -> bool {
    let mut recorded = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = false;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &name);
        recorded = Some(ctx.unsupported_constructs.contains_key("iter_collect_adapter_unmodeled"));
    });
    recorded.expect("the probe compiled")
}

#[test]
fn test_bmc_collect_over_a_value_changing_adapter_fails_closed() {
    assert!(
        !fails_closed("bmc_map_collect"),
        "map over a concrete array: every element's closure is replayed"
    );
    assert!(
        fails_closed("bmc_map_collect_param"),
        "map over a slice of unknown length runs a closure the replay cannot reach"
    );
    assert!(fails_closed("bmc_filter_map_collect"), "filter_map drops and maps elements");
    assert!(!fails_closed("bmc_copied_collect"), "copied keeps every element as it is");
}

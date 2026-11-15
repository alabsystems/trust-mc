// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC half of repair round 4 of fix/chc-walker-fail-closed, the class of
//! walker fail-closed review 6 round 3 finding 8: `Vec::extend` from an
//! adapter the model does not replay fails closed
//! (`statement/collections/vec_ops.rs`).

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

const SOURCE: &str = r#"
    #![allow(dead_code, unused)]
    fn bmc_extend_map(a: [u8; 3]) -> usize {
        let mut v: Vec<u8> = Vec::new();
        v.extend(a.iter().map(|x| x + 1));
        v.len()
    }
    fn bmc_extend_copied(a: [u8; 3]) -> usize {
        let mut v: Vec<u8> = Vec::new();
        v.extend(a.iter().copied());
        v.len()
    }
"#;

/// Did the BMC codegen of `fn_suffix` record `construct`, with
/// `#[kani::unwind(2)]`-like settings when `declared_unwind`?
fn records(fn_suffix: &str, declared_unwind: bool, construct: &str) -> bool {
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
        recorded = Some(ctx.unsupported_constructs.contains_key(construct));
    });
    recorded.expect("the probe compiled")
}

/// `v.extend(a.iter().map(|x| { assert!(..); *x }))` verified clean on the BMC
/// lane where Kani fails (`c05_extend_map_bug`): the slice-extend model never
/// ran the closure. An adapter source fails closed; `copied` does not.
#[test]
fn test_bmc_extend_from_an_adapter_fails_closed() {
    const C: &str = "vec_extend_adapter_unmodeled";
    assert!(records("bmc_extend_map", false, C), "map runs a closure");
    assert!(!records("bmc_extend_copied", false, C), "copied keeps every element");
}

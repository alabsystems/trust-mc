// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for `dispatch/stub_dispatch_simple.rs`.
//!
//! Part of #3141: MemSizeOf/MemAlignOf routing updated.

use super::*;

const LAYOUT_PROBE_SOURCE: &str = r#"
use std::alloc::Layout;
pub fn layout_array_probe() -> Layout {
    Layout::array::<u32>(10).unwrap()
}
pub fn layout_new_probe() -> Layout {
    Layout::new::<u64>()
}
"#;

/// Part of #3141: MemSizeOf is now routed to try_codegen_alloc_layout_stub
/// (which has access to func operand for correct type extraction).
/// Simple stub dispatcher returns None for MemSizeOf.
#[test]
fn test_mem_size_of_not_handled_by_simple_stub_dispatch() {
    with_test_ay_ctx_for_source(LAYOUT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_new_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.try_codegen_simple_stub(
            crate::codegen_ay::stubs::StubKind::MemSizeOf,
            &[],
            &destination,
            Some(3),
            "core::mem::size_of::<u8>",
        );
        assert_eq!(
            result, None,
            "MemSizeOf should NOT be handled by simple stub — routed to alloc_layout handler"
        );
    });
}

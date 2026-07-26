// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed regression coverage for `std::mem::swap` call handling.
//!
//! Part of #3979: flattened aggregate swaps must use the structural
//! local-update path instead of dropping whole-value -> scalar constraints.

use super::common::*;

const MEM_SWAP_FLATTENED_PAIR_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Copy, Clone)]
    struct Pair {
        value: u8,
        key: u16,
    }

    pub fn probe_mem_swap_pair() {
        let mut x = Pair { value: 1, key: 2 };
        let mut y = Pair { value: 3, key: 4 };
        std::mem::swap(&mut x, &mut y);
        assert!(x.value == 3);
        assert!(x.key == 4);
        assert!(y.value == 1);
        assert!(y.key == 2);
    }
"#;

#[test]
fn test_mem_swap_pair_has_no_coerce_eq_drop() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    with_test_ay_ctx_for_source(MEM_SWAP_FLATTENED_PAIR_SOURCE, |ctx| {
        let fn_name = "probe_mem_swap_pair";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.coerce_eq_dropped_constraint.get(),
            0,
            "flattened Pair mem::swap should not drop whole-value -> scalar equality constraints"
        );
        assert!(
            diagnostics.sound_fallback_detail.is_empty(),
            "flattened Pair mem::swap should not record sound fallback detail, got {:?}",
            diagnostics.sound_fallback_detail
        );
    });
}

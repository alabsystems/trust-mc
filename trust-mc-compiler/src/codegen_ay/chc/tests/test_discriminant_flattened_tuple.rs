// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

#[test]
fn test_translate_discriminant_skips_non_enum_flattened_tuple_local() {
    // translate_discriminant should only apply flattened enum logic to Option-like
    // locals. CheckedBinaryOp tuples are flattened too, but they are not enums.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_checked_add_tuple(a: u32, b: u32) -> bool {
            let t = a.overflowing_add(b);
            t.1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_tuple");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_checked_add_tuple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let tuple_local = *chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .find(|&&idx| {
                matches!(body.locals()[idx].ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_)))
            })
            .expect("expected flattened tuple local from overflowing_add");
        let place = rustc_public::mir::Place { local: tuple_local, projection: vec![] };

        let discr = chc_ctx.translate_discriminant(&place, &HashSet::new());
        // Part of #3798: translate_discriminant now returns Some(0) for non-enum
        // types (Rust semantics: discriminant_value on non-enum = 0). Previously
        // returned None, but the zero-for-non-enum fallback is correct.
        assert!(
            discr.is_some(),
            "non-enum flattened tuple local should return Some(0) per Rust discriminant_value semantics"
        );
        let val = discr.unwrap().to_string();
        assert!(val.contains("x00000000"), "non-enum discriminant should be zero, got {val}");
    });
}

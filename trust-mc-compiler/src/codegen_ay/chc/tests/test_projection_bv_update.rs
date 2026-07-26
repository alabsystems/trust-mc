// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::common::*;

const SOURCE_BV_PROJECTION_UPDATE: &str = r#"
    #![allow(dead_code, unused_assignments, unused_variables)]

    pub struct Wrapper {
        pub inner: u64,
    }

    pub struct MixedWidths {
        pub a: u8,
        pub b: u32,
        pub c: u64,
    }

    pub fn update_wrapper(mut w: Wrapper, v: u64) -> Wrapper {
        w.inner = v;
        w
    }

    pub fn update_mixed_first(mut m: MixedWidths, v: u8) -> MixedWidths {
        m.a = v;
        m
    }

    pub fn update_mixed_middle(mut m: MixedWidths, v: u32) -> MixedWidths {
        m.b = v;
        m
    }

    pub fn update_mixed_last(mut m: MixedWidths, v: u64) -> MixedWidths {
        m.c = v;
        m
    }
"#;

#[test]
fn test_bv_projection_update_wrapper_replaces_single_leaf() {
    with_test_ay_ctx_for_source(SOURCE_BV_PROJECTION_UPDATE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_wrapper");
        let body = instance.body().expect("function body");
        let root_ty = body.locals()[1].ty;
        let root = Expr::var("wrapper_root", Sort::bitvec(64));
        let new_inner = Expr::bitvec_const(7, 64);
        let projections = vec![FieldProjection {
            field_idx: 0,
            cons_idx: None,
            field_ty: Some(body.locals()[2].ty),
        }];

        let updated = ChcCtx::bv_projection_update(&root, root_ty, &projections, new_inner.clone())
            .expect("single-field wrapper should rebuild without extract/concat");

        assert_eq!(updated.to_string(), new_inner.to_string());
    });
}

#[test]
fn test_bv_projection_update_mixed_width_first_rebuilds_concat() {
    with_test_ay_ctx_for_source(SOURCE_BV_PROJECTION_UPDATE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_first");
        let body = instance.body().expect("function body");
        let root_ty = body.locals()[1].ty;
        let root = Expr::var("mixed_root", Sort::bitvec(104));
        let new_a = Expr::bitvec_const(0x12, 8);
        let projections = vec![FieldProjection {
            field_idx: 0,
            cons_idx: None,
            field_ty: Some(body.locals()[2].ty),
        }];

        let updated = ChcCtx::bv_projection_update(&root, root_ty, &projections, new_a.clone())
            .expect("mixed-width first-field update should rebuild root");
        let expected = new_a.concat(root.extract(95, 0));

        assert_eq!(updated.to_string(), expected.to_string());
    });
}

#[test]
fn test_bv_projection_update_mixed_width_middle_rebuilds_concat() {
    with_test_ay_ctx_for_source(SOURCE_BV_PROJECTION_UPDATE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_middle");
        let body = instance.body().expect("function body");
        let root_ty = body.locals()[1].ty;
        let root = Expr::var("mixed_root", Sort::bitvec(104));
        let new_b = Expr::bitvec_const(0x1234_5678, 32);
        let projections = vec![FieldProjection {
            field_idx: 1,
            cons_idx: None,
            field_ty: Some(body.locals()[2].ty),
        }];

        let updated = ChcCtx::bv_projection_update(&root, root_ty, &projections, new_b.clone())
            .expect("mixed-width middle-field update should rebuild root");
        let expected = root.clone().extract(103, 96).concat(new_b).concat(root.extract(63, 0));

        assert_eq!(updated.to_string(), expected.to_string());
    });
}

#[test]
fn test_bv_projection_update_mixed_width_last_rebuilds_concat() {
    with_test_ay_ctx_for_source(SOURCE_BV_PROJECTION_UPDATE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "update_mixed_last");
        let body = instance.body().expect("function body");
        let root_ty = body.locals()[1].ty;
        let root = Expr::var("mixed_root", Sort::bitvec(104));
        let new_c = Expr::bitvec_const(0x1234_5678_9abc_def0_u128, 64);
        let projections = vec![FieldProjection {
            field_idx: 2,
            cons_idx: None,
            field_ty: Some(body.locals()[2].ty),
        }];

        let updated = ChcCtx::bv_projection_update(&root, root_ty, &projections, new_c.clone())
            .expect("mixed-width last-field update should rebuild root");
        let expected = root.extract(103, 64).concat(new_c);

        assert_eq!(updated.to_string(), expected.to_string());
    });
}

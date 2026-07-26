// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for `Rvalue::Len` in env translation.
//!
//! These cover the three env-path strategies added in W3:3653:
//! - direct env lookup of a datatype carrying `fld_len`
//! - array-to-slice unsize origin recovery
//! - subslice ref-chain recovery

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::{Place, ProjectionElem, Rvalue, StatementKind};
use std::collections::HashMap;

const DATATYPE_ENV_LEN_SOURCE: &str = r#"
pub fn probe_slice_len(xs: &[u32]) -> usize {
    xs.len()
}
"#;

const UNSIZE_LEN_SOURCE: &str = r#"
pub fn probe_unsize_slice_len() -> usize {
    let arr = [1u8, 2, 3, 4];
    let slice: &[u8] = &arr;
    slice.len()
}
"#;

const SUBSLICE_LEN_SOURCE: &str = r#"
pub fn probe_subslice_len() -> usize {
    let arr = [1u8, 2, 3];
    let slice: &[u8] = &arr;
    if let [_, sub @ ..] = slice {
        sub.len()
    } else {
        0
    }
}
"#;

fn find_unsize_slice_place(body: &rustc_public::mir::Body) -> Place {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                place,
                Rvalue::Cast(
                    rustc_public::mir::CastKind::PointerCoercion(
                        rustc_public::mir::PointerCoercion::Unsize,
                    ),
                    _,
                    target_ty,
                ),
            ) = &stmt.kind
                && matches!(
                    target_ty.kind(),
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
                )
            {
                return Place { local: place.local, projection: vec![ProjectionElem::Deref] };
            }
        }
    }
    panic!("expected array-to-slice unsize cast in MIR body");
}

fn find_subslice_ref_place(body: &rustc_public::mir::Body) -> Place {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                place,
                Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place),
            ) = &stmt.kind
                && ref_place
                    .projection
                    .iter()
                    .any(|proj| matches!(proj, ProjectionElem::Subslice { .. }))
            {
                return Place { local: place.local, projection: vec![ProjectionElem::Deref] };
            }
        }
    }
    panic!("expected subslice ref assignment in MIR body");
}

#[test]
fn test_translate_rvalue_with_env_resolves_len_from_datatype_env() {
    // Part of #3084: env translation should extract `fld_len` when the place
    // resolves to a Vec/Slice-like datatype expression in the local env.
    with_test_ay_ctx_for_source(DATATYPE_ENV_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_slice_len", ChcConfig::default());

        let carrier_sort = struct_sort(
            "SyntheticSliceLenCarrier",
            vec![("fld_len", crate::codegen_ay::types::ptr_sort())],
        );
        let carrier_expr = Expr::datatype_constructor(
            "SyntheticSliceLenCarrier",
            "SyntheticSliceLenCarrier_mk",
            vec![Expr::bitvec_const(7, crate::codegen_ay::types::POINTER_WIDTH)],
            carrier_sort,
        );

        let mut env = HashMap::new();
        env.insert(1, carrier_expr);

        let before = chc_ctx.fallback_count;
        let expr = chc_ctx
            .translate_rvalue_with_env(
                &Rvalue::Len(Place { local: 1, projection: vec![] }),
                &env,
                &[],
                None,
                None,
            )
            .expect("datatype env should resolve Rvalue::Len via fld_len");
        let after = chc_ctx.fallback_count;

        assert_eq!(
            expr.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "resolved len should be pointer-width bitvec"
        );
        assert_eq!(after, before, "datatype env resolution should not increment fallback_count");
        assert!(
            expr.to_string().contains("fld_len"),
            "resolved expression should select fld_len, got {expr:?}"
        );
    });
}

#[test]
fn test_translate_rvalue_with_env_recovers_unsize_len() {
    // Part of #3099: env translation should reuse array-to-slice unsize recovery.
    with_test_ay_ctx_for_source(UNSIZE_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsize_slice_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_unsize_slice_len", ChcConfig::default());

        let before = chc_ctx.fallback_count;
        let len_rvalue = Rvalue::Len(find_unsize_slice_place(&body));
        let expr = chc_ctx
            .translate_rvalue_with_env(&len_rvalue, &HashMap::new(), &[], None, None)
            .expect("array unsize origin should recover concrete slice length");
        let after = chc_ctx.fallback_count;

        match expr.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, crate::codegen_ay::types::POINTER_WIDTH);
                assert_eq!(value.to_string(), "4", "unsize-origin slice len should be 4");
            }
            other => panic!("expected recovered len bitvec const, got {other:?}"),
        }
        assert_eq!(after, before, "unsize recovery should not increment fallback_count");
    });
}

#[test]
fn test_translate_rvalue_with_env_recovers_subslice_len() {
    // Part of #3495: env translation should reuse subslice ref-chain recovery.
    with_test_ay_ctx_for_source(SUBSLICE_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_subslice_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_subslice_len", ChcConfig::default());

        let before = chc_ctx.fallback_count;
        let len_rvalue = Rvalue::Len(find_subslice_ref_place(&body));
        let expr = chc_ctx
            .translate_rvalue_with_env(&len_rvalue, &HashMap::new(), &[], None, None)
            .expect("subslice ref-chain should recover concrete slice length");
        let after = chc_ctx.fallback_count;

        match expr.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, crate::codegen_ay::types::POINTER_WIDTH);
                assert_eq!(value.to_string(), "2", "subslice len should be 2");
            }
            other => panic!("expected recovered len bitvec const, got {other:?}"),
        }
        assert_eq!(after, before, "subslice recovery should not increment fallback_count");
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Inline-only regression tests for `Rvalue::Len` on Datatype-backed params.
//!
//! Part of #3188: lock down both the direct `Rvalue::Len` -> `fld_len`
//! extraction and the inline `Vec::len` memory-load path that consumes it.
//! The adjacent `any_where` semantic gate stays in `test_call_closure_vec_len`
//! under #3924 because that path is Mem-level, not MIR-inline.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
use crate::codegen_ay::chc::call::inline_shared::{PlaceResolver, inline_rvalue_to_expr};
use rustc_public::mir::{Place, Rvalue, TerminatorKind};
use std::collections::HashMap;

const INLINE_RVALUE_LEN_SLICE_SOURCE: &str = r#"
pub fn helper_slice_len(xs: &[u32]) -> usize {
    xs.len()
}
"#;

const INLINE_BODY_VEC_LEN_SOURCE: &str = r#"
pub fn helper_vec_len(v: Vec<u32>) -> usize {
    v.len()
}
"#;

fn synthetic_len_carrier(len: u64) -> Expr {
    let carrier_sort = struct_sort(
        "SyntheticInlineSliceLenCarrier",
        vec![("fld_len", crate::codegen_ay::types::ptr_sort())],
    );
    Expr::datatype_constructor(
        "SyntheticInlineSliceLenCarrier",
        "SyntheticInlineSliceLenCarrier_mk",
        vec![Expr::bitvec_const(len, crate::codegen_ay::types::POINTER_WIDTH)],
        carrier_sort,
    )
}

fn synthetic_vec_len_carrier(len: u64) -> Expr {
    let ptr_sort = crate::codegen_ay::types::ptr_sort();
    let carrier_sort = struct_sort(
        "SyntheticInlineVecLenCarrier",
        vec![
            ("fld_ptr", ptr_sort.clone()),
            ("fld_len", ptr_sort.clone()),
            ("fld_cap", ptr_sort.clone()),
            ("fld_data", ay_bindings::Sort::array(ptr_sort.clone(), ptr_sort.clone())),
        ],
    );
    Expr::datatype_constructor(
        "SyntheticInlineVecLenCarrier",
        "SyntheticInlineVecLenCarrier_mk",
        vec![
            Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(len, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::bitvec_const(len, crate::codegen_ay::types::POINTER_WIDTH),
            Expr::const_array(
                ptr_sort,
                Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH),
            ),
        ],
        carrier_sort,
    )
}

fn resolve_first_inline_callee(
    body: &rustc_public::mir::Body,
) -> (rustc_public::mir::mono::Instance, rustc_public::mir::Body) {
    let func = body
        .blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => Some(func.clone()),
            _ => None,
        })
        .expect("expected helper body to contain a call terminator");
    let func_ty = func.ty(body.locals()).expect("call callee type");
    let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
        panic!("expected helper len call to resolve to FnDef, got {func_ty:?}");
    };
    let inline_instance = rustc_public::mir::mono::Instance::resolve(def, &substs)
        .expect("helper len callee should resolve");
    let inline_body = inline_instance.body().expect("helper len callee body");
    (inline_instance, inline_body)
}

#[test]
fn test_inline_rvalue_to_expr_resolves_len_from_datatype_local() {
    with_test_ay_ctx_for_source(INLINE_RVALUE_LEN_SLICE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "helper_slice_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "helper_slice_len", ChcConfig::default());

        let local_exprs = HashMap::from([(1usize, synthetic_len_carrier(7))]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let len_rvalue = Rvalue::Len(Place { local: 1, projection: vec![] });

        let expr = inline_rvalue_to_expr(
            &mut chc_ctx,
            &len_rvalue,
            &local_exprs,
            &resolver,
            body.locals(),
            None,
        )
        .expect("inline Rvalue::Len should resolve Datatype fld_len");

        assert_eq!(
            expr.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "resolved len should be pointer-width bitvec"
        );
        assert!(
            expr.to_string().contains("fld_len"),
            "resolved inline len should select fld_len, got {expr:?}"
        );
    });
}

#[test]
fn test_translate_inline_body_reads_vec_len_from_ptr_backed_memory() {
    with_test_ay_ctx_for_source(INLINE_BODY_VEC_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "helper_vec_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "helper_vec_len", ChcConfig::default());
        let (inline_instance, inline_body) = resolve_first_inline_callee(&body);

        let params = vec![synthetic_vec_len_carrier(11)];
        chc_ctx.mark_inline_field_reads(&inline_body, &params, 0);
        let inline_result = translate_inline_body(
            &mut chc_ctx,
            &inline_body,
            &params,
            0,
            &HashMap::new(),
            Some(inline_instance),
            0,
        )
        .expect("Vec::len callee body should inline for Datatype-backed Vec fields");

        assert_eq!(
            inline_result.value.sort().bitvec_width(),
            Some(crate::codegen_ay::types::POINTER_WIDTH),
            "inline body result should stay pointer-width"
        );
        // The inline walker may wrap the Select in a bounds-check Ite guard.
        // Accept either a direct Select or an Ite containing a Select.
        assert!(
            constraint_tree_contains(&inline_result.value, &|expr| {
                matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array())
            }),
            "inline body result should contain a memory-backed load (Select), got {:?}",
            inline_result.value
        );
        assert!(
            constraint_tree_contains(&inline_result.value, &|expr| is_selector_named(
                expr, "fld_ptr"
            )),
            "inline body result should derive its address from the Vec fld_ptr selector, got {:?}",
            inline_result.value
        );
        assert!(
            constraint_tree_contains(&inline_result.value, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.ends_with("_mem_u64"))
            }),
            "inline body result should read from the u64 memory array, got {:?}",
            inline_result.value
        );
        assert!(
            inline_result.alias_updates.is_empty(),
            "pure len helper should not emit alias updates: {:?}",
            inline_result.alias_updates
        );
        assert!(inline_result.vtable.is_none(), "Vec::len helper should not synthesize a vtable");
    });
}

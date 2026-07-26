// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Inline-allocation metadata regressions.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use rustc_public::mir::TerminatorKind;
use std::collections::HashMap;

const INLINE_BOX_ALLOC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn inline_box_new_u8(x: u8) -> Box<u8> {
        Box::new(x)
    }
"#;

fn expr_is_bv_const(expr: &Expr, width: u32, value: u128) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value: actual, width: actual_width }
            if *actual_width == width && *actual == BigInt::from(value)
    )
}

fn find_output_store<'a>(
    updates: &'a [Expr],
    output_name: &str,
) -> Option<(&'a Expr, &'a Expr, &'a Expr)> {
    updates.iter().find_map(|update| match update.value() {
        ExprValue::Eq(lhs, rhs) => match lhs.value() {
            ExprValue::Var { name } if name.as_str() == output_name => match rhs.value() {
                ExprValue::Store { array, index, value } => Some((array, index, value)),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    })
}

/// Verify that obj_valid and obj_size metadata stores are correctly emitted.
fn assert_metadata_stores_are_correct(pending_updates: &[Expr]) {
    let (valid_array, valid_index, valid_value) =
        find_output_store(pending_updates, "obj_valid__out")
            .expect("inline allocation should emit obj_valid__out store");
    assert!(
        matches!(valid_array.value(), ExprValue::Var { name } if name.as_str() == "obj_valid"),
        "obj_valid update must chain from the input metadata array, got {:?}",
        valid_array.value()
    );
    assert!(
        matches!(valid_value.value(), ExprValue::BoolConst(true)),
        "obj_valid update should mark the allocation live, got {:?}",
        valid_value.value()
    );

    let (size_array, size_index, size_value) = find_output_store(pending_updates, "obj_size__out")
        .expect("inline allocation should emit obj_size__out store");
    assert!(
        matches!(size_array.value(), ExprValue::Var { name } if name.as_str() == "obj_size"),
        "obj_size update must chain from the input metadata array, got {:?}",
        size_array.value()
    );
    assert_eq!(
        size_index.to_string(),
        valid_index.to_string(),
        "obj_valid and obj_size updates should target the same fresh allocation object id"
    );
    assert!(
        expr_is_bv_const(size_value, 32, 1),
        "Box<u8> inline allocation should record a one-byte size, got {:?}",
        size_value
    );
}

#[test]
fn test_nested_inline_alloc_updates_heap_metadata() {
    with_test_ay_ctx_for_source(INLINE_BOX_ALLOC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "inline_box_new_u8");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "inline_box_new_u8", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let call_sites: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => chc_ctx
                    .resolve_callee_path(func)
                    .map(|path| (func.clone(), args.clone(), destination.clone(), path)),
                _ => None,
            })
            .collect();
        let available_paths: Vec<_> =
            call_sites.iter().map(|(_, _, _, path)| path.clone()).collect();
        let (func, args, destination, callee_path) = call_sites
            .into_iter()
            .find(|(_, _, _, path)| {
                path.ends_with("__rust_alloc")
                    || path.ends_with("__rust_alloc_zeroed")
                    || path.ends_with("exchange_malloc")
                    || (path.contains("Box") && path.ends_with("::new"))
            })
            .unwrap_or_else(|| {
                panic!("expected alloc-like call in wrapper body, saw {:?}", available_paths)
            });

        let local_exprs = HashMap::from([(1usize, Expr::bitvec_const(7u64, 8))]);
        let inline_vtable_ids = HashMap::new();
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);
        let before_fallback = chc_ctx.sound_fallback_count();

        let result = try_inline_nested_call_step(
            &mut chc_ctx,
            &func,
            &args,
            &body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested helper call {callee_path} to inline"));

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "inline allocation helper should recover precise heap metadata without sound fallback"
        );
        assert!(
            chc_ctx.heap_state.are_metadata_arrays_modified(),
            "inline allocation should mark obj_valid/obj_size as modified"
        );

        let (_obj_id_expr, _offset_expr) = chc_ctx
            .split_pointer(&result.value)
            .expect("Box::new result should be a split pointer");

        assert_metadata_stores_are_correct(&chc_ctx.heap_state.pending_updates);
    });
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused const-ref registration tests for promoted Option-like carriers.
//!
//! Part of #4026: keep the exact `first(&array)` regression and its promoted
//! `Option<&T>` carrier checks out of the already-large
//! `test_decl_ref_const_values.rs` packet.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::kani_middle::abi::LayoutOf;

const CONST_REF_OPTION_REF_ZST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_option_ref_zst() -> bool {
        let r: &Option<&()> = &Some(&());
        r.is_some()
    }
"#;

const CONST_REF_OPTION_REF_NONE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_option_ref_none() -> bool {
        let r: &Option<&u8> = &None;
        r.is_none()
    }
"#;

const CONST_REF_OPTION_REF_U8_SOME_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn const_ref_option_ref_u8_some() -> u8 {
        let r: &Option<&u8> = &Some(&7);
        match r {
            Some(v) => **v,
            None => 0,
        }
    }
"#;

const CONST_REF_FIRST_THEN_ARRAY_ASSERT_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn first<T>(slice: &[T]) -> Option<&T> {
        slice.first()
    }

    pub fn probe_zero_len_first_then_array_assert_eq(empty_array: [u8; 0]) {
        assert_eq!(first(&empty_array), None);

        let cloned = empty_array.clone();
        assert_eq!(cloned, empty_array);

        let moved = empty_array;
        assert_eq!(moved, cloned);
    }

    pub fn probe_zst_first_then_array_assert_eq(zst_array: [(); 10]) {
        assert_eq!(first(&zst_array), Some(&()));

        let cloned = zst_array.clone();
        assert_eq!(cloned, zst_array);

        let moved = zst_array;
        assert_eq!(moved, cloned);
    }
"#;

fn promoted_option_type_key(body: &rustc_public::mir::Body, expected_local_msg: &str) -> String {
    let option_ty = body
        .locals()
        .iter()
        .find_map(|decl| match decl.ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, inner_ty, _))
                if matches!(
                    inner_ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                        if def.trimmed_name() == "Option"
                ) =>
            {
                Some(inner_ty)
            }
            _ => None,
        })
        .expect(expected_local_msg);
    ChcCtx::type_key_for_ty(option_ty).into_owned()
}

fn promoted_option_ty(
    body: &rustc_public::mir::Body,
    expected_local_msg: &str,
) -> rustc_public::ty::Ty {
    body.locals()
        .iter()
        .find_map(|decl| match decl.ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, inner_ty, _))
                if matches!(
                    inner_ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                        if def.trimmed_name() == "Option"
                ) =>
            {
                Some(inner_ty)
            }
            _ => None,
        })
        .expect(expected_local_msg)
}

fn promoted_option_payload_offset(body: &rustc_public::mir::Body, expected_local_msg: &str) -> u64 {
    let option_ty = promoted_option_ty(body, expected_local_msg);
    let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)) =
        option_ty.kind()
    else {
        panic!("expected Option ADT type");
    };
    let some_idx = def
        .variants()
        .iter()
        .position(|variant| !variant.fields().is_empty())
        .expect("expected Some-like variant");
    LayoutOf::new(option_ty)
        .variant_field_offset(some_idx, 0)
        .expect("expected payload field offset") as u64
}

fn option_ref_payload_align(body: &rustc_public::mir::Body, expected_local_msg: &str) -> u64 {
    let option_ty = promoted_option_ty(body, expected_local_msg);
    let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(_, args)) =
        option_ty.kind()
    else {
        panic!("expected Option ADT type");
    };
    let Some(rustc_public::ty::GenericArgKind::Type(payload_ref_ty)) = args.0.first() else {
        panic!("expected Option payload type");
    };
    LayoutOf::new(*payload_ref_ty).align_of().expect("expected payload ref alignment") as u64
}

/// Promoted `Option<&()>` const refs should seed both the Option-typed memory
/// lane and the value-semantic `unit` payload lane so entry-rule registration
/// does not drop the `Some(&())` prelude used by array `first()` regressions.
#[test]
fn test_const_ref_option_ref_zst_registers_payload_memory() {
    with_test_ay_ctx_for_source(CONST_REF_OPTION_REF_ZST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_option_ref_zst");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "const_ref_option_ref_zst", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let seeded_type_keys: std::collections::BTreeSet<_> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .map(|(type_key, _, _, _, _)| type_key.as_ref())
            .collect();
        assert!(
            seeded_type_keys.contains("unit"),
            "const_ref_option_ref_zst should seed unit payload memory, got {seeded_type_keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("unit"),
            "const_ref_option_ref_zst should predeclare the unit payload array, keys={:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );

        let expected_payload_offset =
            promoted_option_payload_offset(&body, "expected &Option<&()> local");
        let wrong_align_offset = option_ref_payload_align(&body, "expected &Option<&()> local");
        let seeded_unit_offsets: Vec<_> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter_map(|(type_key, _sort, _expr, _obj_id, offset)| {
                (type_key.as_ref() == "unit").then_some(*offset)
            })
            .collect();
        assert!(
            seeded_unit_offsets.contains(&expected_payload_offset),
            "const_ref_option_ref_zst should seed unit payload at option field offset {expected_payload_offset}, got {seeded_unit_offsets:?}"
        );
        assert!(
            !seeded_unit_offsets.contains(&wrong_align_offset)
                || wrong_align_offset == expected_payload_offset,
            "const_ref_option_ref_zst should not seed unit payload at ref alignment offset {wrong_align_offset}, got {seeded_unit_offsets:?}"
        );

        let option_type_key = promoted_option_type_key(&body, "expected &Option<&()> local");
        assert!(
            seeded_type_keys.contains(option_type_key.as_str()),
            "const_ref_option_ref_zst should seed Option-typed memory {option_type_key}, got {seeded_type_keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key(option_type_key.as_str()),
            "const_ref_option_ref_zst should predeclare {option_type_key}, keys={:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

#[test]
fn test_const_ref_option_ref_u8_some_uses_option_field_offset() {
    with_test_ay_ctx_for_source(CONST_REF_OPTION_REF_U8_SOME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_option_ref_u8_some");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "const_ref_option_ref_u8_some", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let expected_payload_offset =
            promoted_option_payload_offset(&body, "expected &Option<&u8> local");
        let wrong_align_offset = option_ref_payload_align(&body, "expected &Option<&u8> local");
        let seeded_u8_offsets: Vec<_> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter_map(|(type_key, _sort, _expr, _obj_id, offset)| {
                (type_key.as_ref() == "u8").then_some(*offset)
            })
            .collect();

        assert!(
            seeded_u8_offsets.contains(&expected_payload_offset),
            "const_ref_option_ref_u8_some should seed u8 payload at option field offset {expected_payload_offset}, got {seeded_u8_offsets:?}"
        );
        assert!(
            !seeded_u8_offsets.contains(&wrong_align_offset)
                || wrong_align_offset == expected_payload_offset,
            "const_ref_option_ref_u8_some should not seed u8 payload at ref alignment offset {wrong_align_offset}, got {seeded_u8_offsets:?}"
        );
    });
}

/// Promoted `None::<&u8>` const refs should still seed and predeclare the
/// Option-typed memory lane used by `assert_eq!(first(&[]), None)`.
#[test]
fn test_const_ref_option_ref_none_registers_option_memory() {
    with_test_ay_ctx_for_source(CONST_REF_OPTION_REF_NONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_ref_option_ref_none");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "const_ref_option_ref_none", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let seeded_type_keys: std::collections::BTreeSet<_> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .map(|(type_key, _, _, _, _)| type_key.as_ref())
            .collect();

        let option_type_key = promoted_option_type_key(&body, "expected &Option<&u8> local");
        assert!(
            seeded_type_keys.contains(option_type_key.as_str()),
            "const_ref_option_ref_none should seed Option-typed memory {option_type_key}, got {seeded_type_keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key(option_type_key.as_str()),
            "const_ref_option_ref_none should predeclare {option_type_key}, keys={:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

/// The exact `first(&array)` regression harnesses should not generate any
/// const-ref memory init whose type key is missing from the predeclared array
/// registry after declaration setup.
#[test]
fn test_const_ref_first_then_array_assert_eq_registers_generated_type_arrays() {
    with_test_ay_ctx_for_source(CONST_REF_FIRST_THEN_ARRAY_ASSERT_EQ_SOURCE, |ctx| {
        for fn_name in
            ["probe_zero_len_first_then_array_assert_eq", "probe_zst_first_then_array_assert_eq"]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            chc_ctx.declare_block_relations();

            let generated_type_keys: std::collections::BTreeSet<_> = chc_ctx
                .ref_resolution
                .const_ref_memory_inits
                .iter()
                .map(|(type_key, _, _, _, _)| type_key.as_ref())
                .collect();
            assert!(
                !generated_type_keys.is_empty(),
                "{fn_name} should generate const-ref memory init keys"
            );

            let missing_keys: Vec<_> = generated_type_keys
                .iter()
                .copied()
                .filter(|type_key| !chc_ctx.heap_state.type_arrays.contains_key(*type_key))
                .collect();
            assert!(
                missing_keys.is_empty(),
                "{fn_name} should predeclare every generated const-ref type array; missing={missing_keys:?}, generated={generated_type_keys:?}, registered={:?}",
                chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
            );
        }
    });
}

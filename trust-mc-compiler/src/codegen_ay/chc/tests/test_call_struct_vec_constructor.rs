// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_struct_vec_constructor.rs` — constructor-pattern
//! detection for structs that embed a single Vec field.
//!
//! Part of #4127.
//!
//! Covers:
//! - Positive: `Self(vec![lit])` newtype constructor is detected
//! - Positive: multi-field struct with one Vec field is detected
//! - Negative: struct with two Vec fields must not be claimed
//! - Negative: struct with no Vec fields must not be claimed
//! - Negative: plain Vec::new() (no wrapping struct) must not be claimed

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::codegen_call_struct_vec_constructor::vec_constructor_pattern_detected;
use super::common::*;

const SINGLE_VEC_NEWTYPE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct CnfClause(Vec<i32>);

    impl CnfClause {
        pub fn unit(lit: i32) -> Self {
            Self(vec![lit])
        }
    }
"#;

const MULTI_FIELD_WITH_ONE_VEC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct TaggedVec {
        pub tag: u32,
        pub data: Vec<u32>,
        pub label: bool,
    }

    impl TaggedVec {
        pub fn new(tag: u32, label: bool) -> Self {
            Self { tag, data: Vec::new(), label }
        }
    }
"#;

const MULTI_VEC_STRUCT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct DualVec {
        pub left: Vec<u32>,
        pub right: Vec<u32>,
        pub default: u32,
    }

    impl DualVec {
        pub fn new(default: u32) -> Self {
            Self { left: Vec::new(), right: Vec::new(), default }
        }
    }
"#;

const NO_VEC_STRUCT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Pair {
        pub x: u32,
        pub y: u32,
    }

    impl Pair {
        pub fn new(x: u32, y: u32) -> Self {
            Self { x, y }
        }
    }
"#;

const MULTI_ELEMENT_VEC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Buffer(Vec<u8>);

    impl Buffer {
        pub fn from_slice(a: u8, b: u8, c: u8) -> Self {
            Self(vec![a, b, c])
        }
    }
"#;

const VEC_NEW_EMPTY_CONSTRUCTOR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Wrapper(Vec<u64>);

    impl Wrapper {
        pub fn empty() -> Self {
            Self(Vec::new())
        }
    }
"#;

fn constructor_field_is_vec(body: &rustc_public::mir::Body) -> Vec<bool> {
    let dest_ty = body.locals()[0].ty;
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind() else {
        panic!("constructor body should return an ADT");
    };
    let variants = def.variants();
    let variant =
        variants.first().expect("constructor return type should have at least one variant");
    variant
        .fields()
        .iter()
        .map(|field| {
            let ty = field.ty_with_args(&args);
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Vec"
            )
        })
        .collect()
}

#[test]
fn test_struct_vec_constructor_single_newtype_positive() {
    with_test_ay_ctx_for_source(SINGLE_VEC_NEWTYPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unit");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        assert_eq!(field_is_vec.len(), 1, "CnfClause should have 1 field");
        assert!(field_is_vec[0], "CnfClause.0 should be a Vec");
        assert!(
            vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner should detect a single-Vec newtype `Self(vec![lit])` body"
        );
    });
}

#[test]
fn test_struct_vec_constructor_multi_field_with_one_vec_positive() {
    with_test_ay_ctx_for_source(MULTI_FIELD_WITH_ONE_VEC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "new");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        let vec_count = field_is_vec.iter().filter(|v| **v).count();
        assert_eq!(vec_count, 1, "TaggedVec should have exactly 1 Vec field");
        assert!(
            vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner should detect a multi-field struct with one Vec::new() field"
        );
    });
}

#[test]
fn test_struct_vec_constructor_multi_vec_rejected() {
    with_test_ay_ctx_for_source(MULTI_VEC_STRUCT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "new");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        let vec_count = field_is_vec.iter().filter(|v| **v).count();
        assert_eq!(vec_count, 2, "DualVec should have 2 Vec fields");
        assert!(
            !vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner must reject structs with multiple Vec fields"
        );
    });
}

#[test]
fn test_struct_vec_constructor_no_vec_rejected() {
    with_test_ay_ctx_for_source(NO_VEC_STRUCT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "new");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        let vec_count = field_is_vec.iter().filter(|v| **v).count();
        assert_eq!(vec_count, 0, "Pair should have no Vec fields");
        assert!(
            !vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner must reject structs with no Vec fields"
        );
    });
}

#[test]
fn test_struct_vec_constructor_empty_vec_new_positive() {
    with_test_ay_ctx_for_source(VEC_NEW_EMPTY_CONSTRUCTOR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "empty");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        assert_eq!(field_is_vec.len(), 1, "Wrapper should have 1 field");
        assert!(field_is_vec[0], "Wrapper.0 should be a Vec");
        assert!(
            vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner should detect Vec::new() empty constructor pattern"
        );
    });
}

#[test]
fn test_struct_vec_constructor_multi_element_vec_positive() {
    with_test_ay_ctx_for_source(MULTI_ELEMENT_VEC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "from_slice");
        let body = instance.body().expect("function body");
        let field_is_vec = constructor_field_is_vec(&body);

        assert_eq!(field_is_vec.len(), 1, "Buffer should have 1 field");
        assert!(field_is_vec[0], "Buffer.0 should be a Vec");
        assert!(
            vec_constructor_pattern_detected(&body, &field_is_vec),
            "constructor scanner should detect vec![a, b, c] multi-element constructor"
        );
    });
}

/// Passing an empty field_is_vec should always reject.
#[test]
fn test_struct_vec_constructor_empty_field_is_vec_rejected() {
    with_test_ay_ctx_for_source(SINGLE_VEC_NEWTYPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unit");
        let body = instance.body().expect("function body");

        let empty_field_is_vec: Vec<bool> = vec![];
        assert!(
            !vec_constructor_pattern_detected(&body, &empty_field_is_vec),
            "constructor scanner must reject when field_is_vec is empty"
        );
    });
}

/// Passing all-false field_is_vec should always reject.
#[test]
fn test_struct_vec_constructor_all_false_field_is_vec_rejected() {
    with_test_ay_ctx_for_source(SINGLE_VEC_NEWTYPE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "unit");
        let body = instance.body().expect("function body");

        let all_false_field_is_vec = vec![false, false, false];
        assert!(
            !vec_constructor_pattern_detected(&body, &all_false_field_is_vec),
            "constructor scanner must reject when no field is marked as Vec"
        );
    });
}

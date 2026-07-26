// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_struct_map_constructor.rs` — constructor-pattern
//! detection for structs that embed a single BTreeMap/HashMap field.
//!
//! Part of #3348.
//!
//! Covers:
//! - Positive: simple `Self { data: BTreeMap::new(), default }` constructor is detected
//! - Negative: unrelated `String::new()` field must not be mistaken for the map field
//! - Negative: multi-map structs are out of scope and must not be claimed

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::codegen_call_struct_map_constructor::constructor_pattern_detected;
use super::common::*;

const SINGLE_MAP_CONSTRUCTOR_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::BTreeMap;

    pub struct DataStore {
        pub data: BTreeMap<u32, u32>,
        pub default: u32,
    }

    impl DataStore {
        pub fn new(default: u32) -> Self {
            Self { data: BTreeMap::new(), default }
        }
    }
"#;

const NON_MAP_NEW_FALSE_POSITIVE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::BTreeMap;

    pub struct DataStore {
        pub data: BTreeMap<u32, u32>,
        pub label: String,
    }

    impl DataStore {
        pub fn with_label(data: BTreeMap<u32, u32>) -> Self {
            Self { data, label: String::new() }
        }
    }
"#;

const MULTI_MAP_CONSTRUCTOR_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::BTreeMap;

    pub struct DualStore {
        pub left: BTreeMap<u32, u32>,
        pub right: BTreeMap<u32, u32>,
        pub default: u32,
    }

    impl DualStore {
        pub fn new(right: BTreeMap<u32, u32>, default: u32) -> Self {
            Self { left: BTreeMap::new(), right, default }
        }
    }
"#;

fn constructor_field_is_map(body: &rustc_public::mir::Body) -> Vec<bool> {
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
        .map(|field| ChcCtx::type_is_hashmap(&field.ty_with_args(&args)))
        .collect()
}

#[test]
fn test_struct_map_constructor_pattern_positive() {
    with_test_ay_ctx_for_source(SINGLE_MAP_CONSTRUCTOR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "new");
        let body = instance.body().expect("function body");
        let field_is_map = constructor_field_is_map(&body);

        assert!(
            constructor_pattern_detected(&body, &field_is_map),
            "constructor scanner should detect a single-map `Self {{ data: BTreeMap::new(), ... }}` body"
        );
    });
}

#[test]
fn test_struct_map_constructor_pattern_ignores_non_map_new_fields() {
    with_test_ay_ctx_for_source(NON_MAP_NEW_FALSE_POSITIVE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "with_label");
        let body = instance.body().expect("function body");
        let field_is_map = constructor_field_is_map(&body);

        assert!(
            !constructor_pattern_detected(&body, &field_is_map),
            "constructor scanner must not treat `String::new()` or other non-map `new()` calls as the embedded map field"
        );
    });
}

#[test]
fn test_struct_map_constructor_pattern_rejects_multi_map_structs() {
    with_test_ay_ctx_for_source(MULTI_MAP_CONSTRUCTOR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "new");
        let body = instance.body().expect("function body");
        let field_is_map = constructor_field_is_map(&body);

        assert!(
            field_is_map.iter().filter(|is_map| **is_map).count() == 2,
            "test probe must contain two map fields"
        );
        assert!(
            !constructor_pattern_detected(&body, &field_is_map),
            "constructor scanner only supports a single embedded map field and must decline multi-map structs"
        );
    });
}

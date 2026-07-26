// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_stmt_store_array.rs` — direct array element store
//! via Index/ConstantIndex projection.
//!
//! Part of #2303 (codegen_stmt_store_array.rs, 203 LOC, zero dedicated coverage).
//! Covers:
//! - `handle_array_element_store`: arr[idx] = value via Index
//! - `handle_array_element_store`: arr[const] = value via ConstantIndex
//! - Sort coercion at store boundaries (Part of #2244)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Array element store via variable Index
// =============================================================================

const ARRAY_INDEX_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_index_store(arr: &mut [u32; 4], idx: usize, val: u32) {
        arr[idx] = val;
    }
"#;

/// Array store via variable Index produces a VC without panicking.
#[test]
fn test_array_index_store_generates_vc() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_index_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_index_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_index_store", body.blocks.len());

        // u32 array store should produce bv32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 array index store should have bv32 sort in relations");
    });
}

/// Array store should produce rules referencing SMT store operations.
#[test]
fn test_array_index_store_has_transition_rules() {
    with_test_ay_ctx_for_source(ARRAY_INDEX_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_index_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_index_store", ChcConfig::default());

        // Should have transition rules (not just entry + error)
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "array store should produce transition rules"
        );
    });
}

// =============================================================================
// Array element store via constant index
// =============================================================================

const ARRAY_CONST_INDEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_const_store(arr: &mut [u32; 4]) {
        arr[0] = 10;
        arr[1] = 20;
        arr[2] = 30;
    }
"#;

/// Constant-index array store produces a VC.
#[test]
fn test_array_const_index_store_generates_vc() {
    with_test_ay_ctx_for_source(ARRAY_CONST_INDEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_const_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_const_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_const_store", body.blocks.len());

        // Constant-index array store should produce transition rules
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "const-index array store should produce transition rules"
        );
    });
}

// =============================================================================
// Array store with conditional index
// =============================================================================

const ARRAY_CONDITIONAL_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_conditional_store(arr: &mut [u32; 4], flag: bool) {
        if flag {
            arr[0] = 100;
        } else {
            arr[1] = 200;
        }
    }
"#;

/// Conditional array store generates VC with SwitchInt branches.
#[test]
fn test_conditional_array_store_generates_vc() {
    with_test_ay_ctx_for_source(ARRAY_CONDITIONAL_STORE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_conditional_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_conditional_store", ChcConfig::default());

        assert_vc_structure(&vc, "probe_conditional_store", body.blocks.len());

        // SwitchInt on flag should produce at least 2 guarded rules
        let guarded_count = vc
            .rules
            .iter()
            .filter(|r| {
                r.body.relation.is_some() && r.body.constraints.iter().any(|c| c.sort().is_bool())
            })
            .count();

        assert!(
            guarded_count >= 2,
            "conditional store should produce >= 2 guarded rules, got {}",
            guarded_count
        );
    });
}

// =============================================================================
// Array store at Mem level
// =============================================================================

const ARRAY_MEM_LEVEL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_mem_store(arr: &mut [u32; 2], idx: usize) {
        arr[idx] = 42;
    }
"#;

/// Array store at Mem level should also generate a valid VC.
#[test]
fn test_array_store_mem_level_generates_vc() {
    with_test_ay_ctx_for_source(ARRAY_MEM_LEVEL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_mem_store");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_array_mem_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_array_mem_store", body.blocks.len());

        // Mem-level array store should produce transition rules
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "Mem-level array store should produce transition rules"
        );
    });
}

// =============================================================================
// Non-array store should not be handled by handle_array_element_store
// =============================================================================

/// Simple scalar assignment has no Index projection — handle_array_element_store
/// returns false. This test verifies the pipeline still generates valid VC.
#[test]
fn test_scalar_store_not_array_store() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]
        pub fn probe_scalar_store(x: u32) -> u32 {
            let y = x + 1;
            y
        }
        "#,
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_store");
            let body = instance.body().expect("body");
            let vc = mir_to_chc(ctx.tcx, &body, "probe_scalar_store", ChcConfig::default());

            assert_vc_structure(&vc, "probe_scalar_store", body.blocks.len());

            // Scalar u32 store should produce bv32 state vars
            let has_bv32 = vc
                .relations
                .iter()
                .any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
            assert!(has_bv32, "scalar u32 store should have bv32 sort in relations");
        },
    );
}

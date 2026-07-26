// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tests for infer_flattened_discr type-based fallback (#2841, #3136).
// Verifies that missing discriminant map entries fall back to type inference:
// Option → (1,0), Result → (0,1), general 2-variant ADTs → variant structure.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const RESULT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_result_discriminant(x: Result<u32, u32>) -> isize {
        match x {
            Ok(_) => 0,
            Err(_) => 1,
        }
    }
"#;

const OPTION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_option_discriminant(x: Option<u32>) -> isize {
        match x {
            Some(_) => 1,
            None => 0,
        }
    }
"#;

/// When flattened_enum_discr map is missing for a Result local,
/// infer_flattened_discr should return (0, 1) via type-based inference
/// (Ok=variant 0, Err=variant 1), NOT the old hardcoded (1, 0) default.
///
/// Part of #2841: Result discriminant inversion from Option-like default.
#[test]
fn test_infer_flattened_discr_result_missing_map_returns_0_1() {
    with_test_ay_ctx_for_source(RESULT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_result_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a flattened Result local (Bool fld0 = is_ok proxy).
        let result_local = chc_ctx.flatten.flattened_tuple_locals.iter().copied().find(|&idx| {
            let vec_idx = chc_ctx.state_idx_for_local(idx);
            chc_ctx.state_var_mgr.state_vars.get(vec_idx).is_some_and(|(_, sort)| sort.is_bool())
        });
        let result_local =
            result_local.expect("should find a flattened Result local with Bool fld0");

        // Clear the discriminant map to simulate the missing-map scenario.
        // In production, this happens when codegen_decl_state_vars doesn't
        // populate the map for a Result local (e.g., indirect Result types,
        // monomorphization edge cases).
        chc_ctx.flatten.flattened_enum_discr.clear();

        // Call infer_flattened_discr — should return (0, 1) via type inference.
        let (true_val, false_val) = chc_ctx.infer_flattened_discr(result_local);
        assert_eq!(
            (true_val, false_val),
            (0, 1),
            "Result with missing discriminant map should infer (0, 1) = (Ok, Err), \
             got ({true_val}, {false_val}) — #2841 regression"
        );
    });
}

/// When flattened_enum_discr map is missing for an Option local,
/// infer_flattened_discr should return (1, 0) via type-based inference.
/// This verifies the Option path wasn't broken by the Result fix.
#[test]
fn test_infer_flattened_discr_option_missing_map_returns_1_0() {
    with_test_ay_ctx_for_source(OPTION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = chc_ctx.flatten.flattened_tuple_locals.iter().copied().find(|&idx| {
            let vec_idx = chc_ctx.state_idx_for_local(idx);
            chc_ctx.state_var_mgr.state_vars.get(vec_idx).is_some_and(|(_, sort)| sort.is_bool())
        });
        let option_local =
            option_local.expect("should find a flattened Option local with Bool fld0");

        chc_ctx.flatten.flattened_enum_discr.clear();

        let (true_val, false_val) = chc_ctx.infer_flattened_discr(option_local);
        assert_eq!(
            (true_val, false_val),
            (1, 0),
            "Option with missing discriminant map should infer (1, 0) = (Some, None), \
             got ({true_val}, {false_val})"
        );
    });
}

// Part of #3136: Source with a custom 2-variant option-like enum.
// Variant Active has a payload (fields > 0), variant Inactive is empty.
// Discriminants: Active=0, Inactive=1 (default sequential).
const CUSTOM_OPTION_LIKE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Status { Active(u32), Inactive }

    pub fn probe_custom_discriminant(x: Status) -> isize {
        match x {
            Status::Active(_) => 0,
            Status::Inactive => 1,
        }
    }
"#;

/// Part of #3136: When flattened_enum_discr map is missing for a custom
/// 2-variant option-like enum, infer_flattened_discr should infer
/// discriminants from variant structure instead of recording a fallback.
/// For Status { Active(u32), Inactive }: Active=variant 0 has payload,
/// so true_val=0 (payload variant), false_val=1 (empty variant).
#[test]
fn test_infer_flattened_discr_custom_option_like_enum() {
    use rustc_public::ty::{RigidTy, TyKind};

    with_test_ay_ctx_for_source(CUSTOM_OPTION_LIKE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_custom_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find a local whose type is the custom Status enum.
        let status_local = body.locals().iter().enumerate().find_map(|(idx, decl)| {
            if let TyKind::RigidTy(RigidTy::Adt(def, _)) = decl.ty.kind() {
                if def.trimmed_name() == "Status" {
                    return Some(idx);
                }
            }
            None
        });
        let status_local = status_local.expect("should find a Status enum local");

        // Manually insert into flattened_tuple_locals to simulate the
        // scenario where the enum is flattened with Bool fld0 but the
        // discriminant map was not populated.
        chc_ctx.flatten.flattened_tuple_locals.insert(status_local);
        chc_ctx.flatten.flattened_enum_discr.clear();

        let (true_val, false_val) = chc_ctx.infer_flattened_discr(status_local);

        // Status::Active = variant 0 (has payload) → true_val = 0
        // Status::Inactive = variant 1 (empty) → false_val = 1
        assert_eq!(
            (true_val, false_val),
            (0, 1),
            "Custom option-like enum should infer payload variant's discriminant as true_val, \
             got ({true_val}, {false_val})"
        );
    });
}

// Part of #3136: Source with a custom 2-variant both-payload enum.
// Both variants have fields — exercises the non-swap path (d0, d1).
const CUSTOM_BOTH_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Either { Left(u32), Right(u64) }

    pub fn probe_either_discriminant(x: Either) -> isize {
        match x {
            Either::Left(_) => 0,
            Either::Right(_) => 1,
        }
    }
"#;

/// Part of #3136: Both-payload 2-variant enum (like Result but not named Result).
/// Convention: true = variant 0. So true_val=0, false_val=1.
/// This exercises the non-swap path in the general 2-variant ADT inference.
#[test]
fn test_infer_flattened_discr_custom_both_payload_enum() {
    use rustc_public::ty::{RigidTy, TyKind};

    with_test_ay_ctx_for_source(CUSTOM_BOTH_PAYLOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_either_discriminant");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_either_discriminant", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let either_local = body.locals().iter().enumerate().find_map(|(idx, decl)| {
            if let TyKind::RigidTy(RigidTy::Adt(def, _)) = decl.ty.kind() {
                if def.trimmed_name() == "Either" {
                    return Some(idx);
                }
            }
            None
        });
        let either_local = either_local.expect("should find an Either enum local");

        chc_ctx.flatten.flattened_tuple_locals.insert(either_local);
        chc_ctx.flatten.flattened_enum_discr.clear();

        let (true_val, false_val) = chc_ctx.infer_flattened_discr(either_local);

        // Either::Left = variant 0, Either::Right = variant 1.
        // Both have payloads → no swap → true_val = disc_0 = 0, false_val = disc_1 = 1.
        assert_eq!(
            (true_val, false_val),
            (0, 1),
            "Both-payload enum should infer (variant 0 disc, variant 1 disc), \
             got ({true_val}, {false_val})"
        );
    });
}

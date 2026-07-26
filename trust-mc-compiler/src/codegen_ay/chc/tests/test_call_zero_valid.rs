// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Localizer for the current-head `zero_valid` residual.
//!
//! Part of #3702: distinguish whether the remaining failure seam is in
//! aggregate zero materialization or in the generic derived-`PartialEq` path.

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::emit_chc;

const ZERO_VALID_SOURCE: &str = r#"
    #![allow(dead_code, invalid_value, unused_assignments)]

    use std::mem;

    #[repr(C)]
    #[derive(PartialEq, Eq)]
    struct S {
        a: u8,
        b: u16,
    }

    pub fn probe_zero_valid_scalar_u32() {
        let x: u32 = unsafe { mem::zeroed() };
        assert!(x == 0);
    }

    pub fn probe_zero_valid_struct_direct() {
        let x: S = unsafe { mem::zeroed() };
        assert!(x == S { a: 0, b: 0 });
    }

    fn do_test<T: Eq>(init: T, expected: T) {
        let mut x: T = init;
        x = unsafe { mem::zeroed() };
        assert!(expected == x);
    }

    pub fn probe_zero_valid_struct_generic() {
        do_test::<S>(S { a: 42, b: 42 }, S { a: 0, b: 0 });
    }

    pub fn probe_zero_invalid_ref() {
        let _: &u8 = unsafe { mem::zeroed() };
    }
"#;

const ABORT_SOURCE: &str = r#"
    #![allow(dead_code, internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_intrinsic_abort() {
        core::intrinsics::abort()
    }
"#;

const ASSERT_VALIDITY_SOURCE: &str = r#"
    #![allow(dead_code, internal_features)]
    #![feature(core_intrinsics)]

    pub fn probe_intrinsic_assert_zero_valid() {
        core::intrinsics::assert_zero_valid::<&u8>();
    }
"#;

const USER_ABORT_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod user {
        pub mod intrinsics {
            #[inline(never)]
            pub fn abort() {
                std::hint::black_box(());
            }
        }
    }

    pub fn probe_user_abort() {
        user::intrinsics::abort()
    }
"#;

const USER_ASSERT_VALIDITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod user {
        pub mod intrinsics {
            #[inline(never)]
            pub fn assert_zero_valid<T>() {
                std::hint::black_box(std::marker::PhantomData::<T>);
            }
        }
    }

    pub fn probe_user_assert_zero_valid() {
        user::intrinsics::assert_zero_valid::<&u8>()
    }
"#;

fn assert_definite_diverging_failure(
    source: &str,
    fn_name: &str,
    callee_suffix: &str,
    expected_kind: trust_mc_core::violation::PropertyKind,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                else {
                    return None;
                };
                let callee_path = chc_ctx.resolve_callee_path(func)?;
                callee_path.ends_with(callee_suffix).then_some((
                    bb_idx,
                    func,
                    args,
                    destination,
                    callee_path,
                ))
            })
            .unwrap_or_else(|| panic!("expected call ending in {callee_suffix}"));

        // The regression targets the fallback reached for a diverging
        // dispatch. rustc may retain a nominal continuation for a validity
        // intrinsic, so construct that dispatcher input explicitly.
        let forced_diverging_target = None;

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &forced_diverging_target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: Some(callee_path),
        };

        assert!(
            !chc_ctx.codegen_call_terminator(&dcx),
            "the terminal failure emits an error edge, not a successor edge"
        );
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            0,
            "a statically proven failure must not retain the unknown-diverging-call taint"
        );
        assert_eq!(chc_ctx.vc.properties.len(), 1);
        assert_eq!(chc_ctx.vc.properties[0].kind, expected_kind);
        assert!(
            chc_ctx.vc.rules.iter().any(|rule| rule.head.name.starts_with("error_p")),
            "reaching the proven-failure call must derive a named error property"
        );
    });
}

fn assert_zero_valid_probe_unsat(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(ZERO_VALID_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(fallback_count, 0, "{fn_name} should stay off the CHC fallback path");

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });

    let translation_drops = take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
    assert_eq!(drop_count, 0, "{fn_name} should have zero translation drops, sites={fn_sites:?}");

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_zero_valid_scalar_u32_solver_produces_unsat() {
    assert_zero_valid_probe_unsat("probe_zero_valid_scalar_u32");
}

#[test]
fn test_zero_valid_struct_direct_solver_produces_unsat() {
    assert_zero_valid_probe_unsat("probe_zero_valid_struct_direct");
}

#[test]
fn test_zero_valid_struct_generic_solver_produces_unsat() {
    assert_zero_valid_probe_unsat("probe_zero_valid_struct_generic");
}

#[test]
fn test_intrinsic_assert_zero_valid_is_named_ub_without_unknown_taint() {
    assert_definite_diverging_failure(
        ASSERT_VALIDITY_SOURCE,
        "probe_intrinsic_assert_zero_valid",
        "::intrinsics::assert_zero_valid",
        trust_mc_core::violation::PropertyKind::UndefinedBehavior,
    );
}

#[test]
fn test_intrinsic_abort_is_named_panic_without_unknown_taint() {
    assert_definite_diverging_failure(
        ABORT_SOURCE,
        "probe_intrinsic_abort",
        "::intrinsics::abort",
        trust_mc_core::violation::PropertyKind::Panic,
    );
}

#[test]
fn test_user_intrinsics_abort_stays_unknown_and_tainted() {
    assert_user_diverging_call_stays_unknown(
        USER_ABORT_SOURCE,
        "probe_user_abort",
        "::intrinsics::abort",
    );
}

#[test]
fn test_user_intrinsics_assert_zero_valid_stays_unknown_and_tainted() {
    assert_user_diverging_call_stays_unknown(
        USER_ASSERT_VALIDITY_SOURCE,
        "probe_user_assert_zero_valid",
        "::intrinsics::assert_zero_valid",
    );
}

fn assert_user_diverging_call_stays_unknown(source: &str, fn_name: &str, callee_suffix: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                else {
                    return None;
                };
                let callee_path = chc_ctx.resolve_callee_path(func)?;
                callee_path.ends_with(callee_suffix).then_some((
                    bb_idx,
                    func,
                    args,
                    destination,
                    callee_path,
                ))
            })
            .unwrap_or_else(|| panic!("expected user call ending in {callee_suffix}"));

        // Keep an ordinary user call in the corpus so rustc cannot erase it
        // based on no-return analysis, then force the diverging-dispatch input.
        // This exercises the namespace authority check directly rather than a
        // particular rustc lowering of user-defined `fn() -> !` calls.
        let forced_diverging_target = None;

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &forced_diverging_target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: Some(callee_path),
        };

        assert!(!chc_ctx.codegen_call_terminator(&dcx));
        assert_eq!(
            chc_ctx.diagnostics.diverging_call_drop.get(),
            1,
            "a user function ending in {callee_suffix} must remain fail-closed"
        );
        assert!(
            chc_ctx.vc.properties.is_empty(),
            "an unknown diverging call must not be upgraded to a named genuine property"
        );
        assert!(
            chc_ctx.vc.rules.iter().any(|rule| rule.head.name == "error"),
            "the unknown diverging call must retain the aggregate fail-closed error edge"
        );
    });
}

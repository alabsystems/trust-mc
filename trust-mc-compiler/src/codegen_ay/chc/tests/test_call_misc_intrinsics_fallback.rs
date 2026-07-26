// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for misc intrinsic sound-fallback bookkeeping.
//!
//! `codegen_call_cmp_string::misc_intrinsics` has several branches that emit a
//! goto with the destination left nondeterministic. These must increment
//! `record_sound_fallback()` so CTREX classify as OverApproximation instead of
//! Genuine.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_cmp_string::CallCmpString;
use super::common::*;
use crate::codegen_ay::emit_chc;

const SOURCE_MISC_INTRINSICS: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code, internal_features, unused_unsafe)]

    use std::intrinsics::{arith_offset, float_to_int_unchecked, ptr_guaranteed_cmp, write_bytes};

    pub unsafe fn probe_write_bytes(dst: *mut u8, val: u8, count: usize) {
        unsafe { write_bytes(dst, val, count) };
    }

    pub unsafe fn probe_arith_offset(base: *const i32, off: isize) -> *const i32 {
        unsafe { arith_offset(base, off) }
    }

    pub unsafe fn probe_ptr_guaranteed_cmp(a: *const u8, b: *const u8) -> u8 {
        ptr_guaranteed_cmp(a, b)
    }

    pub unsafe fn probe_float_to_int_unchecked(x: f32) -> i32 {
        unsafe { float_to_int_unchecked(x) }
    }
"#;

fn with_misc_intrinsic_dispatch_source(
    source: &str,
    probe_suffix: &str,
    intrinsic_name: &str,
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains(intrinsic_name)
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!("expected {intrinsic_name} call terminator in {probe_suffix}")
            });

        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

fn with_misc_intrinsic_dispatch(
    probe_suffix: &str,
    intrinsic_name: &str,
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_misc_intrinsic_dispatch_source(
        SOURCE_MISC_INTRINSICS,
        probe_suffix,
        intrinsic_name,
        assertions,
    );
}

fn assert_sound_fallback_only(chc_ctx: &ChcCtx<'_, '_>, before_rules: usize) {
    assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        1,
        "misc intrinsic fallback should increment sound fallback exactly once"
    );
    assert_eq!(
        chc_ctx.fallback_count, 0,
        "misc intrinsic fallback must stay sound-approximation, not demoted chc_fallback"
    );
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "misc intrinsic fallback must stay off the unhandled-call path"
    );
}

/// Part of #3703 finding 2: WriteBytes/VolatileCopy identity retention is
/// under-approximation (not sound over-approximation), so these must use
/// `record_fallback` (DEMOTED) instead of `record_sound_fallback`.
fn assert_demoted_fallback_only(chc_ctx: &ChcCtx<'_, '_>, before_rules: usize) {
    assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
    assert_eq!(
        chc_ctx.fallback_count, 1,
        "memory-mutating intrinsic should increment demoted fallback exactly once"
    );
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        0,
        "memory-mutating intrinsic must NOT use sound_fallback (identity retention is under-approx)"
    );
    assert_eq!(
        chc_ctx.diagnostics.unhandled_call.get(),
        0,
        "memory-mutating intrinsic fallback must stay off the unhandled-call path"
    );
}

#[test]
fn test_write_bytes_unconstrained_handler_records_sound_fallback() {
    with_misc_intrinsic_dispatch(
        "probe_write_bytes",
        "write_bytes",
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("write_bytes"),
                "precondition: expected write_bytes callee path, got {callee_path}"
            );
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound starts at zero");
            assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted starts at zero");

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);
            // Part of #3703 finding 2: write_bytes is memory-mutating with
            // identity retention (under-approximation), so it uses
            // record_fallback (DEMOTED), not record_sound_fallback.
            assert_demoted_fallback_only(chc_ctx, before_rules);
        },
    );
}

#[test]
fn test_write_bytes_full_local_symbolic_fill_avoids_sound_fallback() {
    const SOURCE: &str = r#"
        #![feature(core_intrinsics)]
        #![allow(dead_code, internal_features, unused_unsafe)]

        use std::intrinsics::write_bytes;

        pub unsafe fn probe_write_bytes_full_local(val: u8) -> u32 {
            let mut dst: u32 = 7;
            unsafe { write_bytes(&mut dst as *mut u32, val, 1) };
            dst
        }
    "#;

    with_misc_intrinsic_dispatch_source(
        SOURCE,
        "probe_write_bytes_full_local",
        "write_bytes",
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("write_bytes"),
                "precondition: expected write_bytes callee path, got {callee_path}"
            );
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound starts at zero");
            assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted starts at zero");
            let before_rules = chc_ctx.vc.rules.len();

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "full-local write_bytes should model the referent without sound fallback"
            );
            assert_eq!(
                chc_ctx.fallback_count, 0,
                "full-local write_bytes should stay off the demoted fallback path"
            );
        },
    );
}

#[test]
fn test_arith_offset_missing_args_records_sound_fallback() {
    with_misc_intrinsic_dispatch(
        "probe_arith_offset",
        "arith_offset",
        |chc_ctx,
         func,
         _actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("arith_offset"),
                "precondition: expected arith_offset callee path, got {callee_path}"
            );
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

            let target_opt = Some(target);
            let empty_args: &[Operand] = &[];
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: empty_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);
            assert_sound_fallback_only(chc_ctx, before_rules);
        },
    );
}

#[test]
fn test_ptr_guaranteed_cmp_missing_args_records_sound_fallback() {
    with_misc_intrinsic_dispatch(
        "probe_ptr_guaranteed_cmp",
        "ptr_guaranteed_cmp",
        |chc_ctx,
         func,
         _actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("ptr_guaranteed_cmp"),
                "precondition: expected ptr_guaranteed_cmp callee path, got {callee_path}"
            );
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

            let target_opt = Some(target);
            let empty_args: &[Operand] = &[];
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: empty_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);
            assert_sound_fallback_only(chc_ctx, before_rules);
        },
    );
}

#[test]
fn test_float_to_int_unchecked_missing_args_records_sound_fallback() {
    with_misc_intrinsic_dispatch(
        "probe_float_to_int_unchecked",
        "float_to_int_unchecked",
        |chc_ctx,
         func,
         _actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("float_to_int_unchecked"),
                "precondition: expected float_to_int_unchecked callee path, got {callee_path}"
            );
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");

            let target_opt = Some(target);
            let empty_args: &[Operand] = &[];
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: empty_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);
            assert_sound_fallback_only(chc_ctx, before_rules);
        },
    );
}

#[test]
fn test_float_to_int_unchecked_uses_precise_bv_path_for_i32() {
    with_misc_intrinsic_dispatch(
        "probe_float_to_int_unchecked",
        "float_to_int_unchecked",
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("float_to_int_unchecked"),
                "precondition: expected float_to_int_unchecked callee path, got {callee_path}"
            );
            assert_eq!(actual_args.len(), 1, "precondition: expected one float argument");
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound starts at zero");
            assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted starts at zero");

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "precise float_to_int_unchecked lowering must not record sound fallback"
            );
            assert_eq!(
                chc_ctx.fallback_count, 0,
                "precise float_to_int_unchecked lowering must not use demoted fallback"
            );

            let smt = emit_chc(&chc_ctx.vc).to_string();
            assert!(
                smt.contains("extract 30 23") && smt.contains("extract 22 0"),
                "float_to_int_unchecked(i32) should lower through the IEEE-754 BV extractor, got: {smt}"
            );
            let forbidden_rounding_tokens = [
                "fp.to_sbv",
                "fp.to_ubv",
                " RTZ ",
                "roundTowardZero",
                " RNE ",
                "roundNearestTiesToEven",
                " RNA ",
                "roundNearestTiesToAway",
                " RTP ",
                "roundTowardPositive",
                " RTN ",
                "roundTowardNegative",
            ]
            .into_iter()
            .filter(|token| smt.contains(token))
            .collect::<Vec<_>>();
            assert!(
                forbidden_rounding_tokens.is_empty(),
                "float_to_int_unchecked(i32) must stay off CHC FP rounding-mode terms, found {forbidden_rounding_tokens:?} in: {smt}"
            );
        },
    );
}

// =============================================================================
// arith_offset fallback (migrated from test_call_misc.rs, Part of #3746)
// =============================================================================

const ARITH_OFFSET_FALLBACK_SOURCE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code, internal_features, unused_unsafe)]

    use std::intrinsics::arith_offset;

    pub unsafe fn probe_arith_offset_unknown_size(base: *const i32, off: isize) -> *const i32 {
        arith_offset(base, off)
    }
"#;

fn with_arith_offset_dispatch(
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(ARITH_OFFSET_FALLBACK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arith_offset_unknown_size");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_arith_offset_unknown_size", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("arith_offset")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .expect("expected arith_offset call terminator");

        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

#[test]
fn test_arith_offset_unknown_pointee_size_emits_unconstrained_goto() {
    with_arith_offset_dispatch(
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("arith_offset"),
                "precondition: expected arith_offset callee path, got {callee_path}"
            );
            assert!(
                actual_args.len() >= 2,
                "precondition: expected base and offset args for arith_offset"
            );

            let unknown_pointee_args = vec![actual_args[1].clone(), actual_args[1].clone()];
            let before_rules = chc_ctx.vc.rules.len();
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: start at zero");
            assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted starts at zero");

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: &unknown_pointee_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                1,
                "unknown pointee size must increment sound_fallback_count exactly once"
            );
            assert_eq!(
                chc_ctx.fallback_count, 0,
                "unknown pointee size must stay a sound fallback, not a demoted fallback"
            );

            let rule = chc_ctx.vc.rules.last().expect("expected fallback goto rule");
            assert_ne!(rule.head.name, "error", "unknown pointee size should stay fail-open");
            assert_eq!(
                rule.body.constraints.len(),
                stmt_constraints.len(),
                "unknown pointee size must not add a destination equality constraint"
            );
        },
    );
}

// =============================================================================
// Partial-overwrite localizer (Part of #3949)
// =============================================================================

/// Part of #3949: partial stack-array write_bytes must not crash.
///
/// `WriteBytes/main.rs` calls `write_bytes(arr.as_mut_ptr(), 0xfe, 2)` on
/// `[u32; 4]`, which writes 8 of 16 bytes. The handler should encode this as
/// a prefix store chain over the array and preserve the untouched suffix.
#[test]
fn test_write_bytes_partial_stack_array_prefix_store() {
    const SOURCE: &str = r#"
        #![feature(core_intrinsics)]
        #![allow(dead_code, internal_features, unused_unsafe)]

        use std::intrinsics::write_bytes;

        pub fn probe_write_bytes_partial_stack_array() -> [u32; 4] {
            let mut arr: [u32; 4] = [0, 0, 0, 0];
            unsafe { write_bytes(arr.as_mut_ptr(), 0xfe, 2) };
            arr
        }
    "#;

    with_misc_intrinsic_dispatch_source(
        SOURCE,
        "probe_write_bytes_partial_stack_array",
        "write_bytes",
        |chc_ctx,
         func,
         actual_args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            assert!(
                callee_path.contains("write_bytes"),
                "precondition: expected write_bytes callee path, got {callee_path}"
            );
            assert_eq!(chc_ctx.sound_fallback_count(), 0, "precondition: sound starts at zero");
            assert_eq!(chc_ctx.fallback_count, 0, "precondition: demoted starts at zero");
            let before_rules = chc_ctx.vc.rules.len();

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args: actual_args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_call_primitive_cmp(&dcx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one goto rule");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                0,
                "partial prefix write_bytes should be modeled precisely"
            );
            assert_eq!(
                chc_ctx.fallback_count, 0,
                "partial prefix write_bytes should stay off the demoted fallback path"
            );

            let rule = chc_ctx.vc.rules.last().expect("expected write_bytes goto rule");
            let smt = format!("{:?}", rule.body.constraints);
            assert!(
                smt.contains("Store"),
                "partial prefix write_bytes should constrain the array with store(), got {smt}"
            );
        },
    );
}

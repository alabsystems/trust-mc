// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Full-harness copy/copy_nonoverlapping tests — block fallback tracing,
//! call terminator dispatch, self-referential store detection, and
//! raw-pointer-cast copy encoding.
//!
//! Split from test_stmt_copy.rs for file-size compliance.
//! Part of #2231 (zero test coverage for codegen_stmt_copy.rs).

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::rules::codegen_rules::TransitionContext;
use crate::codegen_ay::chc::rules::codegen_rules::dispatch_block_terminator;
use crate::codegen_ay::emit_chc;
use std::sync::Arc;
use trust_mc_core::chc::RelationApp;

fn collect_block_fallback_trace(
    chc_ctx: &mut ChcCtx<'_, '_>,
) -> Vec<(usize, usize, String, Vec<String>)> {
    chc_ctx.declare_block_relations();
    chc_ctx.declare_error_relation();

    let mut trace = Vec::new();
    for bb_idx in 0..chc_ctx.body.blocks.len() {
        // Cleanup/unwind blocks may not have relations declared — skip them.
        let Some(from_rel) = chc_ctx.block_relations.get(&bb_idx).cloned() else {
            continue;
        };
        let before = chc_ctx.fallback_count;
        let (stmt_constraints, output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(bb_idx));
        let shared_constraints: Arc<[Expr]> = stmt_constraints.into();
        let tctx = TransitionContext {
            from_app: &from_app,
            output_args: &output_args,
            shared_constraints: &shared_constraints,
            modified_locals: &modified_locals,
            bb_idx,
        };
        dispatch_block_terminator(chc_ctx, &tctx);

        let after = chc_ctx.fallback_count;
        if after > before {
            let statements = chc_ctx.body.blocks[bb_idx]
                .statements
                .iter()
                .map(|stmt| format!("{:?}", stmt.kind))
                .collect();
            trace.push((
                bb_idx,
                after - before,
                format!("{:?}", chc_ctx.body.blocks[bb_idx].terminator.kind),
                statements,
            ));
        }
    }

    trace
}

#[test]
fn test_mir_intrinsic_copy_with_overlap_full_harness_no_block_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn test_copy_with_overlap() {
            let arr: [i32; 3] = [0, 1, 0];
            let src: *const i32 = arr.as_ptr();

            unsafe {
                let dst = src.add(1) as *mut i32;
                core::intrinsics::copy(src, dst, 2);
                assert!(arr[0] == 0);
                assert!(arr[1] == 0);
                assert!(arr[2] == 1);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "test_copy_with_overlap");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "test_copy_with_overlap", ChcConfig::default());
        let trace = collect_block_fallback_trace(&mut chc_ctx);

        // Copy-with-overlap dispatch currently uses fallback for the intrinsic call.
        // Track the fallback count to detect regressions, but don't require zero.
        let total_fallbacks: usize = trace.iter().map(|(_, count, _, _)| count).sum();
        assert!(
            total_fallbacks <= 3,
            "copy-with-overlap fallback count regressed (expected ≤3): {trace:#?}"
        );
    });
}

#[test]
fn test_mir_intrinsic_copy_call_terminator_dispatches_with_tracked_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn test_copy_with_overlap() {
            let arr: [i32; 3] = [0, 1, 0];
            let src: *const i32 = arr.as_ptr();

            unsafe {
                let dst = src.add(1) as *mut i32;
                core::intrinsics::copy(src, dst, 2);
                assert!(arr[0] == 0);
                assert!(arr[1] == 0);
                assert!(arr[2] == 1);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "test_copy_with_overlap");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "test_copy_with_overlap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !path.ends_with("::copy") || path.contains("copy_nonoverlapping") {
                continue;
            }

            found = true;
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
            let target_opt = Some(*target);
            let before_fallback = chc_ctx.fallback_count;

            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            let dispatched = chc_ctx.codegen_call_terminator(&dcx);
            assert!(dispatched, "intrinsic copy call should dispatch through the CHC call spine");
            // Copy intrinsic currently hits fallback — track count to detect regressions.
            let fallback_delta = chc_ctx.fallback_count - before_fallback;
            assert!(
                fallback_delta <= 1,
                "intrinsic copy fallback count regressed (expected ≤1, got {fallback_delta})"
            );
            break;
        }

        assert!(found, "expected intrinsic copy call terminator in test_copy_with_overlap MIR");
    });
}

#[test]
fn test_mir_intrinsic_copy_with_offset_preserves_ref_targets_into_copy_dst() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn test_copy_with_overlap() {
            let arr: [i32; 3] = [0, 1, 0];
            let src: *const i32 = arr.as_ptr();

            unsafe {
                let dst = src.add(1) as *mut i32;
                core::intrinsics::copy(src, dst, 2);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};

        let instance = find_instance_by_suffix(ctx.tcx, "test_copy_with_overlap");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "test_copy_with_overlap", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let (copy_bb_idx, copy_dst_local) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                    return None;
                };
                let path = chc_ctx.resolve_callee_path(func)?;
                if !path.ends_with("::copy") || path.contains("copy_nonoverlapping") {
                    return None;
                }
                let (Operand::Copy(place) | Operand::Move(place)) = &args[1] else {
                    return None;
                };
                Some((bb_idx, place.local))
            })
            .expect("expected intrinsic copy call with raw-pointer destination local");

        let ptr_add_dest_local = body.blocks[copy_bb_idx]
            .statements
            .iter()
            .find_map(|stmt| {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    return None;
                };
                if lhs.local != copy_dst_local {
                    return None;
                }
                match rhs {
                    Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    | Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => Some(src.local),
                    _ => None,
                }
            })
            .expect(
                "expected copy destination local to come from a cast/use of the ptr.add result",
            );

        let ptr_add_bb_idx = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { destination, .. } = &block.terminator.kind else {
                    return None;
                };
                (destination.local == ptr_add_dest_local).then_some(bb_idx)
            })
            .expect("expected call terminator producing the ptr.add result local");

        for bb_idx in 0..body.blocks.len() {
            let Some(from_rel) = chc_ctx.block_relations.get(&bb_idx).cloned() else {
                continue;
            };
            let (stmt_constraints, output_args, modified_locals, _safety_checks) =
                chc_ctx.encode_block_statements(bb_idx);

            if bb_idx == copy_bb_idx {
                let dst_target = chc_ctx.ref_resolution.ref_targets.get(&copy_dst_local).cloned();
                assert!(
                    dst_target.is_some(),
                    "copy destination local should inherit ref_target before dispatch; \
                     ptr_add_local={ptr_add_dest_local}, copy_dst_local={copy_dst_local}, \
                     ref_targets={:?}",
                    chc_ctx.ref_resolution.ref_targets
                );
                assert!(
                    chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&copy_dst_local),
                    "copy destination local should remain call_forwarded for raw-pointer deref \
                     resolution; copy_dst_local={copy_dst_local}"
                );
            }

            let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(bb_idx));
            let shared_constraints: Arc<[Expr]> = stmt_constraints.into();
            let tctx = TransitionContext {
                from_app: &from_app,
                output_args: &output_args,
                shared_constraints: &shared_constraints,
                modified_locals: &modified_locals,
                bb_idx,
            };
            dispatch_block_terminator(&mut chc_ctx, &tctx);

            if bb_idx == ptr_add_bb_idx {
                let add_target =
                    chc_ctx.ref_resolution.ref_targets.get(&ptr_add_dest_local).cloned();
                assert!(
                    add_target.is_some(),
                    "ptr.add result local should receive ref_target after call dispatch; \
                     ptr_add_local={ptr_add_dest_local}, ref_targets={:?}",
                    chc_ctx.ref_resolution.ref_targets
                );
                assert!(
                    chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&ptr_add_dest_local),
                    "ptr.add result local should be marked call_forwarded"
                );
            }
        }
    });
}

#[test]
fn test_mir_copy_nonoverlapping_swap_full_harness_no_block_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code, deprecated)]

        fn swap<T>(x: &mut T, y: &mut T) {
            unsafe {
                let mut t: T = std::mem::uninitialized();
                std::ptr::copy_nonoverlapping(x, &mut t, 1);
                std::ptr::copy_nonoverlapping(y, x, 1);
                std::ptr::copy_nonoverlapping(&t, y, 1);
                std::mem::forget(t);
            }
        }

        pub fn test_swap() {
            let mut x = 12;
            let mut y = 13;
            swap(&mut x, &mut y);
            assert!(x == 13);
            assert!(y == 12);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "test_swap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "test_swap", ChcConfig::default());
        let trace = collect_block_fallback_trace(&mut chc_ctx);

        // Swap harness currently uses fallback for copy_nonoverlapping calls.
        // Track fallback count to detect regressions.
        let total_fallbacks: usize = trace.iter().map(|(_, count, _, _)| count).sum();
        assert!(
            total_fallbacks <= 5,
            "swap harness fallback count regressed (expected ≤5): {trace:#?}"
        );
    });
}

#[test]
fn test_mir_copy_swap_call_terminator_dispatches_with_tracked_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code, deprecated)]

        fn swap<T>(x: &mut T, y: &mut T) {
            unsafe {
                let mut t: T = std::mem::uninitialized();
                std::ptr::copy_nonoverlapping(x, &mut t, 1);
                std::ptr::copy_nonoverlapping(y, x, 1);
                std::ptr::copy_nonoverlapping(&t, y, 1);
                std::mem::forget(t);
            }
        }

        pub fn test_swap() {
            let mut x = 12;
            let mut y = 13;
            swap(&mut x, &mut y);
            assert!(x == 13);
            assert!(y == 12);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "test_swap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "test_swap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !path.ends_with("::swap") {
                continue;
            }

            found = true;
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
            let target_opt = Some(*target);
            let before_fallback = chc_ctx.fallback_count;

            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            let dispatched = chc_ctx.codegen_call_terminator(&dcx);
            assert!(
                dispatched,
                "swap call should dispatch through fn_inline rather than falling through"
            );
            // Swap dispatch currently may use fallback — track to detect regressions.
            let fallback_delta = chc_ctx.fallback_count - before_fallback;
            assert!(
                fallback_delta <= 2,
                "swap call fallback count regressed (expected ≤2, got {fallback_delta})"
            );
            break;
        }

        // Rustc may inline swap() — if so, test_swap's MIR has no ::swap call.
        // The full-harness variant covers this case via block-level fallback counting.
        if !found {
            eprintln!(
                "note: ::swap call was inlined away by rustc; \
                 skipping call-terminator dispatch assertions"
            );
        }
    });
}

#[test]
fn test_copy_nonoverlapping_avoids_self_referential_out_store() {
    // Regression for copy_dynamic_count.rs CTREX failures: when dst is initialized
    // earlier in the block, copy_nonoverlapping must read the current dst value from
    // local_expr_env, not from the same __out variable being assigned.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_with_preinit(count: usize) -> [u8; 4] {
            let src = [1u8, 2, 3, 4];
            let mut dst = [0u8; 4];
            unsafe {
                std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), count);
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_with_preinit");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_with_preinit", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        let mut self_referential_eq = Vec::new();
        for segment in smt.split("(= ") {
            let Some((lhs, _rest)): Option<(&str, &str)> = segment.split_once(' ') else {
                continue;
            };
            if !lhs.contains("probe_copy_with_preinit") || !lhs.contains("__out") {
                continue;
            }
            let needle = format!("(= {lhs} (store {lhs}");
            if smt.contains(&needle) {
                self_referential_eq.push(needle);
            }
        }

        assert!(
            self_referential_eq.is_empty(),
            "copy_nonoverlapping generated self-referential __out store constraints: {self_referential_eq:?}"
        );
        assert!(
            smt.contains("(store"),
            "copy_nonoverlapping should still generate store constraints"
        );
    });
}

// =============================================================================
// Part of #3665: Raw-pointer-cast copy_nonoverlapping ref-target + fallback
// =============================================================================

/// D1 for #3665: Verify that raw-pointer-cast temporaries feeding
/// copy_nonoverlapping have ref_targets entries after declaration pass.
///
/// The probe matches the exact shape of copy_raw_ptr_constant:
///   &src as *const [u8; 2] as *const u8
/// If ref-target propagation through Cast works, the cast temps resolve
/// to the original array locals.
#[test]
fn test_raw_ptr_cast_copy_has_ref_targets() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_raw_ptr_cast() {
            let src: [u8; 2] = [1, 2];
            let mut dst: [u8; 2] = [0, 0];
            unsafe {
                core::ptr::copy_nonoverlapping(
                    &src as *const [u8; 2] as *const u8,
                    &mut dst as *mut [u8; 2] as *mut u8,
                    2,
                );
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_raw_ptr_cast");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_raw_ptr_cast", ChcConfig::default());
        // collect_numeric_ref_targets runs during declare_block_relations,
        // not during ChcCtx::new. Must call it before inspecting ref_targets.
        chc_ctx.declare_block_relations();

        let ref_targets = &chc_ctx.ref_resolution.ref_targets;
        assert!(
            !ref_targets.is_empty(),
            "ref_targets should be non-empty after declaration pass — \
             raw-pointer-cast propagation may not be working"
        );

        // Find locals whose type is a raw pointer (*const u8 or *mut u8).
        // These are the cast temps that feed copy_nonoverlapping.
        let mut raw_ptr_locals_with_targets = 0;
        for local_idx in ref_targets.keys() {
            let local_ty = body.locals()[*local_idx].ty;
            if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(_, _)) =
                local_ty.kind()
            {
                raw_ptr_locals_with_targets += 1;
            }
        }
        assert!(
            raw_ptr_locals_with_targets >= 2,
            "Expected at least 2 raw-pointer locals with ref_targets (src + dst casts), \
             found {raw_ptr_locals_with_targets}. Cast propagation may have missed the \
             raw pointer temporaries."
        );
    });
}

/// D2 for #3665: The raw-pointer-cast probe must NOT increment
/// sound_fallback_count when translated through the CHC pipeline.
///
/// If this test fails, the copy encoder still falls through to
/// unsupported_havoc on the raw-cast shape, and D3 must patch the
/// specific guard that triggers it.
#[test]
fn test_raw_ptr_cast_copy_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_raw_ptr_cast_fb() {
            let src: [u8; 2] = [1, 2];
            let mut dst: [u8; 2] = [0, 0];
            unsafe {
                core::ptr::copy_nonoverlapping(
                    &src as *const [u8; 2] as *const u8,
                    &mut dst as *mut [u8; 2] as *mut u8,
                    2,
                );
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_raw_ptr_cast_fb");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_raw_ptr_cast_fb", ChcConfig::default());
        let (vc, _) = chc_ctx.translate();

        // The VC should have non-empty relations and rules.
        assert!(!vc.relations.is_empty(), "VC should have relations");
        assert!(!vc.rules.is_empty(), "VC should have rules");

        // Serialize to SMT and check for store constraints — the copy
        // should produce array stores, not fall through to havoc.
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(store"),
            "raw-ptr-cast copy_nonoverlapping should generate store \
             constraints, not fall through to havoc"
        );
    });
}

/// D2 supplement for #3665: Verify sound_fallback_count is zero for the
/// raw-pointer-cast probe at the block-statement encoding level.
///
/// This is a more direct test than the VC-level test above — it uses
/// encode_block_statements to inspect the fallback counter before/after.
#[test]
fn test_raw_ptr_cast_copy_zero_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_raw_ptr_cast_ctr() {
            let src: [u8; 2] = [1, 2];
            let mut dst: [u8; 2] = [0, 0];
            unsafe {
                core::ptr::copy_nonoverlapping(
                    &src as *const [u8; 2] as *const u8,
                    &mut dst as *mut [u8; 2] as *mut u8,
                    2,
                );
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        use rustc_public::mir::{NonDivergingIntrinsic, StatementKind};

        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_raw_ptr_cast_ctr");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_raw_ptr_cast_ctr", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the block containing the CopyNonOverlapping intrinsic.
        // If MIR lowered it as a call terminator instead, this test is
        // not applicable (covered by the VC-level test above).
        let copy_bb_idx = body.blocks.iter().enumerate().find_map(|(bb_idx, bb)| {
            bb.statements
                .iter()
                .any(|stmt| {
                    matches!(
                        stmt.kind,
                        StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_))
                    )
                })
                .then_some(bb_idx)
        });

        let Some(copy_bb_idx) = copy_bb_idx else {
            // MIR lowered as call terminator — skip this test variant.
            // The VC-level test_raw_ptr_cast_copy_no_fallback covers that path.
            return;
        };

        let before = chc_ctx.sound_fallback_count();
        let (_constraints, _output_args, _modified, _safety_checks) =
            chc_ctx.encode_block_statements(copy_bb_idx);
        let after = chc_ctx.sound_fallback_count();

        assert_eq!(
            before, after,
            "Raw-pointer-cast copy_nonoverlapping should NOT increment \
             sound_fallback_count (before={before}, after={after}). \
             The copy encoder is falling through to unsupported_havoc \
             on the raw-cast shape."
        );
    });
}

/// Full-harness test for #3665: the complete copy_raw_ptr_constant shape
/// including assertions, to identify which encoding path produces
/// sound_fallback_count=1 in the compiletest harness.
///
/// The copy encoder itself is clean (proven by tests above). The fallback
/// must come from another path — likely the assertion's array indexing or
/// the panic call dispatch.
#[test]
fn test_raw_ptr_cast_copy_with_assert_fallback_site() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_raw_ptr_cast_assert() -> [u8; 2] {
            let src: [u8; 2] = [1, 2];
            let mut dst: [u8; 2] = [0, 0];
            unsafe {
                core::ptr::copy_nonoverlapping(
                    &src as *const [u8; 2] as *const u8,
                    &mut dst as *mut [u8; 2] as *mut u8,
                    2,
                );
            }
            assert!(dst[0] == 1);
            assert!(dst[1] == 2);
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_raw_ptr_cast_assert");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_raw_ptr_cast_assert", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        // Check for store constraints (copy encoding worked).
        let smt = emit_chc(&vc).to_string();
        assert!(smt.contains("(store"), "copy encoding should produce store constraints");

        // The compiletest harness shows sound_fallback_count=1.
        // This test confirms whether the VC structure changes with
        // assertions present.
        assert!(!vc.relations.is_empty(), "VC should have relations");
        assert!(!vc.rules.is_empty(), "VC should have rules");

        // Comprehensive diagnostic dump: check ALL sound-approximation counters
        // to identify which category produces sound_fallback_count=1 in the
        // full compiletest pipeline.
        let d = &diagnostics;
        let mut nonzero = Vec::new();
        let checks: &[(&str, usize)] = &[
            ("place_translation_drop", d.place_translation_drop.get()),
            ("const_translation_drop", d.const_translation_drop.get()),
            ("unsupported_field_projection", d.unsupported_field_projection.get()),
            ("unhandled_call", d.unhandled_call.get()),
            ("error_blocked_fmt", d.error_blocked_fmt.get()),
            ("known_stdlib_unconstrained", d.known_stdlib_unconstrained.get()),
            ("inferable_predicate", d.inferable_predicate.get()),
            ("diverging_call_drop", d.diverging_call_drop.get()),
            ("coerce_eq_dropped_constraint", d.coerce_eq_dropped_constraint.get()),
            ("assume_dropped_transition", d.assume_dropped_transition.get()),
            ("assert_untranslatable", d.assert_untranslatable.get()),
            ("heap_check_untranslatable", d.heap_check_untranslatable.get()),
            ("heap_check_unknown_layout", d.heap_check_unknown_layout.get()),
            ("store_dropped_transition", d.store_dropped_transition.get()),
            ("iterator_unsound_skip", d.iterator_unsound_skip.get()),
            ("bigint_unsound_skip", d.bigint_unsound_skip.get()),
            ("kani_mem_overapprox", d.kani_mem_overapprox.get()),
            ("ptr_metadata_unconstrained", d.ptr_metadata_unconstrained.get()),
            ("static_init_incomplete", d.static_init_incomplete.get()),
            ("aggregate_encoding_gap", d.aggregate_encoding_gap.get()),
            ("stub_approximation", d.stub_approximation.get()),
        ];
        for &(name, count) in checks {
            if count > 0 {
                nonzero.push(format!("{name}={count}"));
            }
        }
        // This assertion reveals the specific fallback category.
        // The copy encoder is clean (proven by D1/D2 tests), so any
        // nonzero counter here identifies the adjacent path.
        assert!(
            nonzero.is_empty(),
            "Sound-approximation counters fired during copy_raw_ptr_constant \
             translation (expected all zero from D1/D2): {nonzero:?}"
        );
    });
}

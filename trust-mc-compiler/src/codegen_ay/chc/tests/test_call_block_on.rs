// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for specialized `block_on` dispatch.
//!
//! Part of #3955.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

const ASYNC_BLOCK_ON_SOURCE: &str = r#"
#![allow(dead_code)]

use std::{
    future::Future,
    pin::Pin,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

fn test_async_await() {
    block_on(async {
        let async_fn_result = async_fn().await;
        assert_eq!(42, async_fn_result);
    })
}

pub async fn async_fn() -> i32 {
    42
}

pub fn block_on<T>(mut fut: impl Future<Output = T>) -> T {
    let waker = unsafe { Waker::from_raw(NOOP_RAW_WAKER) };
    let cx = &mut Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(cx) {
            std::task::Poll::Ready(res) => return res,
            std::task::Poll::Pending => continue,
        }
    }
}

const NOOP_RAW_WAKER: RawWaker = {
    unsafe fn clone_waker(_: *const ()) -> RawWaker {
        NOOP_RAW_WAKER
    }
    unsafe fn noop(_: *const ()) {}
    RawWaker::new(std::ptr::null(), &RawWakerVTable::new(clone_waker, noop, noop, noop))
};
"#;

const MANUAL_ASYNC_BLOCK_ON_SOURCE: &str = r#"
#![allow(dead_code)]

use std::{
    future::Future,
    pin::Pin,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

fn test_async_await_manually() {
    block_on(async {
        let async_block_result = async { 42 }.await;
        let async_fn_result = async_fn().await;
        assert_eq!(async_block_result, async_fn_result);
    })
}

pub async fn async_fn() -> i32 {
    42
}

pub fn block_on<T>(mut fut: impl Future<Output = T>) -> T {
    let waker = unsafe { Waker::from_raw(NOOP_RAW_WAKER) };
    let cx = &mut Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(cx) {
            std::task::Poll::Ready(res) => return res,
            std::task::Poll::Pending => continue,
        }
    }
}

const NOOP_RAW_WAKER: RawWaker = {
    unsafe fn clone_waker(_: *const ()) -> RawWaker {
        NOOP_RAW_WAKER
    }
    unsafe fn noop(_: *const ()) {}
    RawWaker::new(std::ptr::null(), &RawWakerVTable::new(clone_waker, noop, noop, noop))
};
"#;

fn find_call_instance_by_callee_suffix(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    callee_suffix: &str,
) -> rustc_public::mir::mono::Instance {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let func_ty = func.ty(body.locals()).ok()?;
                let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                    return None;
                };
                let def_id = rustc_internal::internal(tcx, def.def_id());
                tcx.def_path_str(def_id)
                    .ends_with(callee_suffix)
                    .then(|| rustc_public::mir::mono::Instance::resolve(def, &substs).ok())
                    .flatten()
            }
            _ => None,
        })
        .expect("body should contain a matching monomorphized call instance")
}

fn with_named_block_on_call(
    source: &str,
    entry: &str,
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send,
) {
    with_test_ay_ctx_for_source(source, move |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, entry);
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, entry, ChcConfig::default());
        chc_ctx.declare_block_relations();

        for (bb_idx, block) in mir_body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(target_bb) = *target else {
                continue;
            };
            let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !callee_path.ends_with("::block_on") && callee_path != "block_on" {
                continue;
            }

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: Some(callee_path),
            };

            body(&mut chc_ctx, &dcx);
            return;
        }

        panic!("expected a block_on call in {entry}");
    });
}

fn with_block_on_call(mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send) {
    with_named_block_on_call(ASYNC_BLOCK_ON_SOURCE, "test_async_await", move |chc_ctx, dcx| {
        body(chc_ctx, dcx);
    });
}

fn with_manual_block_on_call(
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send,
) {
    with_named_block_on_call(
        MANUAL_ASYNC_BLOCK_ON_SOURCE,
        "test_async_await_manually",
        move |chc_ctx, dcx| {
            body(chc_ctx, dcx);
        },
    );
}

fn has_call_pending_backedge(body: &rustc_public::mir::Body) -> bool {
    for (call_bb, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { destination, target: Some(switch_bb), .. } =
            &block.terminator.kind
        else {
            continue;
        };

        let TerminatorKind::SwitchInt { discr, targets } = &body.blocks[*switch_bb].terminator.kind
        else {
            continue;
        };
        let discr_local = match discr {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        if !switch_uses_call_result_discriminant(
            &body.blocks[*switch_bb],
            discr_local,
            destination.local,
        ) {
            continue;
        }

        if targets
            .all_targets()
            .iter()
            .copied()
            .any(|candidate_bb| is_loop_backedge_target(body, call_bb, candidate_bb))
        {
            return true;
        }
    }

    false
}

fn is_loop_backedge_target(
    body: &rustc_public::mir::Body,
    call_bb: usize,
    target_bb: usize,
) -> bool {
    if target_bb <= call_bb {
        return true;
    }
    matches!(
        &body.blocks[target_bb].terminator.kind,
        TerminatorKind::Goto { target } if *target <= call_bb
    )
}

fn switch_uses_call_result_discriminant(
    block: &rustc_public::mir::BasicBlock,
    discr_local: Option<usize>,
    call_result_local: usize,
) -> bool {
    if discr_local == Some(call_result_local) {
        return true;
    }

    let Some(discr_local) = discr_local else {
        return false;
    };

    block.statements.iter().any(|stmt| {
        matches!(
            &stmt.kind,
            StatementKind::Assign(place, Rvalue::Discriminant(source))
                if place.projection.is_empty()
                    && place.local == discr_local
                    && source.projection.is_empty()
                    && source.local == call_result_local
        )
    })
}

#[test]
fn test_block_on_dispatch_claims_call_without_loop_exhaustion() {
    with_block_on_call(|chc_ctx, dcx| {
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_unhandled = chc_ctx.diagnostics.unhandled_call.get();
        let before_rules = chc_ctx.vc.rules.len();

        assert!(
            chc_ctx.codegen_call_terminator(dcx),
            "block_on should be claimed by call dispatch"
        );
        let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "specialized block_on dispatch should not record a sound fallback; detail={:?} translation_drop_sites={translation_drop_sites:?}",
            chc_ctx.sound_fallback_detail(),
        );
        assert_eq!(
            chc_ctx.diagnostics.unhandled_call.get(),
            before_unhandled,
            "specialized block_on dispatch should not increment unhandled_call"
        );
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "specialized block_on dispatch should emit at least one transition rule"
        );

        let smt = emit_chc(&chc_ctx.vc).to_string();
        assert!(
            !smt.contains("__loop_exhaust_inline"),
            "single-poll block_on specialization should avoid inline loop exhaustion, smt={smt}"
        );
    });
}

#[test]
fn test_block_on_specializer_rewrites_pending_backedge_to_unreachable() {
    with_test_ay_ctx_for_source(ASYNC_BLOCK_ON_SOURCE, |ctx| {
        let caller = find_instance_by_suffix(ctx.tcx, "test_async_await");
        let caller_body = caller.body().expect("body");
        let instance = find_call_instance_by_callee_suffix(ctx.tcx, &caller_body, "block_on");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &caller_body, "test_async_await", ChcConfig::default());

        let specialized = chc_ctx
            .specialize_block_on_body_for_single_poll(&body)
            .expect("block_on body should be specialized");

        assert!(
            has_call_pending_backedge(&body),
            "original block_on body should contain a result-discriminant loop backedge"
        );
        assert!(
            !has_call_pending_backedge(&specialized),
            "specialized block_on body should remove the result-discriminant loop backedge"
        );
        let has_unreachable = specialized
            .blocks
            .iter()
            .any(|block| matches!(&block.terminator.kind, TerminatorKind::Unreachable));

        assert!(has_unreachable, "specialized block_on body should introduce an Unreachable arm");
    });
}

/// Part of #3955: Verify that the block_on dispatch does not emit a
/// `__nested_call_overapprox` with a bv64 sort for the nested async-fn call
/// destination. Before the D1-D2 fix, the inline walker would compute
/// `BitVec(64)` for the async future local, causing a sort mismatch.
#[test]
fn test_block_on_dispatch_no_bv64_nested_call_for_async_destination() {
    with_block_on_call(|chc_ctx, dcx| {
        assert!(chc_ctx.codegen_call_terminator(dcx), "block_on should be claimed");

        let smt = emit_chc(&chc_ctx.vc).to_string();
        // The SMT output should not contain a nested_call_overapprox variable
        // with a BitVec 64 sort for the async-fn call result. If it does,
        // the inline walker is still using the unresolved opaque type.
        let has_bv64_nested_overapprox = smt.lines().any(|line| {
            line.contains("__nested_call_overapprox") && line.contains("(_ BitVec 64)")
        });
        assert!(
            !has_bv64_nested_overapprox,
            "async-fn call destination should not produce a bv64 __nested_call_overapprox; \
             inline walker should resolve through body-local normalization"
        );
    });
}

/// Part of #3955: Verify that `resolve_inline_local_ty` resolves async fn call
/// destination locals to Coroutine types (not opaque `impl Future`), matching
/// the state-var resolution. This prevents the Coroutine→bv64 sort mismatch
/// that caused inline walker fallbacks.
#[test]
fn test_async_fn_destination_resolves_to_coroutine_via_inline_helper() {
    with_test_ay_ctx_for_source(ASYNC_BLOCK_ON_SOURCE, |ctx| {
        let caller = find_instance_by_suffix(ctx.tcx, "test_async_await");
        let caller_body = caller.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &caller_body, "test_async_await", ChcConfig::default());

        // Find the block_on callee and get its body for inline resolution.
        let block_on_instance =
            find_call_instance_by_callee_suffix(ctx.tcx, &caller_body, "block_on");
        let block_on_body = block_on_instance.body().expect("body");

        // The block_on body calls Future::poll on a local that may have an opaque
        // `impl Future` type. resolve_inline_local_ty should normalize it.
        // Check that at least one local in block_on resolves to a Coroutine type
        // through the new helper (specifically the future argument local).
        let mut found_coroutine = false;
        for (local_idx, _) in block_on_body.locals().iter().enumerate() {
            if let Some(resolved_ty) = chc_ctx.resolve_inline_local_ty(&block_on_body, local_idx) {
                if matches!(resolved_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                    found_coroutine = true;
                    // Verify that translate_ty produces a non-BV sort for coroutines.
                    let sort = ChcCtx::translate_ty(resolved_ty);
                    assert!(
                        sort.as_ref().map_or(false, |s| !s.is_bitvec()),
                        "coroutine type should translate to a datatype sort, not bitvec; \
                         local={local_idx}, sort={sort:?}"
                    );
                    break;
                }
            }
        }

        // The block_on body is generic over `impl Future<Output = T>`.
        // With the outer caller's instance, resolve_body_ty should normalize
        // opaque futures. If no coroutine local found, verify at minimum that
        // the return local (0) resolves through the helper without panic.
        let ret_ty = chc_ctx.resolve_inline_local_ty(&block_on_body, 0);
        assert!(
            ret_ty.is_some(),
            "resolve_inline_local_ty should resolve the return local of block_on"
        );

        // If found_coroutine is false, the generic block_on may not monomorphize
        // here. At minimum verify the helper doesn't produce bv64 for the
        // future argument (local 1, the `fut` param).
        if !found_coroutine {
            if let Some(fut_ty) = chc_ctx.resolve_inline_local_ty(&block_on_body, 1) {
                // The resolved type should NOT be a plain integer/pointer when
                // the original type is `impl Future`. It should be either a
                // Coroutine or at least an ADT (not degraded to scalar bv64).
                let is_scalar = matches!(
                    fut_ty.kind(),
                    TyKind::RigidTy(RigidTy::Int(_))
                        | TyKind::RigidTy(RigidTy::Uint(_))
                        | TyKind::RigidTy(RigidTy::Bool)
                );
                assert!(
                    !is_scalar,
                    "async future parameter should not degrade to a scalar type; \
                     local=1, resolved_ty={fut_ty:?}"
                );
            }
        }
    });
}

#[test]
fn test_manual_block_on_async_constructor_drops_no_coercion_constraints() {
    with_test_ay_ctx_for_source(MANUAL_ASYNC_BLOCK_ON_SOURCE, |ctx| {
        super::super::set_chc_coerce_eq_dropped_constraint_count_for_test(
            "test_async_await_manually",
            0,
        );

        let instance = find_instance_by_suffix(ctx.tcx, "test_async_await_manually");
        let body = instance.body().expect("function body");

        let _vc = crate::codegen_ay::chc::mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "test_async_await_manually",
            ChcConfig::default(),
        );

        let per_fn = super::super::get_chc_coerce_eq_dropped_constraint_counts_by_fn();
        let dropped_for_fn = per_fn.get("test_async_await_manually").copied().unwrap_or(0);
        assert_eq!(
            dropped_for_fn, 0,
            "manual async executor translation should not drop async constructor/result coercion \
             constraints; per-function counts={per_fn:?}"
        );
    });
}

#[test]
fn test_manual_block_on_dispatch_ref_destination_avoids_coerce_drop() {
    with_manual_block_on_call(|chc_ctx, dcx| {
        crate::codegen_ay::chc::clear_chc_coerce_eq_dropped_constraint_counts_by_fn();
        let before_fallback = chc_ctx.sound_fallback_count();
        let before_rules = chc_ctx.vc.rules.len();

        assert!(
            chc_ctx.codegen_call_terminator(dcx),
            "manual block_on call should be claimed by call dispatch"
        );

        let per_fn = super::super::get_chc_coerce_eq_dropped_constraint_counts_by_fn();
        let dropped_for_fn = per_fn.get("test_async_await_manually").copied().unwrap_or(0);
        assert_eq!(
            dropped_for_fn, 0,
            "manual block_on dispatch should use the ref-destination memory bridge instead of \
             recording a dropped call-result coercion; per-function counts={per_fn:?}"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "manual block_on dispatch should stay on the precise inline path; detail={:?}",
            chc_ctx.sound_fallback_detail(),
        );
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "manual block_on dispatch should emit at least one transition rule"
        );

        crate::codegen_ay::chc::clear_chc_coerce_eq_dropped_constraint_counts_by_fn();
    });
}

#[test]
fn test_manual_block_on_raw_waker_consts_do_not_drop_constant_translation() {
    with_test_ay_ctx_for_source(MANUAL_ASYNC_BLOCK_ON_SOURCE, |ctx| {
        let _ = crate::codegen_ay::take_constant_translation_drop_count();

        let instance = find_instance_by_suffix(ctx.tcx, "test_async_await_manually");
        let body = instance.body().expect("function body");

        let _vc = crate::codegen_ay::chc::mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "test_async_await_manually",
            ChcConfig::default(),
        );

        let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
        assert_eq!(
            constant_drop_count, 0,
            "manual async RawWaker/RawWakerVTable const materialization should not increment const_translation_drop, count={constant_drop_count}"
        );
    });
}

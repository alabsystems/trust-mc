// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_coroutine_support.rs` — coroutine detection helpers.
//!
//! Part of #4127.
//!
//! Covers:
//! - `has_coroutine_arg`: detects coroutine-typed call arguments
//! - `returns_coroutine_state`: detects CoroutineState return types
//! - `has_simple_coroutine_yield_variant`: detects simple yield patterns
//! - `coroutine_owner_local_for_state_idx`: reverse-maps state index to owning local
//! - Negative: non-coroutine calls must not be detected

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::TerminatorKind;

const COROUTINE_RESUME_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_resume_call() -> i32 {
        let mut g = #[coroutine] |_x: i32| {
            yield 42;
            -1
        };
        match Pin::new(&mut g).resume(0) {
            CoroutineState::Yielded(v) => v,
            CoroutineState::Complete(v) => v,
        }
    }
"#;

const NON_COROUTINE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_plain_call(x: u32) -> u32 {
        x.wrapping_add(1)
    }
"#;

const COROUTINE_OWNER_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;

    pub fn probe_owner(x: i32) -> i32 {
        let mut g = #[coroutine] |_state: i32| {
            yield 1;
            2
        };
        let mut g = Pin::new(&mut g);
        match g.as_mut().resume(x) {
            CoroutineState::Yielded(v) => v,
            CoroutineState::Complete(v) => v,
        }
    }
"#;

#[test]
fn test_has_coroutine_arg_positive_on_resume() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_resume_call");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_resume_call", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the resume call -- it will have a coroutine-typed argument
        let found_coro_arg = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                let Ok(func_ty) = func.ty(body.locals()) else { return false };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
                    return false;
                };
                let name = def.trimmed_name();
                if name.contains("resume") {
                    return ChcCtx::test_has_coroutine_arg(args, &chc_ctx);
                }
            }
            false
        });

        assert!(found_coro_arg, "resume() call should be detected as having a coroutine argument");
    });
}

#[test]
fn test_has_coroutine_arg_negative_on_plain_call() {
    with_test_ay_ctx_for_source(NON_COROUTINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_plain_call");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_plain_call", ChcConfig::default());

        // Every call in this body should have no coroutine argument
        let any_coro = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { args, .. } = &block.terminator.kind {
                ChcCtx::test_has_coroutine_arg(args, &chc_ctx)
            } else {
                false
            }
        });

        assert!(!any_coro, "plain u32 function should not have any coroutine-typed arguments");
    });
}

#[test]
fn test_returns_coroutine_state_positive_on_resume() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_resume_call");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_resume_call", ChcConfig::default());

        // Find any Call whose return type is CoroutineState
        let found_coro_return = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                ChcCtx::test_returns_coroutine_state(func, &chc_ctx)
            } else {
                false
            }
        });

        assert!(found_coro_return, "resume() call should be detected as returning CoroutineState");
    });
}

#[test]
fn test_returns_coroutine_state_negative_on_plain_call() {
    with_test_ay_ctx_for_source(NON_COROUTINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_plain_call");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_plain_call", ChcConfig::default());

        let any_coro_return = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                ChcCtx::test_returns_coroutine_state(func, &chc_ctx)
            } else {
                false
            }
        });

        assert!(
            !any_coro_return,
            "plain u32 function should not have any call returning CoroutineState"
        );
    });
}

#[test]
fn test_coroutine_owner_local_for_state_idx_resolves_registered_coroutine() {
    with_test_ay_ctx_for_source(COROUTINE_OWNER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_owner");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_owner", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find any local with Coroutine type and check if it has a state index
        let coroutine_locals: Vec<usize> = body
            .locals()
            .iter()
            .enumerate()
            .filter_map(|(idx, local)| {
                matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))).then_some(idx)
            })
            .collect();

        assert!(
            !coroutine_locals.is_empty(),
            "probe_owner should have at least one local with Coroutine type"
        );

        // For each coroutine local that has a state index, verify the reverse lookup
        for &local_idx in &coroutine_locals {
            if let Some(state_idx) = chc_ctx.try_state_idx_for_local(local_idx) {
                let resolved = chc_ctx.coroutine_owner_local_for_state_idx(state_idx);
                assert_eq!(
                    resolved,
                    Some(local_idx),
                    "coroutine_owner_local_for_state_idx should resolve back to the owning local {local_idx}"
                );
            }
        }
    });
}

// -------------------------------------------------------------------------
// has_simple_coroutine_yield_variant tests
// -------------------------------------------------------------------------

/// A coroutine with both Yielded AND Complete returns (yield 42; -1) is NOT
/// a "simple yield variant" -- the function should return false because the
/// Complete branch makes the coroutine non-trivial to encode.
#[test]
fn test_has_simple_coroutine_yield_variant_negative_on_yield_and_complete() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_resume_call");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_resume_call", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the resume() call and check has_simple_coroutine_yield_variant
        let found_simple_yield = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let Ok(func_ty) = func.ty(body.locals()) else { return false };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
                    return false;
                };
                let name = def.trimmed_name();
                if name.contains("resume") {
                    return ChcCtx::test_has_simple_coroutine_yield_variant(func, &chc_ctx);
                }
            }
            false
        });

        assert!(
            !found_simple_yield,
            "resume() on a coroutine with both Yielded and Complete should NOT be detected as simple yield variant"
        );
    });
}

/// A plain (non-coroutine) function should never be detected as having
/// a simple coroutine yield variant.
#[test]
fn test_has_simple_coroutine_yield_variant_negative_on_plain_call() {
    with_test_ay_ctx_for_source(NON_COROUTINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_plain_call");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_plain_call", ChcConfig::default());

        let any_simple_yield = body.blocks.iter().any(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                ChcCtx::test_has_simple_coroutine_yield_variant(func, &chc_ctx)
            } else {
                false
            }
        });

        assert!(
            !any_simple_yield,
            "plain u32 function should not have any call with a simple coroutine yield variant"
        );
    });
}

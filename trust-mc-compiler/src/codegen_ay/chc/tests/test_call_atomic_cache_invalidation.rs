// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for atomic write cache invalidation.
//!
//! Part of #3937, #3938: atomic writes must clear stale cross-block
//! `const_folded_call_results` entries for the referent local.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_atomic::{CallDispatchAtomic, resolve_ptr_target_local};
use super::common::*;
use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;
use trust_mc_core::chc::RelationApp;

const ATOMIC_CMP_EXCHANGE_PROBE: &str = r#"
    use std::sync::atomic::{AtomicBool, Ordering};

    pub fn probe_compare_exchange() -> bool {
        let a = AtomicBool::new(true);
        a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst).unwrap();
        a.load(Ordering::SeqCst)
    }
"#;

const ATOMIC_FETCH_ADD_PROBE: &str = r#"
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_fetch_add() -> usize {
        let a = AtomicUsize::new(0);
        a.fetch_add(1, Ordering::SeqCst)
    }
"#;

fn find_atomic_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    expected_fragments: &[&str],
) -> (usize, Operand, Vec<Operand>, Place, Option<rustc_public::mir::BasicBlockIdx>, String) {
    let mut seen_paths = Vec::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let TerminatorKind::Call { func, args, destination, target, .. } = &block.terminator.kind
            && let Some(path) = chc_ctx.resolve_callee_path(func)
        {
            seen_paths.push(path.clone());
            if expected_fragments.iter().any(|fragment| path.contains(fragment)) {
                return (bb_idx, func.clone(), args.clone(), destination.clone(), *target, path);
            }
        }
    }

    panic!(
        "expected atomic call matching {expected_fragments:?}; observed call paths: {seen_paths:?}"
    );
}

fn block_relation_app(chc_ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> RelationApp {
    let from_rel = chc_ctx
        .block_relations
        .get(&bb_idx)
        .expect("source relation for atomic call block")
        .clone();
    let output_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    RelationApp::new(&from_rel, output_args)
}

fn assert_atomic_write_invalidates_const_cache(
    source: &str,
    fn_suffix: &str,
    expected_fragments: &[&str],
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, func, args, destination, target, callee_path) =
            find_atomic_call_site(&chc_ctx, &body, expected_fragments);
        let referent_local =
            resolve_ptr_target_local(&chc_ctx, args.first().expect("atomic write pointer arg"))
                .expect("atomic write pointer should resolve through ref_targets");

        chc_ctx.encode.const_folded_call_results.insert(referent_local, Expr::bool_const(true));
        assert!(
            chc_ctx.encode.const_folded_call_results.contains_key(&referent_local),
            "{callee_path}: test setup should seed const cache for referent local _{referent_local}"
        );

        let from_app = block_relation_app(&chc_ctx, bb_idx);
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func: &func,
            args: &args,
            destination: &destination,
            target: &target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: Some(callee_path.clone()),
        };
        assert!(
            chc_ctx.try_dispatch_call_atomic(&dcx),
            "{callee_path}: dispatcher should claim atomic write"
        );
        assert!(
            !chc_ctx.encode.const_folded_call_results.contains_key(&referent_local),
            "{callee_path}: atomic write must invalidate stale const cache for referent local _{referent_local}"
        );
    });
}

#[test]
fn test_atomic_compare_exchange_invalidates_const_cache_for_referent_local() {
    assert_atomic_write_invalidates_const_cache(
        ATOMIC_CMP_EXCHANGE_PROBE,
        "probe_compare_exchange",
        &["compare_exchange", "atomic_cxchg"],
    );
}

#[test]
fn test_atomic_fetch_add_invalidates_const_cache_for_referent_local() {
    assert_atomic_write_invalidates_const_cache(
        ATOMIC_FETCH_ADD_PROBE,
        "probe_fetch_add",
        &["fetch_add", "atomic_xadd", "atomic_uadd"],
    );
}

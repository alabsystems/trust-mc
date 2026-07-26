// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for coroutine-root pre-registration in CHC state-var setup.
//!
//! Part of #3807: `Pin<&mut Coroutine>` resume chains should resolve to the
//! concrete coroutine root without rediscovering the Pin unwrap at each use.

#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashSet;

use super::common::*;
use rustc_public::ty::{RigidTy, TyKind};

pub(super) const COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(coroutines, coroutine_trait)]
    #![feature(stmt_expr_attributes)]

    use std::ops::{Coroutine, CoroutineState};
    use std::pin::Pin;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DROP: AtomicUsize = AtomicUsize::new(0);

    #[derive(PartialEq, Eq, Debug)]
    struct Dropper(String);

    impl Drop for Dropper {
        fn drop(&mut self) {
            DROP.fetch_add(1, Ordering::SeqCst);
        }
    }

    pub fn probe_resume_live_across_yield() {
        let mut g = #[coroutine]
        |mut _d| {
            _d = yield;
            _d
        };

        let mut g = Pin::new(&mut g);

        match g.as_mut().resume(Dropper(String::from("Hello world!"))) {
            CoroutineState::Yielded(()) => {}
            _ => unreachable!(),
        }

        match g.as_mut().resume(Dropper(String::from("Number Two"))) {
            CoroutineState::Complete(dropper) => {
                let _ = dropper.0;
            }
            _ => unreachable!(),
        }

        drop(g);
    }
"#;

fn find_coroutine_closure_body(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    suffix: &str,
) -> rustc_public::mir::Body {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path.contains(suffix) && path.contains("{closure#0}")
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing closure for '{suffix}'"),
        [single] => single.body().expect("closure body should exist"),
        many => panic!("ambiguous closure for '{suffix}': {many:?}"),
    }
}

fn is_double_ref_to_coroutine(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(
                inner.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                    if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Coroutine(..)))
            )
    )
}

#[test]
fn test_coroutine_root_map_resolves_double_ref_resume_chain() {
    with_test_ay_ctx_for_source(COROUTINE_RESUME_LIVE_ACROSS_YIELD_SOURCE, |ctx| {
        let body = find_coroutine_closure_body(ctx.tcx, "probe_resume_live_across_yield");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_resume_live_across_yield::{closure#0}",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let inherited_root_locals: Vec<_> = chc_ctx
            .ref_resolution
            .coroutine_root_map
            .keys()
            .copied()
            .filter(|&local_idx| local_idx > body.arg_locals().len())
            .collect();
        assert!(
            !inherited_root_locals.is_empty(),
            "resume-live-across-yield closure should propagate coroutine roots beyond the Pin arg"
        );

        for local_idx in &inherited_root_locals {
            let root_expr = chc_ctx
                .resolve_coroutine_root_expr(*local_idx, &HashSet::new())
                .expect("propagated coroutine-root local should resolve");
            assert!(
                crate::codegen_ay::types::coroutine_discriminant_select(root_expr).is_some(),
                "propagated coroutine-root local {local_idx} should resolve to a coroutine root"
            );
        }

        let double_ref_locals: Vec<_> = body
            .local_decls()
            .filter_map(|(local_idx, local_decl)| {
                is_double_ref_to_coroutine(local_decl.ty).then_some(local_idx)
            })
            .collect();

        for local_idx in double_ref_locals {
            assert!(
                chc_ctx.ref_resolution.coroutine_root_map.contains_key(&local_idx),
                "double-ref coroutine local {local_idx} should inherit a pre-registered root"
            );
        }
    });
}

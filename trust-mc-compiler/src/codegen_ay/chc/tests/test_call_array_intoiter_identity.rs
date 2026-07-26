// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array IntoIter identity-call regression tests.
//!
//! `#3711` added CHC identity fast paths for:
//! - the array-iterator `unsize_mut/unsize` bridge
//! - `ManuallyDrop::deref_mut/deref`
//! - `Pin::new_unchecked` / `Pin::as_mut`
//!
//! `IntoIter::unsize_mut` is private, so the public `iter.next()` path is the
//! stable regression check for that bridge. `ManuallyDrop::deref_mut` is public
//! via `DerefMut`, and `Pin::as_mut` is public on a concrete `Pin<&mut T>`, so
//! both get focused direct-dispatch tests.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use rustc_public::mir::TerminatorKind;

const ARRAY_INTO_ITER_NEXT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_array_into_iter_next() -> Option<u32> {
        let mut iter = IntoIterator::into_iter([1u32, 2]);
        iter.next()
    }
"#;

const MANUALLY_DROP_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::mem::ManuallyDrop;
    use std::ops::DerefMut;

    pub fn probe_manually_drop_deref_mut(md: &mut ManuallyDrop<[u32; 2]>) -> &mut [u32; 2] {
        <ManuallyDrop<[u32; 2]> as DerefMut>::deref_mut(md)
    }
"#;

const PIN_AS_MUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::pin::Pin;

    pub fn probe_pin_as_mut<'a>(pin: &'a mut Pin<&'a mut [u32; 2]>) -> Pin<&'a mut [u32; 2]> {
        pin.as_mut()
    }
"#;

const PIN_NEW_UNCHECKED_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::pin::Pin;

    pub unsafe fn probe_pin_new_unchecked<'a>(
        value: &'a mut [u32; 2],
    ) -> Pin<&'a mut [u32; 2]> {
        unsafe { Pin::new_unchecked(value) }
    }
"#;

fn assert_no_unhandled_calls(source: &str, fn_name: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "{fn_name} should not leave array-iterator identity calls unhandled"
        );
    });
}

fn with_dispatch_calls(
    source: &str,
    fn_name: &str,
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>) + Send,
) {
    with_test_ay_ctx_for_source(source, move |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &mir_body, fn_name, ChcConfig::default());
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
                callee_path: None,
            };

            body(&mut chc_ctx, &dcx);
        }
    });
}

#[test]
fn test_array_into_iter_next_has_no_unhandled_calls() {
    assert_no_unhandled_calls(ARRAY_INTO_ITER_NEXT_SOURCE, "probe_array_into_iter_next");
}

#[test]
fn test_manually_drop_deref_identity_dispatch_avoids_fallback() {
    let mut found = 0usize;
    with_dispatch_calls(
        MANUALLY_DROP_DEREF_SOURCE,
        "probe_manually_drop_deref_mut",
        |chc_ctx, dcx| {
            if !chc_ctx.detect_manually_drop_deref_call(dcx.func) {
                return;
            }

            let before_fallback = chc_ctx.sound_fallback_count();
            let before_unhandled = chc_ctx.diagnostics.unhandled_call.get();
            let before_rules = chc_ctx.vc.rules.len();

            assert!(
                chc_ctx.codegen_call_terminator(dcx),
                "ManuallyDrop::deref_mut/deref should be handled by call dispatch"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before_fallback,
                "ManuallyDrop::deref_mut/deref should not record a sound fallback"
            );
            assert_eq!(
                chc_ctx.diagnostics.unhandled_call.get(),
                before_unhandled,
                "ManuallyDrop::deref_mut/deref should not increment unhandled_call"
            );
            assert!(
                chc_ctx.vc.rules.len() > before_rules,
                "ManuallyDrop::deref_mut/deref should emit at least one transition rule"
            );
            found += 1;
        },
    );

    assert!(found > 0, "expected at least one ManuallyDrop::deref_mut/deref call in MIR");
}

#[test]
fn test_pin_as_mut_identity_dispatch_avoids_fallback() {
    let mut found = 0usize;
    with_dispatch_calls(PIN_AS_MUT_SOURCE, "probe_pin_as_mut", |chc_ctx, dcx| {
        if !chc_ctx.detect_pin_as_mut_call(dcx.func) {
            return;
        }

        let before_fallback = chc_ctx.sound_fallback_count();
        let before_unhandled = chc_ctx.diagnostics.unhandled_call.get();
        let before_rules = chc_ctx.vc.rules.len();

        assert!(
            chc_ctx.codegen_call_terminator(dcx),
            "Pin::as_mut should be handled by call dispatch"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "Pin::as_mut should not record a sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.unhandled_call.get(),
            before_unhandled,
            "Pin::as_mut should not increment unhandled_call"
        );
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "Pin::as_mut should emit at least one transition rule"
        );
        found += 1;
    });

    assert!(found > 0, "expected at least one Pin::as_mut call in MIR");
}

#[test]
fn test_pin_new_unchecked_identity_dispatch_avoids_fallback() {
    let mut found = 0usize;
    with_dispatch_calls(PIN_NEW_UNCHECKED_SOURCE, "probe_pin_new_unchecked", |chc_ctx, dcx| {
        if !chc_ctx.detect_pin_new_unchecked_call(dcx.func) {
            return;
        }

        let before_fallback = chc_ctx.sound_fallback_count();
        let before_unhandled = chc_ctx.diagnostics.unhandled_call.get();
        let before_rules = chc_ctx.vc.rules.len();

        assert!(
            chc_ctx.codegen_call_terminator(dcx),
            "Pin::new_unchecked should be handled by call dispatch"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "Pin::new_unchecked should not record a sound fallback"
        );
        assert_eq!(
            chc_ctx.diagnostics.unhandled_call.get(),
            before_unhandled,
            "Pin::new_unchecked should not increment unhandled_call"
        );
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "Pin::new_unchecked should emit at least one transition rule"
        );
        found += 1;
    });

    assert!(found > 0, "expected at least one Pin::new_unchecked call in MIR");
}

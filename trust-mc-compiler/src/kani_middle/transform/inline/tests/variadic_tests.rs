// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for the C-variadic call specialization (`inline::variadic`).

use super::{FunctionInlinePass, InlineConfig, find_instance_by_suffix, with_test_tcx_for_source};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{AssertMessage, Body, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

/// A Rust-defined `extern "C" fn(u64, ...)` whose body fetches in a loop.
const VA_FETCH_LOOP: &str = r#"
#![feature(c_variadic)]
#![allow(dead_code)]

pub unsafe extern "C" fn va_sum(num: u64, mut args: ...) -> u64 {
    let mut accum: u64 = 0;
    let mut i: u64 = 0;
    while i < num {
        accum = accum.wrapping_add(unsafe { args.arg::<u64>() });
        i += 1;
    }
    accum
}

pub fn calls_va_sum() -> u64 {
    unsafe { va_sum(2, 5u64, 7u64) }
}
"#;

/// A variadic callee that never fetches: nothing to specialize, no bound.
const VA_NO_FETCH: &str = r#"
#![feature(c_variadic)]
#![allow(dead_code)]

pub unsafe extern "C" fn va_noop(_num: u64, _args: ...) {}

pub fn calls_va_noop() {
    unsafe { va_noop(0, 1u64, 2u64) }
}
"#;

/// The fetch asks for a type WIDER than the actual that was passed: reading
/// eight bytes where four were passed is UB whose value no sound model can
/// supply, so the specialization must decline instead of inventing a coercion.
const VA_WIDENING_FETCH: &str = r#"
#![feature(c_variadic)]
#![allow(dead_code)]

pub unsafe extern "C" fn va_widen(mut args: ...) -> u64 {
    unsafe { args.arg::<u64>() }
}

pub fn calls_va_widen() -> u64 {
    unsafe { va_widen(7u32) }
}
"#;

fn run_inline(tcx: rustc_middle::ty::TyCtxt<'_>, suffix: &str) -> (FunctionInlinePass, Body) {
    let instance = find_instance_by_suffix(tcx, suffix);
    let body = instance.body().expect("caller body");
    let mut pass = FunctionInlinePass::new(InlineConfig { max_depth: 4, enabled: true });
    let (_changed, out) =
        pass.transform_with_body_provider(tcx, body, instance, |callee: Instance| callee.body());
    (pass, out)
}

fn has_va_arg_call(body: &Body) -> bool {
    body.blocks.iter().any(|block| {
        let TerminatorKind::Call { func, .. } = &block.terminator.kind else { return false };
        let Ok(ty) = func.ty(body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = ty.kind() else { return false };
        let name = fn_def.0.name();
        name.ends_with("::va_arg") || (name.contains("VaList") && name.ends_with("::arg"))
    })
}

fn bounds_check_assert_count(body: &Body) -> usize {
    body.blocks
        .iter()
        .filter(|block| {
            matches!(
                &block.terminator.kind,
                TerminatorKind::Assert { msg: AssertMessage::BoundsCheck { .. }, .. }
            )
        })
        .count()
}

fn has_switch_int(body: &Body) -> bool {
    body.blocks.iter().any(|b| matches!(b.terminator.kind, TerminatorKind::SwitchInt { .. }))
}

#[test]
fn variadic_fetch_becomes_a_cursor_switch_with_a_ub_obligation() {
    with_test_tcx_for_source(VA_FETCH_LOOP, |tcx| {
        let (pass, body) = run_inline(tcx, "calls_va_sum");

        // The actual argument list came from the CALLER's MIR, so the callee no
        // longer needs a `VaListImpl` at all.
        assert!(!has_va_arg_call(&body), "va_arg fetch survived specialization");
        assert!(has_switch_int(&body), "no cursor switch was emitted for the fetch");

        // `va_arg` past the end of the actual list is UB: it must be CHECKED.
        assert!(
            bounds_check_assert_count(&body) >= 1,
            "specialized fetch carries no `cursor < N` obligation"
        );

        // Two actuals were passed, so no non-failing run fetches more than twice.
        assert_eq!(pass.variadic_actual_bound(), Some(2));
    });
}

#[test]
fn variadic_callee_without_a_fetch_reports_no_unwind_bound() {
    with_test_tcx_for_source(VA_NO_FETCH, |tcx| {
        let (pass, body) = run_inline(tcx, "calls_va_noop");
        assert!(!has_va_arg_call(&body));
        assert_eq!(pass.variadic_actual_bound(), None);
        assert_eq!(bounds_check_assert_count(&body), 0);
    });
}

#[test]
fn fetch_wider_than_the_actual_declines_instead_of_coercing() {
    with_test_tcx_for_source(VA_WIDENING_FETCH, |tcx| {
        let (pass, _body) = run_inline(tcx, "calls_va_widen");
        // Declining leaves the ordinary paths in charge: no bound is reported,
        // and no fabricated value is produced for the mismatched fetch.
        assert_eq!(pass.variadic_actual_bound(), None);
    });
}

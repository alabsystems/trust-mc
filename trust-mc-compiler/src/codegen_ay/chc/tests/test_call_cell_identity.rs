// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cell::new value-identity and Rc auto-trait-strip regression probes.
//! Part of #3681: unsized Rc dyn-trait cast recovery.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call_dispatch_misc::CallDispatchMisc;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::decl::Decl;

fn mir_to_chc_default(tcx: TyCtxt<'_>, body: &rustc_public::mir::Body, fn_name: &str) -> ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

const CELL_NEW_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_new(val: usize) -> Cell<usize> {
        Cell::new(val)
    }
"#;

/// Regression guard (#3681): `Cell::new` must be handled by misc dispatch
/// as a value-identity operation (dest = arg0), not left unhandled.
/// Cell<T> is already T at the sort level; this tests the call-dispatch bridge.
#[test]
fn test_cell_new_handled_by_misc_dispatch() {
    with_test_ay_ctx_for_source(CELL_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_new");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cell_new", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !callee_path.contains("Cell") || !callee_path.ends_with("::new") {
                continue;
            }
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

            let before = chc_ctx.sound_fallback_count();
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

            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "Cell::new should be handled by misc dispatch: {callee_path}"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before,
                "Cell::new should not record a sound fallback"
            );
            found += 1;
        }
        assert!(found > 0, "expected at least one Cell::new call in probe_cell_new MIR");
    });
}

const CELLAR_NEW_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod cell {
        pub struct Cellar(pub usize);

        impl Cellar {
            #[inline(never)]
            pub fn new(value: usize) -> Self { Self(value) }
        }
    }

    pub fn probe_cellar_new(value: usize) -> cell::Cellar {
        cell::Cellar::new(value)
    }
"#;

/// A user type whose path merely starts with `cell::Cell` must never receive
/// the canonical standard-library `Cell::new` identity semantics.
#[test]
fn test_cell_new_detector_rejects_cellar_prefix_collision() {
    with_test_ay_ctx_for_source(CELLAR_NEW_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cellar_new");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cellar_new", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path.ends_with("Cellar::new") {
                found = true;
                assert!(
                    !chc_ctx.detect_cell_new_call(func),
                    "user-defined {path} must not be intercepted as standard Cell::new"
                );
            }
        }
        assert!(found, "expected a Cellar::new call in probe MIR");
    });
}

const UNSAFE_CELLAR_GET_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct MyUnsafeCell(usize);

    impl MyUnsafeCell {
        #[inline(never)]
        pub fn get(&self) -> usize { self.0 }
    }

    pub fn probe_unsafe_cellar_get(cell: &MyUnsafeCell) -> usize {
        cell.get()
    }
"#;

/// A user method whose owner name contains `UnsafeCell` must not receive the
/// canonical core pointer-identity semantics.
#[test]
fn test_unsafe_cell_get_detector_rejects_name_collision() {
    with_test_ay_ctx_for_source(UNSAFE_CELLAR_GET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unsafe_cellar_get");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unsafe_cellar_get", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path.ends_with("MyUnsafeCell::get") {
                found = true;
                assert!(
                    !chc_ctx.detect_unsafe_cell_get_call(func),
                    "user-defined {path} must not be intercepted as standard UnsafeCell::get"
                );
            }
        }
        assert!(found, "expected a MyUnsafeCell::get call in probe MIR");
    });
}

const CELL_ACCESSOR_QUARANTINE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_accessor_quarantine(
        cell: &Cell<u32>,
        other: &Cell<u32>,
        value: u32,
    ) -> u32 {
        cell.set(value);
        let replaced = cell.replace(value.wrapping_add(1));
        let taken = cell.take();
        cell.swap(other);
        cell.get().wrapping_add(replaced).wrapping_add(taken)
    }
"#;

/// Every canonical Cell accessor call must be TAKEN by misc dispatch — either
/// modeled precisely by the certified semantic lane (codegen_call_cell.rs) or
/// routed to the publication-blocking quarantine fallback — never left to the
/// known false-Safe deep-inline lane. Operations the semantic lane does not
/// model (`swap` here) must always record the fail-closed fallback.
#[test]
fn test_cell_accessors_are_fail_closed_at_dispatch() {
    with_test_ay_ctx_for_source(CELL_ACCESSOR_QUARANTINE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_accessor_quarantine");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_cell_accessor_quarantine", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut quarantined = 0usize;
        let mut callee_paths = Vec::new();
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            callee_paths.push(path.clone());
            if !(path.starts_with("core::cell::Cell") || path.starts_with("std::cell::Cell"))
                || path.ends_with("::new")
            {
                continue;
            }
            let Some(target_bb) = *target else { continue };
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
                callee_path: Some(path.clone()),
            };

            let before = chc_ctx.sound_fallback_count();
            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "{path} must be taken by dispatch (semantic lane or quarantine)"
            );
            if path.ends_with("::swap") {
                assert!(
                    chc_ctx.sound_fallback_count() > before,
                    "unmodeled {path} must record a fail-closed fallback"
                );
            }
            quarantined += 1;
        }
        assert_eq!(
            quarantined, 5,
            "expected all five dispatched Cell operations; calls={callee_paths:?}"
        );
    });
}

const RC_AUTO_TRAIT_STRIP_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub trait Byte {
        fn eq(&self, byte: u8) -> bool;
    }

    impl Byte for u8 {
        fn eq(&self, byte: u8) -> bool {
            *self == byte
        }
    }

    pub fn all_zero_rc(num: Rc<dyn Byte>) -> bool {
        num.eq(0x0)
    }

    pub fn probe_rc_auto_trait_strip(num: u8) -> bool {
        let rc: Rc<dyn Byte + Sync> = Rc::new(num);
        all_zero_rc(rc)
    }
"#;

/// Regression guard (#3681): the auto-trait-strip coercion
/// `Rc<dyn Byte + Sync> -> Rc<dyn Byte>` must not generate inferable summaries
/// for Rc wrapper calls. This mirrors the exact harness pattern in
/// `tests/trust_mc/DynTrait/unsized_rc_cast.rs`.
#[test]
fn test_rc_auto_trait_strip_avoids_inferable_summaries() {
    with_test_ay_ctx_for_source(RC_AUTO_TRAIT_STRIP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_auto_trait_strip");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_rc_auto_trait_strip");

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fun { name, .. }
                    if name.starts_with("P_inf_")
                        && (name.contains("from_inner_in")
                            || (name.contains("Deref>") && name.ends_with("::deref"))) =>
                {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();

        assert!(
            inferable_decls.is_empty(),
            "Rc auto-trait-strip coercion should bypass inferable summaries, \
             found: {inferable_decls:?}"
        );
    });
}

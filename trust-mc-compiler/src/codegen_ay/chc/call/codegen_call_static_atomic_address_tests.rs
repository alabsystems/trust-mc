// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_public::mir::{Place, ProjectionElem, TerminatorKind};
use std::collections::HashSet;
use trust_mc_core::chc::RelationApp;

#[test]
fn static_atomic_as_ptr_rejects_projected_destination_without_rebinding_root() {
    const SOURCE: &str = r#"
        use std::sync::atomic::AtomicU32;
        static CELLS: [AtomicU32; 2] = [AtomicU32::new(11), AtomicU32::new(23)];
        pub fn address(_output: &mut *mut u32) -> *mut u32 { CELLS[1].as_ptr() }
    "#;
    let mut exercised = false;
    with_test_ay_ctx_for_source(SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx.tcx, "address");
        let body = instance.body().unwrap();
        for projected in [false, true] {
            let accounting =
                crate::codegen_ay::unstubbed_accounting::AccountingScope::begin(Some(instance));
            let mut ctx = ChcCtx::new(
                tcx.tcx,
                &body,
                "address",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            ctx.declare_block_relations();
            let (bb_idx, func, args, destination, target) = body
                .blocks
                .iter()
                .enumerate()
                .find_map(|(bb, block)| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, destination, target, .. }
                        if ctx
                            .resolve_callee_path(func)
                            .is_some_and(|p| p.ends_with("::as_ptr")) =>
                    {
                        Some((bb, func, args, destination, target))
                    }
                    _ => None,
                })
                .expect("actual Atomic::as_ptr call in raw MIR");
            assert!(destination.projection.is_empty());
            ctx.current_instance = Some(instance);
            let TyKind::RigidTy(RigidTy::FnDef(def, generic_args)) =
                func.ty(body.locals()).unwrap().kind()
            else {
                panic!("direct call");
            };
            let callee = rustc_public::mir::mono::Instance::resolve(def, &generic_args).unwrap();
            crate::codegen_ay::unstubbed_accounting::begin_inventory();
            crate::codegen_ay::unstubbed_accounting::record_reachable_body(instance, &body);
            crate::codegen_ay::unstubbed_accounting::record_pending(
                "as_ptr",
                callee,
                Some(crate::kani_middle::reachability::AbstractionCallsite {
                    caller: instance,
                    body: &body,
                    block: bb_idx,
                }),
                true,
            );
            crate::codegen_ay::unstubbed_accounting::finish_inventory();
            let custody =
                crate::codegen_ay::unstubbed_accounting::before_root_inline(instance, &body);
            crate::codegen_ay::unstubbed_accounting::after_root_inline(custody, &body);
            let attempt = crate::codegen_ay::unstubbed_accounting::EncodingAttempt::begin(
                Some(instance),
                &body,
            );
            // A legal return place for the same pointer value. Its root
            // is also pointer-width, so the old sort check admitted it.
            let indirect = Place { local: 1, projection: vec![ProjectionElem::Deref] };
            assert_eq!(indirect.ty(body.locals()).unwrap(), destination.ty(body.locals()).unwrap());
            let destination = if projected { &indirect } else { destination };
            let (_, root) = ctx.resolve_destination(destination.local).unwrap();
            assert_eq!(root.sort(), &crate::codegen_ay::types::ptr_sort());
            let from = RelationApp::new(
                ctx.block_relations.get(&bb_idx).unwrap().clone(),
                ctx.state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                    .collect(),
            );
            let modified = HashSet::new();
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target,
                from_app: &from,
                stmt_constraints: &[],
                modified_locals: &modified,
                callee_path: None,
            };
            let before = ctx.vc.rules.len();
            assert_eq!(try_static_atomic_as_ptr(&mut ctx, &dcx), !projected);
            attempt.finish();
            assert_eq!(
                crate::codegen_ay::unstubbed_accounting::unresolved_for_test(),
                usize::from(projected)
            );
            if !projected {
                // The same callee reached without complete callsite custody
                // prevents the already-exact sibling from clearing either event.
                crate::codegen_ay::unstubbed_accounting::record_pending(
                    "as_ptr", callee, None, true,
                );
                assert_eq!(crate::codegen_ay::unstubbed_accounting::unresolved_for_test(), 2);
            }
            accounting.finish();
            assert_eq!(
                ctx.vc.rules.len(),
                before + usize::from(!projected),
                "an indirect return must not emit an equality for its pointer root"
            );
        }
        exercised = true;
    });
    assert!(exercised, "the compiler-backed destination checks must execute");
}

#[test]
fn static_atomic_as_ptr_rejects_a_core_named_user_crate() {
    const SOURCE: &str = r#"
        pub mod sync { pub mod atomic {
            pub fn as_ptr(_: &std::sync::atomic::AtomicU32) -> *mut u32 {
                std::ptr::null_mut()
            }
        }}
        static CELLS: [std::sync::atomic::AtomicU32; 2] = [
            std::sync::atomic::AtomicU32::new(11),
            std::sync::atomic::AtomicU32::new(23),
        ];
        pub fn spoof() -> *mut u32 { sync::atomic::as_ptr(&CELLS[1]) }
    "#;
    let mut exercised = false;
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        SOURCE,
        &["--crate-name=core"],
        |tcx| {
            let body = find_instance_by_suffix(tcx.tcx, "spoof").body().unwrap();
            let mut ctx = ChcCtx::new(
                tcx.tcx,
                &body,
                "spoof",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            ctx.declare_block_relations();
            let (bb_idx, func, args, destination, target) = body
                .blocks
                .iter()
                .enumerate()
                .find_map(|(bb, block)| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, destination, target, .. }
                        if ctx
                            .resolve_callee_path(func)
                            .is_some_and(|p| p.ends_with("::as_ptr")) =>
                    {
                        Some((bb, func, args, destination, target))
                    }
                    _ => None,
                })
                .expect("the spoofed call must survive in the raw MIR");
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).unwrap().kind()
            else {
                panic!("direct spoofed function")
            };
            assert_eq!(def.krate().name.as_str(), "core");
            assert!(def.name().contains("sync::atomic"));
            assert!(ctx.static_array_address_origins(&args[0]).is_some());
            let from = RelationApp::new(
                ctx.block_relations.get(&bb_idx).unwrap().clone(),
                ctx.state_var_mgr
                    .state_vars
                    .iter()
                    .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                    .collect(),
            );
            let modified = HashSet::new();
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target,
                from_app: &from,
                stmt_constraints: &[],
                modified_locals: &modified,
                callee_path: None,
            };
            let before = ctx.vc.rules.len();
            assert!(!try_static_atomic_as_ptr(&mut ctx, &dcx));
            assert_eq!(ctx.vc.rules.len(), before, "a spoof cannot return the real static address");
            exercised = true;
        },
    );
    assert!(exercised, "the compiler-backed fake-core check must execute");
}

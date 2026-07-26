// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for raw pointer `as_ref`/`as_mut` Option construction.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_dispatch_option_ptr::CallDispatchOptionPtr;
use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::types::RefTarget;

/// Raw pointer `as_ref` is an Option wrapper, not a pointer identity cast.
///
/// Regression guard for FatPointers/dyn-pointer paths: null must map to None,
/// non-null must map to Some(ptr), and pointer metadata must keep flowing to
/// later unwrap/deref code without an unconstrained fallback.
#[test]
fn test_raw_ptr_as_ref_wraps_option_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_raw_ptr_as_ref(p: *const u8) -> Option<&'static u8> {
            unsafe { p.as_ref() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_as_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_ptr_as_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut seen_paths = Vec::new();
        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                let path = chc_ctx
                    .resolve_callee_path(func)
                    .or_else(|| chc_ctx.resolve_fn_def_name(func))
                    .unwrap_or_else(|| "<unresolved>".to_string());
                seen_paths.push(path.clone());
                if path.ends_with("::as_ref")
                    && (path.contains("ptr::const_ptr") || path.contains("*const"))
                {
                    call_site =
                        Some((bb_idx, func, args.clone(), destination.clone(), *target, path));
                    break;
                }
            }
        }

        let (bb_idx, func, args, destination, target, path) = call_site.unwrap_or_else(|| {
            panic!("expected raw pointer as_ref call in MIR, saw paths: {seen_paths:?}")
        });
        let src_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected direct raw pointer source local, got {other:?}"),
        };
        chc_ctx.known_alloc_ids.insert(src_local, 0x1234_u32);
        chc_ctx
            .ref_resolution
            .ref_targets
            .insert(src_local, RefTarget::with_projections(src_local, vec![]));

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let target_opt = Some(target);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args: &args,
            destination: &destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: Some(path),
        };

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.sound_fallback_count();
        assert!(
            chc_ctx.try_dispatch_call_option_pointer(&dcx),
            "raw pointer as_ref should be handled by the Option/pointer dispatch pre-route"
        );

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "raw pointer as_ref should avoid sound fallback"
        );
        assert_eq!(
            chc_ctx.known_alloc_ids.get(&destination.local),
            Some(&0x1234_u32),
            "raw pointer as_ref should propagate allocation identity to the Option result"
        );
        let dest_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&destination.local)
            .expect("raw pointer as_ref should propagate ref_target metadata");
        assert_eq!(
            dest_target.local, src_local,
            "raw pointer as_ref should preserve source referent metadata"
        );

        let rendered_constraints = chc_ctx
            .vc
            .rules
            .last()
            .expect("raw pointer as_ref transition rule")
            .body
            .constraints
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("ite"),
            "raw pointer as_ref should encode null-sensitive Option construction:\n{rendered_constraints}"
        );
    });
}

#[test]
fn test_raw_dyn_ptr_as_ref_wraps_option_with_vtable_payload() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub trait Subscriber {
            fn process(&self) -> u32;
        }

        pub unsafe fn probe_raw_dyn_ptr_as_ref<'a>(
            p: *const dyn Subscriber,
        ) -> Option<&'a dyn Subscriber> {
            unsafe { p.as_ref() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_dyn_ptr_as_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_raw_dyn_ptr_as_ref", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut seen_paths = Vec::new();
        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            {
                let path = chc_ctx
                    .resolve_callee_path(func)
                    .or_else(|| chc_ctx.resolve_fn_def_name(func))
                    .unwrap_or_else(|| "<unresolved>".to_string());
                seen_paths.push(path.clone());
                if path.ends_with("::as_ref")
                    && (path.contains("ptr::const_ptr") || path.contains("*const"))
                {
                    call_site =
                        Some((bb_idx, func, args.clone(), destination.clone(), *target, path));
                    break;
                }
            }
        }

        let (bb_idx, func, args, destination, target, path) = call_site.unwrap_or_else(|| {
            panic!("expected raw dyn pointer as_ref call in MIR, saw paths: {seen_paths:?}")
        });
        let src_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected direct raw dyn pointer source local, got {other:?}"),
        };
        let expected_vtable = Expr::bitvec_const(7u128, crate::codegen_ay::types::POINTER_WIDTH);
        chc_ctx.dyn_vtable_ids.insert(src_local, expected_vtable.clone());

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let target_opt = Some(target);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args: &args,
            destination: &destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: Some(path),
        };

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.sound_fallback_count();
        assert!(
            chc_ctx.try_dispatch_call_option_pointer(&dcx),
            "raw dyn pointer as_ref should be handled by the Option/pointer dispatch pre-route"
        );

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "raw dyn pointer as_ref should avoid sound fallback"
        );
        let stored_vtable = chc_ctx
            .dyn_vtable_ids
            .get(&destination.local)
            .expect("raw dyn pointer as_ref should capture vtable metadata on the Option result");
        assert_eq!(stored_vtable.to_string(), expected_vtable.to_string());

        let rendered_constraints = chc_ctx
            .vc
            .rules
            .last()
            .expect("raw dyn pointer as_ref transition rule")
            .body
            .constraints
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("ite"),
            "raw dyn pointer as_ref should encode null-sensitive Option construction:\n{rendered_constraints}"
        );
        assert!(
            rendered_constraints.contains(&expected_vtable.to_string()),
            "raw dyn pointer as_ref should encode the known vtable in the Option payload:\n{rendered_constraints}"
        );
        assert!(
            rendered_constraints.contains("__vtable_sv_"),
            "raw dyn pointer as_ref should emit a side-state vtable constraint:\n{rendered_constraints}"
        );
    });
}

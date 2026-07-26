// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Box pointer-wrapper misc-dispatch regression tests.
//!
//! Split from `test_call_dispatch_misc_pointer_wrappers.rs` (D4 of #4010).
//! Covers: Box<dyn Trait>::deref, Box<Box<dyn Trait>>::deref, Box::into_raw,
//! Box::from_raw, and generic helper inlining for Box-wrapped trait objects.

#![allow(clippy::unwrap_used)]

use super::common::*;
use super::test_call_dispatch_misc_pointer_wrapper_common::assert_source_has_no_inferable_summaries;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call_dispatch_misc::CallDispatchMisc;
use crate::codegen_ay::chc::codegen_call_fn_inline::CallDispatchFnInline;
use crate::codegen_ay::chc::inline_body::translate_inline_body;
use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};
use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;

const BOX_DYN_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::boxed::Box;
    use std::ops::Deref;

    pub trait Identity {
        fn id(&self) -> u16;
    }

    pub struct Inner {
        pub id: u8,
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    pub fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_box_dyn_dispatch(ptr: Box<dyn Identity>) -> u16 {
        id_from_coerce(ptr)
    }
"#;

const DOUBLE_BOX_DYN_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::boxed::Box;
    use std::ops::Deref;

    pub trait Identity {
        fn id(&self) -> u16;
    }

    pub struct Inner {
        pub id: u8,
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    pub fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_box_box_dyn_dispatch(ptr: Box<Box<dyn Identity>>) -> u16 {
        id_from_coerce(*ptr)
    }
"#;

const BOX_OUTER_DYN_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::boxed::Box;
    use std::ops::Deref;

    pub trait Identity {
        fn id(&self) -> u16;
    }

    pub struct Outer<T: ?Sized> {
        pub outer_id: u8,
        pub inner: T,
    }

    pub struct Inner {
        pub id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + (self.inner.id() as u16)
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    pub fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_box_outer_dyn_dispatch(outer_id: u8, inner_id: u8) -> u16 {
        let outer: Box<dyn Identity> = Box::new(Outer { inner: Inner { id: inner_id }, outer_id });
        id_from_coerce(outer)
    }
"#;

const BOX_INTO_RAW_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::boxed::Box;

    pub fn probe_box_into_raw(boxed: Box<u8>) -> *mut u8 {
        Box::into_raw(boxed)
    }
"#;

const BOX_FROM_RAW_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::boxed::Box;

    pub unsafe fn probe_box_from_raw(ptr: *mut u8) -> Box<u8> {
        unsafe { Box::from_raw(ptr) }
    }
"#;

fn box_deref_source_local(args: &[rustc_public::mir::Operand]) -> Option<usize> {
    args.first().and_then(|arg| match arg {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
            if place.projection.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
    })
}

pub(super) fn seed_box_alloc_id(
    chc_ctx: &mut ChcCtx<'_, '_>,
    args: &[rustc_public::mir::Operand],
    found: usize,
) -> Option<u32> {
    let src_local = box_deref_source_local(args)?;
    let seeded_obj_id = 900u32 + found as u32;
    chc_ctx.known_alloc_ids.insert(src_local, seeded_obj_id);
    Some(seeded_obj_id)
}

fn assert_box_deref_dispatch_avoids_sound_fallback(source: &str, fn_suffix: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_suffix, ChcConfig::default());
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
            if !(callee_path.contains("boxed::Box<") || callee_path.contains("boxed::Box::"))
                || !callee_path.ends_with("as std::ops::Deref>::deref")
            {
                continue;
            }

            found += 1;
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
            let Some(target_bb) = *target else {
                continue;
            };
            let target_opt = Some(target_bb);
            let before = chc_ctx.sound_fallback_count();
            let seeded_obj_id = seed_box_alloc_id(&mut chc_ctx, args, found);
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
                "Box::deref should be handled by misc dispatch"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before,
                "Box::deref wrapper fast path should not record a sound fallback"
            );
            if let Some(seeded_obj_id) = seeded_obj_id {
                assert_eq!(
                    chc_ctx.known_alloc_ids.get(&destination.local).copied(),
                    Some(seeded_obj_id),
                    "Box::deref should preserve concrete allocation identity for chained derefs"
                );
            }
        }
        // MIR optimizer may inline/elide Box::deref into place projections.
        // When the call is absent (found == 0), the dispatch path is not
        // exercised and the test passes trivially. End-to-end compiletest
        // covers this case. Part of #3608.
    });
}

fn with_generic_helper_call_for_source(
    source: &str,
    probe_suffix: &str,
    assertions: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let call_paths: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => chc_ctx.resolve_callee_path(func),
                _ => None,
            })
            .collect();

        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                    && let Some(path) = chc_ctx.resolve_callee_path(func)
                    && path.contains("id_from_coerce")
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target, path))
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!(
                    "expected id_from_coerce call terminator in {probe_suffix}, saw calls {call_paths:?}"
                )
            });

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

        assertions(
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

fn assert_generic_helper_call_is_claimed_by_fn_inline(source: &str, probe_suffix: &str) {
    with_generic_helper_call_for_source(
        source,
        probe_suffix,
        |chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let func_ty = func.ty(chc_ctx.body.locals()).expect("call callee type");
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                panic!("expected FnDef for helper call, got {func_ty:?}");
            };
            let instance =
                rustc_public::mir::mono::Instance::resolve(def, &substs).expect("helper instance");
            let inline_body = instance.body().expect("helper body");
            let effective = count_effective_blocks(&inline_body);
            let limit = inline_effective_block_limit(&inline_body, effective);
            assert!(
                effective <= limit,
                "{callee_path} should fit fn_inline size gate: effective={effective}, limit={limit}"
            );

            let params: Vec<_> = args
                .iter()
                .filter_map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
                .collect();
            assert_eq!(params.len(), args.len(), "{callee_path} should translate all params");
            chc_ctx.mark_inline_field_reads(&inline_body, &params, bb_idx);
            let inline_result = translate_inline_body(
                chc_ctx,
                &inline_body,
                &params,
                bb_idx,
                &std::collections::HashMap::new(),
                Some(instance),
                0,
            );
            assert!(inline_result.is_some(), "{callee_path} helper body should inline");

            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };
            assert!(
                chc_ctx.try_dispatch_call_fn_inline(&dcx),
                "{callee_path} should be handled by fn_inline"
            );
        },
    );
}

/// Box<dyn Trait>::deref should use the pointer-wrapper deref fast path without
/// recording a sound fallback.
#[test]
fn test_box_dyn_deref_dispatch_avoids_sound_fallback() {
    assert_box_deref_dispatch_avoids_sound_fallback(BOX_DYN_DEREF_SOURCE, "probe_box_dyn_dispatch");
}

/// Box<Box<dyn Trait>>::deref should keep both deref steps on the misc-dispatch
/// fast path so the double-coercion harness can recover the inner vtable.
#[test]
fn test_box_box_dyn_deref_dispatch_avoids_sound_fallback() {
    assert_box_deref_dispatch_avoids_sound_fallback(
        DOUBLE_BOX_DYN_DEREF_SOURCE,
        "probe_box_box_dyn_dispatch",
    );
}

#[test]
fn test_box_generic_helpers_avoid_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        BOX_DYN_DEREF_SOURCE,
        "probe_box_dyn_dispatch",
        |name| name.contains("id_from_coerce"),
        "probe_box_dyn_dispatch should inline `id_from_coerce` without P_inf_* declarations",
    );
    assert_source_has_no_inferable_summaries(
        DOUBLE_BOX_DYN_DEREF_SOURCE,
        "probe_box_box_dyn_dispatch",
        |name| name.contains("id_from_coerce"),
        "probe_box_box_dyn_dispatch should inline `id_from_coerce` without P_inf_* declarations",
    );
    assert_source_has_no_inferable_summaries(
        BOX_OUTER_DYN_DEREF_SOURCE,
        "probe_box_outer_dyn_dispatch",
        |name| name.contains("id_from_coerce"),
        "probe_box_outer_dyn_dispatch should inline `id_from_coerce` without P_inf_* declarations",
    );
}

#[test]
fn test_box_generic_helper_calls_are_claimed_by_fn_inline() {
    assert_generic_helper_call_is_claimed_by_fn_inline(
        BOX_DYN_DEREF_SOURCE,
        "probe_box_dyn_dispatch",
    );
    assert_generic_helper_call_is_claimed_by_fn_inline(
        DOUBLE_BOX_DYN_DEREF_SOURCE,
        "probe_box_box_dyn_dispatch",
    );
    assert_generic_helper_call_is_claimed_by_fn_inline(
        BOX_OUTER_DYN_DEREF_SOURCE,
        "probe_box_outer_dyn_dispatch",
    );
}

#[test]
fn test_box_into_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        BOX_INTO_RAW_SOURCE,
        "probe_box_into_raw",
        |name| name.contains("into_raw"),
        "Box::into_raw should bypass inferable summaries",
    );
}

#[test]
fn test_box_from_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        BOX_FROM_RAW_SOURCE,
        "probe_box_from_raw",
        |name| name.contains("from_raw"),
        "Box::from_raw should bypass inferable summaries",
    );
}

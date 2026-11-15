// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real preprocessing and ownership checks for native Box release.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::mir::{Body, TerminatorKind, mono::Instance};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    #[inline(never)]
    fn heap_pointer() -> *mut u32 {
        let owner = Box::new(17u32);
        Box::into_raw(owner)
    }
    pub fn holder_exit_safe() { assert!(unsafe { *heap_pointer() } == 17); }
    pub fn holder_exit_bug() { assert!(unsafe { *heap_pointer() } == 18); }
    pub fn moved_safe() {
        let owner = Box::new(17u32);
        let moved = owner;
        let pointer = Box::into_raw(moved);
        assert!(unsafe { *pointer } == 17);
    }
    pub fn distinct_safe() {
        let first = Box::into_raw(Box::new(3u32));
        let second = Box::into_raw(Box::new(17u32));
        assert!(first != second);
        assert!(unsafe { *first } == 3 && unsafe { *second } == 17);
    }
    pub fn distinct_bug() {
        let first = Box::into_raw(Box::new(3u32));
        let second = Box::into_raw(Box::new(17u32));
        assert!(first == second);
    }
    pub fn unknown_owner(owner: Box<u32>) -> *mut u32 { Box::into_raw(owner) }
    pub unsafe fn forged_owner(pointer: *mut u32) -> *mut u32 {
        Box::into_raw(unsafe { Box::from_raw(pointer) })
    }
    pub fn joined_owner(branch: bool) -> *mut u32 {
        let owner = if branch { Box::new(17u32) } else { Box::new(19u32) };
        Box::into_raw(owner)
    }
    #[inline(never)]
    fn replace(owner: &mut Box<u32>) { *owner = Box::new(19u32); }
    pub fn mutated_owner() -> *mut u32 {
        let mut owner = Box::new(17u32);
        replace(&mut owner);
        Box::into_raw(owner)
    }
    pub fn cyclic_owner(count: usize) {
        for _ in 0..count {
            let pointer = Box::into_raw(Box::new(17u32));
            assert!(!pointer.is_null());
        }
    }
"#;

fn transformed(tcx: TyCtxt<'_>, name: &str) -> Body {
    let abstraction = StdAbstraction::resolve(tcx);
    let instance = find_instance_by_suffix(tcx, name);
    FunctionInlinePass::new(InlineConfig {
        max_depth: 32,
        chc_native_box_drop: true,
        ..InlineConfig::default()
    })
    .transform_with_body_provider(tcx, instance.callee_body().unwrap(), instance, |callee| {
        if abstraction.abstracts_public_instance(tcx, callee) { None } else { callee.callee_body() }
    })
    .1
}

fn has_native_release(tcx: TyCtxt<'_>, body: &Body) -> bool {
    body.blocks.iter().any(|block| {
        let TerminatorKind::Call { func, .. } = &block.terminator.kind else { return false };
        let Ok(ty) = func.ty(body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return false };
        Instance::resolve(def, &args).ok().is_some_and(|instance| {
            crate::codegen_ay::native_bmc_box_into_raw(tcx, &instance).is_some()
        })
    })
}

#[test]
fn native_box_release_preserves_real_boundary_and_heap_after_holder_exit() {
    with_native_box_ctx(SOURCE, |ctx| {
        for name in
            ["holder_exit_safe", "holder_exit_bug", "moved_safe", "distinct_safe", "distinct_bug"]
        {
            let body = transformed(ctx.tcx, name);
            assert!(has_native_release(ctx.tcx, &body), "{name}: native release was inlined");
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let actual = run_z3_on_smt2_with_timeout(&smt, 30);
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: translation debt");
            assert_eq!(actual.as_deref(), Ok(expected), "{name}: wrong heap result");
            assert!(
                smt.contains("obj_valid") && smt.contains("obj_size"),
                "missing allocation checks"
            );
        }
    });
}

#[test]
fn native_box_release_requires_unique_unexposed_acyclic_typed_birth() {
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    assert_eq!(
        fallback_soundness("native_box_into_raw_without_custody"),
        FallbackSoundness::FailClose
    );
    with_native_box_ctx(SOURCE, |ctx| {
        for name in
            ["unknown_owner", "forged_owner", "joined_owner", "mutated_owner", "cyclic_owner"]
        {
            let body = transformed(ctx.tcx, name);
            assert!(has_native_release(ctx.tcx, &body), "{name}: native release was inlined");
            let (_, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            assert!(diagnostics.place_translation_drop.get() > 0, "{name}: lost refusal");
            assert!(
                reasons.contains_key("native_box_into_raw_without_custody"),
                "{name}: {reasons:?}"
            );
        }
    });
}

#[test]
fn native_box_release_selects_memory_with_default_configuration() {
    with_native_box_ctx(SOURCE, |ctx| {
        for name in ["holder_exit_safe", "holder_exit_bug"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = transformed(ctx.tcx, name);
            let vc = crate::codegen_ay::chc::mir_to_chc_with_instance(
                ctx.tcx,
                &body,
                instance,
                name,
                ChcConfig::default(),
            );
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            assert!(
                smt.contains("obj_valid") && smt.contains("obj_size"),
                "default configuration must select the checked memory model"
            );
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            assert_eq!(run_z3_on_smt2_with_timeout(&smt, 30).as_deref(), Ok(expected));
        }
    });
}

#[test]
fn native_box_release_never_uses_native_custody_with_active_unit_stubs() {
    with_native_box_ctx(SOURCE, |ctx| {
        let name = "moved_safe";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = transformed(ctx.tcx, name);
        assert!(has_native_release(ctx.tcx, &body));
        let callees: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else { return None };
                let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                    func.ty(body.locals()).ok()?.kind()
                else {
                    return None;
                };
                let callee = Instance::resolve(def, &args).ok()?;
                crate::codegen_ay::native_bmc_box_into_raw(ctx.tcx, &callee).map(|_| callee)
            })
            .collect();
        assert!(!callees.is_empty());
        let TyKind::RigidTy(RigidTy::FnDef(marker, _)) = instance.ty().kind() else {
            panic!("fixture function definition");
        };
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(marker, marker)]),
        );
        assert!(callees.iter().all(|callee| {
            crate::codegen_ay::native_bmc_box_into_raw(ctx.tcx, callee).is_none()
                && crate::codegen_ay::shared::native_box_raw::native_box_into_raw_identity(
                    ctx.tcx, callee,
                )
                .is_some()
        }));
        let (_, _, diagnostics) =
            ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
        assert!(
            diagnostics.place_translation_drop.get() > 0,
            "active stubs must not obtain a clean native ownership certificate"
        );
    });
}

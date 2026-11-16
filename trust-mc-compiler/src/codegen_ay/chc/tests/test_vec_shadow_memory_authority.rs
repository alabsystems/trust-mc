// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Native callee-identity and opaque-effect boundary controls; no solver calls.
#![cfg(trust_toolchain)]
use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::kani_functions::KaniModel;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::mir::TerminatorKind;

const SOURCE: &str = r###"#![feature(register_tool)]
#![register_tool(kanitool)]
// UNRUN fragment: append as one block to the parent's physical Vec fixture.
// The enclosing module avoids collision with its existing local mem_init.
mod shadow_name_authority {
    pub mod mem_init {
        #[inline(never)] pub fn grow(v: &mut Vec<u64>) { v.push(4); }
        #[inline(never)] pub unsafe fn read(p: *const u64) -> u64 { unsafe { *p } }
        #[inline(never)] pub unsafe fn write(p: *mut u64, value: u64) { unsafe { *p = value; } }
    }
    pub mod ub_checks {
        #[inline(never)] pub unsafe fn inspect(p: *const u64) -> u64 { unsafe { *p } }
    }
    #[inline(never)] pub unsafe fn add(p: *const u64) -> u64 { unsafe { *p } }
    #[inline(never)] pub unsafe fn write_bytes(p: *mut u64, value: u64) { unsafe { *p = value; } }
}


pub fn shadow_name_read_after_growth_refusal() {
    let mut v = vec![3u64]; v.push(4);
    let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::mem_init::read(p) } == 3);
}

pub fn shadow_name_write_after_growth_refusal() {
    let mut v = vec![3u64]; v.push(4);
    let p = v.as_mut_ptr();
    unsafe { shadow_name_authority::mem_init::write(p, 9); }
    assert!(v[0] == 9);
}

pub fn shadow_name_write_then_model_refusal() {
    let mut v = vec![3u64]; let p = v.as_mut_ptr();
    unsafe { shadow_name_authority::mem_init::write(p, 9); }
    assert!(v[0] == 9);
}

pub fn shadow_name_write_bytes_then_model_refusal() {
    let mut v = vec![3u64]; let p = v.as_mut_ptr();
    unsafe { shadow_name_authority::write_bytes(p, 9); }
    assert!(v[0] == 9);
}

// Native-prescan-only extra controls. Do not register these as semantic proofs.
pub fn shadow_name_add_after_growth_refusal() {
    let mut v = vec![3u64]; v.push(4); let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::add(p) } == 3);
}
pub fn shadow_name_ub_after_growth_refusal() {
    let mut v = vec![3u64]; v.push(4); let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::ub_checks::inspect(p) } == 3);
}
pub fn shadow_name_preborrowed_grow_refusal() {
    let mut v = vec![3u64]; let receiver = &mut v;
    let p = receiver.as_ptr(); shadow_name_authority::mem_init::grow(receiver);
    assert!(unsafe { *p } == 3);
}

mod forged_marker {
    #[kanitool::fn_marker = "IsPtrInitializedModel"]
    #[inline(never)] pub fn inspect(_: *const u64) -> bool { true }
}
pub fn probe_core_addresses(p: *const u64) -> (usize, *const u64, bool) {
    (p.addr(), unsafe { p.add(1) }, p.is_null())
}
pub fn probe_forged_shadow_marker(p: *const u64) -> bool { forged_marker::inspect(p) }
"###;

#[test]
fn native_vec_shadow_names_do_not_hide_pointer_effects() {
    with_native_box_ctx(SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for (name, reason) in [
                ("shadow_name_read_after_growth_refusal", "vec_buffer_access_after_mutation"),
                ("shadow_name_write_after_growth_refusal", "vec_buffer_access_after_mutation"),
                ("shadow_name_write_then_model_refusal", "vec_model_read_after_buffer_write"),
                ("shadow_name_write_bytes_then_model_refusal", "vec_model_read_after_buffer_write"),
                ("shadow_name_add_after_growth_refusal", "vec_buffer_access_after_mutation"),
                ("shadow_name_ub_after_growth_refusal", "vec_buffer_access_after_mutation"),
                ("shadow_name_preborrowed_grow_refusal", "vec_buffer_access_after_mutation"),
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let (_, body) = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                })
                .transform_with_body_provider(
                    ctx.tcx,
                    instance.callee_body().unwrap(),
                    instance,
                    |callee| {
                        if abstraction.abstracts_public_instance(ctx.tcx, callee)
                            || callee.name().contains("shadow_name_authority")
                        {
                            None
                        } else {
                            callee.callee_body()
                        }
                    },
                );
                assert!(
                    body.blocks.iter().any(|block| match &block.terminator.kind {
                        TerminatorKind::Call { func, .. } => {
                            let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                            context
                                .resolve_callee_path(func)
                                .is_some_and(|path| path.contains("shadow_name_authority"))
                        }
                        _ => false,
                    }),
                    "opaque local call retained: {name} depth={depth}"
                );
                let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                let (vc, _, _) = context.translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                assert!(
                    reasons.get(reason).copied().unwrap_or(0) > 0,
                    "specific boundary required: {name} depth={depth}: {reasons:?}"
                );
                assert!(
                    !vc.approximation_identity_complete,
                    "opaque byte effect cannot gain proof/refutation authority"
                );
            }
        }
    });
}

#[test]
fn native_vec_call_permissions_use_core_and_canonical_model_identity() {
    with_native_box_ctx(SOURCE, |ctx| {
        let name = "probe_core_addresses";
        let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
        let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
        let mut core_calls = 0;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                assert!(
                    context.vec_address_only_call_for_test(func, args),
                    "genuine core pointer query"
                );
                assert!(!context.vec_shadow_memory_call_for_test(func));
                core_calls += 1;
            }
        }
        assert!(core_calls >= 3, "actual core addr/add/is_null calls must be retained");
        let name = "probe_forged_shadow_marker";
        let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
        let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
        let mut forged_calls = 0;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                assert_eq!(context.detect_kani_model(func), Some(KaniModel::IsPtrInitialized));
                assert!(
                    !context.vec_shadow_memory_call_for_test(func),
                    "local marker is not canonical"
                );
                assert!(!context.vec_address_only_call_for_test(func, args));
                forged_calls += 1;
            }
        }
        assert_eq!(forged_calls, 1);
    });
}

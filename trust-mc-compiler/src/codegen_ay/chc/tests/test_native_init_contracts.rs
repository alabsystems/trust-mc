// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Identity, receiver and ownership boundaries of native initialization.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::mir::{CastKind, Operand, Rvalue, StatementKind, TerminatorKind};

#[test]
fn maybe_memory_domain_uses_exposed_native_storage_not_opaque_capacity_nodes() {
    let source = r#"
        use core::mem::MaybeUninit;
        pub struct Wrapped {slot:MaybeUninit<bool>}
        pub fn exposed(_value:MaybeUninit<bool>,_reference:&MaybeUninit<bool>,_raw:*const MaybeUninit<bool>,_wrapped:Wrapped,_non_null:core::ptr::NonNull<MaybeUninit<bool>>,_vec:Vec<MaybeUninit<bool>>){}
        pub fn opaque(_tree:std::collections::BTreeMap<u32,u32>,_phantom:core::marker::PhantomData<MaybeUninit<bool>>){}
    "#;
    with_native_box_ctx(source, |ctx| {
        for (name, expected) in [("exposed", true), ("opaque", false)] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            for local in body.arg_locals() {
                assert_eq!(
                    crate::codegen_ay::shared::native_maybe_memory::native_maybe_memory_type(
                        ctx.tcx, local.ty
                    ),
                    expected,
                    "{name}: {:?}",
                    local.ty
                );
            }
        }
    });
}

#[test]
fn unrelated_native_raw_pointer_call_does_not_read_its_value_as_a_usize_count() {
    with_native_box_ctx(
        r#"pub fn pointer_write(){let mut value=0u32;let pointer=&mut value as *mut u32;unsafe{pointer.write(17u32)};assert!(value==17);}"#,
        |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "pointer_write").callee_body().unwrap();
            assert!(body.blocks.iter().any(|b|matches!(&b.terminator.kind,TerminatorKind::Call{args,..} if args.len()==2&&matches!(args[0].ty(body.locals()).unwrap().kind(),TyKind::RigidTy(RigidTy::RawPtr(..))))));
            let chc = ChcCtx::new(ctx.tcx, &body, "pointer_write", mem_config());
            assert!(chc.wrapping_step_defs().is_empty(), "ptr::write is not a wrapping step");
        },
    );
}

fn transformed(tcx: TyCtxt<'_>, name: &str, depth: usize) -> rustc_public::mir::Body {
    let abstraction = StdAbstraction::resolve(tcx);
    let instance = find_instance_by_suffix(tcx, name);
    FunctionInlinePass::new(InlineConfig {
        max_depth: depth,
        chc_native_box_drop: true,
        ..InlineConfig::default()
    })
    .transform_with_body_provider(tcx, instance.callee_body().unwrap(), instance, |callee| {
        if abstraction.abstracts_public_instance(tcx, callee) { None } else { callee.callee_body() }
    })
    .1
}

#[test]
fn native_init_rejects_erased_receivers_wrong_values_and_active_stubs() {
    let source = r#"
        pub fn contract() {
            let mut boxed=Box::<u32>::new_uninit(); boxed.write(17);
            let value=unsafe{boxed.assume_init()};assert!(*value==17);
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "contract");
        let TyKind::RigidTy(RigidTy::FnDef(marker, _)) = instance.ty().kind() else {
            panic!("native function")
        };
        for depth in [0, 32] {
            let original = transformed(ctx.tcx, "contract", depth);
            let pointer = original
                .blocks
                .iter()
                .flat_map(|b| &b.statements)
                .find_map(|s| {
                    matches!(
                        &s.kind,
                        StatementKind::Assign(_, Rvalue::Cast(CastKind::BoxDerefTransmute, ..))
                    )
                    .then(|| match &s.kind {
                        StatementKind::Assign(lhs, _) => Operand::Copy(lhs.clone()),
                        _ => unreachable!(),
                    })
                })
                .expect("actual native Box payload pointer");
            let write_site = original
                .blocks
                .iter()
                .position(|b| {
                    let TerminatorKind::Call { func, .. } = &b.terminator.kind else {
                        return false;
                    };
                    let Ok(ty) = func.ty(original.locals()) else {
                        return false;
                    };
                    let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(
                        def,
                        args,
                    )) = ty.kind()
                    else {
                        return false;
                    };
                    rustc_public::mir::mono::Instance::resolve(def, &args).is_ok_and(|i| {
                        crate::codegen_ay::native_maybe_uninit_write(ctx.tcx, &i).is_some()
                    })
                })
                .unwrap();
            for mode in ["erased_receiver", "wrong_payload", "active_stub"] {
                let mut body = original.clone();
                let _scope = (mode == "active_stub").then(|| {
                    crate::kani_middle::transform::UnitStubsTestScope::install(
                        std::collections::HashMap::from([(marker, marker)]),
                    )
                });
                if mode != "active_stub" {
                    let TerminatorKind::Call { args, .. } =
                        &mut body.blocks[write_site].terminator.kind
                    else {
                        unreachable!()
                    };
                    args[usize::from(mode == "wrong_payload")] = pointer.clone();
                }
                let (_, _, diagnostics) = ChcCtx::new(ctx.tcx, &body, "contract", mem_config())
                    .translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove("contract")
                    .unwrap_or_default();
                assert!(
                    reasons.contains_key("native_maybe_write_without_custody_or_valid_value"),
                    "{mode} depth{depth}: {reasons:?}"
                );
                assert!(
                    diagnostics.place_translation_drop.get() > 0,
                    "{mode} must refuse certification"
                );
            }
        }
    });
}

#[test]
fn native_init_does_not_capture_user_maybe_accessor_names_or_bodies() {
    let source = r#"
        struct MaybeUninit(bool);
        impl MaybeUninit {unsafe fn assume_init_read(&self)->bool{self.0}}
        pub fn lookalike_safe(){let v=unsafe{MaybeUninit(false).assume_init_read()};assert!(!v);}
        pub fn lookalike_bug(){let v=unsafe{MaybeUninit(false).assume_init_read()};assert!(v);}
    "#;
    with_native_box_ctx(source, |ctx| {
        let method = find_instance_by_suffix(ctx.tcx, "assume_init_read");
        assert!(!crate::codegen_ay::native_maybe_unsafe_accessor(ctx.tcx, &method));
        for depth in [0, 32] {
            for (name, expected) in [("lookalike_safe", "unsat"), ("lookalike_bug", "sat")] {
                let body = transformed(ctx.tcx, name, depth);
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name} {reasons:?}");
                assert_eq!(
                    run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30)
                        .as_deref(),
                    Ok(expected)
                );
            }
        }
    });
}

#[test]
fn native_init_never_blesses_a_custom_global_allocator() {
    let source = r#"
        struct Custom;
        unsafe impl std::alloc::GlobalAlloc for Custom {
            unsafe fn alloc(&self,l:std::alloc::Layout)->*mut u8{unsafe{std::alloc::GlobalAlloc::alloc(&std::alloc::System,l)}}
            unsafe fn dealloc(&self,p:*mut u8,l:std::alloc::Layout){unsafe{std::alloc::GlobalAlloc::dealloc(&std::alloc::System,p,l)}}
        }
        #[global_allocator] static CUSTOM:Custom=Custom;
        pub fn custom_allocator(){let mut boxed=Box::<bool>::new_uninit();boxed.write(true);let value=unsafe{boxed.assume_init()};assert!(*value);}
    "#;
    with_native_box_ctx(source, |ctx| {
        for depth in [0, 32] {
            for uninit_checks in [false, true] {
                let body = transformed(ctx.tcx, "custom_allocator", depth);
                let (_, _, diagnostics) = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    "custom_allocator",
                    ChcConfig { uninit_checks, ..mem_config() },
                )
                .translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove("custom_allocator")
                    .unwrap_or_default();
                assert!(
                    diagnostics.place_translation_drop.get() > 0,
                    "custom allocator is not Global allocation authority: {reasons:?}"
                );
                assert!(
                    reasons.contains_key("native_initialized_handoff_without_custody"),
                    "{reasons:?}"
                );
            }
        }
    });
}
